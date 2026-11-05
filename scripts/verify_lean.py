"""Rebuild every shipped proof module and audit the recorded theorem set."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', type=Path, required=True, help='Lean 4.35.0 binary')
    parser.add_argument('--output', type=Path, default=Path('build/lean'))
    args = parser.parse_args()
    require(__debug__, 'Optimized Python is not supported')
    out = args.output.resolve()
    require(ROOT / 'build' in out.parents and not out.exists(),
            'Use a new output directory under this package build/')
    manifest = json.loads((ROOT / 'formal/proof-manifest.json').read_text())
    before = {p: sha(ROOT / p) for p in manifest['source_sha256']}
    require(before == manifest['source_sha256'], 'Proof input differs from accepted sources')
    out.mkdir(parents=True)
    compiled = out / 'compiled'
    compiled.mkdir()
    env = dict(os.environ, LEAN_PATH=str(compiled))
    env.pop('LEAN_SYSROOT', None)
    env.pop('LEAN_SRC_PATH', None)
    lean = args.lean.resolve()
    report = {'status': 'RUNNING', 'started_utc': datetime.now(timezone.utc).isoformat(),
              'source_sha256': before, 'commands': [],
              'scope': 'Fresh relocated combined build; pinned Lean binary and bundled Std trusted. Not independent human review.'}
    audits = {}

    def run(label, command, reject=False):
        p = subprocess.run(command, cwd=ROOT, env=env, capture_output=True, text=True)
        log = p.stdout + p.stderr
        (out / (label + '.txt')).write_text(log)
        report['commands'].append({'label': label, 'command': command, 'exit_code': p.returncode,
                                   'expected_rejection': reject,
                                   'log_sha256': hashlib.sha256(log.encode()).hexdigest()})
        if reject:
            require(p.returncode != 0 and log.count('error:') == 1 and
                    'Tactic `decide` proved that the proposition' in log and 'is false' in log,
                    'Wrong rejection: ' + label + '\n' + log)
            require(not any(s in log for s in ['unknown identifier', 'unknown module',
                    'unexpected token', 'failed to synthesize']), 'Malformed fixture: ' + label)
        else:
            require(p.returncode == 0, 'Command failed: ' + label + '\n' + log)
        return log

    try:
        version = run('version', [str(lean), '--version']).strip()
        require(version.startswith('Lean (version 4.35.0,'), 'Wrong Lean version')
        require((ROOT / 'formal/lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0',
                'Toolchain pin changed')
        prefix = run('prefix', [str(lean), '--print-prefix']).strip()
        report.update(lean_version=version, lean_binary_sha256=sha(lean), standard_library_prefix=prefix)
        for item in manifest['modules']:
            path = ROOT / item['path']
            text = path.read_text()
            require(re.findall(r'^import (\S+)$', text, re.M) == item['imports'], 'Import changed')
            require(not re.search(r'\b(sorry|admit|axiom|unsafe|implemented_by|native_decide)\b', text),
                    'Forbidden proof token: ' + str(path))
            log = run('build-' + item['module'], [str(lean), '-R', str(path.parent),
                      '-DwarningAsError=true', str(path), '-o', str(compiled / (item['module'] + '.olean'))])
            current = {n: [a.strip() for a in xs.split(',') if a.strip()] for n, xs in
                       re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", log)}
            current.update({n: [] for n in re.findall(r"'([^']+)' does not depend on any axioms", log)})
            expected = set(re.findall(r'^#print axioms (\S+)$', text, re.M))
            require(set(current) == expected, 'Incomplete audit output: ' + item['module'])
            for n, ax in current.items():
                require(set(ax) <= {'propext', 'Classical.choice', 'Quot.sound'}, 'Unexpected axiom: ' + n)
                require(n not in audits or audits[n] == ax, 'Inconsistent audit: ' + n)
                audits[n] = ax
            print('built ' + item['module'], flush=True)
        require(audits == manifest['expected_axioms'], 'Combined audit differs from accepted declarations')
        for item in manifest['fixtures']:
            path = ROOT / item['path']
            run('reject-' + item['id'], [str(lean), '-R', str(path.parent),
                '-DwarningAsError=true', str(path)], reject=True)
        require(before == {p: sha(ROOT / p) for p in before}, 'Proof sources changed during execution')
        report.update(status='PASS', modules=len(manifest['modules']), axiom_audits=audits,
                      mathematical_rejections=len(manifest['fixtures']),
                      proof_manifest_sha256=sha(ROOT / 'formal/proof-manifest.json'),
                      runner_sha256=sha(Path(__file__)),
                      compiled_sha256={p.name: sha(p) for p in sorted(compiled.iterdir())})
    except Exception as error:
        report.update(status='FAIL', error=str(error))
        raise
    finally:
        report['finished_utc'] = datetime.now(timezone.utc).isoformat()
        (out / 'run.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in ['status', 'modules', 'mathematical_rejections', 'finished_utc']}))


if __name__ == '__main__':
    main()
