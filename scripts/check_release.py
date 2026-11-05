"""Check exact package bytes, independently of mathematical validity."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath


def check(root):
    root = Path(root).resolve()
    manifest = json.loads((root / 'release-manifest.json').read_text())
    if manifest.get('schema_version') != 1 or manifest.get('stage') not in {'build-input', 'release-candidate'}:
        raise ValueError('Unknown package inventory format')
    entries = manifest['files']
    required = {'README.md', 'VERSION', 'CITATION.cff', 'LICENSE', 'EXPORT_PROVENANCE.json',
                'formal/proof-manifest.json', 'formal/lean-toolchain', 'paper/heraclitus-coverage.tex',
                'docs/REVIEW_GUIDE.md', 'scripts/verify_lean.py', 'scripts/check_entrance.py'}
    if not required <= set(entries):
        raise ValueError('Missing required components')
    if manifest['stage'] == 'release-candidate':
        if not {'paper/heraclitus-coverage.pdf', 'evidence/combined/run.json',
                'evidence/pdf-review.json'} <= set(entries):
            raise ValueError('Release candidate lacks PDF/reproduction evidence')
    for name, expected in entries.items():
        p = PurePosixPath(name)
        if p.is_absolute() or '..' in p.parts or str(p) != name:
            raise ValueError('Unsafe inventory path: ' + name)
        target = root / name
        if target.is_symlink() or root not in target.resolve().parents:
            raise ValueError('Nonlocal inventory entry: ' + name)
        data = target.read_bytes()
        if {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()} != expected:
            raise ValueError('Changed package file: ' + name)
    actual = set()
    for p in root.rglob('*'):
        rel = p.relative_to(root)
        if rel.parts[0] in {'.git', 'build'} or '__pycache__' in rel.parts:
            continue
        if p.is_symlink():
            raise ValueError('Unexpected symlink')
        if p.is_file() and p.name != '.DS_Store':
            actual.add(rel.as_posix())
    if actual != set(entries) | {'release-manifest.json'}:
        raise ValueError('Unexpected or missing files: ' + repr(sorted(actual ^ (set(entries) | {'release-manifest.json'}))))
    proof = json.loads((root / 'formal/proof-manifest.json').read_text())
    for p, h in proof['source_sha256'].items():
        if entries[p]['sha256'] != h:
            raise ValueError('Accepted proof source mismatch: ' + p)
    comparison = json.loads((root / 'evidence/type-comparison.json').read_text())
    if comparison['status'] != 'PASS' or comparison['selected_source_sha256'] != {
        p.split('/')[-1]: h for p,h in proof['source_sha256'].items() if '/negative/' not in p}:
        raise ValueError('Declaration type comparison mismatch')
    receipt = root / 'evidence/combined/run.json'
    if receipt.exists():
        r = json.loads(receipt.read_text())
        if r['status'] != 'PASS' or r['source_sha256'] != proof['source_sha256'] or r['axiom_audits'] != proof['expected_axioms']:
            raise ValueError('Combined receipt mismatch')
        if r['modules'] != len(proof['modules']) or r['mathematical_rejections'] != len(proof['fixtures']):
            raise ValueError('Combined scope mismatch')
        if r['runner_sha256'] != entries['scripts/verify_lean.py']['sha256']:
            raise ValueError('Runner differs from reproduced version')
        if r['proof_manifest_sha256'] != entries['formal/proof-manifest.json']['sha256']:
            raise ValueError('Proof manifest differs from reproduced version')
        review=json.loads((root/'evidence/pdf-review.json').read_text())
        if review['status']!='PASS' or review['pdf_sha256']!=entries['paper/heraclitus-coverage.pdf']['sha256'] or review['source_sha256']!=entries['paper/heraclitus-coverage.tex']['sha256']:
            raise ValueError('PDF review mismatch')
    return len(entries)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    print(f'PASS: {check(args.root)} package files; byte integrity, not a proof check')
