"""Compile the editable manuscript in build/paper without overwriting release files."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--engine', default='pdflatex')
    p.add_argument('--output', type=Path, default=Path('build/paper'))
    args = p.parse_args()
    out = args.output.resolve()
    if ROOT / 'build' not in out.parents or out.exists():
        raise ValueError('Use a new directory under the package build/')
    out.mkdir(parents=True)
    shutil.copyfile(ROOT / 'paper/heraclitus-coverage.tex', out / 'heraclitus-coverage.tex')
    for n in range(1,4):
        r = subprocess.run([args.engine, '-interaction=nonstopmode', '-halt-on-error',
                            '-file-line-error', 'heraclitus-coverage.tex'], cwd=out,
                           capture_output=True, text=True)
        (out / f'pass-{n}.txt').write_text(r.stdout+r.stderr)
        if r.returncode:
            raise RuntimeError('TeX failed: ' + str(out / f'pass-{n}.txt'))
    log = (out / 'heraclitus-coverage.log').read_text()
    errors = [s for s in ['Overfull', 'Missing character:', 'undefined references',
                          'undefined citations', 'Rerun to get cross-references right'] if s in log]
    if errors:
        raise RuntimeError('TeX review required: ' + repr(errors))
    subprocess.run(['pdftotext', '-layout', str(out/'heraclitus-coverage.pdf'),
                    str(out/'heraclitus-coverage.txt')], check=True)
    print(json.dumps({'status': 'PASS: source compilation and log checks; visual review separate',
                      'pdf': str(out/'heraclitus-coverage.pdf')}))


if __name__ == '__main__':
    main()
