"""Distribution-boundary rejection checks; no change to mathematical inputs."""
import hashlib
import json
from pathlib import Path
import shutil
import tempfile
from check_release import check

ROOT = Path(__file__).resolve().parents[1]


def main():
    check(ROOT)
    outcomes = ['valid distribution accepted']
    with tempfile.TemporaryDirectory(prefix='heraclitus-package-tests-') as temp:
        base = Path(temp)
        entries = json.loads((ROOT/'release-manifest.json').read_text())['files']
        def copy(name):
            d=base/name;d.mkdir()
            for p in list(entries)+['release-manifest.json']:
                dest=d/p;dest.parent.mkdir(parents=True,exist_ok=True)
                shutil.copyfile(ROOT/p,dest)
            return d
        def rewrite(d, name, data):
            p=d/name;p.write_text(json.dumps(data))
            manifest=d/'release-manifest.json';r=json.loads(manifest.read_text())
            r['files'][name]={'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
            manifest.write_text(json.dumps(r))
        cases=[]
        d=copy('missing');(d/'formal/ResidueCoverage.lean').unlink();cases.append(('missing proof',d))
        d=copy('changed');(d/'formal/ResidueCoverage.lean').write_text('changed\n');cases.append(('changed proof',d))
        d=copy('extra');(d/'private-note.txt').write_text('unexpected');cases.append(('unlisted file',d))
        d=copy('unsafe');p=d/'release-manifest.json';r=json.loads(p.read_text());r['files']['../escape']={'bytes':0,'sha256':''};p.write_text(json.dumps(r));cases.append(('unsafe path',d))
        d=copy('symlink');p=d/'README.md';p.unlink();p.symlink_to(ROOT/'README.md');cases.append(('symlink',d))
        d=copy('binding');p=d/'formal/proof-manifest.json';r=json.loads(p.read_text());r['source_sha256']['formal/ResidueCoverage.lean']='0'*64;rewrite(d,'formal/proof-manifest.json',r);cases.append(('changed proof binding',d))
        d=copy('type-binding');p=d/'evidence/type-comparison.json';r=json.loads(p.read_text());r['selected_source_sha256']['ResidueCoverage.lean']='0'*64;rewrite(d,'evidence/type-comparison.json',r);cases.append(('changed type comparison binding',d))
        for name,d in cases:
            try:
                check(d)
            except (ValueError,FileNotFoundError):
                outcomes.append(name+' rejected')
            else:
                raise RuntimeError('Damaged package accepted: '+name)
        d=copy('build-output');(d/'build').mkdir();(d/'build/local.txt').write_text('permitted');check(d)
        outcomes.append('local build output accepted')
    print(json.dumps({'status':'PASS','checks':outcomes},indent=2))


if __name__=='__main__':
    main()
