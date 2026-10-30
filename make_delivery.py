"""Prepare the source-only delivery after the final build and audit pass."""
from pathlib import Path
import hashlib, json, shutil

ROOT = Path(__file__).resolve().parent
DEST = ROOT / 'delivery'
report = json.loads((ROOT / 'verification/source_audit.json').read_text(encoding='utf-8'))
if report['status'] != 'PASS':
    raise SystemExit('A passing source audit is required')

selected = [ROOT / e['path'] for e in report['sources']]
selected += [ROOT / name for name in ('README.txt', 'lean-toolchain', 'lakefile.toml',
    'compile.py', 'audit_project.py', 'make_delivery.py')]
selected += [ROOT / 'verification' / name for name in (
    'final_build.json', 'source_audit.json', 'trust_boundary_final.txt',
    'manuscript_coverage_final.txt', 'manuscript_sources.json', 'environment.json',
    'mathlib-source-provenance.json', 'dependency-source-provenance.json')]
for entry in report['sources']:
    module = '.'.join(Path(entry['path']).with_suffix('').parts)
    selected.append(ROOT / 'verification' / (module.replace('.', '_') + '.log'))

manifest = []
for source in selected:
    relative = source.relative_to(ROOT)
    target = DEST / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, target)
    digest = hashlib.sha256(source.read_bytes()).hexdigest()
    if hashlib.sha256(target.read_bytes()).hexdigest() != digest:
        raise SystemExit('Copy verification failed: ' + str(relative))
    manifest.append(dict(path=relative.as_posix(), sha256=digest, bytes=target.stat().st_size))
(DEST / 'verification/delivery_manifest.json').write_text(
    json.dumps(manifest, ensure_ascii=False, indent=2), encoding='utf-8')
print(json.dumps(dict(destination=str(DEST), files=len(manifest)+1,
    bytes=sum(r['bytes'] for r in manifest)), ensure_ascii=False, indent=2))
