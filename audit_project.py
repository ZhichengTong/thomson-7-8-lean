"""Audit source, final compile records and theorem dependency report."""
from pathlib import Path
import hashlib, json, re, sys

ROOT = Path(__file__).resolve().parent
VERIFY = ROOT / 'verification'

def strip_lean(text):
    result, depth, index = [], 0, 0
    while index < len(text):
        if text.startswith('/-', index):
            depth += 1
            index += 2
        elif depth and text.startswith('-/', index):
            depth -= 1
            index += 2
        elif depth:
            if text[index] == '\n': result.append('\n')
            index += 1
        elif text.startswith('--', index):
            stop = text.find('\n', index)
            index = len(text) if stop < 0 else stop
        elif text[index] == '"':
            index += 1
            while index < len(text):
                if text[index] == '\\': index += 2
                elif text[index] == '"':
                    index += 1
                    break
                else: index += 1
            result.append(' ')
        else:
            result.append(text[index])
            index += 1
    return ''.join(result)

sources = [ROOT / 'Thomson78.lean'] + sorted((ROOT / 'Thomson78').glob('*.lean'))
failures, entries = [], []
build_file = VERIFY / 'final_build.json'
build_records = {r['module']: r for r in json.loads(build_file.read_text(encoding='utf-8'))} if build_file.exists() else {}
for source in sources:
    raw = source.read_text(encoding='utf-8-sig')
    clean = strip_lean(raw)
    forbidden = re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide|ofReduceBool)\b', clean)
    if forbidden: failures.append(f'{source.name}: forbidden tokens {forbidden}')
    imports = re.findall(r'^\s*import\s+([\w.]+)', clean, re.M)
    if any(not (name == 'Thomson78' or name.startswith(('Thomson78.', 'Mathlib.', 'Lean.'))) for name in imports):
        failures.append(f'{source.name}: unexpected imports {imports}')
    module = '.'.join(source.relative_to(ROOT).with_suffix('').parts)
    record = build_records.get(module)
    digest = hashlib.sha256(source.read_bytes()).hexdigest()
    if not record or record['exit_code'] != 0 or record['source_sha256'] != digest:
        failures.append(f'{module}: missing successful final build record for this source hash')
    log = VERIFY / (module.replace('.', '_') + '.log')
    if not log.exists():
        failures.append(f'{module}: missing compile log')
    else:
        output = log.read_text(encoding='utf-8')
        if re.search(r'error(?:\(|:)|sorryAx|unsolved goals|Unexpected axiom', output):
            failures.append(f'{module}: non-passing compile log')
    entries.append(dict(path=source.relative_to(ROOT).as_posix(),
        sha256=digest, lines=len(raw.splitlines())))

audit_log = VERIFY / 'Thomson78_Audit.log'
text = audit_log.read_text(encoding='utf-8') if audit_log.exists() else ''
result = re.search(r'AUDIT_OK: (\d+) project theorems;', text)
if not result: failures.append('Final namespace axiom audit is absent or failed')

report = dict(status='PASS' if not failures else 'FAIL',
    lean_version='4.35.0', mathlib_version='v4.35.0',
    module_count=len(sources), source_lines=sum(e['lines'] for e in entries),
    checked_theorem_declarations_including_generated=int(result[1]) if result else 0,
    allowed_axioms=['propext', 'Classical.choice', 'Quot.sound'],
    sources=entries, failures=failures)
(VERIFY / 'source_audit.json').write_text(json.dumps(report, ensure_ascii=False, indent=2), encoding='utf-8')
print(json.dumps({k:v for k,v in report.items() if k != 'sources'}, ensure_ascii=False, indent=2))
sys.exit(0 if not failures else 1)
