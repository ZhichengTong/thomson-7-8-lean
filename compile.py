"""Compile this project; reuse local pinned dependencies read-only.

Usage: python compile.py Thomson78/Seven.lean
Missing dependency artifacts are compiled from their source into this project's
build directory. No source or build artifact in an external project is modified.
"""
from pathlib import Path
import argparse, hashlib, json, os, re, shutil, subprocess, sys, time

ROOT = Path(__file__).resolve().parent
PACKAGES = Path(os.environ.get('THOMSON_MATHLIB_PACKAGES', r'F:\Smale5Formalization-v16\.lake\packages'))
LEAN = Path(os.environ.get('THOMSON_LEAN', r'F:\Lean\.elan\toolchains\leanprover--lean4---v4.35.0\bin\lean.exe'))
BUILD = ROOT / '.lake/build/lib/lean'
LOGS = ROOT / 'verification'
BUILD.mkdir(parents=True, exist_ok=True)
LOGS.mkdir(exist_ok=True)
sources = [ROOT] + list(PACKAGES.iterdir())
paths = [BUILD] + [p / '.lake/build/lib/lean' for p in sources[1:]]
env = os.environ.copy()
env['LEAN_PATH'] = os.pathsep.join(str(p) for p in paths)
env['LEAN_NUM_THREADS'] = '1'
env['PATH'] = str(LEAN.parent) + os.pathsep + env.get('PATH', '')

def imports(source):
    text = source.read_text(encoding='utf-8-sig')
    clean = []
    depth = 0
    i = 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            if text[i] == '\n': clean.append('\n')
            i += 1
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end == -1 else end
        else:
            clean.append(text[i])
            i += 1
    text = ''.join(clean)
    # Imports in this project and mathlib occur on one line each.
    return re.findall(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)', text, re.M)

def locate(module):
    relative = Path(*module.split('.')).with_suffix('.lean')
    for base in sources:
        if (base / relative).is_file():
            return base, relative
    return None

def compiled(module):
    relative = Path(*module.split('.')).with_suffix('.olean')
    return any((p / relative).is_file() for p in paths)

seen = set()
records = []
rebuild_own = False
def build(module, force=False):
    if module in seen:
        return
    location = locate(module)
    if location is None:
        return  # Lean's standard library is resolved by LEAN_SYSROOT.
    base, relative = location
    source = base / relative
    own = base == ROOT
    for dependency in imports(source):
        build(dependency)
    output = BUILD / relative.with_suffix('.olean')
    if not own:
        cached = base / '.lake/build/lib/lean' / relative.with_suffix('.olean')
        if cached.exists():
            output.parent.mkdir(parents=True, exist_ok=True)
            for suffix in ('.olean', '.olean.private', '.olean.server', '.ir', '.ir.sig'):
                src = cached.with_suffix(suffix)
                dst = output.with_suffix(suffix)
                if src.exists() and (not dst.exists() or src.stat().st_size != dst.stat().st_size):
                    temporary = dst.with_name(dst.name + '.' + str(os.getpid()) + '.tmp')
                    shutil.copy2(src, temporary)
                    os.replace(temporary, dst)
            seen.add(module)
            return
        if output.exists():
            seen.add(module)
            return
    if own and not force and not rebuild_own and output.exists() and output.stat().st_mtime >= source.stat().st_mtime:
        seen.add(module)
        return
    output.parent.mkdir(parents=True, exist_ok=True)
    command = [str(LEAN), '-j1', '-M8000', '-o', str(output), str(relative)]
    print('Compiling ' + module, flush=True)
    start = time.monotonic()
    result = subprocess.run(command, cwd=base, env=env, capture_output=True, text=True, encoding='utf-8', errors='replace')
    log = LOGS / (module.replace('.', '_') + '.log')
    log.write_text(result.stdout + result.stderr, encoding='utf-8')
    record = dict(module=module, source=str(source), source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(), exit_code=result.returncode, seconds=round(time.monotonic()-start, 3), log=str(log.relative_to(ROOT)))
    records.append(record)
    print(f'{module}: {result.returncode} ({record["seconds"]}s)', flush=True)
    if result.stdout or result.stderr:
        message = result.stdout + result.stderr
        if len(message) > 8000:
            print('[Full output saved to ' + str(log) + ']\n' + message[-3000:], flush=True)
        else:
            print(message, flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)
    seen.add(module)

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--rebuild-own', action='store_true', help='Recheck every project module from source')
    parser.add_argument('--report', help='Write the successful build records to this JSON path')
    parser.add_argument('files', nargs='+')
    args = parser.parse_args()
    rebuild_own = args.rebuild_own
    for name in args.files:
        module = name.removesuffix('.lean').replace('\\', '.').replace('/', '.')
        build(module, force=True)
    report = Path(args.report) if args.report else LOGS / ('build_' + str(os.getpid()) + '.json')
    report.write_text(json.dumps(records, ensure_ascii=False, indent=2), encoding='utf-8')
