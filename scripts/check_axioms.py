"""Build the project and check every request in Verification/Axioms.lean.

Requires Python 3.11 or later and Lake on PATH. Complete command output and a
JSON report are saved beneath --output (default: .verification).
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = frozenset({'propext', 'Classical.choice', 'Quot.sound'})
CONFIGS = ('principals', 'real-support', 'hermite-support', 'complex-support')
EXPECTED_CONFIG_COUNTS = (12, 646, 199, 922)
AXIOM_PATTERN = re.compile(
    r"^'(?P<name>[^\r\n]+)'[ \t]+(?:depends on axioms:\s*\[(?P<axioms>[^\]]*)\]"
    r"|does not depend on any axioms)[ \t]*\r?$", re.MULTILINE)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def requested_names(source: str) -> list[str]:
    names = []
    for line in source.splitlines():
        if line.lstrip().startswith('#print'):
            match = re.fullmatch(r'\s*#print\s+axioms\s+(\S+)\s*', line)
            require(match is not None, 'Malformed axiom request: ' + line)
            names.append(match.group(1))
    require(bool(names), 'The static audit has no axiom requests')
    require(len(names) == len(set(names)), 'The static audit repeats a declaration')
    return names


def parse_axioms(output: str, expected: list[str]) -> dict[str, list[str]]:
    require(len(expected) == len(set(expected)), 'Expected declarations are not unique')
    found = {}
    for match in AXIOM_PATTERN.finditer(output):
        name = match.group('name')
        require(name not in found, 'Duplicate axiom output: ' + name)
        raw = match.group('axioms')
        axioms = [item.strip() for item in raw.split(',')] if raw and raw.strip() else []
        require(len(axioms) == len(set(axioms)), 'Duplicate axiom in output: ' + name)
        forbidden = set(axioms) - ALLOWED_AXIOMS
        require(not forbidden, 'Disallowed axioms for ' + name + ': ' + ', '.join(sorted(forbidden)))
        found[name] = axioms
    remainder = AXIOM_PATTERN.sub('', output)
    require(not re.search(r'depends on axioms|does not depend on any axioms', remainder),
            'An axiom-output record could not be parsed')
    missing, extra = set(expected) - set(found), set(found) - set(expected)
    require(not missing and not extra, 'Axiom inventory mismatch; missing: ' + ', '.join(sorted(missing))
            + '; extra: ' + ', '.join(sorted(extra)))
    return found


def inspect_inputs() -> tuple[list[str], set[str], dict]:
    names = requested_names((ROOT / 'Verification/Axioms.lean').read_text(encoding='utf-8-sig'))
    require(len(names) == 1202, 'Expected 1202 explicit axiom requests in Verification/Axioms.lean')
    targets, configs = set(), {}
    for label, count in zip(CONFIGS, EXPECTED_CONFIG_COUNTS):
        relative = 'Verification/' + label + '.json'
        config = json.loads((ROOT / relative).read_text(encoding='utf-8-sig'))
        listed = config['theorem_names']
        require(isinstance(listed, list) and all(isinstance(n, str) and n for n in listed), relative + ': invalid theorem list')
        require(len(listed) == len(set(listed)) == count, relative + ': incorrect or repeated theorem targets')
        require(config['definition_names'] == [], relative + ': definition targets must be empty')
        require(isinstance(config['permitted_axioms'], list) and len(config['permitted_axioms']) == 3
                and set(config['permitted_axioms']) == ALLOWED_AXIOMS, relative + ': incorrect axiom allowlist')
        require(config['enable_nanoda'] is False, relative + ': enable_nanoda must be false')
        require(config['solution_module'] == 'All', relative + ': solution_module must be All')
        targets.update(listed)
        configs[label] = {'path': relative, 'theorem_count': len(listed), 'theorem_names': listed}
    require(len(targets) == 1058, 'Expected 1058 distinct configured theorem targets')
    require(targets <= set(names), 'Configured theorem targets missing from the static axiom audit: '
            + ', '.join(sorted(targets - set(names))))
    return names, targets, configs


def inspect_packages() -> list[dict]:
    require((ROOT / 'lean-toolchain').read_text(encoding='utf-8').strip() == 'leanprover/lean4:v4.33.1',
            'The project toolchain must be Lean 4.33.1')
    packages = json.loads((ROOT / 'lake-manifest.json').read_text(encoding='utf-8-sig'))['packages']
    require(len(packages) == 9 and len({p['name'] for p in packages}) == 9,
            'The lockfile must contain nine distinct public dependencies')
    require(all(p['type'] == 'git' and re.fullmatch(r'[0-9a-f]{40}', p['rev']) for p in packages),
            'Every locked dependency must have a fixed Git revision')
    mathlib = [p for p in packages if p['name'] == 'mathlib']
    require(len(mathlib) == 1 and mathlib[0]['rev'] == '0df444a360eaa60ab8c11dca51a86af692955474'
            and mathlib[0]['url'] == 'https://github.com/leanprover-community/mathlib4.git',
            'The Mathlib lockfile revision does not match this release')
    return [{'name': p['name'], 'url': p['url'], 'rev': p['rev']} for p in packages]


def input_hashes(output_dir: Path) -> dict[str, str]:
    paths = {'lean-toolchain', 'lake-manifest.json', 'lakefile.toml', 'scripts/check_axioms.py'}
    paths.update('Verification/' + name + '.json' for name in CONFIGS)
    excluded_output = output_dir.resolve()
    for directory, subdirectories, filenames in os.walk(ROOT, followlinks=False):
        subdirectories[:] = sorted(d for d in subdirectories if d not in {'.lake', '.git', '.verification'}
            and not (Path(directory) / d).resolve().is_relative_to(excluded_output))
        for filename in filenames:
            if filename.endswith('.lean'):
                paths.add((Path(directory) / filename).relative_to(ROOT).as_posix())
    return {path: sha256(ROOT / path) for path in sorted(paths)}


def portable_error(error: Exception, output_dir: Path) -> str:
    message = str(error)
    for path, label in ((output_dir, '<report directory>'), (ROOT, '.')):
        for spelling in (str(path).replace('\\', '\\\\'), str(path)):
            message = message.replace(spelling, label)
    return message


def run_command(command: list[str], output_dir: Path, name: str, report: dict) -> str:
    filename = name + '.log'
    started = time.monotonic()
    record = {'command': command, 'cwd': '.', 'output_file': filename}
    report['runs'].append(record)
    try:
        with (output_dir / filename).open('xb') as stream:
            completed = subprocess.run(command, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT, check=False)
        record['exit_code'] = completed.returncode
    except OSError as error:
        record.update(error=portable_error(error, output_dir), exit_code=None)
        raise RuntimeError('Could not start ' + command[0] + ': ' + str(error)) from error
    finally:
        record['elapsed_seconds'] = time.monotonic() - started
        if (output_dir / filename).is_file():
            record['output_sha256'] = sha256(output_dir / filename)
    require(completed.returncode == 0, 'Command exited with status ' + str(completed.returncode) + ': ' + ' '.join(command))
    return (output_dir / filename).read_text(encoding='utf-8', errors='replace')


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('.verification'),
                        help='parent directory for a new timestamped run; relative paths use the repository root')
    args = parser.parse_args(argv)
    if sys.version_info < (3, 11):
        print('Python 3.11 or later is required.', file=sys.stderr)
        return 2
    output_base = args.output if args.output.is_absolute() else ROOT / args.output
    output_dir = output_base / ('axioms-' + str(time.time_ns()))
    try:
        output_dir.mkdir(parents=True, exist_ok=False)
    except OSError as error:
        print('Could not create the output directory: ' + str(error), file=sys.stderr)
        return 2
    report = {'complete': False, 'scope': 'Build and explicit axiom-dependency check',
              'allowed_axioms': sorted(ALLOWED_AXIOMS), 'runs': [],
              'output_paths_relative_to': 'report directory', 'command_cwd': 'repository root'}
    exit_code = 1
    try:
        names, targets, configs = inspect_inputs()
        packages = inspect_packages()
        hashes = input_hashes(output_dir)
        report.update(requested_declaration_count=len(names), configured_theorem_count=len(targets),
                      additional_audited_declaration_count=len(set(names)-targets), configurations=configs,
                      requested_names=names, input_sha256=hashes, packages=packages,
                      lean_source_file_count=sum(path.endswith(".lean") for path in hashes))
        require(shutil.which('lake') is not None, 'Lake was not found on PATH. Install elan and use the pinned lean-toolchain.')
        print('Running lake env lean --version', flush=True)
        version = run_command(['lake', 'env', 'lean', '--version'], output_dir, '00-version', report)
        require(re.search(r'\bversion 4\.33\.1(?:,|\s)', version) is not None
                and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version,
                'The actual Lean executable must be version 4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6')
        report['lean_version'] = '4.33.1'
        report['lean_commit'] = '819816b2e0a3bf405af45ae5c7af2491d8f5bee6'
        print('Running lake build', flush=True)
        run_command(['lake', 'build'], output_dir, '01-build', report)
        print('Running lake env lean Verification/Axioms.lean', flush=True)
        output = run_command(['lake', 'env', 'lean', 'Verification/Axioms.lean'], output_dir, '02-axioms', report)
        axioms = parse_axioms(output, names)
        require(input_hashes(output_dir) == hashes, 'The repository Lean sources or audit inputs changed during checking')
        report.update(axioms=axioms, actual_declaration_count=len(axioms),
                      actual_axiom_union=sorted({a for values in axioms.values() for a in values}),
                      inputs_unchanged=True, complete=True)
        exit_code = 0
    except (ValueError, KeyError, TypeError, OSError, RuntimeError) as error:
        report['error'] = portable_error(error, output_dir)
        print('Check failed: ' + str(error), file=sys.stderr)
    finally:
        with (output_dir / 'report.json').open('x', encoding='utf-8') as stream:
            json.dump(report, stream, indent=2); stream.write('\n')
        try:
            display = output_dir.relative_to(ROOT).as_posix() + '/report.json'
        except ValueError:
            display = output_dir.name + '/report.json (under --output)'
        print('Report: ' + display, flush=True)
    if exit_code == 0:
        print(f'Checked {len(names)} declarations, including all {len(targets)} configured theorem targets.', flush=True)
    return exit_code


if __name__ == '__main__':
    raise SystemExit(main())
