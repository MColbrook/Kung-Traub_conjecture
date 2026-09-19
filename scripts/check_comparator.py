#!/usr/bin/env python3
"""Compare the theorem statements in fresh, isolated Linux workspaces."""

from __future__ import annotations

import argparse
import errno
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import socket
import stat
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
TOOLCHAIN = "leanprover/lean4:v4.33.1"
LEAN_COMMIT = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
REVISIONS = {
    "comparator": "3927ad383f208ae977c340a91c48ac9b497d2097",
    "lean4export": "15f6055e299ad5b89345e533cc2192f4cc00f659",
    "landrun": "811cfff51ceaf3d9843708aa6d22e9b84ccac8b4",
}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
CASES = {
    "principals": ("Challenge", 12),
    "real-support": ("support_reference.SupportChallenge", 646),
    "hermite-support": ("appendix_reference.SupportChallenge", 199),
    "complex-support": ("appendix_b_reference.SupportChallenge", 922),
}
PUBLIC_EXPORTS = [
    "Nat.add", "Nat.sub",
    "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod", "Nat.beq",
    "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft",
    "Nat.shiftRight", "String.ofList", "Char.ofNat", "List", "eagerReduce",
]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def digest(path: Path) -> str:
    require(stat.S_ISREG(path.lstat().st_mode), f"Expected a regular file: {path}")
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def read_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8-sig"))


def write_json(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def linux_user() -> None:
    require(sys.version_info >= (3, 11), "Python 3.11 or later is required")
    require(sys.platform == "linux", "Comparator checking requires Linux")
    require(os.getuid() != 0, "Run as an unprivileged user")


def safe_path(path: Path) -> Path:
    path = Path(os.path.abspath(path.expanduser()))
    for item in (path, *path.parents):
        require(not item.is_symlink(), f"Symlink boundary is not permitted: {item}")
    return path


def clean_environment(leanbin: Path | None = None) -> dict[str, str]:
    env = {k: v for k, v in os.environ.items()
           if not k.startswith(("LEAN_", "LAKE_", "COMPARATOR_", "LD_", "DYLD_", "GIT_"))}
    if leanbin is not None:
        env["PATH"] = str(leanbin) + ":/usr/local/bin:/usr/bin:/bin"
    env["GIT_CONFIG_NOSYSTEM"] = "1"
    env["GIT_CONFIG_GLOBAL"] = "/dev/null"
    return env


def capture(command: list[str], cwd: Path, env=None) -> str:
    proc = subprocess.run(command, cwd=cwd, env=env, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    require(proc.returncode == 0, f"Command failed: {command}\n{proc.stdout}")
    return proc.stdout


def files_under(root: Path, excluded: set[str] | None = None,
                allowed_links: dict | None = None):
    excluded = excluded or set()
    allowed_links = allowed_links or {}
    pending = [safe_path(root)]
    while pending:
        directory = pending.pop()
        for path in sorted(directory.iterdir()):
            relative = path.relative_to(root).as_posix()
            if path.is_symlink():
                require(relative in allowed_links, f"Unapproved symlink in input tree: {path}")
                expected = allowed_links[relative]
                require(os.readlink(path) == expected["target"], f"Changed symlink target: {path}")
                target = safe_path(path.parent / expected["target"])
                require(target.is_file() and digest(target) == expected["target_sha256"],
                        f"Changed symlink destination: {path}")
                yield path
                continue
            require(relative not in allowed_links, f"Pinned symlink replaced by a regular entry: {path}")
            if path.name in excluded:
                continue
            mode = path.lstat().st_mode
            if stat.S_ISDIR(mode):
                pending.append(path)
            else:
                require(stat.S_ISREG(mode), f"Special file in input tree: {path}")
                yield path


def link_hash(record: dict) -> dict:
    target = record["target"]
    return {"type": "symlink", "target": target,
            "sha256": hashlib.sha256(target.encode("utf-8")).hexdigest()}


def tree_hashes(root: Path, excluded: set[str] | None = None,
                allowed_links: dict | None = None) -> dict:
    links = allowed_links or {}
    return {p.relative_to(root).as_posix():
            link_hash(links[p.relative_to(root).as_posix()]) if p.is_symlink() else digest(p)
            for p in files_under(root, excluded, links)}


def source_files(root: Path) -> dict[str, str]:
    paths = [root / name for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain")]
    paths += list(root.glob("*.lean"))
    for name in ("KungTraub", "KungTraubAppendices", "Verification/References"):
        paths += [p for p in files_under(root / name) if p.suffix == ".lean"]
    paths += [root / "Verification" / (name + ".json") for name in CASES]
    return {p.relative_to(root).as_posix(): digest(p) for p in sorted(paths)}


def isolation_checks() -> dict:
    result = {}
    for label, family in (("unix", socket.AF_UNIX), ("ipv4", socket.AF_INET)):
        try:
            with socket.socket(family, socket.SOCK_STREAM) as probe:
                probe.settimeout(1)
                if family == socket.AF_INET:
                    probe.connect(("192.0.2.1", 9))
            result[label] = {"operation_succeeded": True}
        except OSError as exc:
            result[label] = {"errno": exc.errno, "message": str(exc)}
    require(result["unix"].get("errno") == errno.EAFNOSUPPORT,
            "AF_UNIX must be disabled by the calling service")
    require(result["ipv4"].get("errno") == errno.ENETUNREACH,
            "Run in a private network namespace with no external IPv4 route")
    return result


def checked_configs(root: Path) -> dict:
    configs = {}
    for name, (challenge, count) in CASES.items():
        config = read_json(root / "Verification" / (name + ".json"))
        require(set(config) == {"challenge_module", "solution_module", "theorem_names",
                               "definition_names", "permitted_axioms", "enable_nanoda"},
                f"Unexpected configuration fields: {name}")
        targets = config["theorem_names"]
        require(isinstance(targets, list) and all(isinstance(t, str) for t in targets), name)
        require(len(targets) == len(set(targets)) == count, f"Wrong target inventory: {name}")
        require(config["challenge_module"] == challenge and config["solution_module"] == "All",
                f"Wrong comparison modules: {name}")
        require(config["definition_names"] == [], f"Definition holes are not permitted: {name}")
        require(len(config["permitted_axioms"]) == 3 and set(config["permitted_axioms"]) == ALLOWED,
                f"Wrong axiom policy: {name}")
        require(config["enable_nanoda"] is False, f"The Lean default kernel is required: {name}")
        configs[name] = config
    require(len({n for c in configs.values() for n in c["theorem_names"]}) == 1058,
            "The combined comparison inventory must contain 1058 distinct theorems")
    return configs


def check_solution_imports(root: Path) -> list[str]:
    def without_comments(text: str) -> str:
        result = []
        i, depth = 0, 0
        while i < len(text):
            if depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                    result.append(" ")
                else:
                    if text[i] == "\n":
                        result.append("\n")
                    i += 1
            elif text.startswith("/-", i):
                depth = 1
                i += 2
            elif text.startswith("--", i):
                i = text.find("\n", i)
                if i < 0:
                    break
            elif text[i] == '"':
                result.append('"')
                i += 1
                while i < len(text):
                    char = text[i]
                    result.append("\n" if char == "\n" else " ")
                    i += 1
                    if char == "\\":
                        i += 1
                    elif char == '"':
                        break
            else:
                result.append(text[i])
                i += 1
        require(depth == 0, "Unclosed Lean block comment")
        return "".join(result)

    pending, visited = ["All"], set()
    forbidden = ("Challenge", "support_reference", "appendix_reference", "appendix_b_reference")
    while pending:
        module = pending.pop()
        if module in visited:
            continue
        require(not any(module == p or module.startswith(p + ".") for p in forbidden),
                f"The solution imports a reference module: {module}")
        source = root / (module.replace(".", "/") + ".lean")
        if not source.is_file():
            require(not module.startswith(("KungTraub", "Solution", "All")),
                    f"Missing project module: {module}")
            continue
        visited.add(module)
        text = without_comments(source.read_text(encoding="utf-8-sig"))
        for body in re.findall(r"^\s*(?:(?:public|private|meta)\s+)?import\s+([^\n]+)", text, re.MULTILINE):
            pending.extend(body.split())
    return sorted(visited)


def filesystem_isolation_check(landrun: Path, directory: Path, env: dict) -> dict:
    canary = directory / "filesystem-canary.txt"
    canary.write_text("unchanged\n", encoding="utf-8")
    original = digest(canary)
    program = (
        "import pathlib,sys\n"
        "try:\n"
        " pathlib.Path(sys.argv[1]).write_text('changed\\n')\n"
        "except PermissionError:\n"
        " print('filesystem-write-denied')\n"
        "else:\n"
        " raise SystemExit('filesystem confinement failed')\n"
    )
    command = [str(landrun), "--best-effort", "--ro", "/", "--rw", "/dev",
               "-ldd", "-add-exec", "--", str(Path(sys.executable).resolve()),
               "-I", "-c", program, str(canary)]
    output = capture(command, directory, env)
    require(output.strip() == "filesystem-write-denied" and digest(canary) == original,
            "Landrun did not enforce the read-only filesystem boundary")
    return {"command": command, "output": output, "canary_sha256": original}


def pinned_dependency_links(directory: Path, entries: dict, env: dict) -> dict:
    links = {}
    for relative, (mode, kind, blob) in entries.items():
        if mode != "120000":
            continue
        path = directory / relative
        require(kind == "blob" and path.is_symlink(), f"Expected a Git-tracked symlink: {path}")
        require(path.suffix != ".lean" and not {".git", ".lake"}.intersection(Path(relative).parts),
                f"Symlinks are not permitted in Lean sources or build inputs: {path}")
        proc = subprocess.run(["git", "cat-file", "blob", blob], cwd=directory, env=env,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        require(proc.returncode == 0, f"Cannot read pinned symlink blob: {path}")
        literal = proc.stdout.decode("utf-8")
        require(literal and not any(c in literal for c in "\r\n\0") and
                not Path(literal).is_absolute() and os.readlink(path) == literal,
                f"Symlink text differs from its pinned Git blob: {path}")
        target = safe_path(path.parent / literal)
        require(target.is_relative_to(directory) and target.is_file(),
                f"Symlink destination must be a regular file in its own dependency: {path}")
        target_relative = target.relative_to(directory).as_posix()
        require(target_relative in entries and entries[target_relative][0] in {"100644", "100755"} and
                not {".git", ".lake"}.intersection(Path(target_relative).parts),
                f"Symlink destination must be a pinned regular source file: {path}")
        links[relative] = {"git_blob": blob, "target": literal,
                           "target_relative": target_relative, "target_sha256": digest(target)}
    return links


def dependency_snapshot(cache: Path, manifest: dict, env: dict) -> dict:
    require(manifest["packagesDir"] == ".lake/packages", "Unexpected package directory")
    packages = manifest["packages"]
    require(len(packages) == 9 and all(p["type"] == "git" for p in packages),
            "Exactly nine pinned public Git dependencies are required")
    require({p.name for p in cache.iterdir()} == {p["name"] for p in packages},
            "Unexpected directories in the public dependency cache")
    heads, tracked, links = {}, {}, {}
    for package in packages:
        name, revision = package["name"], package["rev"]
        require(re.fullmatch(r"[0-9a-f]{40}", revision) is not None, f"Unpinned dependency: {name}")
        directory = safe_path(cache / name)
        require((directory / ".git").is_dir(), f"A complete Git checkout is required: {name}")
        head = capture(["git", "--no-optional-locks", "rev-parse", "HEAD"], directory, env).strip()
        require(head == revision, f"Wrong dependency revision: {name}")
        flags = capture(["git", "ls-files", "-v", "-z"], directory, env).split("\0")
        require(all(not row or (row[0].isupper() and row[0] != "S") for row in flags),
                f"Hidden Git index entries are not permitted: {name}")
        capture(["git", "--no-optional-locks", "-c", "core.fsmonitor=false", "diff",
                 "--no-ext-diff", "--no-textconv", "--exit-code", "HEAD", "--"], directory, env)
        tree = capture(["git", "ls-tree", "-r", "-z", "HEAD"], directory, env).split("\0")
        entries = {}
        for row in tree:
            if row:
                header, relative = row.split("\t", 1)
                entries[relative] = tuple(header.split())
        tracked[name] = set(entries)
        heads[name] = head
        package_links = pinned_dependency_links(directory, entries, env)
        links.update({name + "/" + relative: record for relative, record in package_links.items()})
        for path in files_under(directory, {".git", ".lake"}, package_links):
            if path.suffix == ".lean":
                require(path.relative_to(directory).as_posix() in tracked[name],
                        f"Untracked Lean source in public dependency: {path}")
    sources = {name + "/" + relative:
               link_hash(links[name + "/" + relative]) if name + "/" + relative in links
               else digest(cache / name / relative)
               for name, names in tracked.items() for relative in sorted(names)}
    libraries, origins = {}, {}
    for package in packages:
        name = package["name"]
        library = cache / name / ".lake/build/lib/lean"
        if not library.is_dir():
            continue
        for path in files_under(library):
            relative = path.relative_to(cache).as_posix()
            libraries[relative] = digest(path)
            if path.suffix == ".olean":
                source = path.relative_to(library).with_suffix(".lean").as_posix()
                require(source in tracked[name], f"Unknown compiled public module: {relative}")
                origins[relative] = {"source": name + "/" + source,
                                     "sha256": sources[name + "/" + source]}
    require(libraries and origins, "Download the public dependency cache before checking")
    return {"heads": heads, "sources": sources, "libraries": libraries, "origins": origins, "symlinks": links}


def load_tools(args) -> tuple[dict[str, Path], dict]:
    prefix = safe_path(Path(args.tools))
    inventory_path = prefix / "tools.json"
    inventory = read_json(inventory_path)
    require(inventory.get("complete") is True and inventory["revisions"] == REVISIONS,
            "Incomplete or incompatible tool inventory")
    require(inventory["toolchain"] == TOOLCHAIN, "Wrong toolchain in tools.json")
    require(set(inventory["binaries"]) == {"comparator", "lean4export", "landrun", "lean", "lake"},
            "Unexpected binary inventory")
    overrides = (args.comparator, args.landrun, args.exporter, args.lean_bin)
    if any(overrides):
        require(all(overrides), "Supply all four binary override options together")
        leanbin = Path(args.lean_bin).expanduser().resolve(strict=True)
        paths = {"comparator": Path(args.comparator), "landrun": Path(args.landrun),
                 "lean4export": Path(args.exporter), "lean": leanbin / "lean", "lake": leanbin / "lake"}
    else:
        paths = {name: (prefix / item["path"]).resolve(strict=True)
                 for name, item in inventory["binaries"].items()}
    paths = {name: safe_path(path.resolve(strict=True)) for name, path in paths.items()}
    for name, path in paths.items():
        require(digest(path) == inventory["binaries"][name]["sha256"], f"Changed tool: {name}")
        require(os.access(path, os.X_OK), f"Tool is not executable: {path}")
    require(paths["lake"].parent == paths["lean"].parent, "Lean and Lake must share a toolchain")
    provenance = {"mode": "setup-inventory", "inventory_sha256": digest(inventory_path),
                  "revisions": inventory["revisions"], "relocated": any(overrides)}
    return paths, provenance


def check_exports(text: str, config: dict) -> dict:
    expected = config["theorem_names"] + config["permitted_axioms"] + PUBLIC_EXPORTS
    exports = {}
    for side in (config["challenge_module"], config["solution_module"]):
        lines = [line for line in text.splitlines()
                 if line.startswith("Exporting #[") and line.endswith("] from " + side)]
        require(len(lines) == 1, f"Missing or duplicate export list for {side}")
        actual = lines[0][len("Exporting #["):].rsplit("] from ", 1)[0].split(", ")
        require(actual == expected, f"Incorrect export inventory for {side}")
        exports[side] = actual
    require("Lean default kernel accepts the solution" in text, "Default-kernel acceptance is absent")
    require("Your solution is okay!" in text, "Comparator acceptance is absent")
    return exports


def remove_completed_workspace(run: Path, workspace: Path, local_cache: Path,
                               original_cache: Path, dependency_links: dict | None = None) -> None:
    run = safe_path(run)
    workspace = safe_path(workspace)
    local_cache = safe_path(local_cache)
    require(workspace.parent == run and workspace.name in CASES,
            "Cleanup is restricted to one case in the current run")
    resolved_run = run.resolve(strict=True)
    resolved_workspace = workspace.resolve(strict=True)
    resolved_cache = local_cache.resolve(strict=True)
    resolved_original = original_cache.resolve(strict=True)
    require(resolved_workspace.parent == resolved_run and
            resolved_workspace == resolved_run / workspace.name,
            "Cleanup target escaped the current run")
    require(resolved_cache == resolved_workspace / ".lake/packages",
            "Cleanup dependency cache escaped the case workspace")
    require(resolved_original != resolved_cache and
            not resolved_original.is_relative_to(resolved_workspace),
            "Cleanup must not contain the original dependency cache")
    # Only the exact copied, Git-validated dependency links are permitted.
    links = {".lake/packages/" + name: record for name, record in (dependency_links or {}).items()}
    for _ in files_under(resolved_workspace, allowed_links=links):
        pass
    shutil.rmtree(resolved_workspace)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tools", default=str(ROOT / ".verification/tools"))
    parser.add_argument("--output", default=str(ROOT / ".verification/comparator"))
    parser.add_argument("--case", choices=[*CASES, "all"], default="all")
    parser.add_argument("--dependencies", help="Public .lake/packages cache; defaults to this repository's cache")
    parser.add_argument("--keep-workspaces", action="store_true",
                        help="Retain successful workspaces; each case requires another full dependency-cache copy")
    parser.add_argument("--comparator")
    parser.add_argument("--landrun")
    parser.add_argument("--exporter")
    parser.add_argument("--lean-bin", help="Directory containing the matching Lean and Lake binaries")
    args = parser.parse_args()
    linux_user()
    isolation = isolation_checks()
    output = safe_path(Path(args.output))
    output.mkdir(parents=True, exist_ok=True)
    run = output / str(time.time_ns())
    run.mkdir(exist_ok=False)
    report = {"complete": False, "isolation": isolation, "uid": os.getuid(), "cases": [],
              "checking_script_sha256": digest(Path(__file__))}
    report_path = run / "report.json"
    write_json(report_path, report)
    try:
        tools, provenance = load_tools(args)
        env = clean_environment(tools["lean"].parent)
        report["filesystem_isolation"] = filesystem_isolation_check(tools["landrun"], run, env)
        write_json(report_path, report)
        version = capture([str(tools["lean"]), "--version"], ROOT, env).strip()
        require("version 4.33.1," in version and LEAN_COMMIT in version, "Incorrect Lean version or commit")
        env.update(COMPARATOR_LANDRUN=str(tools["landrun"]), COMPARATOR_LEAN4EXPORT=str(tools["lean4export"]))
        tool_hashes = {n: digest(p) for n, p in tools.items()}
        configs = checked_configs(ROOT)
        report["solution_imports"] = check_solution_imports(ROOT)
        sources = source_files(ROOT)
        require((ROOT / "lean-toolchain").read_text().strip() == TOOLCHAIN, "Incorrect project toolchain")
        manifest = read_json(ROOT / "lake-manifest.json")
        require(next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
                == "0df444a360eaa60ab8c11dca51a86af692955474", "Incorrect Mathlib pin")
        cache = safe_path(Path(args.dependencies) if args.dependencies else ROOT / ".lake/packages")
        require(not output.is_relative_to(cache), "Output must be outside the dependency cache")
        dependencies = dependency_snapshot(cache, manifest, env)
        links = dependencies["symlinks"]
        cache_hashes = tree_hashes(cache, allowed_links=links)
        report.update(lean_version=version, tools=provenance,
                      tool_binaries={n: {"path": str(p), "sha256": tool_hashes[n]} for n, p in tools.items()},
                      source_sha256=sources, dependency_snapshot=dependencies,
                      dependency_cache_sha256=cache_hashes)
        write_json(report_path, report)
        selected = list(CASES) if args.case == "all" else [args.case]
        for name in selected:
            workspace = run / name
            workspace.mkdir(exist_ok=False)
            for relative, expected in sources.items():
                target = workspace / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / relative, target)
                require(digest(target) == expected, f"Source copy changed: {relative}")
            local_cache = workspace / ".lake/packages"
            local_cache.parent.mkdir()
            require(shutil.disk_usage(workspace).free > sum(p.lstat().st_size for p in files_under(cache, allowed_links=links)) + 2 * 1024**3,
                    "Insufficient free space for an independent dependency cache")
            shutil.copytree(cache, local_cache, copy_function=shutil.copy2, symlinks=True)
            require(tree_hashes(local_cache, allowed_links=links) == cache_hashes, "Copied dependency cache differs from its source")
            require(not (workspace / ".lake/build").exists(), "Project build objects must not be copied")
            require(all(p.lstat().st_nlink == 1 for p in files_under(local_cache, allowed_links=links)), "Copied cache contains hardlinks")
            config = configs[name]
            command = [str(tools["lake"]), "env", str(tools["comparator"]), "Verification/" + name + ".json"]
            log = run / (name + ".txt")
            entry = {"case": name, "workspace": str(workspace), "config": config,
                     "command": command, "output_file": log.name, "complete": False}
            report["cases"].append(entry)
            write_json(report_path, report)
            print(f"Comparing {name}: {len(config['theorem_names'])} theorems", flush=True)
            start = time.monotonic()
            with log.open("w", encoding="utf-8") as stream:
                proc = subprocess.run(command, cwd=workspace, env=env, stdout=stream, stderr=subprocess.STDOUT)
            entry.update(exit_code=proc.returncode, elapsed_seconds=time.monotonic() - start,
                         output_sha256=digest(log))
            write_json(report_path, report)
            require(proc.returncode == 0, f"Comparator failed; see {log}")
            entry["exported_declarations"] = check_exports(log.read_text(encoding="utf-8"), config)
            require(source_files(workspace) == sources, "Checking modified its source files")
            require(source_files(ROOT) == sources, "The release sources changed during checking")
            require({n: digest(p) for n, p in tools.items()} == tool_hashes, "A checker binary changed")
            require(tree_hashes(cache, allowed_links=links) == cache_hashes, "The original dependency cache changed")
            after = dependency_snapshot(local_cache, manifest, env)
            require(after["heads"] == dependencies["heads"] and after["sources"] == dependencies["sources"] and
                    after["symlinks"] == links,
                    "Pinned public dependency sources changed")
            require(all(after["libraries"].get(n) == h for n, h in dependencies["libraries"].items()),
                    "A pre-existing public dependency library file changed")
            entry.update(complete=True, sources_unchanged=True, tools_unchanged=True,
                         original_dependency_cache_unchanged=True, dependency_snapshot_after=after,
                         workspace_retained=True)
            write_json(report_path, report)
            if not args.keep_workspaces:
                remove_completed_workspace(run, workspace, local_cache, cache, links)
                entry["workspace_retained"] = False
                write_json(report_path, report)
        report["complete"] = True
        write_json(report_path, report)
        print(json.dumps({"complete": True, "report": str(report_path)}), flush=True)
        return 0
    except Exception as exc:
        report["error"] = f"{type(exc).__name__}: {exc}"
        write_json(report_path, report)
        print(report["error"], file=sys.stderr, flush=True)
        print(f"Report: {report_path}", file=sys.stderr, flush=True)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
