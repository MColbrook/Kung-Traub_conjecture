#!/usr/bin/env python3
"""Build the pinned Comparator, exporter and Landrun tools on Linux."""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import shutil
import subprocess
import sys

from check_comparator import (ROOT, TOOLCHAIN, LEAN_COMMIT, REVISIONS, capture,
                              clean_environment, digest, linux_user, require,
                              safe_path, tree_hashes, write_json)

URLS = {
    "comparator": "https://github.com/leanprover/comparator.git",
    "lean4export": "https://github.com/leanprover/lean4export.git",
    "landrun": "https://github.com/Zouuup/landrun.git",
}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", default=str(ROOT / ".verification/tools"))
    parser.add_argument("--lean-bin", help="Installed Lean 4.33.1 bin directory; otherwise resolve with elan")
    parser.add_argument("--threads", type=int, default=4, help="Lean worker threads (default: 4)")
    args = parser.parse_args()
    linux_user()
    require(args.threads > 0, "The thread count must be positive")
    for executable in ("git", "go") + (() if args.lean_bin else ("elan",)):
        require(shutil.which(executable) is not None, f"Required executable not found: {executable}")
    prefix = safe_path(Path(args.prefix))
    require(not prefix.exists(), "The tool prefix must be a new directory")
    prefix.mkdir(parents=True, exist_ok=False)
    env = clean_environment()
    env.update(GOTOOLCHAIN="local", GOCACHE=str(prefix / "go-cache"), GOMODCACHE=str(prefix / "go-modules"))
    env["LEAN_NUM_THREADS"] = str(args.threads)
    evidence = []

    def run(command: list[str], cwd: Path = prefix) -> str:
        proc = subprocess.run(command, cwd=cwd, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        evidence.append({"command": command, "cwd": os.path.relpath(cwd, prefix),
                         "exit_code": proc.returncode, "output": proc.stdout})
        write_json(prefix / "build-log.json", evidence)
        print(proc.stdout, end="", flush=True)
        require(proc.returncode == 0, f"Tool build command failed: {command}")
        return proc.stdout

    try:
        if args.lean_bin:
            lean = (Path(args.lean_bin).expanduser() / "lean").resolve(strict=True)
        else:
            env["ELAN_TOOLCHAIN"] = TOOLCHAIN
            lean = Path(run(["elan", "which", "lean"]).strip()).resolve(strict=True)
        lake = lean.with_name("lake")
        env["PATH"] = str(lean.parent) + ":" + env["PATH"]
        lean_version = run([str(lean), "--version"]).strip()
        require("version 4.33.1," in lean_version and LEAN_COMMIT in lean_version,
                "Lean 4.33.1 with the pinned commit is required")
        versions = {"lean": lean_version, "lake": run([str(lake), "--version"]).strip(),
                    "go": run(["go", "version"]).strip(), "git": run(["git", "--version"]).strip()}
        paths = {"comparator": prefix / "comparator",
                 "lean4export": prefix / "comparator/.lake/packages/lean4export",
                 "landrun": prefix / "landrun"}
        for name, destination in paths.items():
            destination.parent.mkdir(parents=True, exist_ok=True)
            run(["git", "clone", "--no-checkout", URLS[name], str(destination)])
            run(["git", "checkout", "--detach", REVISIONS[name]], destination)
            require(run(["git", "rev-parse", "HEAD"], destination).strip() == REVISIONS[name], name)
        patch = ROOT / "Verification/comparator-4.33.1.patch"
        require(digest(patch) == "1d887ee75befbdab714a7bdba5f02a884219476bc1b87053450dc003b7e455a5",
                "The compatibility patch differs from the published patch")
        changed = {"lean-toolchain", "lakefile.toml", "lake-manifest.json"}
        run(["git", "apply", "--check", str(patch)], paths["comparator"])
        run(["git", "apply", str(patch)], paths["comparator"])
        actual = set(run(["git", "diff", "--name-only"], paths["comparator"]).splitlines())
        require(actual == changed, "The compatibility patch must change only the three build files")
        source_snapshots = {name: tree_hashes(path, {".git", ".lake"}) for name, path in paths.items()}
        run([str(lake), "build", "lean4export", "comparator"], paths["comparator"])
        run(["go", "build", "-mod=readonly", "-trimpath", "-o", "landrun", "./cmd/landrun"], paths["landrun"])
        for name, path in paths.items():
            current = tree_hashes(path, {".git", ".lake"})
            if name == "landrun":
                current.pop("landrun", None)
            require(current == source_snapshots[name], f"Tool source files changed during compilation: {name}")
            require(run(["git", "rev-parse", "HEAD"], path).strip() == REVISIONS[name], name)
        binaries = {"lean": lean, "lake": lake,
                    "comparator": paths["comparator"] / ".lake/build/bin/comparator",
                    "lean4export": paths["lean4export"] / ".lake/build/bin/lean4export",
                    "landrun": paths["landrun"] / "landrun"}
        inventory = {"complete": True, "toolchain": TOOLCHAIN, "revisions": REVISIONS, "threads": args.threads,
                     "versions": versions, "compatibility_patch_sha256": digest(patch),
                     "source_sha256": source_snapshots,
                     "binaries": {name: {"path": os.path.relpath(path, prefix), "sha256": digest(path)}
                                  for name, path in binaries.items()}}
        write_json(prefix / "tools.json", inventory)
        print(f"Tools: {prefix / 'tools.json'}", flush=True)
        return 0
    except Exception as exc:
        write_json(prefix / "setup-failure.json", {"complete": False, "error": f"{type(exc).__name__}: {exc}"})
        print(str(exc), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
