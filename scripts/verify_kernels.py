#!/usr/bin/env python3
"""Compare theorem contracts and replay them with Lean, NanoDa, and con-ron."""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
LEAN_COMMIT = "470d5ce1400764999581fd26d5d72b00d990b0f4"
LEAN_VERSION = "leanprover/lean4:v4.35.0-rc3"


def digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def require_clean_candidate(root: Path = ROOT) -> str:
    """Return the candidate SHA only when it names the complete source state."""
    status = subprocess.check_output(
        ["git", "status", "--porcelain=v1", "--untracked-files=all"],
        cwd=root, text=True,
    )
    if status:
        raise SystemExit(
            "Exact-commit kernel verification requires a clean checkout. "
            "Commit the intended candidate and remove or ignore unrelated "
            "untracked files before running this command. No verification "
            "record has been created for the dirty source state."
        )
    return subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=root, text=True,
    ).strip()


def main() -> None:
    work = ROOT / ".lake/verification"
    work.mkdir(parents=True, exist_ok=True)
    record_path = work / "kernels.json"
    # Invalidate previous success before platform, checkout, or tool checks.
    record_path.unlink(missing_ok=True)

    if platform.system() != "Linux":
        raise SystemExit("Comparator and the independent-kernel run require Linux")
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    if toolchain != LEAN_VERSION:
        raise SystemExit("Update the audited release pin before changing the verification toolchain")
    sha = require_clean_candidate()
    prefix = Path(subprocess.check_output(["lake", "env", "lean", "--print-prefix"], cwd=ROOT, text=True).strip())
    tools = {name: prefix / "bin" / name for name in
             ("lake", "lean", "leanexport", "leanchecker", "nanoda_bin", "con-ron")}
    if any(not path.is_file() or not os.access(path, os.X_OK) for path in tools.values()):
        raise SystemExit("The selected release lacks a required bundled checker")
    config = json.loads((ROOT / "comparator.json").read_text())
    config.pop("enable_nanoda", None)
    config["external_kernels"] = {
        "nanoda": [str(tools["nanoda_bin"])],
        "con-ron": [str(tools["con-ron"]), "--jobs=2"],
    }
    path = work / "comparator-with-kernels.json"
    path.write_text(json.dumps(config, indent=2) + "\n")
    record = {"candidate_sha": sha, "toolchain": toolchain, "lean_source_commit": LEAN_COMMIT,
              "platform": platform.platform(), "tool_sha256": {n: digest(p) for n, p in tools.items()},
              "manifest_sha256": digest(ROOT / "lake-manifest.json"),
              "comparator_config_sha256": digest(ROOT / "comparator.json"),
              "external_kernels": config["external_kernels"], "status": "running"}
    bwrap = os.environ.get("COMPARATOR_BWRAP")
    if bwrap:
        record["bwrap_sha256"] = digest(Path(bwrap))
    record_path.write_text(json.dumps(record, indent=2) + "\n")
    command = [str(tools["lake"]), "comparator", "--config", str(path)]
    record["command"] = command
    with (work / "comparator.log").open("w") as log:
        process = subprocess.Popen(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, bufsize=1)
        assert process.stdout is not None
        for line in process.stdout:
            print(line, end="", flush=True)
            log.write(line)
            log.flush()
        code = process.wait()
    output = (work / "comparator.log").read_text()
    expected = [name + " kernel accepts the solution" for name in ("Lean default", "nanoda", "con-ron")]
    record["exit_code"] = code
    record["kernel_acceptance"] = {name: name in output for name in expected}
    final_sha = require_clean_candidate()
    if final_sha != sha:
        raise SystemExit("The candidate commit changed during verification")
    passed = code == 0 and all(record["kernel_acceptance"].values())
    record["status"] = "passed" if passed else "failed"
    record_path.write_text(json.dumps(record, indent=2) + "\n")
    if not passed:
        raise SystemExit(code or 1)
    print("Comparator statement comparison, axiom checks, and all three kernel replays passed")


if __name__ == "__main__":
    main()
