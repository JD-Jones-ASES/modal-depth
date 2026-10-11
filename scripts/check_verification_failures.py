#!/usr/bin/env python3
"""Check that failed verification attempts cannot retain earlier success reports.

Each case imports a copy of the real verification script in a temporary project.
Preflight and compiler failures are simulated explicitly; no Lean build, kernel
replay, sandbox change, or network access is performed by this regression check.
"""
from __future__ import annotations

from contextlib import ExitStack, redirect_stderr, redirect_stdout
import importlib.util
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from types import ModuleType
from typing import Callable
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]
Setup = Callable[[ExitStack, ModuleType, Path], None]


def missing_lake(stack: ExitStack, module: ModuleType, root: Path) -> None:
    stack.enter_context(patch.object(module.shutil, "which", return_value=None))


def missing_executable(stack: ExitStack, module: ModuleType, root: Path) -> None:
    # Exercise a real process-launch failure using a path inside the fresh directory.
    stack.enter_context(patch.object(sys, "argv", ["check", "--lake", str(root / "missing-lake")]))


def failed_build(stack: ExitStack, module: ModuleType, root: Path) -> None:
    stack.enter_context(patch.object(sys, "argv", ["check", "--lake", "simulated-lake"]))
    stack.enter_context(patch.object(module, "run", return_value=
                                    subprocess.CompletedProcess([], 1, "simulated build failure\n")))


def failed_baseline(stack: ExitStack, module: ModuleType, root: Path) -> None:
    stack.enter_context(patch.object(sys, "argv", ["check", "--lake", "simulated-lake"]))
    stack.enter_context(patch.object(module, "run", side_effect=[
        subprocess.CompletedProcess([], 0, "simulated successful build\n"),
        subprocess.CompletedProcess([], 1, "simulated baseline failure\n"),
    ]))


def unsupported_platform(stack: ExitStack, module: ModuleType, root: Path) -> None:
    stack.enter_context(patch.object(module.platform, "system", return_value="UnsupportedOS"))


def mismatched_pin(stack: ExitStack, module: ModuleType, root: Path) -> None:
    stack.enter_context(patch.object(module.platform, "system", return_value="Linux"))
    (root / "lean-toolchain").write_text("unapproved-toolchain\n")


def dirty_checkout(stack: ExitStack, module: ModuleType, root: Path) -> None:
    stack.enter_context(patch.object(module.platform, "system", return_value="Linux"))
    stack.enter_context(patch.object(module.subprocess, "check_output", return_value=" M source.lean\n"))


def missing_checker(stack: ExitStack, module: ModuleType, root: Path) -> None:
    stack.enter_context(patch.object(module.platform, "system", return_value="Linux"))
    # Simulate clean Git metadata and a release prefix with no checker executables.
    stack.enter_context(patch.object(module.subprocess, "check_output", side_effect=[
        "", "a" * 40 + "\n", str(root / "missing-release") + "\n",
    ]))


def check_case(name: str, script: str, report: str, setup: Setup,
               expected_code: int, diagnostic: str) -> None:
    with tempfile.TemporaryDirectory(prefix="modal-depth-verification-failure-") as directory:
        root = Path(directory)
        scripts = root / "scripts"
        scripts.mkdir()
        copied = scripts / script
        shutil.copyfile(ROOT / "scripts" / script, copied)
        shutil.copyfile(ROOT / "lean-toolchain", root / "lean-toolchain")
        work = root / ".lake" / "verification"
        work.mkdir(parents=True)
        report_path = work / report
        report_path.write_text(json.dumps({"status": "passed", "success": True,
                                           "candidate_sha": "old-candidate"}) + "\n")
        spec = importlib.util.spec_from_file_location("verification_failure_target", copied)
        if spec is None or spec.loader is None:
            raise RuntimeError(f"Cannot import copied verification script: {script}")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        captured = io.StringIO()
        with ExitStack() as stack, redirect_stdout(captured), redirect_stderr(captured):
            stack.enter_context(patch.object(sys, "argv", [str(copied)]))
            setup(stack, module, root)
            try:
                result = module.main()
                code = 0 if result is None else result
            except SystemExit as error:
                code = error.code if isinstance(error.code, int) else 1
                if isinstance(error.code, str):
                    print(error.code)
        output = captured.getvalue()
        if code != expected_code or diagnostic not in output:
            raise AssertionError(f"{name}: wrong failure ({code!r}):\n{output}")
        if report_path.exists():
            raise AssertionError(f"{name}: failed run retained a verification summary")
        print(f"PASS: {name} removes the earlier success report")


def main() -> None:
    negative = "check_negative_controls.py"
    kernel = "verify_kernels.py"
    cases = [
        ("missing lake", negative, "negative-controls.json", missing_lake, 2,
         "lake is not on PATH"),
        ("missing compiler executable", negative, "negative-controls.json", missing_executable, 2,
         "compiler execution failed"),
        ("failed module build", negative, "negative-controls.json", failed_build, 1,
         "positive control module failed to build"),
        ("failed positive baseline", negative, "negative-controls.json", failed_baseline, 1,
         "accepted theorem baseline did not compile"),
        ("unsupported kernel platform", kernel, "kernels.json", unsupported_platform, 1,
         "require Linux"),
        ("mismatched toolchain pin", kernel, "kernels.json", mismatched_pin, 1,
         "Update the audited release pin"),
        ("dirty candidate checkout", kernel, "kernels.json", dirty_checkout, 1,
         "requires a clean checkout"),
        ("missing independent checker", kernel, "kernels.json", missing_checker, 1,
         "lacks a required bundled checker"),
    ]
    for case in cases:
        check_case(*case)
    print(f"Verification failure regressions passed: {len(cases)} isolated cases")


if __name__ == "__main__":
    main()
