#!/usr/bin/env python3
"""Reject proof placeholders and extra trust mechanisms in implementation sources."""
from __future__ import annotations

import json
import os
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
FORBIDDEN = {"sorry", "sorryAx", "admit", "axiom", "axioms", "native_decide"}
TOKEN = re.compile(r"[A-Za-z_][A-Za-z_0-9']*")


def code_only(source: str, path: Path) -> str:
    """Blank strings and nested Lean comments while preserving line numbers."""
    result = list(source)
    i = 0
    depth = 0
    in_string = False
    line_comment = False
    while i < len(source):
        char = source[i]
        pair = source[i:i + 2]
        if line_comment:
            if char == "\n":
                line_comment = False
            else:
                result[i] = " "
            i += 1
        elif depth:
            if pair == "/-":
                result[i:i + 2] = [" ", " "]
                depth += 1
                i += 2
            elif pair == "-/":
                result[i:i + 2] = [" ", " "]
                depth -= 1
                i += 2
            else:
                if char != "\n":
                    result[i] = " "
                i += 1
        elif in_string:
            if char == "\\":
                result[i] = " "
                if i + 1 < len(source):
                    if source[i + 1] != "\n":
                        result[i + 1] = " "
                    i += 2
                else:
                    i += 1
            else:
                if char != "\n":
                    result[i] = " "
                if char == '"':
                    in_string = False
                i += 1
        elif pair == "--":
            result[i:i + 2] = [" ", " "]
            line_comment = True
            i += 2
        elif pair == "/-":
            result[i:i + 2] = [" ", " "]
            depth = 1
            i += 2
        elif char == '"':
            result[i] = " "
            in_string = True
            i += 1
        else:
            i += 1
    if depth or in_string:
        raise ValueError(f"{path}: unterminated comment or string")
    return "".join(result)


def main() -> None:
    try:
        config = json.loads((ROOT / "comparator.json").read_text())
    except (OSError, ValueError) as error:
        raise SystemExit(f"Cannot read comparator.json: {error}") from error
    challenge = config.get("challenge_module")
    if not isinstance(challenge, str) or not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*", challenge):
        raise SystemExit("Invalid challenge_module in comparator.json")
    challenge_path = ROOT.joinpath(*challenge.split(".")).with_suffix(".lean")
    if not challenge_path.is_file():
        raise SystemExit(f"Missing challenge module: {challenge_path.relative_to(ROOT)}")
    paths: list[Path] = []
    for directory, subdirectories, files in os.walk(ROOT):
        subdirectories[:] = [name for name in subdirectories if not name.startswith(".")]
        paths.extend(Path(directory) / name for name in files
                     if name.endswith(".lean") and name != "lakefile.lean")
    paths.sort()
    if not paths or not any(ROOT / "ModalDepth" in path.parents for path in paths):
        raise SystemExit("No implementation Lean sources found")
    errors: list[str] = []
    placeholders = 0
    for path in paths:
        code = code_only(path.read_text(), path.relative_to(ROOT))
        for match in TOKEN.finditer(code):
            token = match.group()
            if token not in FORBIDDEN:
                continue
            if token == "sorry" and path == challenge_path:
                placeholders += 1
                continue
            line = code.count("\n", 0, match.start()) + 1
            errors.append(f"{path.relative_to(ROOT)}:{line}: forbidden token {token}")
        if path != challenge_path and re.search(r"\bimport\s+" + re.escape(challenge) + r"\b", code):
            errors.append(f"{path.relative_to(ROOT)}: implementation imports challenge placeholders")
    if errors:
        raise SystemExit("Source check failed:\n" + "\n".join(errors))
    print(f"Source check passed: {len(paths)} Lean modules; "
          f"{placeholders} expected challenge placeholders")


if __name__ == "__main__":
    main()
