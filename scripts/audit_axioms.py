#!/usr/bin/env python3
"""Audit compared declarations and all public ModalDepth theorems in Lean's environment."""
from __future__ import annotations

import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / ".lake" / "verification"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*\Z")
INVENTORY = "MODAL_DEPTH_AXIOM_INVENTORY "
REPORT = "MODAL_DEPTH_AXIOM_REPORT "
COMPLETE = "MODAL_DEPTH_AXIOM_COMPLETE "


def fail(message: str) -> None:
    raise SystemExit(message)


def lake_command() -> str:
    candidate = os.environ.get("LAKE") or shutil.which("lake")
    if candidate:
        return candidate
    fallback = Path.home() / ".elan" / "bin" / "lake"
    if fallback.is_file():
        return str(fallback)
    fail("lake is unavailable; add the elan bin directory to PATH or set LAKE")


def checked_names(value: object, field: str) -> list[str]:
    if not isinstance(value, list) or not all(isinstance(x, str) and NAME.fullmatch(x) for x in value):
        fail(f"Invalid {field} in comparator.json")
    if len(set(value)) != len(value):
        fail(f"Duplicate declaration in {field}")
    return value


def run(command: list[str], log_name: str) -> str:
    proc = subprocess.run(command, cwd=ROOT, text=True, capture_output=True, check=False)
    output = proc.stdout + proc.stderr
    (WORK / log_name).write_text(output)
    if proc.returncode:
        fail(f"Command failed ({proc.returncode}): {' '.join(command)}\n{output}")
    return output


def lean_array(names: list[str]) -> str:
    return "#[" + ", ".join(json.dumps(name) for name in names) + "]"


def main() -> None:
    WORK.mkdir(parents=True, exist_ok=True)
    report_path = WORK / "axioms.json"
    # A failed run must not leave a previous successful report in place.
    report_path.unlink(missing_ok=True)
    try:
        config = json.loads((ROOT / "comparator.json").read_text())
    except (OSError, ValueError) as error:
        fail(f"Cannot read comparator.json: {error}")
    theorems = checked_names(config.get("theorem_names"), "theorem_names")
    definitions = checked_names(config.get("definition_names", []), "definition_names")
    principal = theorems + definitions
    if not theorems or len(principal) != len(set(principal)):
        fail("Compared declarations must contain theorems and have unique names")
    if set(config.get("permitted_axioms", [])) != ALLOWED:
        fail("comparator.json must permit exactly propext, Classical.choice, and Quot.sound")
    solution = config.get("solution_module")
    if not isinstance(solution, str) or not NAME.fullmatch(solution):
        fail("Invalid solution_module in comparator.json")
    modules = sorted({".".join(path.relative_to(ROOT).with_suffix("").parts)
                      for path in (ROOT / "ModalDepth").rglob("*.lean")} | {solution})
    if len(modules) < 2:
        fail("No ModalDepth implementation modules found")
    lake = lake_command()
    # Build every imported implementation module, so stale oleans cannot hide edits.
    run([lake, "build", *[f"+{module}:olean" for module in modules]], "axioms-build.log")
    imports = "\n".join(f"import {module}" for module in modules)
    source = WORK / "AxiomAudit.lean"
    source.write_text(f'''import Lean.Util.CollectAxioms
{imports}

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let principal : Array String := {lean_array(principal)}
  let comparedTheorems : Array String := {lean_array(theorems)}
  let mut supporting : Array Name := #[]
  for (name, info) in env.constants do
    if (`ModalDepth).isPrefixOf name then
      if info.isAxiom then
        throwError "Custom axiom in implementation namespace: {{name}}"
      if info.isTheorem then
        supporting := supporting.push name
  unless !supporting.isEmpty do
    throwError "No public supporting theorems found"
  let mut names := supporting
  for text in principal do
    let name := text.toName
    let some info := env.find? name | throwError "Missing compared declaration: {{text}}"
    if comparedTheorems.contains text && !info.isTheorem then
      throwError "Compared theorem is not a theorem: {{text}}"
    unless names.contains name do
      names := names.push name
  liftIO <| IO.println ("{INVENTORY}" ++ (Json.mkObj [
    ("supporting", toJson (supporting.map toString)),
    ("names", toJson (names.map toString))]).compress)
  for name in names do
    let axioms ← collectAxioms name
    liftIO <| IO.println ("{REPORT}" ++ (Json.mkObj [
      ("name", toJson name.toString),
      ("axioms", toJson (axioms.map toString))]).compress)
  liftIO <| IO.println ("{COMPLETE}" ++ toString names.size)
''')
    output = run([lake, "env", "lean", str(source)], "axioms.log")
    inventories: list[object] = []
    reports: dict[str, list[str]] = {}
    completions: list[int] = []
    try:
        for line in output.splitlines():
            if line.startswith(INVENTORY):
                inventories.append(json.loads(line[len(INVENTORY):]))
            elif line.startswith(REPORT):
                entry = json.loads(line[len(REPORT):])
                name, axioms = entry["name"], entry["axioms"]
                if not isinstance(name, str) or name in reports:
                    fail(f"Duplicate or invalid axiom report: {name}")
                if not isinstance(axioms, list) or not all(isinstance(a, str) for a in axioms):
                    fail(f"Invalid axiom list: {name}")
                if set(axioms) - ALLOWED:
                    fail(f"Unpermitted axioms for {name}: {sorted(set(axioms) - ALLOWED)}")
                reports[name] = sorted(set(axioms))
            elif line.startswith(COMPLETE):
                completions.append(int(line[len(COMPLETE):]))
    except (ValueError, KeyError, TypeError) as error:
        fail(f"Malformed Lean axiom report: {error}")
    if len(inventories) != 1:
        fail("Missing or duplicate Lean theorem inventory")
    inventory = inventories[0]
    if not isinstance(inventory, dict):
        fail("Malformed Lean theorem inventory")
    names = checked_names(inventory.get("names"), "Lean inventory")
    supporting = checked_names(inventory.get("supporting"), "supporting inventory")
    if not supporting or set(names) != set(supporting) | set(principal):
        fail("Incomplete Lean theorem inventory")
    if set(reports) != set(names):
        fail(f"Missing or unexpected axiom reports: {sorted(set(reports) ^ set(names))}")
    if completions != [len(names)]:
        fail("Missing or inconsistent axiom audit completion marker")
    result = {
        "permitted_axioms": sorted(ALLOWED),
        "compared_declarations": principal,
        "public_supporting_theorems": sorted(supporting),
        "axioms": dict(sorted(reports.items())),
    }
    report_path.write_text(json.dumps(result, indent=2) + "\n")
    print(f"Permitted-axiom audit passed: {len(principal)} compared declarations, "
          f"{len(supporting)} public supporting theorems, {len(names)} distinct declarations")


if __name__ == "__main__":
    main()
