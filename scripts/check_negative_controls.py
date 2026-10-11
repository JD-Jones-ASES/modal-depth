#!/usr/bin/env python3
"""Compile boundary witnesses, then require corrupted proofs to fail.

Generated Lean sources and compiler logs stay in .lake/verification. A missing
import, executable failure, or an unexpected diagnostic does not count as a
successful rejection. These controls supplement the mathematical counterexamples
in NegativeControls.lean; they are not an exhaustive mutation test.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys


HEADER = """import ModalDepth
open ModalDepth ModalDepth.NegativeControls
"""

POSITIVE = HEADER + """
example : Provable 1 transitivityInput := transitivityInput_provable
example : ¬ Provable 1 (encode Bool.not false transitivityInput) :=
  two_cycle_loses_provability
example : ¬ UnsignedCraig 1 (fun d => d % 2) ℕ := parity_GL_fails
example : ¬ UnsignedCraig 2 (fun d => d) ℕ := exact_depth_two_fails
example : canonicalOrbit 2 (by decide) 0 ≠ canonicalOrbit 2 (by decide) 2 :=
  root_ne_positive_even
example : decode Bool.not false wrongColor = .bot :=
  selective_decoder_removes_wrong_color
example : ¬ DepthSubstitution 1 (fun d => d % 2) ℕ Empty :=
  parity_GL_substitution_fails
example : DepthSubstitution 2 (fun d => d % 2) ℕ Empty :=
  parity_two_substitution
example : Provable 3 (.imp ((Formula.atom (0 : ℕ)).boxes 2)
    ((Formula.atom 0).boxes 5)) :=
  (boxes_atom_imp_iff_arithmetic 3 (by decide) 2 5 0).mpr
    (Or.inr ⟨by decide, by decide, by decide⟩)
example : ¬ Provable 3 (.imp ((Formula.atom (0 : ℕ)).boxes 2)
    ((Formula.atom 0).boxes 4)) := by
  intro h
  have hbad := (boxes_atom_imp_iff_arithmetic 3 (by decide) 2 4 0).mp h
  norm_num at hbad
example : ¬ DepthCompositionClosed CompositionBoundary.coarseLabel ℕ ℕ PEmpty := by
  intro h
  exact CompositionBoundary.no_single_coarse_substitution
    (h CompositionBoundary.insertBox CompositionBoundary.selectTruth)
"""

CONTROLS = [
    (
        "dropped_box_order",
        "Try to reverse a valid same-residue box implication by dropping the order condition.",
        """example : Provable 3 (.imp ((Formula.atom (0 : ℕ)).boxes 5)
    ((Formula.atom 0).boxes 2)) := by
  apply (boxes_atom_imp_iff 3 (by decide) 5 2 0).mpr
  exact ⟨by decide, by decide⟩
""",
        "is false",
    ),
    (
        "dropped_root_restriction",
        "Treat the root as an ordinary positive residue in the box implication criterion.",
        """example : Provable 3 (.imp (Formula.atom (0 : ℕ))
    ((Formula.atom 0).boxes 3)) := by
  apply (boxes_atom_imp_iff_arithmetic 3 (by decide) 0 3 0).mpr
  exact Or.inr ⟨by decide, by decide, by decide⟩
""",
        "is false",
    ),
    (
        "periodicity_implies_composition",
        "Use admissible periodicity where composition requires successor compatibility.",
        """example : DepthCompositionClosed CompositionBoundary.coarseLabel ℕ ℕ PEmpty := by
  exact depthCompositionClosed_of_compatible CompositionBoundary.coarseLabel_periodic
""",
        "Application type mismatch",
    ),
    (
        "wrong_substitution_period",
        "Replace the valid period-two substitution result with a period-one claim.",
        """example : DepthSubstitution 1 (fun d => d % 2) ℕ Empty := by
  exact parity_two_substitution
""",
        "Type mismatch",
    ),
    (
        "blind_decoder",
        "Replace selective decoding by blind color erasure in its support theorem.",
        """example : ∀ (A : Formula (ℕ × Bool)) (s : Bool) (p : ℕ) (z : Bool),
    (rename Prod.fst A).support (fun d => Bool.not^[d] false) s p z →
      A.vocab s (p,z) := by
  intro A s p z h
  exact decode_support Bool.not false A s p z h
""",
        "Application type mismatch",
    ),
    (
        "inadmissible_phase_preservation",
        "Try using transitivity after encoding it with an inadmissible phase action.",
        """example : Provable 1 (encode Bool.not false transitivityInput) := by
  exact Obstruction.n_transitivity (.atom (0, true))
""",
        "Type mismatch",
    ),
    (
        "false_phase_identity",
        "Claim that a two-cycle satisfies the GL phase power identity.",
        """example : ∀ q : Bool, Bool.not^[1 + 1] q = Bool.not q := by
  decide
""",
        "is false",
    ),
    (
        "root_cycle_collapse",
        "Merge the root with positive even depth in the canonical phase space.",
        """example : canonicalOrbit 2 (by decide) 0 =
    canonicalOrbit 2 (by decide) 2 := by
  decide
""",
        "is false",
    ),
    (
        "forbidden_modulus_witness",
        "Claim the necessary parity identity at depth one for period one.",
        """example : ((1 + 1) % 2 : ℕ) = 1 % 2 := by
  decide
""",
        "is false",
    ),
]


def run(command: list[str], root: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command, cwd=root, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, timeout=180, check=False,
    )


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    output = root / ".lake" / "verification"
    output.mkdir(parents=True, exist_ok=True)
    # Even an early compiler/setup failure must invalidate a previous success.
    (output / "negative-controls.json").unlink(missing_ok=True)

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default=shutil.which("lake"))
    args = parser.parse_args()
    if args.lake is None:
        print("ERROR: lake is not on PATH; provide --lake PATH", file=sys.stderr)
        return 2

    try:
        build = run([args.lake, "build", "ModalDepth"], root)
        (output / "negative-build.log").write_text(build.stdout, encoding="utf-8")
        if build.returncode != 0:
            print("ERROR: positive control module failed to build", file=sys.stderr)
            print(build.stdout, file=sys.stderr)
            return 1

        positive_path = output / "PositiveControl.lean"
        positive_path.write_text(POSITIVE, encoding="utf-8")
        positive = run([args.lake, "env", "lean", str(positive_path)], root)
        (output / "PositiveControl.log").write_text(positive.stdout, encoding="utf-8")
        if positive.returncode != 0:
            print("ERROR: accepted theorem baseline did not compile", file=sys.stderr)
            print(positive.stdout, file=sys.stderr)
            return 1

        results = []
        for name, purpose, source, diagnostic in CONTROLS:
            path = output / f"{name}.lean"
            path.write_text(HEADER + source, encoding="utf-8")
            compiled = run([args.lake, "env", "lean", str(path)], root)
            (output / f"{name}.log").write_text(compiled.stdout, encoding="utf-8")
            infrastructure_errors = (
                "unknown module prefix", "object file", "Unknown identifier",
                "unknown constant", "failed to synthesize instance",
            )
            rejected_as_expected = (
                compiled.returncode != 0
                and "error:" in compiled.stdout
                and diagnostic.lower() in compiled.stdout.lower()
                and not any(item.lower() in compiled.stdout.lower()
                            for item in infrastructure_errors)
            )
            results.append({
                "name": name, "purpose": purpose,
                "expected_diagnostic": diagnostic,
                "returncode": compiled.returncode,
                "rejected_as_expected": rejected_as_expected,
            })
            if not rejected_as_expected:
                print(f"FAIL: {name}", file=sys.stderr)
                print(compiled.stdout, file=sys.stderr)
            else:
                print(f"PASS: {name} rejected at the intended proof boundary")

        success = all(result["rejected_as_expected"] for result in results)
        report = {"positive_baseline_compiled": True, "success": success,
                  "controls": results}
        (output / "negative-controls.json").write_text(
            json.dumps(report, indent=2) + "\n", encoding="utf-8")
        return 0 if success else 1
    except (OSError, subprocess.TimeoutExpired) as error:
        print(f"ERROR: compiler execution failed: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
