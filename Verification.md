# Verification

The package pins Lean `v4.35.0-rc3` and Mathlib commit
`a98628e16c11f5167f16124105ddce53efa9bfe5`. All implementation proofs are
checked by Lean. The permitted logical axioms are `propext`,
`Classical.choice`, and `Quot.sound`.

## Scope

The main formal results are the three structural classification equivalences
in [the solution contracts](ModalDepthSolution.lean). They preserve the
ordinary interpolation properties on the right-hand side. The corollaries
that remove those properties take them as explicit hypotheses. No declaration
asserts that ordinary interpolation has been established for these logics.

The substitution classification is unconditional: all formula-valued,
depth-label substitutions preserve theoremhood exactly for positive-periodic
labels. The phase-action classification and the explicit failure witness are
also compared contracts. Their source atom type is nonempty; the target atom
type is arbitrary.

The Hilbert derivability relation contains propositional tautology instances,
K, the weak Löb schema, modus ponens, and necessitation. The semantic
obstruction uses natural-number worlds with accessibility to strictly smaller
worlds; each pointed generated frame is a finite strict chain. The formal
proof does not need completeness or general finite-frame soundness.

## Reproduce

```sh
lake exe cache get
lake build
python3 scripts/check_sources.py
python3 scripts/audit_axioms.py
python3 scripts/check_negative_controls.py
```

[The comparison configuration](comparator.json) lists 22 theorem contracts
and 22 definition contracts. `ModalDepthChallenge.lean` is an independent
statement fixture with proof placeholders; `ModalDepthSolution.lean` imports
the proved implementation and supplies every contract. The implementation
never imports the challenge fixture. Placeholder axioms are forbidden in the
solution and supporting proofs.

The axiom audit inspects the compiled environment, including nested
namespaces, and checks all supporting theorems. The boundary controls prove
concrete counterexamples and require six corrupted proof attempts to fail
with their intended diagnostics. They cover blind color erasure, an
inadmissible phase action, a false phase identity, root/cycle collapse,
an incompatible residue modulus, and the wrong period for depth substitution.
The accepted baseline also exercises substitution into an empty target alphabet.
These are targeted controls, not exhaustive
mutation testing.

All Lean sources use explicit module visibility and expose the definitions
needed by the public interfaces. The source check also enforces module headers,
source size limits, and the absence of symbolic-link sources.

## Independent replay

[The Linux workflow](.github/workflows/verify.yml) takes an expected full Git
SHA, checks the checkout against it, builds the package, audits axioms and
runs the controls. Comparator checks elaborated statements and definitions;
Lean, NanoDa and con-ron replay the solution proof closure. A separate job
builds all project modules from a fresh checkout. Both jobs retain logs as
workflow artifacts and check that tracked sources remain unchanged.

For a configured Linux environment with the bundled checker tools and
sandbox, run:

```sh
python3 scripts/verify_kernels.py
```

The script requires a clean committed checkout and records its exact SHA,
tool and manifest hashes, comparator output, and each kernel's acceptance in
`.lake/verification/`. A successful local build alone does not establish
that the independent Linux replay has passed.
