# Modal-depth interpolation and substitution

A Lean 4 formalization of the depth-labeling criterion for interpolation in
Sacchetti's modal logics. For each positive integer $`n`$, let

```math
\mathsf{wGL}_n=\mathsf{K}+\{\Box(\Box^n A\to A)\to\Box A\}.
```

An occurrence carries its variable, polarity, and a label $`c(d)`$ of its modal
depth $`d`$. The label type is arbitrary. The exact condition on labels is

```math
P_n(c):\qquad c(k+n)=c(k)\quad\text{for every }k>0.
```

The package proves the following structural equivalences over natural-number
atoms. Each equivalence is a theorem without an ordinary interpolation hypothesis;
the corresponding ordinary property appears on its right-hand side.

| Property with depth labels | Equivalent condition | Lean theorem |
| --- | --- | --- |
| Uniform signed interpolation with source support | Ordinary uniform signed interpolation with source support, and $`P_n(c)`$ | `uniformSigned_iff` |
| Signed Craig interpolation | Ordinary Lyndon interpolation, and $`P_n(c)`$ | `signedCraig_iff` |
| Unsigned Craig interpolation | Ordinary Craig interpolation, and $`P_n(c)`$ | `unsignedCraig_iff` |

Ordinary uniform interpolation with source support is itself proved equivalent to
`OrdinaryULI ∧ OrdinaryLyndon` in `sourceULI_iff`. Thus the first classification can
also be stated using those two ordinary properties separately.

The same condition exactly classifies **labelings that permit every substitution**.
Choose an arbitrary replacement formula for each variable-label pair, and
replace all original occurrences simultaneously. `depthSubstitution_iff`
proves that every such substitution preserves theoremhood if and only if
$`P_n(c)`$. This result has no interpolation premise and permits arbitrary
target formulas, including formulas over an empty atom type. The source atom
type must be nonempty. `phaseSubstitution_iff` gives the equivalent sharp
condition for substitutions controlled by a successor map:
$`\delta^{n+1}=\delta`$.

The package does **not** prove the ordinary interpolation theorems from the
literature. In particular, `classification_from_ordinary` retains explicit
`OrdinaryULI` and `OrdinaryLyndon` hypotheses. Its conclusion identifies uniform
signed interpolation with $`P_n(c)`$; its positive existence assertion depends on
those hypotheses. The structural equivalences, phase-transfer proofs, and
obstructions are proved here.

The canonical labels distinguish depth zero from all positive depths and record
positive depth modulo $`n`$. Every admissible labeling is a coarsening of these
$`n+1`$ labels. Consequently:

- Residues modulo $`m>0`$ satisfy the criterion exactly when $`m\mid n`$.
- Parity satisfies it exactly when $`n`$ is even.
- Literal modal depth fails even unsigned Craig interpolation for every $`n>0`$.
- The root label may coincide with any cycle label; no successor operation on the
  user's label type is assumed.

This addresses the question of including depth in interpolation vocabulary
raised in the conclusion of [Sierra Miranda and Studer's 2026 paper](https://arxiv.org/pdf/2607.06359v1).
It determines all admissible depth labelings and supplies an explicit failed
substitution whenever positive-depth periodicity is violated.

## Further exact results

[Extensions.md](Extensions.md) develops four applications of the classification:

- **Parameter spectrum.** A labeling with least positive-depth period $`p`$
  permits all substitutions in exactly the logics with $`p\mid n`$.
  A labeling works separately for parameters $`a,b>0`$ exactly when it has
  positive-depth period $`\gcd(a,b)`$.
- **Boxed-atom implications.** For $`n>0`$,
  $`\mathsf{wGL}_n\vdash\Box^k p\to\Box^\ell p`$ exactly when
  $`k=\ell`$, or $`0<k\le\ell`$ and $`n\mid(\ell-k)`$.
  Different box depths remain pairwise inequivalent.
- **Composition.** Phase-controlled substitutions compose. For arbitrary
  labels, all successive substitutions can be represented by one substitution
  with the same labels exactly when equal labels have equal successor labels.
  Positive periodicity alone does not guarantee this. An explicit admissible
  period-two scheme fails even to represent a particular composite up to
  agreement on theoremhood.
- **Interpolation transfer.** Encoding preserves and reflects theoremhood.
  Encoding and decoding preserve syntax-tree node count and modal depth exactly.
  A given ordinary source-supported uniform interpolant therefore transfers
  with no additional nodes or boxes. An ordinary interpolation algorithm
  remains an external input.

Read [Proof.md](Proof.md) for the definitions, proof, and mathematical references.
The ordinary inputs are [Sierra Miranda and Studer, Theorem 5.9](https://arxiv.org/pdf/2607.06359v1),
[Iwata, Theorem 12.7](https://da.lib.kobe-u.ac.jp/da/kernel/D1007785/D1007785.pdf)
for $`n\ge2`$, and [Kurahashi, Theorem 5.2](https://arxiv.org/pdf/1809.00943v3)
for $`n=1`$.

## Build and verification

The Lean toolchain and mathlib revision are pinned in `lean-toolchain` and
`lake-manifest.json`.

```sh
lake build
python3 scripts/check_sources.py
python3 scripts/audit_axioms.py
python3 scripts/check_negative_controls.py
python3 scripts/check_verification_failures.py
```

[Verification.md](Verification.md) describes the proof contracts, negative
controls, and Linux kernel-replay scripts. The mathematical implementation is in
`ModalDepth/`: `Basic`, `Interpolation`, `Phase`, `Renaming`, `Periodic`,
`Obstruction`, `Transfer`, `Craig`, `Substitution`, `PeriodSpectrum`,
`BoxSpectrum`, `Composition`, and `Algorithmic`.

MIT license. Copyright (c) 2026 JD Jones.
