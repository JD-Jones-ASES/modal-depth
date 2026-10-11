# Modal-depth interpolation

A Lean 4 formalization of the depth-labeling criterion for interpolation in
Sacchetti's modal logics. For each positive integer $`n`$, let

```math
\mathsf{wGL}_n=\mathsf K+\{\Box(\Box^n A\to A)\to\Box A\}.
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
```

[Verification.md](Verification.md) describes the proof contracts, negative
controls, and Linux kernel-replay scripts. The mathematical implementation is in
`ModalDepth/`: `Basic`, `Interpolation`, `Phase`, `Renaming`, `Periodic`,
`Obstruction`, `Transfer`, and `Craig`.

MIT license. Copyright (c) 2026 JD Jones.
