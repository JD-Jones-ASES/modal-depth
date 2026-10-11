# Period spectra, boxed implications, and composable substitutions

These results extend the depth-label classification. All mathematical statements
in Sections 1-4 below have Lean proofs in the indicated modules. The ordinary
interpolation inputs remain explicit; none of these additions supplies a proof
of the external ordinary interpolation theorems.

## 1. A labeling's complete parameter spectrum

Write $`P_n(c)`$ for $`c(k+n)=c(k)`$ at every positive depth $`k`$.
The label at depth zero remains unrestricted.

For arbitrary natural numbers $`a,b`$,

```math
P_a(c)\land P_b(c)\quad\Longleftrightarrow\quad P_{\gcd(a,b)}(c).
```

To prove the nontrivial direction, first show that two periods yield their
remainder. If $`a=qb+r`$, periodicity with period $`b`$ gives
$`c(k+a)=c(k+r)`$, while period $`a`$ gives $`c(k+a)=c(k)`$.
All depths used here are positive. Thus $`r`$ is a period, and the Euclidean
algorithm gives the gcd. Conversely, every multiple of a period is a period.
This proof does not inadvertently impose periodicity at depth zero.

If $`c`$ has any positive period, it has a unique least positive period $`p`$,
and

```math
P_n(c)\quad\Longleftrightarrow\quad p\mid n.
```

If $`n`$ is a period, then $`n\bmod p`$ is a period. Minimality of $`p`$ forces that remainder to
be zero. Consequently a fixed labeling admits universal theorem-preserving
substitution in $`\mathsf{wGL}_n`$ exactly for the positive multiples of $`p`$.
If no positive period exists, it works for none of the positive parameters.

For positive $`a,b`$, a labeling works separately in both $`\mathsf{wGL}_a`$ and
$`\mathsf{wGL}_b`$ exactly when its positive depths have period
$`\gcd(a,b)`$. This statement concerns preservation in each logic separately;
it asserts no identity between the join of those logics and another logic.
For parameters 6 and 10, the most informative common labels distinguish the
root and the two positive parity classes. For parameters 4 and 9, all positive
depths must have the same label, while the root can still be different.

The corresponding interpolation spectra retain the ordinary properties:

```math
\mathrm{UniformSigned}_n(c)\Longleftrightarrow U_n\land (p\mid n).
```

```math
\mathrm{SignedCraig}_n(c)\Longleftrightarrow L_n^{\mathrm{int}}\land (p\mid n).
```

```math
\mathrm{UnsignedCraig}_n(c)\Longleftrightarrow C_n^{\mathrm{int}}\land (p\mid n).
```

For positive $`a,b`$, the inclusion order on admissible-label families also recovers divisibility:
every $`a`$-periodic labeling is $`b`$-periodic if and only if $`a\mid b`$.
The necessity is already detected by natural-number labels $`c(d)=d\bmod a`$.

**Lean:** `PeriodSpectrum.lean`, especially `positivePeriodic_gcd_iff`,
`IsLeastPositivePeriod.period_iff`, `positivePeriodic_spectrum`,
`depthSubstitution_pair_iff`, the three interpolation spectrum theorems,
and `positivePeriodic_inclusion_iff`.

## 2. Exact implications between iterated boxes

For $`n>0`$, a source atom $`p`$, and arbitrary depths $`k,\ell\ge0`$,

```math
\mathsf{wGL}_n\vdash\Box^k p\to\Box^\ell p
\quad\Longleftrightarrow\quad
k=\ell\ \lor\ \bigl(0\lt k\le\ell\ \land\ n\mid(\ell-k)\bigr).
```

Equivalently, $`k\le\ell`$ and the canonical labels of $`k`$ and $`\ell`$ agree.

For sufficiency, equal depths give the identity implication. At positive
depth, repeatedly compose the existing theorem
$`\Box^k A\to\Box^{k+n}A`$.

For necessity, there are two independent restrictions. First, if $`k>\ell`$,
a strict descending chain of height $`\ell`$ makes $`\Box^k p`$ vacuously true
at its top, while making $`p`$ false at its bottom falsifies $`\Box^\ell p`$.
Second, any admissible labeling must agree at the two depths of a derivable
implication. Otherwise an admissible label-dependent substitution replacing
the first label by truth and the second by falsity would produce
$`\Box^k\top\to\Box^\ell\bot`$. That formula is false on a chain of height
$`\ell`$. Apply this observation to the canonical labeling.

Two useful consequences are

```math
\mathsf{wGL}_n\vdash\Box p\to\Box^{m+1}p
\quad\Longleftrightarrow\quad n\mid m
```

and

```math
\mathsf{wGL}_n\vdash\Box^k p\leftrightarrow\Box^\ell p
\quad\Longleftrightarrow\quad k=\ell.
```

Thus all iterated boxes of an atom remain pairwise inequivalent. The recurring
vocabulary labels do not identify formulas of different modal depths.

For example, in $`\mathsf{wGL}_3`$, $`\Box^2p\to\Box^5p`$ is derivable,
but $`\Box^2p\to\Box^4p`$, $`\Box^5p\to\Box^2p`$, and
$`p\to\Box^3p`$ are not. The theorem is an exact arithmetic decision rule for
this family of implications, not a decision procedure for all modal formulas.

**Lean:** `BoxSpectrum.lean`, especially `boxes_atom_imp_iff`,
`boxes_atom_imp_iff_arithmetic`, `box_transitivity_spectrum`,
and `boxes_atom_mutual_iff`.

## 3. Exactly when depth substitutions can be combined

For one phase system with successor $`\delta`$, phase substitutions satisfy
the composition law

```math
T_g^q(T_f^q(A))=T_h^q(A),\qquad
h_r(p)=T_g^r(f_r(p)).
```

This is a syntactic identity for every successor map; the weak Loeb power
identity is required only when asserting theorem preservation. Two different
phase systems can be combined using their product phase space.

Coarsening labels creates a real distinction. Let $`T_{c,f}`$ denote
substitution controlled by labels $`c(d)`$. For nonempty source and intermediate
alphabets, with an arbitrary final alphabet, every composition
$`T_{c,g}\circ T_{c,f}`$ equals some single $`T_{c,h}`$ exactly when

```math
\forall d,e\ge0,\quad c(d)=c(e)\Longrightarrow c(d+1)=c(e+1).
```

Call this condition *successor compatibility*. This classification
requires no modal-logic or interpolation assumption. It concerns equality of
the resulting formulas, including the formulas inserted by the first stage.

For sufficiency, successor compatibility propagates equality of labels to
every subsequent depth. Choose a representative depth for each attained label
and translate each replacement formula from that representative. The result
does not depend on the choice, so it defines the required replacement $`h`$.
For necessity, insert one box at every source atom. A second substitution can
distinguish two unequal successor labels using truth and falsity. Testing
$`\Box^d p`$ and $`\Box^e p`$ then forces incompatible replacements at the
same original label.

### A theorem-preserving scheme that fails composition closure

For period two, take

```math
c(0)=c(1)=1,\qquad c(2)=0,\qquad c(3)=1,\qquad c(4)=0,\ldots
```

This satisfies $`P_2(c)`$. Let the first substitution send every atom $`p`$ to
$`\Box p`$, and let the second replace label 1 by $`\top`$ and other labels
by $`\bot`$. Both substitutions preserve theorems of $`\mathsf{wGL}_2`$, as
does their composition. Yet the composite sends

```math
p\longmapsto\Box\top,\qquad
\Box p\longmapsto\Box^2\bot.
```

A single substitution using $`c`$ would send these two inputs to $`H`$ and
$`\Box H`$, because $`c(0)=c(1)`$. It therefore cannot match the composite.
The obstruction is stronger than a mismatch of syntax: no single such
substitution can even agree with the composite on which outputs are theorems.
The first displayed output is a theorem and the second is not; theoremhood of
$`H`$ would force theoremhood of $`\Box H`$ by necessitation.

For implementations, retain the canonical root-and-cycle phase internally when
combining transformations. Arbitrary coarsened labels can remain the public
vocabulary policy. Every one-stage substitution allowed by that policy remains
valid; the hidden phase prevents loss of the information needed by later stages.

**Lean:** `Composition.lean`, especially `phaseTranslate_compose`,
`phaseTranslate_compose_product`, `depthCompositionClosed_iff`, and
`CompositionBoundary.no_theoremhood_equivalent_coarse_substitution`.

## 4. Interpolation transfer without extra syntax nodes or boxes

Encoding preserves and reflects theoremhood for an admissible phase action:

```math
\mathsf{wGL}_n\vdash\mathrm{encode}_q(A)
\quad\Longleftrightarrow\quad\mathsf{wGL}_n\vdash A.
```

The reverse direction decodes the encoded theorem and uses the exact syntactic
round trip. Both encoding and decoding preserve syntax-tree node count and
maximum modal depth. An atom and falsity each count as one node, so replacing
an incorrectly tagged atom by falsity leaves both measures unchanged.

If an ordinary source-supported uniform interpolant $`J`$ for the encoded
formula has been obtained, its decoded interpolant $`I`$ has exactly the node
count and modal depth of $`J`$. The witness-level theorem checks the support
condition, implication, and universal consequence property as well as these
equalities. With the canonical phase space, no more than $`n+1`$ tagged names
per original atom are available, and encoding does not duplicate occurrences.

These identities justify an encode/interpolate/decode wrapper around an ordinary
interpolation procedure. For the finite canonical phase type, phase equality is
decidable. The generic Lean decoder uses classical equality and is declared
noncomputable; the theorem transfers a supplied interpolant rather than
implementing an interpolation procedure. Any bound expressed in these
syntax-tree measures transfers to the decoded witness. Node count treats atom
names as unit-cost leaves and is not a bound on their bit encoding, proof size,
or search runtime.

**Lean:** `Composition.lean` contains `encode_provable_iff`;
`Algorithmic.lean` contains `encode_nodeCount`,
`encode_modalDepth`, `decode_nodeCount`, `decode_modalDepth`, and
`decode_uniformInterpolant`.

## 5. The ordinary-input conventions

The ordinary-input citations in [Proof.md](Proof.md) match the formal boundary.
Sierra Miranda and Studer, arXiv:2607.06359v1, Definition 2.5, use arbitrary
permitted positive and negative vocabularies. This agrees with `OrdinaryULI`;
their Theorem 5.9 supplies this property for every $`n\ge1`$. The additional
source-support requirement is introduced separately in this repository and
obtained using ordinary Lyndon interpolation by `sourceULI_iff`.

Iwata's thesis, Theorem 12.7, already distinguishes unmodalized and modalized
literals for $`n\ge2`$. Thus the root-versus-positive distinction itself
should not be described as new. Kurahashi's arXiv:1809.00943v3, Definition 2.7,
uses finite forbidden signed vocabularies together with support in the source
formula. To obtain the arbitrary-permitted-vocabulary convention for GL, use
the finite forbidden sets $`V^+(A)\setminus W^+`$ and
$`V^-(A)\setminus W^-`$. Any formula with vocabulary in $`W`$ avoids these
sets, and the output support lies in both $`A`$ and $`W`$.

The depth-residue manipulations in Kurahashi and Okawa, arXiv:1811.12827v2,
Definition 4.7 and Lemma 4.8, are relevant precedents. Their fixed-point
construction uses occurrence-selective replacement. The present classification
concerns arbitrary simultaneous formula-valued substitutions and their exact
necessary period. These are distinct statements.
