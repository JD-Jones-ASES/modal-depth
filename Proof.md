# Interpolation with modal-depth labels

Fix an integer $`n>0`$. We work in the normal modal logic $`L_n=\mathsf{wGL}_n`$,
whose additional axiom schema is

```math
\Box(\Box^n A\to A)\to\Box A.
```

The Hilbert presentation in `Basic.lean` includes all classical propositional
tautology instances, the distribution axiom, modus ponens, and necessitation.
Atoms are natural numbers in the main classification theorems.

Sierra Miranda and Studer propose investigating depth as part of the shared
vocabulary in interpolation in the conclusion of their
[2026 paper](https://arxiv.org/pdf/2607.06359v1). The classification below
separates literal depth, which cannot be retained, from the precise periodic
depth distinctions compatible with interpolation. The same criterion also
characterizes the depth labelings for which every associated substitution
preserves theoremhood.

## Occurrences and interpolation properties

An atomic occurrence has polarity $`s\in\{+,-\}`$ and modal depth $`d\in\mathbb{N}`$.
Passing into an implication's antecedent reverses polarity; passing through a box
increases depth by one. Fix an arbitrary type $`C`$ and map $`c:\mathbb{N}\to C`$.
Write $`S_c(A)`$ for the triples $`(s,p,c(d))`$ realized by occurrences in $`A`$.
Unsigned support forgets $`s`$ while retaining the pair $`(p,c(d))`$.

Uniform signed interpolation requires that for every formula $`A`$ and allowed set
$`W\subseteq\{+,-\}\times\mathbb{N}\times C`$, there is a formula $`I`$ such that

```math
S_c(I)\subseteq S_c(A)\cap W,\qquad L_n\vdash A\to I,
```

and, for every $`B`$ with $`S_c(B)\subseteq W`$, derivability of $`A\to B`$ implies
derivability of $`I\to B`$. The set $`W`$ is arbitrary; no finiteness or decidability
hypothesis is imposed. Signed Craig interpolation requires, for each derivable
$`A\to B`$, a factorization through $`I`$ with
$`S_c(I)\subseteq S_c(A)\cap S_c(B)`$. Its unsigned version uses unsigned support.

Let $`U_n`$, $`L_n^{\mathrm{int}}`$, and $`C_n^{\mathrm{int}}`$ denote respectively
ordinary source-supported uniform signed interpolation, ordinary Lyndon
interpolation, and ordinary Craig interpolation, all without depth labels.
To distinguish notation, $`L_n^{\mathrm{int}}`$ is a property of the logic $`L_n`$.
Set

```math
P_n(c)\quad\Longleftrightarrow\quad
\forall k>0,\ c(k+n)=c(k).
```

The main structural theorems are

```math
\mathrm{UniformSigned}_n(c)\Longleftrightarrow U_n\land P_n(c).
```

```math
\mathrm{SignedCraig}_n(c)\Longleftrightarrow L_n^{\mathrm{int}}\land P_n(c).
```

```math
\mathrm{UnsignedCraig}_n(c)\Longleftrightarrow C_n^{\mathrm{int}}\land P_n(c).
```

These are `uniformSigned_iff`, `signedCraig_iff`, and `unsignedCraig_iff`.
No ordinary interpolation property is assumed in their statements.

## Obtaining ordinary source support

`OrdinaryULI` uses only the permitted signed vocabulary in its support clause.
Suppose both `OrdinaryULI` and ordinary Lyndon interpolation hold. Apply the first
to $`A,W`$ to obtain $`J`$, and interpolate $`A\to J`$ by ordinary Lyndon interpolation.
The resulting $`I`$ has signed vocabulary contained in that of both $`A`$ and $`J`$.
Every permitted consequence $`B`$ of $`A`$ follows from $`J`$, and hence from $`I`$.
This proves $`U_n`$. Conversely, $`U_n`$ implies `OrdinaryULI` by forgetting source
support, and implies Lyndon interpolation by taking the permitted vocabulary to
be that of $`B`$. This is the exact equivalence `sourceULI_iff`.

Forgetting labels in a labeled interpolant proves the corresponding ordinary
property. For uniform interpolation, lift the allowed signed vocabulary to all
labels before applying the labeled property.

## Phase-dependent substitution

Let $`Q`$ be a phase type with successor $`\delta:Q\to Q`$ satisfying

```math
\delta^{n+1}(q)=\delta(q)\qquad(q\in Q).
```

Given formulas $`f_q(p)`$, define $`T_q`$ recursively by substituting $`f_q(p)`$ for an
atom, commuting with falsity and implication, and setting
$`T_q(\Box A)=\Box T_{\delta(q)}(A)`$. Then
$`T_q(\Box^r A)=\Box^r T_{\delta^r(q)}(A)`$.

Every $`T_q`$ preserves derivability. Propositional tautologies and distribution
are preserved directly. The weak Löb axiom is preserved because the two copies
of $`A`$ inside its outer box are translated at phases $`\delta^{n+1}(q)`$ and
$`\delta(q)`$, which agree. Modus ponens is immediate. Necessitation uses theorem
preservation at the successor phase. This is `phaseTranslate_provable`.

Encode $`A`$ at $`q`$ by replacing each occurrence of $`p`$ at depth $`d`$ with the atom
$`(p,\delta^d(q))`$. Decode at $`q`$ by replacing an atom $`(p,z)`$ at depth $`d`$ with
$`p`$ if $`z=\delta^d(q)`$ and with $`\bot`$ otherwise. Both operations are instances
of phase-dependent substitution. Decoding an encoded formula gives the original
formula, exactly as syntax, by `decode_encode`.

Encoding identifies signed phase support with ordinary signed vocabulary.
Every decoded occurrence of $`p`$ at depth $`d`$ comes from an occurrence of
$`(p,\delta^d(q))`$ with the same polarity. Apply ordinary interpolation to the
encoded formulas and decode its interpolant. These two occurrence facts give
all required support inclusions, and theorem preservation gives the two
implications. For uniform interpolation, lift $`W`$ to the encoded vocabulary;
any permitted consequence $`B`$ encodes to a permitted consequence, so universality
also survives decoding. The unsigned construction only needs ordinary Craig
interpolation and forgets the polarities when matching support.

This proves `uniformSigned_phase`, `signedCraig_phase`, and
`unsignedCraig_phase`. Their ordinary hypotheses concern atoms in
$`\mathbb{N}\times Q`$. For the finite phase type below, an encoding into
$`\mathbb{N}`$ with a left inverse transfers the corresponding ordinary property.
The renaming proofs transport both derivability and occurrence support.

## The canonical phase space and arbitrary labels

Use a separate root $`\ast`$ followed by a cycle of length $`n`$:

```math
Q_n=\{\ast\}\sqcup\mathbb{Z}/n\mathbb{Z},\qquad
\delta(\ast)=0,\qquad\delta(i)=i+1\pmod n.
```

In Lean, $`Q_n`$ is `Option (Fin n)`. Its successor satisfies
$`\delta^{n+1}=\delta`$. The orbit $`\gamma(d)=\delta^d(\ast)`$ obeys

```math
\gamma(0)=\ast,\qquad \gamma(k+1)=k\bmod n.
```

Thus $`\gamma(d)=\gamma(e)`$ exactly when both depths are zero, or both are
positive and $`d\equiv e\pmod n`$. In particular, the positive multiples of $`n`$
remain distinct from depth zero.

A labeling $`c`$ factors through $`\gamma`$ if and only if $`P_n(c)`$ holds.
For the forward direction, the orbit is periodic at positive depths.
For the reverse direction define $`h(\ast)=c(0)`$ and $`h(i)=c(i+1)`$ for
$`0\le i<n`$. Repeated use of $`P_n(c)`$ gives
$`c(k+1)=c((k\bmod n)+1)`$, hence $`c=h\circ\gamma`$.
This is `canonical_factor_iff`.

All three interpolation properties are preserved by coarsening labels along
any map $`h`$. Apply the property for $`\gamma`$ and map its support inclusions
through $`h`$; in the uniform case lift $`W`$ through $`h`$ first. Combining this with
the phase construction proves every sufficient direction. No compatibility
between equal labels and their successors is required. The root label can be
identified with a cycle label, and at most $`n+1`$ distinct labels occur.

## Necessity for every labeling

First derive $`L_n\vdash\Box A\to\Box^{n+1}A`$ from the Hilbert axioms.
Put $`D=A\land\Box^n A`$. Normality gives $`\Box^nD\to\Box^nA`$, hence
$`A\to(\Box^nD\to D)`$. After necessitation and distribution, the weak Löb
axiom for $`D`$ yields $`\Box A\to\Box D`$, which entails $`\Box^{n+1}A`$.
Further boxing proves

```math
L_n\vdash\Box^k p\to\Box^{k+n}p\qquad(k>0).
```

Suppose $`c(k)\ne c(k+n)`$. The two formulas have disjoint unsigned
variable-label support. An unsigned interpolant would therefore have no atomic
occurrences at all.

Consider the strict descending chain of worlds $`0,1,\ldots,k+n`$, with every
smaller world accessible. The weak Löb axiom is valid on this chain: induction
on a world establishes its conclusion from the boxed antecedent. Together with
the remaining Hilbert rules, this proves the needed soundness directly.
Under the valuation making every atom true, $`\Box^k p`$ holds at the top, so
any proposed interpolant holds there. A formula without atomic occurrences is
independent of the valuation. Change the valuation so that $`p`$ is false at
world zero and true elsewhere. The interpolant still holds, but
$`\Box^{k+n}p`$ fails along the descending path to zero, a contradiction.

Consequently unsigned Craig interpolation forces $`P_n(c)`$, with no ordinary
interpolation assumption. Signed Craig and uniform signed interpolation imply
the unsigned property, so the same obstruction proves all three necessary
directions. `unsignedCraig_periodic` formalizes this argument.

## Exact substitution criterion

For each label $`z`$ and source atom $`p`$, choose an arbitrary target formula
$`f_z(p)`$. Let $`T_{c,f}`$ replace each original occurrence of $`p`$ at depth
$`d`$ by $`f_{c(d)}(p)`$, commuting with the original connectives. Substitution
is simultaneous: it does not recurse into the inserted formulas. The source
atom type is nonempty; the target atom type may even be empty.

The theorem `depthSubstitution_iff` states

```math
\bigl(\forall f,A,\ L_n\vdash A\ \Longrightarrow\ L_n\vdash T_{c,f}(A)\bigr)
\quad\Longleftrightarrow\quad P_n(c).
```

This equivalence has no ordinary interpolation hypothesis. For sufficiency,
factor $`c=h\circ\gamma`$ through the canonical phase space. Substitution with
atomic images $`f_{h(q)}(p)`$ then coincides with $`T_{c,f}`$ at the root,
and the phase-preservation theorem applies.

For necessity, take $`k>0`$ with $`c(k+n)\ne c(k)`$. Substitute
$`\top`$ for atoms with label $`c(k)`$ and $`\bot`$ for atoms with all other
labels in the derivable formula $`\Box^k p\to\Box^{k+n}p`$. Its image is
$`\Box^k\top\to\Box^{k+n}\bot`$. At world $`k+n`$ on the strict descending
chain, the antecedent is true and the consequent is false. Soundness therefore
refutes theoremhood of the image. `depthTranslate_failure` gives this explicit
family of counterexamples.

The phase identity is sharp as well. For any successor map $`\delta:Q\to Q`$,
`phaseSubstitution_iff` proves

```math
\bigl(\forall f,q,A,\ L_n\vdash A\ \Longrightarrow\ L_n\vdash T_q(A)\bigr)
\quad\Longleftrightarrow\quad
\forall q,\ \delta^{n+1}(q)=\delta(q).
```

Necessity follows by applying the depth criterion to each orbit and using
$`k=1`$; sufficiency is `phaseTranslate_provable`. Thus the identity used by
the interpolation transfer is also the exact condition for unrestricted
formula-valued substitution to preserve the logic.

## Consequences and relation to ordinary interpolation

For $`m>0`$, the labels $`c(d)=d\bmod m`$ satisfy $`P_n(c)`$ exactly when $`m\mid n`$:
evaluate periodicity at $`k=m`$ for necessity, and use modular arithmetic for
sufficiency. Parity therefore qualifies exactly for even $`n`$. Literal depth
$`c(d)=d`$ never qualifies when $`n>0`$ and fails unsigned Craig interpolation.
For $`n=1`$, the canonical labeling records precisely zero versus positive depth.

The ordinary inputs are available in the mathematical literature. Sierra
Miranda and Studer, [*Proof Theory and Interpolation for Sacchetti's Logics*,
arXiv:2607.06359v1](https://arxiv.org/pdf/2607.06359v1), Theorem 5.9, establish
ordinary uniform Lyndon interpolation for every $`n\ge1`$. Iwata's thesis,
[*Some results on modal logics having arithmetical interpretations*](https://da.lib.kobe-u.ac.jp/da/kernel/D1007785/D1007785.pdf),
Theorem 12.7, gives Lyndon interpolation for $`n\ge2`$ and already distinguishes
unmodalized from modalized literals. Kurahashi,
[*Uniform Lyndon interpolation property in propositional modal logics*,
arXiv:1809.00943v3](https://arxiv.org/pdf/1809.00943v3), Theorem 5.2 and
Proposition 2.9, supply the uniform and ordinary Lyndon results for $`\mathsf{GL}`$.

Residue-dependent substitution also appears in Kurahashi and Okawa,
[*Effectively constructible fixed points in Sacchetti's modal logics of
provability*, arXiv:1811.12827v2](https://arxiv.org/abs/1811.12827v2),
Definition 4.7, Lemma 4.8, and Examples 5.1–5.2.

The package proves the structural equivalences and transfer arguments above.
It does not formalize these external ordinary interpolation theorems.
`classification_from_ordinary` therefore keeps `OrdinaryULI` and
`OrdinaryLyndon` as explicit hypotheses; applying the cited mathematical
results gives the positive existence corollary outside that formal boundary.
