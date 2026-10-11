module

public import ModalDepth.Basic

@[expose] public section

namespace ModalDepth

variable {α β Q : Type}

/-- A substitution whose atomic image depends on the phase of an occurrence. -/
def phaseTranslate (δ : Q → Q) (f : Q → α → Formula β) (q : Q) :
    Formula α → Formula β
  | .atom p => f q p
  | .bot => .bot
  | .imp A B => .imp (phaseTranslate δ f q A) (phaseTranslate δ f q B)
  | .box A => .box (phaseTranslate δ f (δ q) A)

theorem phaseTranslate_boxes (δ : Q → Q) (f : Q → α → Formula β)
    (k : ℕ) (q : Q) (A : Formula α) :
    phaseTranslate δ f q (A.boxes k) =
      (phaseTranslate δ f (δ^[k] q) A).boxes k := by
  induction k generalizing q with
  | zero => rfl
  | succ k ih =>
    simp only [Formula.boxes, phaseTranslate, ih, Function.iterate_succ_apply]

private def mapTemplate (g : α → β) : PropForm α → PropForm β
  | .atom a => .atom (g a)
  | .bot => .bot
  | .imp A B => .imp (mapTemplate g A) (mapTemplate g B)

private theorem mapTemplate_eval (g : α → β) (t : PropForm α) (v : β → Prop) :
    (mapTemplate g t).eval v = t.eval (fun a => v (g a)) := by
  induction t with
  | atom a => rfl
  | bot => rfl
  | imp A B ihA ihB => simp only [mapTemplate, PropForm.eval, ihA, ihB]

private theorem phaseTranslate_template (δ : Q → Q) (f : Q → α → Formula β)
    (q : Q) (t : PropForm (Formula α)) :
    phaseTranslate δ f q (t.subst id) =
      (mapTemplate (phaseTranslate δ f q) t).subst id := by
  induction t with
  | atom a => rfl
  | bot => rfl
  | imp A B ihA ihB =>
    simp only [PropForm.subst, phaseTranslate, mapTemplate, ihA, ihB]

/-- The weak Löb schema is preserved when phases repeat after the outer box. -/
theorem phaseTranslate_provable (δ : Q → Q) (f : Q → α → Formula β)
    {n : ℕ} (hδ : ∀ q, δ^[n + 1] q = δ q)
    {A : Formula α} (hA : Provable n A) :
    ∀ q, Provable n (phaseTranslate δ f q A) := by
  induction hA with
  | taut t ht =>
    intro q
    rw [phaseTranslate_template]
    apply Provable.taut
    intro v
    rw [mapTemplate_eval]
    exact ht _
  | k A B =>
    intro q
    exact Provable.k _ _
  | loeb A =>
    intro q
    simp only [phaseTranslate, phaseTranslate_boxes]
    have heq : δ^[n] (δ q) = δ q := by
      simpa only [← Function.iterate_succ_apply] using hδ q
    rw [heq]
    exact Provable.loeb _
  | mp hAB hA ihAB ihA =>
    intro q
    exact Provable.mp (ihAB q) (ihA q)
  | nec hA ihA =>
    intro q
    exact Provable.nec (ihA (δ q))

/-- Encode every atom together with its phase. -/
def encode (δ : Q → Q) (q : Q) (A : Formula α) : Formula (α × Q) :=
  phaseTranslate δ (fun q p => .atom (p, q)) q A

/-- Erase an atomic occurrence if its stored phase is incorrect. -/
noncomputable def decode (δ : Q → Q) (q : Q) (A : Formula (α × Q)) : Formula α := by
  classical
  exact phaseTranslate δ (fun q p => if p.2 = q then .atom p.1 else .bot) q A

theorem decode_encode (δ : Q → Q) (q : Q) (A : Formula α) :
    decode δ q (encode δ q A) = A := by
  classical
  induction A generalizing q with
  | atom p => simp [encode, decode, phaseTranslate]
  | bot => rfl
  | imp A B ihA ihB =>
    change Formula.imp (decode δ q (encode δ q A))
      (decode δ q (encode δ q B)) = _
    rw [ihA, ihB]
  | box A ih =>
    change Formula.box (decode δ (δ q) (encode δ (δ q) A)) = _
    rw [ih]

theorem encode_occurs_iff (δ : Q → Q) (q : Q) (A : Formula α)
    (s : Bool) (d : ℕ) (p : α) (z : Q) :
    (encode δ q A).Occurs s d (p, z) ↔
      A.Occurs s d p ∧ δ^[d] q = z := by
  induction A generalizing q s d with
  | atom a =>
    simp only [encode, phaseTranslate, Formula.Occurs, Prod.mk.injEq]
    constructor
    · rintro ⟨hs, hd, hp, hz⟩
      subst d
      exact ⟨⟨hs, rfl, hp⟩, hz.symm⟩
    · rintro ⟨⟨hs, hd, hp⟩, hz⟩
      subst d
      exact ⟨hs, rfl, hp, hz.symm⟩
  | bot => simp [encode, phaseTranslate, Formula.Occurs]
  | imp A B ihA ihB =>
    change ((encode δ q A).Occurs (!s) d (p,z) ∨
      (encode δ q B).Occurs s d (p,z)) ↔ _
    rw [ihA, ihB]
    simp only [Formula.Occurs]
    tauto
  | box A ih =>
    change (∃ e, d = e + 1 ∧ (encode δ (δ q) A).Occurs s e (p,z)) ↔ _
    simp only [ih, Formula.Occurs]
    constructor
    · rintro ⟨e, rfl, ho, he⟩
      exact ⟨⟨e, rfl, ho⟩, by simpa only [Function.iterate_succ_apply] using he⟩
    · rintro ⟨⟨e, rfl, ho⟩, he⟩
      exact ⟨e, rfl, ho, by simpa only [Function.iterate_succ_apply] using he⟩

theorem encode_vocab_iff (δ : Q → Q) (q : Q) (A : Formula α)
    (s : Bool) (p : α) (z : Q) :
    (encode δ q A).vocab s (p,z) ↔
      A.support (fun d => δ^[d] q) s p z := by
  simp only [Formula.vocab, Formula.support, encode_occurs_iff]

theorem decode_occurs (δ : Q → Q) (q : Q) (A : Formula (α × Q))
    (s : Bool) (d : ℕ) (p : α) :
    (decode δ q A).Occurs s d p → A.Occurs s d (p, δ^[d] q) := by
  classical
  induction A generalizing q s d with
  | atom a =>
    by_cases ha : a.2 = q
    · simp only [decode, phaseTranslate, ite_eq_left ha, Formula.Occurs]
      rintro ⟨hs, hd, hp⟩
      subst d
      exact ⟨hs, rfl, Prod.ext hp ha.symm⟩
    · simp [decode, phaseTranslate, ha, Formula.Occurs]
  | bot => simp [decode, phaseTranslate, Formula.Occurs]
  | imp A B ihA ihB =>
    change ((decode δ q A).Occurs (!s) d p ∨ (decode δ q B).Occurs s d p) → _
    intro h
    exact h.elim (fun h => Or.inl (ihA q (!s) d h))
      (fun h => Or.inr (ihB q s d h))
  | box A ih =>
    change (∃ e, d = e + 1 ∧ (decode δ (δ q) A).Occurs s e p) → _
    rintro ⟨e, rfl, ho⟩
    exact ⟨e, rfl, by simpa only [Function.iterate_succ_apply] using ih (δ q) s e ho⟩

theorem decode_support (δ : Q → Q) (q : Q) (A : Formula (α × Q))
    (s : Bool) (p : α) (z : Q) :
    (decode δ q A).support (fun d => δ^[d] q) s p z → A.vocab s (p,z) := by
  rintro ⟨d, ho, hz⟩
  exact ⟨d, by simpa only [hz] using decode_occurs δ q A s d p ho⟩

theorem encode_provable (δ : Q → Q) {n : ℕ}
    (hδ : ∀ q, δ^[n + 1] q = δ q) {A : Formula α} (hA : Provable n A)
    (q : Q) : Provable n (encode δ q A) :=
  phaseTranslate_provable δ _ hδ hA q

theorem decode_provable (δ : Q → Q) {n : ℕ}
    (hδ : ∀ q, δ^[n + 1] q = δ q) {A : Formula (α × Q)} (hA : Provable n A)
    (q : Q) : Provable n (decode δ q A) :=
  phaseTranslate_provable δ _ hδ hA q

end ModalDepth
