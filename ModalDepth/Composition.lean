module

public import ModalDepth.Substitution

@[expose] public section

namespace ModalDepth

variable {α β χ Q R C : Type}

/-- Replacing every atom by itself is the identity, at every phase. -/
theorem phaseTranslate_identity (δ : Q → Q) (q : Q) (A : Formula α) :
    phaseTranslate δ (fun _ p => .atom p) q A = A := by
  induction A generalizing q with
  | atom p => rfl
  | bot => rfl
  | imp A B ihA ihB => simp only [phaseTranslate, ihA, ihB]
  | box A ih => simp only [phaseTranslate, ih]

/-- Successive phase-controlled substitutions compose by translating each
replacement at its own starting phase. No periodicity assumption is needed. -/
theorem phaseTranslate_compose (δ : Q → Q)
    (f : Q → α → Formula β) (g : Q → β → Formula χ)
    (q : Q) (A : Formula α) :
    phaseTranslate δ g q (phaseTranslate δ f q A) =
      phaseTranslate δ (fun r p => phaseTranslate δ g r (f r p)) q A := by
  induction A generalizing q with
  | atom p => rfl
  | bot => rfl
  | imp A B ihA ihB => simp only [phaseTranslate, ihA, ihB]
  | box A ih => simp only [phaseTranslate, ih]

/-- Independent phase systems can be composed by retaining both phases. -/
theorem phaseTranslate_compose_product (δ : Q → Q) (ε : R → R)
    (f : Q → α → Formula β) (g : R → β → Formula χ)
    (q : Q) (r : R) (A : Formula α) :
    phaseTranslate ε g r (phaseTranslate δ f q A) =
      phaseTranslate (fun z : Q × R => (δ z.1, ε z.2))
        (fun z p => phaseTranslate ε g z.2 (f z.1 p)) (q, r) A := by
  induction A generalizing q r with
  | atom p => rfl
  | bot => rfl
  | imp A B ihA ihB => simp only [phaseTranslate, ihA, ihB]
  | box A ih => simp only [phaseTranslate, ih]

/-- Phase encoding preserves and reflects theoremhood: decoding supplies
the reverse implication, without an interpolation premise. -/
theorem encode_provable_iff (δ : Q → Q) {n : ℕ}
    (hδ : ∀ q, δ^[n + 1] q = δ q) (q : Q) (A : Formula α) :
    Provable n (encode δ q A) ↔ Provable n A := by
  constructor
  · intro h
    have hd := decode_provable δ hδ h q
    simpa only [decode_encode] using hd
  · intro h
    exact encode_provable δ hδ h q

/-- Equal depth labels have equal successor labels. Positive periodicity
alone does not imply this condition. -/
def SuccessorCompatible (c : ℕ → C) : Prop :=
  ∀ d e : ℕ, c d = c e → c (d + 1) = c (e + 1)

/-- Every pair of successive substitutions can be represented syntactically
by one substitution using the same original depth labels. -/
def DepthCompositionClosed (c : ℕ → C) (α β χ : Type) : Prop :=
  ∀ (f : C → α → Formula β) (g : C → β → Formula χ),
    ∃ h : C → α → Formula χ, ∀ A : Formula α,
      depthTranslate c h 0 A =
        depthTranslate c g 0 (depthTranslate c f 0 A)

/-- Successor-compatible labels determine every later label as well. -/
theorem SuccessorCompatible.add {c : ℕ → C} (hc : SuccessorCompatible c)
    {d e : ℕ} (hde : c d = c e) (k : ℕ) : c (d + k) = c (e + k) := by
  induction k with
  | zero => simpa only [Nat.add_zero] using hde
  | succ k ih =>
    simpa only [Nat.add_assoc] using hc (d + k) (e + k) ih

/-- A starting label suffices to determine translation exactly when its
future labels are well defined. -/
theorem SuccessorCompatible.depthTranslate_eq {c : ℕ → C}
    (hc : SuccessorCompatible c) (f : C → α → Formula β)
    {d e : ℕ} (hde : c d = c e) (A : Formula α) :
    depthTranslate c f d A = depthTranslate c f e A := by
  induction A generalizing d e with
  | atom p =>
    change f (c d) p = f (c e) p
    rw [hde]
  | bot => rfl
  | imp A B ihA ihB =>
    change Formula.imp (depthTranslate c f d A) (depthTranslate c f d B) =
      Formula.imp (depthTranslate c f e A) (depthTranslate c f e B)
    rw [ihA hde, ihB hde]
  | box A ih =>
    change Formula.box (depthTranslate c f (d + 1) A) =
      Formula.box (depthTranslate c f (e + 1) A)
    rw [ih (hc d e hde)]

private theorem compose_at_representatives {c : ℕ → C}
    (hc : SuccessorCompatible c) (rep : C → ℕ)
    (hrep : ∀ d, c (rep (c d)) = c d)
    (f : C → α → Formula β) (g : C → β → Formula χ)
    (offset : ℕ) (A : Formula α) :
    depthTranslate c g offset (depthTranslate c f offset A) =
      depthTranslate c
        (fun z p => depthTranslate c g (rep z) (f z p)) offset A := by
  induction A generalizing offset with
  | atom p =>
    change depthTranslate c g offset (f (c offset) p) =
      depthTranslate c g (rep (c offset)) (f (c offset) p)
    exact hc.depthTranslate_eq g (hrep offset).symm _
  | bot => rfl
  | imp A B ihA ihB =>
    change Formula.imp
      (depthTranslate c g offset (depthTranslate c f offset A))
      (depthTranslate c g offset (depthTranslate c f offset B)) = _
    rw [ihA, ihB]
    rfl
  | box A ih =>
    change Formula.box
      (depthTranslate c g (offset + 1) (depthTranslate c f (offset + 1) A)) = _
    rw [ih]
    rfl

/-- Successor-compatible labelings support arbitrary staged substitutions. -/
theorem depthCompositionClosed_of_compatible {c : ℕ → C}
    (hc : SuccessorCompatible c) : DepthCompositionClosed c α β χ := by
  classical
  let rep : C → ℕ := fun z => if h : ∃ d, c d = z then Nat.find h else 0
  have hrep : ∀ d, c (rep (c d)) = c d := by
    intro d
    simp only [rep, dite_eq_left (show ∃ e, c e = c d from ⟨d, rfl⟩)]
    exact Nat.find_spec (show ∃ e, c e = c d from ⟨d, rfl⟩)
  intro f g
  refine ⟨fun z p => depthTranslate c g (rep z) (f z p), ?_⟩
  intro A
  exact (compose_at_representatives hc rep hrep f g 0 A).symm

private theorem boxes_injective (k : ℕ) :
    Function.Injective (Formula.boxes k : Formula α → Formula α) := by
  induction k with
  | zero => intro A B h; exact h
  | succ k ih =>
    intro A B h
    exact ih (Formula.box.inj h)

/-- If every composition exists, labels that coincide now must also
coincide after one inserted box. Truth and falsity distinguish the latter. -/
theorem depthCompositionClosed_compatible {c : ℕ → C}
    [Nonempty α] [Nonempty β] (hclosed : DepthCompositionClosed c α β χ) :
    SuccessorCompatible c := by
  classical
  intro d e hde
  by_contra hnext
  let p : α := Classical.choice ‹Nonempty α›
  let b : β := Classical.choice ‹Nonempty β›
  let f : C → α → Formula β := fun _ _ => .box (.atom b)
  let g : C → β → Formula χ :=
    fun z _ => if z = c (d + 1) then .imp .bot .bot else .bot
  obtain ⟨h, hh⟩ := hclosed f g
  have hd := hh (Formula.boxes d (.atom p))
  have he := hh (Formula.boxes e (.atom p))
  simp only [depthTranslate_boxes, Nat.zero_add] at hd he
  change Formula.boxes d (h (c d) p) =
    Formula.boxes d (.box (g (c (d + 1)) b)) at hd
  change Formula.boxes e (h (c e) p) =
    Formula.boxes e (.box (g (c (e + 1)) b)) at he
  have hd' := boxes_injective d hd
  have he' := boxes_injective e he
  simp only [g, ite_eq_left rfl] at hd'
  simp only [g, ite_eq_right (Ne.symm hnext)] at he'
  rw [← hde, hd'] at he'
  cases he'

/-- Exact criterion for closure under composition. Source and intermediate
alphabets are nonempty; the final alphabet may be empty. This is a syntactic
classification and requires no modal-logic or interpolation hypothesis. -/
theorem depthCompositionClosed_iff (c : ℕ → C) [Nonempty α] [Nonempty β] :
    DepthCompositionClosed c α β χ ↔ SuccessorCompatible c :=
  ⟨depthCompositionClosed_compatible, depthCompositionClosed_of_compatible⟩

namespace CompositionBoundary

/-- An admissible period-two labeling whose equal root and first-step
labels have different successors. -/
def coarseLabel (d : ℕ) : ℕ := if d = 0 then 1 else d % 2

theorem coarseLabel_periodic : PositivePeriodic 2 coarseLabel := by
  intro k hk
  simp only [coarseLabel, ite_eq_right (Nat.ne_of_gt hk),
    ite_eq_right (show k + 2 ≠ 0 by omega), Nat.add_mod_right]

/-- Insert a box at each original atomic occurrence. -/
def insertBox : ℕ → ℕ → Formula ℕ := fun _ p => .box (.atom p)

/-- Replace label one by truth and label zero by falsity. The target
language has no atoms, so no target-alphabet assumption is involved. -/
def selectTruth : ℕ → ℕ → Formula PEmpty :=
  fun z _ => if z = 1 then .imp .bot .bot else .bot

/-- Each of these substitutions individually preserves wGL_2. -/
theorem first_preserves {A : Formula ℕ} (hA : Provable 2 A) :
    Provable 2 (depthTranslate coarseLabel insertBox 0 A) :=
  coarseLabel_periodic.depthTranslate_provable (by omega) insertBox 0 hA

theorem second_preserves {A : Formula ℕ} (hA : Provable 2 A) :
    Provable 2 (depthTranslate coarseLabel selectTruth 0 A) :=
  coarseLabel_periodic.depthTranslate_provable (by omega) selectTruth 0 hA

/-- The actual composite remains theorem preserving even though one
substitution using the coarsened labels cannot represent it. -/
theorem composite_preserves {A : Formula ℕ} (hA : Provable 2 A) :
    Provable 2 (depthTranslate coarseLabel selectTruth 0
      (depthTranslate coarseLabel insertBox 0 A)) :=
  second_preserves (first_preserves hA)

/-- The composite cannot be represented by one substitution using this
same coarsened labeling. Its images of p and box p demand different
replacements at occurrences that have the same original label. -/
theorem no_single_coarse_substitution :
    ¬ ∃ h : ℕ → ℕ → Formula PEmpty, ∀ A : Formula ℕ,
      depthTranslate coarseLabel h 0 A =
        depthTranslate coarseLabel selectTruth 0
          (depthTranslate coarseLabel insertBox 0 A) := by
  rintro ⟨h, hh⟩
  have hp := hh (.atom 0)
  have hbp := hh (.box (.atom 0))
  norm_num [depthTranslate, phaseTranslate, coarseLabel, insertBox, selectTruth] at hp hbp
  rw [hp] at hbp
  cases hbp

/-- This particular composite cannot even be matched on which output
formulas are theorems. A single coarsened substitution would have to send
p to a theorem and box p to a nontheorem, contrary to necessitation. -/
theorem no_theoremhood_equivalent_coarse_substitution :
    ¬ ∃ h : ℕ → ℕ → Formula PEmpty, ∀ A : Formula ℕ,
      Provable 2 (depthTranslate coarseLabel h 0 A) ↔
        Provable 2 (depthTranslate coarseLabel selectTruth 0
          (depthTranslate coarseLabel insertBox 0 A)) := by
  rintro ⟨h, hh⟩
  have htop : Provable 2 (Formula.imp (Formula.bot : Formula PEmpty) .bot) :=
    Provable.taut (.imp .bot .bot) (by intro v; exact id)
  have hfirst : Provable 2 (depthTranslate coarseLabel selectTruth 0
      (depthTranslate coarseLabel insertBox 0 (Formula.atom 0))) := by
    change Provable 2 (.box (.imp .bot .bot))
    exact Provable.nec htop
  have hp := (hh (.atom 0)).mpr hfirst
  change Provable 2 (h 1 0) at hp
  have hbox : Provable 2 (depthTranslate coarseLabel h 0 (.box (.atom 0))) := by
    change Provable 2 (.box (h 1 0))
    exact Provable.nec hp
  have hsecond := (hh (.box (.atom 0))).mp hbox
  change Provable 2 (.box (.box .bot)) at hsecond
  have heval := Obstruction.sound (by omega) hsecond (fun _ _ => False) 2
  exact heval 1 (by omega) 0 (by omega)

end CompositionBoundary

end ModalDepth
