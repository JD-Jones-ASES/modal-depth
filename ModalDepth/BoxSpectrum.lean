module

public import ModalDepth.Substitution

@[expose] public section

namespace ModalDepth

variable {α C : Type}

private theorem imp_self (n : ℕ) (A : Formula α) :
    Provable n (.imp A A) :=
  .taut (.imp (.atom A) (.atom A)) (by intro v; exact id)

/-- Iterating the derived n-transitivity theorem gives every admissible
upward shift of a positive box depth. -/
theorem boxes_imp_add_mul (n k t : ℕ) (hk : 0 < k) (A : Formula α) :
    Provable n (.imp (A.boxes k) (A.boxes (k + n * t))) := by
  induction t with
  | zero => simpa using imp_self n (A.boxes k)
  | succ t ih =>
    have hs := Obstruction.positive_n_transitivity (n := n)
      (k := k + n * t) A (by omega)
    simpa only [Nat.mul_succ, Nat.add_assoc] using Obstruction.imp_trans ih hs

private theorem eval_boxes_above_height (r x : ℕ) (hx : x < r)
    (v : ℕ → α → Prop) (A : Formula α) :
    Obstruction.eval v x (A.boxes r) := by
  induction r generalizing x with
  | zero => omega
  | succ r ih =>
    intro y hy
    exact ih y (by omega)

/-- An implication between two iterated boxes of the same atom can only
increase depth. A finite chain of height `l` excludes every downward shift. -/
theorem boxes_atom_imp_le (n : ℕ) (hn : 0 < n) (k l : ℕ) (p : α)
    (h : Provable n (.imp ((Formula.atom p).boxes k) ((Formula.atom p).boxes l))) :
    k ≤ l := by
  by_contra hkl
  have hA := eval_boxes_above_height k l (by omega)
    (fun x (_ : α) => x ≠ 0) (.atom p)
  exact Obstruction.not_eval_boxes_endpoint l p
    (Obstruction.sound hn h _ l hA)

private theorem eval_boxes_truth (r x : ℕ) (v : ℕ → Empty → Prop) :
    Obstruction.eval v x (Formula.boxes r (.imp .bot .bot)) := by
  induction r generalizing x with
  | zero => exact id
  | succ r ih => exact fun y _ => ih y

private theorem not_eval_boxes_falsity (r : ℕ) (v : ℕ → Empty → Prop) :
    ¬ Obstruction.eval v r (Formula.boxes r .bot) := by
  induction r with
  | zero => exact id
  | succ r ih => exact fun h => ih (h r (Nat.lt_succ_self r))

/-- Every theorem between boxed occurrences of one atom preserves every
admissible depth label. Otherwise a theorem-preserving substitution turns
it into a false implication from iterated truth to iterated falsity. -/
theorem boxes_atom_imp_label (n : ℕ) (hn : 0 < n) (k l : ℕ) (p : α)
    {c : ℕ → C} (hc : PositivePeriodic n c)
    (h : Provable n (.imp ((Formula.atom p).boxes k) ((Formula.atom p).boxes l))) :
    c k = c l := by
  classical
  by_contra hne
  let f : C → α → Formula Empty :=
    fun z _ => if z = c k then .imp .bot .bot else .bot
  have ht := hc.depthTranslate_provable hn f 0 h
  change Provable n (.imp (depthTranslate c f 0 ((Formula.atom p).boxes k))
    (depthTranslate c f 0 ((Formula.atom p).boxes l))) at ht
  rw [depthTranslate_boxes, depthTranslate_boxes] at ht
  simp only [Nat.zero_add, depthTranslate, phaseTranslate, f,
    ite_eq_left rfl, ite_eq_right (Ne.symm hne)] at ht
  exact not_eval_boxes_falsity l (fun _ _ => False)
    (Obstruction.sound hn ht _ l (eval_boxes_truth k l (fun _ _ => False)))

/-- Complete classification of implications between iterated boxes of one
atom: depth must increase and the canonical root-and-cycle label must agree. -/
theorem boxes_atom_imp_iff (n : ℕ) (hn : 0 < n) (k l : ℕ) (p : α) :
    Provable n (.imp ((Formula.atom p).boxes k) ((Formula.atom p).boxes l)) ↔
      k ≤ l ∧ canonicalOrbit n hn k = canonicalOrbit n hn l := by
  constructor
  · intro h
    exact ⟨boxes_atom_imp_le n hn k l p h,
      boxes_atom_imp_label n hn k l p (canonicalOrbit_periodic n hn) h⟩
  · rintro ⟨hkl, he⟩
    rcases (canonicalOrbit_eq_iff n hn k l).mp he with hzero | hpos
    · rcases hzero with ⟨rfl, rfl⟩
      exact imp_self n (.atom p)
    · have hdiv : n ∣ l - k := Nat.ModEq.dvd' hpos.2.2
      obtain ⟨t, ht⟩ := hdiv
      have hl : l = k + n * t := by omega
      rw [hl]
      exact boxes_imp_add_mul n k t hpos.1 (.atom p)

/-- Arithmetic form of the complete boxed-atom implication classification. -/
theorem boxes_atom_imp_iff_arithmetic (n : ℕ) (hn : 0 < n) (k l : ℕ) (p : α) :
    Provable n (.imp ((Formula.atom p).boxes k) ((Formula.atom p).boxes l)) ↔
      k = l ∨ (0 < k ∧ k ≤ l ∧ n ∣ l - k) := by
  rw [boxes_atom_imp_iff n hn k l p]
  constructor
  · rintro ⟨hkl, he⟩
    rcases (canonicalOrbit_eq_iff n hn k l).mp he with hzero | hpos
    · exact Or.inl (hzero.1.trans hzero.2.symm)
    · exact Or.inr ⟨hpos.1, hkl, Nat.ModEq.dvd' hpos.2.2⟩
  · rintro (rfl | ⟨hk, hkl, hdiv⟩)
    · exact ⟨le_rfl, rfl⟩
    · exact ⟨hkl, (canonicalOrbit_eq_iff n hn k l).mpr
        (Or.inr ⟨hk, lt_of_lt_of_le hk hkl, (Nat.modEq_iff_dvd' hkl).mpr hdiv⟩)⟩

/-- The precise transitivity spectrum of Sacchetti's logic. -/
theorem box_transitivity_spectrum (n : ℕ) (hn : 0 < n) (m : ℕ) (p : α) :
    Provable n (.imp (.box (.atom p)) ((Formula.atom p).boxes (m + 1))) ↔ n ∣ m := by
  change Provable n (.imp ((Formula.atom p).boxes 1)
    ((Formula.atom p).boxes (m + 1))) ↔ n ∣ m
  rw [boxes_atom_imp_iff_arithmetic n hn 1 (m + 1) p]
  constructor
  · rintro (he | ⟨_, _, hdiv⟩)
    · have hm : m = 0 := by omega
      simp [hm]
    · simpa using hdiv
  · intro hdiv
    exact Or.inr ⟨by omega, by omega, by simpa using hdiv⟩

/-- Equal periodic labels do not make different box depths equivalent:
all iterates of a fixed atom remain pairwise inequivalent. -/
theorem boxes_atom_mutual_iff (n : ℕ) (hn : 0 < n) (k l : ℕ) (p : α) :
    (Provable n (.imp ((Formula.atom p).boxes k) ((Formula.atom p).boxes l)) ∧
      Provable n (.imp ((Formula.atom p).boxes l) ((Formula.atom p).boxes k))) ↔ k = l := by
  constructor
  · rintro ⟨hkl, hlk⟩
    exact Nat.le_antisymm (boxes_atom_imp_le n hn k l p hkl)
      (boxes_atom_imp_le n hn l k p hlk)
  · rintro rfl
    exact ⟨imp_self n _, imp_self n _⟩

end ModalDepth
