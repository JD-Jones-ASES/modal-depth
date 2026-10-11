import ModalDepth.Basic

namespace ModalDepth

/-- A root followed by a cycle of length `n`. -/
abbrev CanonicalPhase (n : ℕ) := Option (Fin n)

/-- Successor on the canonical root-and-cycle phase space. -/
def canonicalSuccessor (n : ℕ) (hn : 0 < n) : CanonicalPhase n → CanonicalPhase n
  | none => some ⟨0, hn⟩
  | some i => some ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

/-- The phase reached at depth `k`. -/
def canonicalOrbit (n : ℕ) (hn : 0 < n) (k : ℕ) : CanonicalPhase n :=
  (canonicalSuccessor n hn)^[k] none

theorem canonicalSuccessor_iterate_some (n : ℕ) (hn : 0 < n)
    (i : Fin n) (k : ℕ) :
    (canonicalSuccessor n hn)^[k] (some i) =
      some ⟨(i.val + k) % n, Nat.mod_lt _ hn⟩ := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [canonicalSuccessor]
    congr 2
    simp only [Nat.mod_add_mod, Nat.add_assoc]

theorem canonicalOrbit_succ (n : ℕ) (hn : 0 < n) (k : ℕ) :
    canonicalOrbit n hn (k + 1) = some ⟨k % n, Nat.mod_lt _ hn⟩ := by
  unfold canonicalOrbit
  rw [Function.iterate_succ_apply]
  simpa [canonicalSuccessor] using
    canonicalSuccessor_iterate_some n hn ⟨0, hn⟩ k

/-- The canonical phase successor obeys the required power identity. -/
theorem canonicalSuccessor_power (n : ℕ) (hn : 0 < n) :
    (canonicalSuccessor n hn)^[n + 1] = canonicalSuccessor n hn := by
  funext q
  cases q with
  | none =>
    change canonicalOrbit n hn (n + 1) = some ⟨0, hn⟩
    rw [canonicalOrbit_succ]
    simp
  | some i =>
    rw [canonicalSuccessor_iterate_some]
    simp only [canonicalSuccessor]
    congr 2
    rw [← Nat.add_assoc, Nat.add_right_comm i.val n 1, Nat.add_mod_right]

theorem canonicalOrbit_periodic (n : ℕ) (hn : 0 < n) :
    PositivePeriodic n (canonicalOrbit n hn) := by
  intro k hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [show j.succ + n = (j + n) + 1 by omega]
  rw [canonicalOrbit_succ, canonicalOrbit_succ]
  simp

/-- Positive-depth periodicity propagates through every whole cycle. -/
theorem PositivePeriodic.add_mul {n : ℕ} {c : ℕ → C}
    (hc : PositivePeriodic n c) {k : ℕ} (hk : 0 < k) (t : ℕ) :
    c (k + n * t) = c k := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, hc _ (by omega), ih]

/-- Every positive depth has the label of its canonical cycle representative. -/
theorem PositivePeriodic.reduce {n : ℕ} {c : ℕ → C}
    (hc : PositivePeriodic n c) (k : ℕ) :
    c (k + 1) = c (k % n + 1) := by
  have h := hc.add_mul (k := k % n + 1) (by omega) (k / n)
  rw [show k % n + 1 + n * (k / n) = k + 1 by
    have := Nat.mod_add_div k n
    omega] at h
  exact h

/-- Labels on the canonical phase space. No successor is required on `C`. -/
def canonicalLabels (c : ℕ → C) : CanonicalPhase n → C
  | none => c 0
  | some i => c (i.val + 1)

/-- Every positive-periodic labeling factors through the canonical orbit. -/
theorem PositivePeriodic.factor {n : ℕ} {c : ℕ → C}
    (hc : PositivePeriodic n c) (hn : 0 < n) :
    ∀ k, canonicalLabels c (canonicalOrbit n hn k) = c k := by
  intro k
  cases k with
  | zero => rfl
  | succ k =>
    rw [canonicalOrbit_succ]
    exact (hc.reduce k).symm

/-- Factorization through the root-and-cycle orbit is exactly positive periodicity. -/
theorem canonical_factor_iff (n : ℕ) (hn : 0 < n) (c : ℕ → C) :
    (∃ l : CanonicalPhase n → C, ∀ k, l (canonicalOrbit n hn k) = c k) ↔
      PositivePeriodic n c := by
  constructor
  · rintro ⟨l, hl⟩ k hk
    rw [← hl (k + n), ← hl k, canonicalOrbit_periodic n hn k hk]
  · intro hc
    exact ⟨canonicalLabels c, hc.factor hn⟩

/-- Residue-class labels qualify precisely when their modulus divides the period. -/
theorem positivePeriodic_mod_iff (n m : ℕ) (_hn : 0 < n) (hm : 0 < m) :
    PositivePeriodic n (fun k => k % m) ↔ m ∣ n := by
  constructor
  · intro h
    have he := h m hm
    simp only [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod] at he
    exact Nat.dvd_of_mod_eq_zero he
  · intro h k _
    simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd h]

/-- Literal depth cannot satisfy any strictly positive period. -/
theorem exactDepth_not_periodic (n : ℕ) (hn : 0 < n) :
    ¬ PositivePeriodic n (fun k => k) := by
  intro h
  have := h 1 (by omega)
  simp only at this
  omega


/-- The orbit distinguishes depth zero and otherwise records depth modulo `n`. -/
theorem canonicalOrbit_eq_iff (n : ℕ) (hn : 0 < n) (d e : ℕ) :
    canonicalOrbit n hn d = canonicalOrbit n hn e ↔
      (d = 0 ∧ e = 0) ∨ (0 < d ∧ 0 < e ∧ d % n = e % n) := by
  cases d with
  | zero =>
    cases e with
    | zero => simp
    | succ e =>
      rw [canonicalOrbit_succ]
      simp [canonicalOrbit]
  | succ d =>
    cases e with
    | zero =>
      rw [canonicalOrbit_succ]
      simp [canonicalOrbit]
    | succ e =>
      rw [canonicalOrbit_succ, canonicalOrbit_succ]
      simp only [Option.some.injEq, Fin.mk.injEq, Nat.succ_ne_zero, false_and,
        Nat.succ_pos, true_and, false_or]
      constructor
      · intro h
        exact Nat.ModEq.add_right 1 h
      · intro h
        exact Nat.ModEq.add_right_cancel (Nat.ModEq.refl 1) h

/-- All root-and-cycle phases occur at a finite depth. -/
theorem canonicalOrbit_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (canonicalOrbit n hn) := by
  intro q
  cases q with
  | none => exact ⟨0, rfl⟩
  | some i =>
    refine ⟨i.val + 1, ?_⟩
    rw [canonicalOrbit_succ]
    simp [Nat.mod_eq_of_lt i.isLt]

/-- At most `n + 1` labels appear in a positive-periodic depth labeling. -/
theorem PositivePeriodic.finite_labels {n : ℕ} {c : ℕ → C}
    (hc : PositivePeriodic n c) (hn : 0 < n) :
    ∃ s : Finset C, (∀ k, c k ∈ s) ∧ s.card ≤ n + 1 := by
  classical
  refine ⟨Finset.univ.image (canonicalLabels c : CanonicalPhase n → C), ?_, ?_⟩
  · intro k
    exact Finset.mem_image.mpr ⟨canonicalOrbit n hn k, Finset.mem_univ _, hc.factor hn k⟩
  · exact (Finset.card_image_le).trans (by simp [CanonicalPhase])

/-- Parity is an admissible depth labeling exactly for even periods. -/
theorem positivePeriodic_parity_iff (n : ℕ) (hn : 0 < n) :
    PositivePeriodic n (fun k => k % 2) ↔ Even n := by
  simpa only [even_iff_two_dvd] using positivePeriodic_mod_iff n 2 hn (by omega)

end ModalDepth
