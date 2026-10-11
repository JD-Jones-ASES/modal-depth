module

public import ModalDepth.Phase
public import ModalDepth.Periodic
public import ModalDepth.Obstruction

@[expose] public section

namespace ModalDepth

variable {α β C Q : Type}

/-- Replace atoms according to their depth label, beginning at a given depth. -/
def depthTranslate (c : ℕ → C) (f : C → α → Formula β) (offset : ℕ) :
    Formula α → Formula β :=
  phaseTranslate Nat.succ (fun d p => f (c d) p) offset

/-- Every formula-valued replacement depending on the atom and its depth label
preserves theorems. Depth is measured in the source formula. -/
def DepthSubstitution (n : ℕ) (c : ℕ → C) (α β : Type) : Prop :=
  ∀ (f : C → α → Formula β) (A : Formula α),
    Provable n A → Provable n (depthTranslate c f 0 A)

theorem depthTranslate_boxes (c : ℕ → C) (f : C → α → Formula β)
    (k offset : ℕ) (A : Formula α) :
    depthTranslate c f offset (A.boxes k) =
      (depthTranslate c f (offset + k) A).boxes k := by
  simp only [depthTranslate, phaseTranslate_boxes, Nat.succ_iterate]

/-- Positive-periodic substitutions factor through the canonical phase space. -/
theorem depthTranslate_canonical {n : ℕ} {c : ℕ → C}
    (hn : 0 < n) (hc : PositivePeriodic n c) (f : C → α → Formula β)
    (offset : ℕ) (A : Formula α) :
    depthTranslate c f offset A =
      phaseTranslate (canonicalSuccessor n hn)
        (fun q p => f (canonicalLabels c q) p) (canonicalOrbit n hn offset) A := by
  induction A generalizing offset with
  | atom p => simp only [depthTranslate, phaseTranslate, hc.factor hn]
  | bot => rfl
  | imp A B ihA ihB =>
    change Formula.imp (depthTranslate c f offset A) (depthTranslate c f offset B) = _
    simp only [phaseTranslate, ihA, ihB]
  | box A ih =>
    change Formula.box (depthTranslate c f (offset + 1) A) = _
    rw [ih]
    simp only [phaseTranslate, canonicalOrbit, Function.iterate_succ_apply']

/-- Theorem preservation holds from every starting depth. -/
theorem PositivePeriodic.depthTranslate_provable {n : ℕ} {c : ℕ → C}
    (hc : PositivePeriodic n c) (hn : 0 < n) (f : C → α → Formula β)
    (offset : ℕ) {A : Formula α} (hA : Provable n A) :
    Provable n (depthTranslate c f offset A) := by
  rw [depthTranslate_canonical hn hc]
  exact phaseTranslate_provable _ _ (fun q => congrFun (canonicalSuccessor_power n hn) q)
    hA _

private theorem eval_boxes_top (r x : ℕ) (v : ℕ → β → Prop) :
    Obstruction.eval v x (Formula.boxes r (.imp .bot .bot)) := by
  induction r generalizing x with
  | zero => exact id
  | succ r ih => exact fun y _ => ih y

private theorem not_eval_boxes_bot (r : ℕ) (v : ℕ → β → Prop) :
    ¬ Obstruction.eval v r (Formula.boxes r .bot) := by
  induction r with
  | zero => exact id
  | succ r ih => exact fun h => ih (h r (Nat.lt_succ_self r))

/-- Distinct positive-depth labels have an explicit top/bottom substitution
whose image of a derivable transitivity formula is not derivable. -/
theorem depthTranslate_failure {n k : ℕ} {c : ℕ → C}
    (hn : 0 < n) (hk : 0 < k) (hc : c (k + n) ≠ c k) (p : α) :
    ∃ f : C → α → Formula β,
      Provable n (.imp ((Formula.atom p).boxes k) ((Formula.atom p).boxes (k + n))) ∧
      ¬ Provable n (depthTranslate c f 0
        (.imp ((Formula.atom p).boxes k) ((Formula.atom p).boxes (k + n)))) := by
  classical
  let f : C → α → Formula β :=
    fun z _ => if z = c k then .imp .bot .bot else .bot
  refine ⟨f, Obstruction.positive_n_transitivity (.atom p) hk, ?_⟩
  intro h
  change Provable n (.imp (depthTranslate c f 0 ((Formula.atom p).boxes k))
    (depthTranslate c f 0 ((Formula.atom p).boxes (k + n)))) at h
  rw [depthTranslate_boxes, depthTranslate_boxes] at h
  simp only [Nat.zero_add, depthTranslate, phaseTranslate,
    f, ite_eq_left rfl, ite_eq_right hc] at h
  have hb := Obstruction.sound hn h (fun _ _ => False) (k + n)
    (eval_boxes_top k (k + n) (fun _ _ => False))
  exact not_eval_boxes_bot (k + n) (fun _ _ => False) hb

/-- Universal depth-label substitution forces positive periodicity. The target
alphabet may be empty: truth and falsity suffice for the obstruction. -/
theorem depthSubstitution_periodic {n : ℕ} {c : ℕ → C}
    (hn : 0 < n) [Nonempty α] (h : DepthSubstitution n c α β) :
    PositivePeriodic n c := by
  classical
  intro k hk
  by_contra hc
  let p : α := Classical.choice ‹Nonempty α›
  obtain ⟨f, hA, hnot⟩ := depthTranslate_failure (β := β) hn hk hc p
  exact hnot (h f _ hA)

/-- Exact characterization of theorem-preserving depth-dependent substitutions. -/
theorem depthSubstitution_iff (n : ℕ) (hn : 0 < n) (c : ℕ → C)
    [Nonempty α] : DepthSubstitution n c α β ↔ PositivePeriodic n c := by
  constructor
  · exact depthSubstitution_periodic hn
  · intro hc f A hA
    exact hc.depthTranslate_provable hn f 0 hA

/-- The depth-orbit presentation of a phase-dependent substitution. -/
theorem phaseTranslate_eq_depthTranslate (δ : Q → Q) (f : Q → α → Formula β)
    (q : Q) (offset : ℕ) (A : Formula α) :
    phaseTranslate δ f (δ^[offset] q) A =
      depthTranslate (fun d => δ^[d] q) f offset A := by
  induction A generalizing offset with
  | atom p => rfl
  | bot => rfl
  | imp A B ihA ihB =>
    change Formula.imp (phaseTranslate δ f (δ^[offset] q) A)
      (phaseTranslate δ f (δ^[offset] q) B) = _
    rw [ihA, ihB]
    rfl
  | box A ih =>
    change Formula.box (phaseTranslate δ f (δ (δ^[offset] q)) A) = _
    rw [← Function.iterate_succ_apply' δ offset q, ih]
    rfl

/-- A phase action preserves all formula-valued substitutions at all starting
phases exactly when its successor obeys the weak Löb power identity. -/
theorem phaseSubstitution_iff (n : ℕ) (hn : 0 < n) (δ : Q → Q)
    [Nonempty α] :
    (∀ (f : Q → α → Formula β) (q : Q) (A : Formula α),
      Provable n A → Provable n (phaseTranslate δ f q A)) ↔
      ∀ q, δ^[n + 1] q = δ q := by
  constructor
  · intro h q
    have hd : DepthSubstitution n (fun d => δ^[d] q) α β := by
      intro f A hA
      rw [← phaseTranslate_eq_depthTranslate]
      exact h f q A hA
    have hp := depthSubstitution_periodic hn hd 1 (by omega)
    simpa only [Nat.add_comm 1 n, Function.iterate_one] using hp
  · intro h f q A hA
    exact phaseTranslate_provable δ f h hA q

end ModalDepth
