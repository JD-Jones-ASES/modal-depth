module

public import ModalDepth

@[expose] public section

namespace ModalDepth.Contracts
variable {α β Q C : Type}

theorem uniform_classification (n : ℕ) (hn : 0 < n) (c : ℕ → C) :
    UniformSigned n c ℕ ↔ SourceULI n ℕ ∧ PositivePeriodic n c := by
  exact uniformSigned_iff n hn c

theorem signed_classification (n : ℕ) (hn : 0 < n) (c : ℕ → C) :
    SignedCraig n c ℕ ↔ OrdinaryLyndon n ℕ ∧ PositivePeriodic n c := by
  exact signedCraig_iff n hn c

theorem unsigned_classification (n : ℕ) (hn : 0 < n) (c : ℕ → C) :
    UnsignedCraig n c ℕ ↔ OrdinaryCraig n ℕ ∧ PositivePeriodic n c := by
  exact unsignedCraig_iff n hn c

theorem classification_given_inputs (n : ℕ) (hn : 0 < n) (c : ℕ → C)
    (hu : OrdinaryULI n ℕ) (hl : OrdinaryLyndon n ℕ) :
    (UniformSigned n c ℕ ↔ PositivePeriodic n c) ∧
    (SignedCraig n c ℕ ↔ PositivePeriodic n c) ∧
    (UnsignedCraig n c ℕ ↔ PositivePeriodic n c) := by
  have hU := classification_from_ordinary n hn c hu hl
  refine ⟨hU, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h; exact unsignedCraig_periodic hn (signedCraig_unsignedCraig h)
  · intro h; exact uniformSigned_signedCraig (hU.mpr h)
  · exact unsignedCraig_periodic hn
  · intro h; exact signedCraig_unsignedCraig (uniformSigned_signedCraig (hU.mpr h))

theorem residue_uniform (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    UniformSigned n (fun d => d % m) ℕ ↔ SourceULI n ℕ ∧ m ∣ n := by
  exact residue_uniform_iff n m hn hm

theorem residue_signed (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    SignedCraig n (fun d => d % m) ℕ ↔ OrdinaryLyndon n ℕ ∧ m ∣ n := by
  rw [signedCraig_iff n hn, positivePeriodic_mod_iff n m hn hm]

theorem residue_unsigned (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    UnsignedCraig n (fun d => d % m) ℕ ↔ OrdinaryCraig n ℕ ∧ m ∣ n := by
  rw [unsignedCraig_iff n hn, positivePeriodic_mod_iff n m hn hm]

theorem canonical_partition (n : ℕ) (hn : 0 < n) (c : ℕ → C) :
    PositivePeriodic n c ↔
      ∀ d e : ℕ, ((d = 0 ∧ e = 0) ∨ (0 < d ∧ 0 < e ∧ d % n = e % n)) → c d = c e := by
  constructor
  · intro hc d e hde
    rw [← hc.factor hn d, ← hc.factor hn e]
    exact congrArg (canonicalLabels c) ((canonicalOrbit_eq_iff n hn d e).mpr hde)
  · intro h k hk
    apply h (k + n) k
    exact Or.inr ⟨by omega, hk, by simp⟩

theorem finite_labels (n : ℕ) (hn : 0 < n) (c : ℕ → C) (hc : PositivePeriodic n c) :
    ∃ s : Finset C, (∀ k, c k ∈ s) ∧ s.card ≤ n + 1 := by
  exact hc.finite_labels hn

theorem positive_transitivity (n k : ℕ) (hk : 0 < k) (A : Formula α) :
    Provable n (.imp (A.boxes k) (A.boxes (k + n))) := by
  exact Obstruction.positive_n_transitivity A hk

theorem unsigned_necessity (n : ℕ) (hn : 0 < n) (c : ℕ → C) [Nonempty α]
    (h : UnsignedCraig n c α) : PositivePeriodic n c := by
  exact unsignedCraig_periodic hn h

theorem exact_depth_obstruction (n : ℕ) (hn : 0 < n) :
    ¬ UnsignedCraig n (fun d => d) ℕ := by
  exact exactDepth_no_unsignedCraig n hn

theorem incompatible_modulus (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (h : ¬ m ∣ n) :
    ¬ UnsignedCraig n (fun d => d % m) ℕ := by
  exact incompatible_residue_no_unsignedCraig n m hn hm h

theorem source_normalization (n : ℕ) :
    SourceULI n α ↔ OrdinaryULI n α ∧ OrdinaryLyndon n α := by
  exact sourceULI_iff

theorem phase_preservation (n : ℕ) (δ : Q → Q) (f : Q → α → Formula β)
    (hδ : ∀ q, δ^[n + 1] q = δ q) (A : Formula α) (hA : Provable n A) (q : Q) :
    Provable n (phaseTranslate δ f q A) := by
  exact phaseTranslate_provable δ f hδ hA q

theorem decode_roundtrip (δ : Q → Q) (q : Q) (A : Formula α) :
    decode δ q (encode δ q A) = A := by
  exact decode_encode δ q A

theorem encoding_support (δ : Q → Q) (q : Q) (A : Formula α) (s : Bool) (p : α) (z : Q) :
    (encode δ q A).vocab s (p, z) ↔ A.support (fun d => δ^[d] q) s p z := by
  exact encode_vocab_iff δ q A s p z

theorem decoding_support (δ : Q → Q) (q : Q) (A : Formula (α × Q)) (s : Bool) (p : α) (z : Q) :
    (decode δ q A).support (fun d => δ^[d] q) s p z → A.vocab s (p, z) := by
  exact decode_support δ q A s p z

theorem parity_with_inputs (hu : OrdinaryULI 2 ℕ) (hl : OrdinaryLyndon 2 ℕ) :
    UniformSigned 2 (fun d => d % 2) ℕ := by
  exact (residue_classification_from_ordinary 2 2 (by decide) (by decide) hu hl).mpr (dvd_refl 2)

theorem depth_substitution_classification (n : ℕ) (hn : 0 < n) (c : ℕ → C) [Nonempty α] :
    DepthSubstitution n c α β ↔ PositivePeriodic n c := by
  exact depthSubstitution_iff n hn c

theorem phase_substitution_classification (n : ℕ) (hn : 0 < n) (δ : Q → Q) [Nonempty α] :
    (∀ (f : Q → α → Formula β) (q : Q) (A : Formula α),
      Provable n A → Provable n (phaseTranslate δ f q A)) ↔
      ∀ q, δ^[n + 1] q = δ q := by
  exact phaseSubstitution_iff n hn δ

theorem failed_depth_substitution (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (c : ℕ → C) (hc : c (k + n) ≠ c k) (p : α) :
    ∃ f : C → α → Formula β,
      Provable n (.imp ((Formula.atom p).boxes k) ((Formula.atom p).boxes (k + n))) ∧
      ¬ Provable n (depthTranslate c f 0
        (.imp ((Formula.atom p).boxes k) ((Formula.atom p).boxes (k + n)))) := by
  exact depthTranslate_failure hn hk hc p

end ModalDepth.Contracts
