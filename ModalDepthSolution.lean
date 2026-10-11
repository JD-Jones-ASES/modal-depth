module

public import ModalDepth

@[expose] public section

namespace ModalDepth.Contracts
variable {α β χ Q C : Type}

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

theorem period_gcd (a b : ℕ) (c : ℕ → C) :
    PositivePeriodic a c ∧ PositivePeriodic b c ↔
      PositivePeriodic (Nat.gcd a b) c := by
  exact positivePeriodic_gcd_iff a b c

theorem common_depth_substitution (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (c : ℕ → C) [Nonempty α] :
    DepthSubstitution a c α β ∧ DepthSubstitution b c α β ↔
      PositivePeriodic (Nat.gcd a b) c := by
  exact depthSubstitution_pair_iff a b ha hb c

theorem positive_period_spectrum (c : ℕ → C)
    (h : ∃ p : ℕ, 0 < p ∧ PositivePeriodic p c) :
    ∃ p : ℕ, 0 < p ∧ ∀ n : ℕ, PositivePeriodic n c ↔ p ∣ n := by
  exact positivePeriodic_spectrum c h

theorem admissible_label_inclusion (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (∀ c : ℕ → ℕ, PositivePeriodic a c → PositivePeriodic b c) ↔ a ∣ b := by
  exact positivePeriodic_inclusion_iff a b ha hb

theorem boxed_implication (n : ℕ) (hn : 0 < n) (k l : ℕ) (p : α) :
    Provable n (.imp ((Formula.atom p).boxes k) ((Formula.atom p).boxes l)) ↔
      k = l ∨ (0 < k ∧ k ≤ l ∧ n ∣ l - k) := by
  exact boxes_atom_imp_iff_arithmetic n hn k l p

theorem boxed_inequivalence (n : ℕ) (hn : 0 < n) (k l : ℕ) (p : α) :
    (Provable n (.imp ((Formula.atom p).boxes k) ((Formula.atom p).boxes l)) ∧
      Provable n (.imp ((Formula.atom p).boxes l) ((Formula.atom p).boxes k))) ↔ k = l := by
  exact boxes_atom_mutual_iff n hn k l p

theorem phase_composition (δ : Q → Q)
    (f : Q → α → Formula β) (g : Q → β → Formula χ) (q : Q) (A : Formula α) :
    phaseTranslate δ g q (phaseTranslate δ f q A) =
      phaseTranslate δ (fun r p => phaseTranslate δ g r (f r p)) q A := by
  exact phaseTranslate_compose δ f g q A

theorem depth_composition_classification (c : ℕ → C) [Nonempty α] [Nonempty β] :
    DepthCompositionClosed c α β χ ↔ SuccessorCompatible c := by
  exact depthCompositionClosed_iff c

theorem encoding_reflection (δ : Q → Q) (n : ℕ)
    (hδ : ∀ q, δ^[n + 1] q = δ q) (q : Q) (A : Formula α) :
    Provable n (encode δ q A) ↔ Provable n A := by
  exact encode_provable_iff δ hδ q A

theorem translation_sizes (δ : Q → Q) (q : Q) (A : Formula α)
    (J : Formula (α × Q)) :
    (encode δ q A).nodeCount = A.nodeCount ∧
    (encode δ q A).modalDepth = A.modalDepth ∧
    (decode δ q J).nodeCount = J.nodeCount ∧
    (decode δ q J).modalDepth = J.modalDepth := by
  exact ⟨encode_nodeCount δ q A, encode_modalDepth δ q A,
    decode_nodeCount δ q J, decode_modalDepth δ q J⟩

theorem uniform_transfer_no_overhead (δ : Q → Q) (q : Q) (n : ℕ)
    (hδ : ∀ q, δ^[n + 1] q = δ q)
    (A : Formula α) (W : Bool → α → Q → Prop) (J : Formula (α × Q))
    (hs : ∀ s p, J.vocab s p → (encode δ q A).vocab s p ∧ W s p.1 p.2)
    (hAJ : Provable n (.imp (encode δ q A) J))
    (hU : ∀ B : Formula (α × Q), (∀ s p, B.vocab s p → W s p.1 p.2) →
      Provable n (.imp (encode δ q A) B) → Provable n (.imp J B)) :
    ∃ I : Formula α,
      (∀ s p z, I.support (fun d => δ^[d] q) s p z →
        A.support (fun d => δ^[d] q) s p z ∧ W s p z) ∧
      Provable n (.imp A I) ∧
      (∀ B : Formula α, (∀ s p z, B.support (fun d => δ^[d] q) s p z → W s p z) →
        Provable n (.imp A B) → Provable n (.imp I B)) ∧
      I.nodeCount = J.nodeCount ∧ I.modalDepth = J.modalDepth := by
  exact decode_uniformInterpolant δ q hδ A W J hs hAJ hU

theorem coarse_composition_obstruction :
    ∃ (c : ℕ → ℕ) (f : ℕ → ℕ → Formula ℕ) (g : ℕ → ℕ → Formula PEmpty),
      PositivePeriodic 2 c ∧
      ¬ ∃ h : ℕ → ℕ → Formula PEmpty, ∀ A : Formula ℕ,
        Provable 2 (depthTranslate c h 0 A) ↔
          Provable 2 (depthTranslate c g 0 (depthTranslate c f 0 A)) := by
  exact ⟨CompositionBoundary.coarseLabel, CompositionBoundary.insertBox,
    CompositionBoundary.selectTruth, CompositionBoundary.coarseLabel_periodic,
    CompositionBoundary.no_theoremhood_equivalent_coarse_substitution⟩

end ModalDepth.Contracts
