module

public import ModalDepth.Phase
public import ModalDepth.Periodic
public import ModalDepth.Interpolation
public import ModalDepth.Obstruction
public import ModalDepth.Renaming

@[expose] public section

namespace ModalDepth

variable {α Q : Type}

/-- Ordinary source-supported interpolation transfers along any admissible phase action. -/
theorem uniformSigned_phase (δ : Q → Q) (q : Q)
    (hδ : ∀ q, δ^[n + 1] q = δ q) (hu : SourceULI n (α × Q)) :
    UniformSigned n (fun d => δ^[d] q) α := by
  intro A W
  obtain ⟨K, hs, hak, hU⟩ := hu (encode δ q A) (fun s p => W s p.1 p.2)
  refine ⟨decode δ q K, ?_, ?_, ?_⟩
  · intro s p z hz
    obtain ⟨ha, hw⟩ := hs s (p, z) (decode_support δ q K s p z hz)
    exact ⟨(encode_vocab_iff δ q A s p z).mp ha, hw⟩
  · have hd := decode_provable δ hδ hak q
    change Provable n (.imp (decode δ q (encode δ q A)) (decode δ q K)) at hd
    rwa [decode_encode] at hd
  · intro B hb hab
    have he := encode_provable δ hδ hab q
    change Provable n (.imp (encode δ q A) (encode δ q B)) at he
    have hKB := hU (encode δ q B) (by
      intro s p hp
      exact hb s p.1 p.2 ((encode_vocab_iff δ q B s p.1 p.2).mp hp)) he
    have hd := decode_provable δ hδ hKB q
    change Provable n (.imp (decode δ q K) (decode δ q (encode δ q B))) at hd
    rwa [decode_encode] at hd

theorem uniformSigned_canonical (n : ℕ) (hn : 0 < n)
    (hu : SourceULI n (α × CanonicalPhase n)) :
    UniformSigned n (canonicalOrbit n hn) α :=
  uniformSigned_phase (canonicalSuccessor n hn) none
    (fun q => congrFun (canonicalSuccessor_power n hn) q) hu

/-- The positive transfer includes arbitrary coarsenings of root-and-cycle colors. -/
theorem uniformSigned_of_periodic (n : ℕ) (hn : 0 < n) {c : ℕ → C}
    (hu : SourceULI n (α × CanonicalPhase n)) (hc : PositivePeriodic n c) :
    UniformSigned n c α := by
  have h := uniformSigned_coarsen (canonicalLabels c) (uniformSigned_canonical n hn hu)
  have he : canonicalLabels c ∘ canonicalOrbit n hn = c := funext (hc.factor hn)
  rwa [he] at h

/-- No interpolation assumption is used to establish the necessary period. -/
theorem uniformSigned_periodic (hn : 0 < n) [Nonempty α]
    (h : UniformSigned n c α) : PositivePeriodic n c :=
  unsignedCraig_periodic hn (signedCraig_unsignedCraig (uniformSigned_signedCraig h))

/-- The exact structural classification, with the ordinary property on both sides.
This equivalence requires no assumption that ordinary interpolation has been proved. -/
theorem uniformSigned_iff (n : ℕ) (hn : 0 < n) (c : ℕ → C) :
    UniformSigned n c ℕ ↔ SourceULI n ℕ ∧ PositivePeriodic n c := by
  constructor
  · intro h
    exact ⟨uniformSigned_sourceULI h, uniformSigned_periodic hn h⟩
  · rintro ⟨hu, hc⟩
    exact uniformSigned_of_periodic n hn (sourceULI_countable hu) hc

/-- The published ordinary inputs yield the full positive classification. -/
theorem classification_from_ordinary (n : ℕ) (hn : 0 < n) (c : ℕ → C)
    (hu : OrdinaryULI n ℕ) (hl : OrdinaryLyndon n ℕ) :
    UniformSigned n c ℕ ↔ PositivePeriodic n c := by
  rw [uniformSigned_iff n hn c]
  exact and_iff_right (sourceULI_of_ordinary hu hl)

theorem residue_uniform_iff (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    UniformSigned n (fun d => d % m) ℕ ↔ SourceULI n ℕ ∧ m ∣ n := by
  rw [uniformSigned_iff n hn, positivePeriodic_mod_iff n m hn hm]

theorem residue_classification_from_ordinary (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hu : OrdinaryULI n ℕ) (hl : OrdinaryLyndon n ℕ) :
    UniformSigned n (fun d => d % m) ℕ ↔ m ∣ n := by
  rw [residue_uniform_iff n m hn hm]
  exact and_iff_right (sourceULI_of_ordinary hu hl)

theorem exactDepth_no_unsignedCraig (n : ℕ) (hn : 0 < n) :
    ¬ UnsignedCraig n (fun d => d) ℕ := by
  intro h
  exact exactDepth_not_periodic n hn (unsignedCraig_periodic hn h)

theorem incompatible_residue_no_unsignedCraig (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (h : ¬ m ∣ n) : ¬ UnsignedCraig n (fun d => d % m) ℕ := by
  intro hc
  exact h ((positivePeriodic_mod_iff n m hn hm).mp (unsignedCraig_periodic hn hc))

end ModalDepth
