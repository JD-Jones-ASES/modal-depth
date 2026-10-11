import ModalDepth.Phase
import ModalDepth.Periodic
import ModalDepth.Interpolation
import ModalDepth.Obstruction
import ModalDepth.Renaming

namespace ModalDepth

variable {α β Q C : Type}

/-- Forget the polarity of an ordinary atomic occurrence. -/
def Formula.unsignedVocab (A : Formula α) (p : α) : Prop := ∃ s, A.vocab s p

/-- Ordinary Craig interpolation, without polarity or depth constraints. -/
def OrdinaryCraig (n : ℕ) (α : Type) : Prop :=
  ∀ A B : Formula α, Provable n (.imp A B) → ∃ I : Formula α,
    Provable n (.imp A I) ∧ Provable n (.imp I B) ∧
    ∀ p, I.unsignedVocab p → A.unsignedVocab p ∧ B.unsignedVocab p

theorem signedCraig_ordinaryLyndon {c : ℕ → C} (h : SignedCraig n c α) :
    OrdinaryLyndon n α := by
  intro A B hab
  obtain ⟨I, hai, hib, hs⟩ := h A B hab
  refine ⟨I, hai, hib, ?_⟩
  intro s p hp
  obtain ⟨d, hd⟩ := hp
  obtain ⟨⟨e, he, _⟩, ⟨f, hf, _⟩⟩ := hs s p (c d) ⟨d, hd, rfl⟩
  exact ⟨⟨e, he⟩, ⟨f, hf⟩⟩

theorem unsignedCraig_ordinaryCraig {c : ℕ → C} (h : UnsignedCraig n c α) :
    OrdinaryCraig n α := by
  intro A B hab
  obtain ⟨I, hai, hib, hs⟩ := h A B hab
  refine ⟨I, hai, hib, ?_⟩
  intro p hp
  obtain ⟨s, d, hd⟩ := hp
  obtain ⟨⟨t, e, he, _⟩, ⟨u, f, hf, _⟩⟩ := hs p (c d) ⟨s, d, hd, rfl⟩
  exact ⟨⟨t, e, he⟩, ⟨u, f, hf⟩⟩

theorem signedCraig_coarsen {k : ℕ → Q} (h : Q → C)
    (hc : SignedCraig n k α) : SignedCraig n (h ∘ k) α := by
  intro A B hab
  obtain ⟨I, hai, hib, hs⟩ := hc A B hab
  refine ⟨I, hai, hib, ?_⟩
  rintro s p z ⟨d, hd, rfl⟩
  obtain ⟨⟨e, he, hke⟩, ⟨f, hf, hkf⟩⟩ := hs s p (k d) ⟨d, hd, rfl⟩
  exact ⟨⟨e, he, congrArg h hke⟩, ⟨f, hf, congrArg h hkf⟩⟩

theorem unsignedCraig_coarsen {k : ℕ → Q} (h : Q → C)
    (hc : UnsignedCraig n k α) : UnsignedCraig n (h ∘ k) α := by
  intro A B hab
  obtain ⟨I, hai, hib, hs⟩ := hc A B hab
  refine ⟨I, hai, hib, ?_⟩
  rintro p z ⟨s, d, hd, rfl⟩
  obtain ⟨⟨t, e, he, hke⟩, ⟨u, f, hf, hkf⟩⟩ := hs p (k d) ⟨s, d, hd, rfl⟩
  exact ⟨⟨t, e, he, congrArg h hke⟩, ⟨u, f, hf, congrArg h hkf⟩⟩

private theorem vocab_retract (i : α → β) (d : β → α)
    (hi : Function.LeftInverse d i) (A : Formula α) (s : Bool) (b : β) (p : α)
    (hb : (rename i A).vocab s b) (hp : d b = p) : A.vocab s p := by
  obtain ⟨a, ha, hab⟩ := (rename_vocab_iff i A s b).mp hb
  have hap : a = p := by
    calc
      a = d (i a) := (hi a).symm
      _ = d b := congrArg d hab
      _ = p := hp
  simpa only [hap] using ha

theorem ordinaryLyndon_of_retract (hl : OrdinaryLyndon n β)
    (i : α → β) (d : β → α) (hi : Function.LeftInverse d i) :
    OrdinaryLyndon n α := by
  intro A B hab
  obtain ⟨J, haj, hjb, hs⟩ := hl (rename i A) (rename i B) (rename_provable i hab)
  refine ⟨rename d J, ?_, ?_, ?_⟩
  · have h := rename_provable d haj
    change Provable n (.imp (rename d (rename i A)) (rename d J)) at h
    simpa only [rename_roundtrip i d hi] using h
  · have h := rename_provable d hjb
    change Provable n (.imp (rename d J) (rename d (rename i B))) at h
    simpa only [rename_roundtrip i d hi] using h
  · intro s p hp
    obtain ⟨b, hb, hbp⟩ := (rename_vocab_iff d J s p).mp hp
    exact ⟨vocab_retract i d hi A s b p (hs s b hb).1 hbp,
      vocab_retract i d hi B s b p (hs s b hb).2 hbp⟩

theorem ordinaryCraig_of_retract (hl : OrdinaryCraig n β)
    (i : α → β) (d : β → α) (hi : Function.LeftInverse d i) :
    OrdinaryCraig n α := by
  intro A B hab
  obtain ⟨J, haj, hjb, hs⟩ := hl (rename i A) (rename i B) (rename_provable i hab)
  refine ⟨rename d J, ?_, ?_, ?_⟩
  · have h := rename_provable d haj
    change Provable n (.imp (rename d (rename i A)) (rename d J)) at h
    simpa only [rename_roundtrip i d hi] using h
  · have h := rename_provable d hjb
    change Provable n (.imp (rename d J) (rename d (rename i B))) at h
    simpa only [rename_roundtrip i d hi] using h
  · rintro p ⟨s, hp⟩
    obtain ⟨b, hb, hbp⟩ := (rename_vocab_iff d J s p).mp hp
    obtain ⟨⟨t, ht⟩, ⟨u, hu⟩⟩ := hs b ⟨s, hb⟩
    exact ⟨⟨t, vocab_retract i d hi A t b p ht hbp⟩,
      ⟨u, vocab_retract i d hi B u b p hu hbp⟩⟩

theorem ordinaryLyndon_countable [Encodable α] [Nonempty α]
    (hl : OrdinaryLyndon n ℕ) : OrdinaryLyndon n α := by
  classical
  let d : ℕ → α := fun k => (Encodable.decode (α := α) k).getD (Classical.choice ‹Nonempty α›)
  apply ordinaryLyndon_of_retract hl Encodable.encode d
  intro a
  simp [d, Encodable.encodek]

theorem ordinaryCraig_countable [Encodable α] [Nonempty α]
    (hl : OrdinaryCraig n ℕ) : OrdinaryCraig n α := by
  classical
  let d : ℕ → α := fun k => (Encodable.decode (α := α) k).getD (Classical.choice ‹Nonempty α›)
  apply ordinaryCraig_of_retract hl Encodable.encode d
  intro a
  simp [d, Encodable.encodek]

/-- Phase encoding transfers ordinary Lyndon interpolation to signed phase support. -/
theorem signedCraig_phase (δ : Q → Q) (q : Q)
    (hδ : ∀ q, δ^[n + 1] q = δ q) (hl : OrdinaryLyndon n (α × Q)) :
    SignedCraig n (fun d => δ^[d] q) α := by
  intro A B hab
  obtain ⟨J, haj, hjb, hs⟩ :=
    hl (encode δ q A) (encode δ q B) (encode_provable δ hδ hab q)
  refine ⟨decode δ q J, ?_, ?_, ?_⟩
  · have h := decode_provable δ hδ haj q
    change Provable n (.imp (decode δ q (encode δ q A)) (decode δ q J)) at h
    rwa [decode_encode] at h
  · have h := decode_provable δ hδ hjb q
    change Provable n (.imp (decode δ q J) (decode δ q (encode δ q B))) at h
    rwa [decode_encode] at h
  · intro s p z hz
    obtain ⟨ha, hb⟩ := hs s (p,z) (decode_support δ q J s p z hz)
    exact ⟨(encode_vocab_iff δ q A s p z).mp ha, (encode_vocab_iff δ q B s p z).mp hb⟩

/-- The unsigned transfer only assumes ordinary Craig interpolation. -/
theorem unsignedCraig_phase (δ : Q → Q) (q : Q)
    (hδ : ∀ q, δ^[n + 1] q = δ q) (hl : OrdinaryCraig n (α × Q)) :
    UnsignedCraig n (fun d => δ^[d] q) α := by
  intro A B hab
  obtain ⟨J, haj, hjb, hs⟩ :=
    hl (encode δ q A) (encode δ q B) (encode_provable δ hδ hab q)
  refine ⟨decode δ q J, ?_, ?_, ?_⟩
  · have h := decode_provable δ hδ haj q
    change Provable n (.imp (decode δ q (encode δ q A)) (decode δ q J)) at h
    rwa [decode_encode] at h
  · have h := decode_provable δ hδ hjb q
    change Provable n (.imp (decode δ q J) (decode δ q (encode δ q B))) at h
    rwa [decode_encode] at h
  · rintro p z ⟨s, hz⟩
    obtain ⟨⟨t, ha⟩, ⟨u, hb⟩⟩ := hs (p,z) ⟨s, decode_support δ q J s p z hz⟩
    exact ⟨⟨t, (encode_vocab_iff δ q A t p z).mp ha⟩,
      ⟨u, (encode_vocab_iff δ q B u p z).mp hb⟩⟩

theorem signedCraig_of_periodic (n : ℕ) (hn : 0 < n) {c : ℕ → C}
    (hl : OrdinaryLyndon n (α × CanonicalPhase n)) (hc : PositivePeriodic n c) :
    SignedCraig n c α := by
  have hq : SignedCraig n (canonicalOrbit n hn) α :=
    signedCraig_phase (canonicalSuccessor n hn) none
      (fun q => congrFun (canonicalSuccessor_power n hn) q) hl
  have h := signedCraig_coarsen (canonicalLabels c) hq
  have he : canonicalLabels c ∘ canonicalOrbit n hn = c := funext (hc.factor hn)
  rwa [he] at h

theorem unsignedCraig_of_periodic (n : ℕ) (hn : 0 < n) {c : ℕ → C}
    (hl : OrdinaryCraig n (α × CanonicalPhase n)) (hc : PositivePeriodic n c) :
    UnsignedCraig n c α := by
  have hq : UnsignedCraig n (canonicalOrbit n hn) α :=
    unsignedCraig_phase (canonicalSuccessor n hn) none
      (fun q => congrFun (canonicalSuccessor_power n hn) q) hl
  have h := unsignedCraig_coarsen (canonicalLabels c) hq
  have he : canonicalLabels c ∘ canonicalOrbit n hn = c := funext (hc.factor hn)
  rwa [he] at h

/-- The signed classification separates the ordinary logical assumption from the labels. -/
theorem signedCraig_iff (n : ℕ) (hn : 0 < n) (c : ℕ → C) :
    SignedCraig n c ℕ ↔ OrdinaryLyndon n ℕ ∧ PositivePeriodic n c := by
  constructor
  · intro h
    exact ⟨signedCraig_ordinaryLyndon h, unsignedCraig_periodic hn (signedCraig_unsignedCraig h)⟩
  · rintro ⟨hl, hc⟩
    exact signedCraig_of_periodic n hn (ordinaryLyndon_countable hl) hc

/-- The unsigned classification requires only ordinary Craig interpolation. -/
theorem unsignedCraig_iff (n : ℕ) (hn : 0 < n) (c : ℕ → C) :
    UnsignedCraig n c ℕ ↔ OrdinaryCraig n ℕ ∧ PositivePeriodic n c := by
  constructor
  · intro h
    exact ⟨unsignedCraig_ordinaryCraig h, unsignedCraig_periodic hn h⟩
  · rintro ⟨hl, hc⟩
    exact unsignedCraig_of_periodic n hn (ordinaryCraig_countable hl) hc

end ModalDepth
