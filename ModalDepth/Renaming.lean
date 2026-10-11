import ModalDepth.Phase
import ModalDepth.Interpolation

namespace ModalDepth

variable {α β : Type}

/-- Ordinary renaming is the one-phase instance of phase translation. -/
def rename (f : α → β) (A : Formula α) : Formula β :=
  phaseTranslate (id : Unit → Unit) (fun _ p => .atom (f p)) () A

theorem rename_provable (f : α → β) {A : Formula α} (hA : Provable n A) :
    Provable n (rename f A) := by
  apply phaseTranslate_provable (id : Unit → Unit) _ _ hA ()
  intro q
  simp

theorem rename_roundtrip (i : α → β) (d : β → α)
    (hi : Function.LeftInverse d i) (A : Formula α) :
    rename d (rename i A) = A := by
  induction A with
  | atom p => simpa only [rename, phaseTranslate] using congrArg Formula.atom (hi p)
  | bot => rfl
  | imp A B ihA ihB =>
    change Formula.imp (rename d (rename i A)) (rename d (rename i B)) = _
    rw [ihA, ihB]
  | box A ih =>
    change Formula.box (rename d (rename i A)) = _
    rw [ih]

theorem rename_occurs_iff (f : α → β) (A : Formula α)
    (s : Bool) (d : ℕ) (b : β) :
    (rename f A).Occurs s d b ↔ ∃ a, A.Occurs s d a ∧ f a = b := by
  induction A generalizing s d with
  | atom a =>
    simp only [rename, phaseTranslate, Formula.Occurs]
    constructor
    · rintro ⟨hs, hd, hb⟩
      exact ⟨a, ⟨hs, hd, rfl⟩, hb.symm⟩
    · rintro ⟨a', ⟨hs, hd, rfl⟩, hb⟩
      exact ⟨hs, hd, hb.symm⟩
  | bot => simp [rename, phaseTranslate, Formula.Occurs]
  | imp A B ihA ihB =>
    change ((rename f A).Occurs (!s) d b ∨ (rename f B).Occurs s d b) ↔ _
    rw [ihA, ihB]
    simp only [Formula.Occurs]
    constructor
    · rintro (⟨a, ha, hab⟩ | ⟨a, ha, hab⟩)
      · exact ⟨a, Or.inl ha, hab⟩
      · exact ⟨a, Or.inr ha, hab⟩
    · rintro ⟨a, ha | ha, hab⟩
      · exact Or.inl ⟨a, ha, hab⟩
      · exact Or.inr ⟨a, ha, hab⟩
  | box A ih =>
    change (∃ e, d = e + 1 ∧ (rename f A).Occurs s e b) ↔ _
    simp only [ih, Formula.Occurs]
    constructor
    · rintro ⟨e, hd, a, ha, hab⟩
      exact ⟨a, ⟨e, hd, ha⟩, hab⟩
    · rintro ⟨a, ⟨e, hd, ha⟩, hab⟩
      exact ⟨e, hd, a, ha, hab⟩

theorem rename_vocab_iff (f : α → β) (A : Formula α) (s : Bool) (b : β) :
    (rename f A).vocab s b ↔ ∃ a, A.vocab s a ∧ f a = b := by
  simp only [Formula.vocab, rename_occurs_iff]
  constructor
  · rintro ⟨d, a, ha, hab⟩
    exact ⟨a, ⟨d, ha⟩, hab⟩
  · rintro ⟨a, ⟨d, ha⟩, hab⟩
    exact ⟨d, a, ha, hab⟩

/-- Source support makes uniform interpolation invariant under retracts of alphabets. -/
theorem sourceULI_of_retract (hu : SourceULI n β) (i : α → β) (d : β → α)
    (hi : Function.LeftInverse d i) : SourceULI n α := by
  intro A W
  obtain ⟨J, hs, hai, hU⟩ := hu (rename i A) (fun s b => W s (d b))
  refine ⟨rename d J, ?_, ?_, ?_⟩
  · intro s p hp
    obtain ⟨b, hb, hbp⟩ := (rename_vocab_iff d J s p).mp hp
    obtain ⟨hA, hW⟩ := hs s b hb
    obtain ⟨a, ha, hab⟩ := (rename_vocab_iff i A s b).mp hA
    have hap : a = p := by
      calc
        a = d (i a) := (hi a).symm
        _ = d b := congrArg d hab
        _ = p := hbp
    exact ⟨by simpa only [hap] using ha, by simpa only [hbp] using hW⟩
  · have h := rename_provable d hai
    change Provable n (.imp (rename d (rename i A)) (rename d J)) at h
    simpa only [rename_roundtrip i d hi] using h
  · intro B hBW hAB
    have hAB' : Provable n (.imp (rename i A) (rename i B)) :=
      rename_provable i hAB
    have hJB := hU (rename i B) (by
      intro s b hb
      obtain ⟨a, ha, hab⟩ := (rename_vocab_iff i B s b).mp hb
      simpa only [← hab, hi a] using hBW s a ha) hAB'
    have h := rename_provable d hJB
    change Provable n (.imp (rename d J) (rename d (rename i B))) at h
    simpa only [rename_roundtrip i d hi] using h

/-- Transfer from natural-number atoms to any nonempty encodable alphabet. -/
theorem sourceULI_countable [Encodable α] [Nonempty α]
    (hu : SourceULI n ℕ) : SourceULI n α := by
  classical
  let d : ℕ → α := fun k => (Encodable.decode (α := α) k).getD (Classical.choice ‹Nonempty α›)
  apply sourceULI_of_retract hu Encodable.encode d
  intro a
  simp [d, Encodable.encodek]

end ModalDepth
