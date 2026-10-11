module

public import ModalDepth.Basic

@[expose] public section

namespace ModalDepth

/-- Ordinary uniform Lyndon interpolation with support in the input formula. -/
def SourceULI (n : ℕ) (α : Type) : Prop :=
  ∀ (A : Formula α) (W : Bool → α → Prop), ∃ I : Formula α,
    (∀ s p, I.vocab s p → A.vocab s p ∧ W s p) ∧
    Provable n (.imp A I) ∧ ∀ B : Formula α,
    (∀ s p, B.vocab s p → W s p) →
      Provable n (.imp A B) → Provable n (.imp I B)

theorem provable_imp_trans {A B D : Formula α}
    (hAB : Provable n (.imp A B)) (hBD : Provable n (.imp B D)) :
    Provable n (.imp A D) := by
  let t : PropForm (Formula α) :=
    .imp (.imp (.atom A) (.atom B))
      (.imp (.imp (.atom B) (.atom D)) (.imp (.atom A) (.atom D)))
  have ht : Provable n (t.subst id) := Provable.taut t (by
    intro v
    dsimp [t, PropForm.eval]
    exact fun hab hbd ha => hbd (hab ha))
  exact Provable.mp (Provable.mp ht hAB) hBD

theorem sourceULI_of_ordinary (hu : OrdinaryULI n α) (hl : OrdinaryLyndon n α) :
    SourceULI n α := by
  intro A W
  obtain ⟨J, hJW, hAJ, hJU⟩ := hu A W
  obtain ⟨I, hAI, hIJ, hI⟩ := hl A J hAJ
  refine ⟨I, ?_, hAI, ?_⟩
  · intro s p hp
    exact ⟨(hI s p hp).1, hJW s p (hI s p hp).2⟩
  · intro B hBW hAB
    exact provable_imp_trans hIJ (hJU B hBW hAB)

theorem sourceULI_ordinary (h : SourceULI n α) : OrdinaryULI n α := by
  intro A W
  obtain ⟨I, hs, hai, hu⟩ := h A W
  exact ⟨I, fun s p hp => (hs s p hp).2, hai, hu⟩

theorem sourceULI_lyndon (h : SourceULI n α) : OrdinaryLyndon n α := by
  intro A B hab
  obtain ⟨I, hs, hai, hu⟩ := h A (fun s p => B.vocab s p)
  exact ⟨I, hai, hu B (fun _ _ h => h) hab, hs⟩

theorem sourceULI_iff : SourceULI n α ↔ OrdinaryULI n α ∧ OrdinaryLyndon n α :=
  ⟨fun h => ⟨sourceULI_ordinary h, sourceULI_lyndon h⟩,
    fun h => sourceULI_of_ordinary h.1 h.2⟩

theorem uniformSigned_sourceULI (h : UniformSigned n c α) : SourceULI n α := by
  intro A W
  obtain ⟨I, hs, hai, hu⟩ := h A (fun s p _ => W s p)
  refine ⟨I, ?_, hai, ?_⟩
  · intro s p hp
    obtain ⟨d, hd⟩ := hp
    obtain ⟨⟨e, he, _⟩, hw⟩ := hs s p (c d) ⟨d, hd, rfl⟩
    exact ⟨⟨e, he⟩, hw⟩
  · intro B hb hab
    apply hu B ?_ hab
    intro s p z hz
    obtain ⟨d, hd, _⟩ := hz
    exact hb s p ⟨d, hd⟩

theorem uniformSigned_signedCraig (h : UniformSigned n c α) : SignedCraig n c α := by
  intro A B hab
  obtain ⟨I, hs, hai, hu⟩ := h A (fun s p z => B.support c s p z)
  exact ⟨I, hai, hu B (fun _ _ _ h => h) hab, hs⟩

theorem signedCraig_unsignedCraig (h : SignedCraig n c α) : UnsignedCraig n c α := by
  intro A B hab
  obtain ⟨I, hai, hib, hs⟩ := h A B hab
  refine ⟨I, hai, hib, ?_⟩
  intro p z hz
  obtain ⟨s, hsI⟩ := hz
  exact ⟨⟨s, (hs s p z hsI).1⟩, ⟨s, (hs s p z hsI).2⟩⟩

theorem uniformSigned_coarsen {k : ℕ → Q} (h : Q → C)
    (hu : UniformSigned n k α) : UniformSigned n (h ∘ k) α := by
  intro A W
  obtain ⟨I, hs, hai, hU⟩ := hu A (fun s p q => W s p (h q))
  refine ⟨I, ?_, hai, ?_⟩
  · intro s p z hz
    obtain ⟨d, hd, rfl⟩ := hz
    obtain ⟨⟨e, he, hke⟩, hw⟩ := hs s p (k d) ⟨d, hd, rfl⟩
    refine ⟨⟨e, he, ?_⟩, hw⟩
    exact congrArg h hke
  · intro B hb hab
    apply hU B ?_ hab
    intro s p q hp
    obtain ⟨d, hd, rfl⟩ := hp
    exact hb s p (h (k d)) ⟨d, hd, rfl⟩

end ModalDepth
