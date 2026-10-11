module

public import ModalDepth.Renaming
public import ModalDepth.Transfer
public import ModalDepth.Substitution

@[expose] public section

namespace ModalDepth.NegativeControls

/-- A colored atom whose stored color disagrees with the initial phase. -/
def wrongColor : Formula (ℕ × Bool) := .atom (0, true)

/-- Forgetting colors blindly creates a support pair absent from the source. -/
theorem blind_decoder_fails_support :
    (rename Prod.fst wrongColor).support (fun d => Bool.not^[d] false) true 0 false ∧
      ¬ wrongColor.vocab true (0, false) := by
  constructor
  · exact ⟨0, ⟨rfl, rfl, rfl⟩, rfl⟩
  · simp [wrongColor, Formula.vocab, Formula.Occurs]

/-- The actual decoder deletes the mismatched occurrence. -/
theorem selective_decoder_removes_wrong_color :
    decode Bool.not false wrongColor = .bot := by
  simp [decode, wrongColor, phaseTranslate]

/-- A two-cycle violates the phase identity for GL. -/
theorem two_cycle_not_GL_phase :
    ¬ (∀ q : Bool, Bool.not^[1 + 1] q = Bool.not q) := by
  intro h
  have hfalse := h false
  contradiction

/-- A concrete theorem of GL used to test phase preservation. -/
def transitivityInput : Formula ℕ :=
  .imp (.box (.atom 0)) (.box (.box (.atom 0)))

theorem transitivityInput_provable : Provable 1 transitivityInput :=
  Obstruction.n_transitivity (.atom 0)

/-- Removing the power condition actually loses theorem preservation. -/
theorem two_cycle_loses_provability :
    ¬ Provable 1 (encode Bool.not false transitivityInput) := by
  intro h
  have he := Obstruction.sound (by decide : 0 < 1) h
    (fun _ p => p.2 = true) 2
  change (∀ y, y < 2 → true = true) →
    ∀ y, y < 2 → ∀ z, z < y → false = true at he
  have hfalse := he (fun _ _ => rfl) 1 (by decide) 0 (by decide)
  contradiction

/-- Even unsigned parity interpolation fails for period one. -/
theorem parity_GL_fails : ¬ UnsignedCraig 1 (fun d => d % 2) ℕ := by
  intro h
  have hp := unsignedCraig_periodic (by decide : 0 < 1) h 1 (by decide)
  norm_num at hp

/-- Literal depth cannot be substituted for periodic depth in the theorem. -/
theorem exact_depth_two_fails : ¬ UnsignedCraig 2 (fun d => d) ℕ := by
  intro h
  exact exactDepth_not_periodic 2 (by decide)
    (unsignedCraig_periodic (by decide : 0 < 2) h)

/-- Depth zero remains distinct from positive even depth in the canonical colors. -/
theorem root_ne_positive_even :
    canonicalOrbit 2 (by decide) 0 ≠ canonicalOrbit 2 (by decide) 2 := by
  decide

/-- The substitution obstruction still applies when no target atoms exist. -/
theorem parity_GL_substitution_fails :
    ¬ DepthSubstitution 1 (fun d => d % 2) ℕ Empty := by
  intro h
  have hp := (depthSubstitution_iff 1 (by decide) (fun d => d % 2)).mp h 1 (by decide)
  norm_num at hp

/-- Constants suffice as target formulas for admissible substitutions too. -/
theorem parity_two_substitution :
    DepthSubstitution 2 (fun d => d % 2) ℕ Empty := by
  apply (depthSubstitution_iff 2 (by decide) (fun d => d % 2)).mpr
  exact (positivePeriodic_mod_iff 2 2 (by decide) (by decide)).mpr (dvd_refl 2)

end ModalDepth.NegativeControls
