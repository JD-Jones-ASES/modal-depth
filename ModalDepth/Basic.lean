module

public import Mathlib.Tactic

@[expose] public section

namespace ModalDepth

inductive Formula (α : Type) where
  | atom : α → Formula α
  | bot : Formula α
  | imp : Formula α → Formula α → Formula α
  | box : Formula α → Formula α
  deriving DecidableEq, Repr

namespace Formula

def boxes (k : ℕ) (A : Formula α) : Formula α :=
  match k with
  | 0 => A
  | k + 1 => .box (boxes k A)

def conj (A B : Formula α) : Formula α := .imp (.imp A (.imp B .bot)) .bot

/-- Joint signed occurrences at a literal modal depth. `true` means positive. -/
def Occurs : Formula α → Bool → ℕ → α → Prop
  | .atom q, s, d, p => s = true ∧ d = 0 ∧ p = q
  | .bot, _, _, _ => False
  | .imp A B, s, d, p => Occurs A (!s) d p ∨ Occurs B s d p
  | .box A, s, d, p => ∃ e, d = e + 1 ∧ Occurs A s e p

def vocab (A : Formula α) (s : Bool) (p : α) : Prop := ∃ d, A.Occurs s d p

def support (c : ℕ → C) (A : Formula α) (s : Bool) (p : α) (z : C) : Prop :=
  ∃ d, A.Occurs s d p ∧ c d = z

def unsigned (c : ℕ → C) (A : Formula α) (p : α) (z : C) : Prop :=
  ∃ s, A.support c s p z

end Formula

/-- A propositional template, whose atoms may be arbitrary modal formulas. -/
inductive PropForm (α : Type) where
  | atom : α → PropForm α
  | bot : PropForm α
  | imp : PropForm α → PropForm α → PropForm α

namespace PropForm

def eval (v : α → Prop) : PropForm α → Prop
  | .atom p => v p
  | .bot => False
  | .imp A B => eval v A → eval v B

def subst (f : α → Formula β) : PropForm α → Formula β
  | .atom p => f p
  | .bot => .bot
  | .imp A B => .imp (subst f A) (subst f B)

end PropForm

/-- The ordinary Hilbert presentation of Sacchetti's logic. -/
inductive Provable (n : ℕ) : Formula α → Prop where
  | taut (t : PropForm (Formula α)) (h : ∀ v, t.eval v) :
      Provable n (t.subst id)
  | k (A B : Formula α) :
      Provable n (.imp (.box (.imp A B)) (.imp (.box A) (.box B)))
  | loeb (A : Formula α) :
      Provable n (.imp (.box (.imp (A.boxes n) A)) (.box A))
  | mp {A B : Formula α} : Provable n (.imp A B) → Provable n A → Provable n B
  | nec {A : Formula α} : Provable n A → Provable n (.box A)

/-- The published vocabulary-only convention; source support is separate. -/
def OrdinaryULI (n : ℕ) (α : Type) : Prop :=
  ∀ (A : Formula α) (W : Bool → α → Prop), ∃ I : Formula α,
    (∀ s p, I.vocab s p → W s p) ∧ Provable n (.imp A I) ∧
    ∀ B : Formula α, (∀ s p, B.vocab s p → W s p) →
      Provable n (.imp A B) → Provable n (.imp I B)

def OrdinaryLyndon (n : ℕ) (α : Type) : Prop :=
  ∀ A B : Formula α, Provable n (.imp A B) → ∃ I : Formula α,
    Provable n (.imp A I) ∧ Provable n (.imp I B) ∧
    ∀ s p, I.vocab s p → A.vocab s p ∧ B.vocab s p

def UniformSigned (n : ℕ) (c : ℕ → C) (α : Type) : Prop :=
  ∀ (A : Formula α) (W : Bool → α → C → Prop), ∃ I : Formula α,
    (∀ s p z, I.support c s p z → A.support c s p z ∧ W s p z) ∧
    Provable n (.imp A I) ∧ ∀ B : Formula α,
    (∀ s p z, B.support c s p z → W s p z) →
      Provable n (.imp A B) → Provable n (.imp I B)

def SignedCraig (n : ℕ) (c : ℕ → C) (α : Type) : Prop :=
  ∀ A B : Formula α, Provable n (.imp A B) → ∃ I : Formula α,
    Provable n (.imp A I) ∧ Provable n (.imp I B) ∧
    ∀ s p z, I.support c s p z → A.support c s p z ∧ B.support c s p z

def UnsignedCraig (n : ℕ) (c : ℕ → C) (α : Type) : Prop :=
  ∀ A B : Formula α, Provable n (.imp A B) → ∃ I : Formula α,
    Provable n (.imp A I) ∧ Provable n (.imp I B) ∧
    ∀ p z, I.unsigned c p z → A.unsigned c p z ∧ B.unsigned c p z

def PositivePeriodic (n : ℕ) (c : ℕ → C) : Prop :=
  ∀ k : ℕ, 0 < k → c (k + n) = c k

end ModalDepth
