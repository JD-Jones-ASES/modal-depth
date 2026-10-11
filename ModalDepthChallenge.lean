import Mathlib.Tactic

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


/-- Ordinary uniform Lyndon interpolation with support in the input formula. -/
def SourceULI (n : ℕ) (α : Type) : Prop :=
  ∀ (A : Formula α) (W : Bool → α → Prop), ∃ I : Formula α,
    (∀ s p, I.vocab s p → A.vocab s p ∧ W s p) ∧
    Provable n (.imp A I) ∧ ∀ B : Formula α,
    (∀ s p, B.vocab s p → W s p) →
      Provable n (.imp A B) → Provable n (.imp I B)


/-- Forget the polarity of an ordinary atomic occurrence. -/
def Formula.unsignedVocab (A : Formula α) (p : α) : Prop := ∃ s, A.vocab s p

/-- Ordinary Craig interpolation, without polarity or depth constraints. -/
def OrdinaryCraig (n : ℕ) (α : Type) : Prop :=
  ∀ A B : Formula α, Provable n (.imp A B) → ∃ I : Formula α,
    Provable n (.imp A I) ∧ Provable n (.imp I B) ∧
    ∀ p, I.unsignedVocab p → A.unsignedVocab p ∧ B.unsignedVocab p


variable {α β Q : Type}
/-- A substitution whose atomic image depends on the phase of an occurrence. -/
def phaseTranslate (δ : Q → Q) (f : Q → α → Formula β) (q : Q) :
    Formula α → Formula β
  | .atom p => f q p
  | .bot => .bot
  | .imp A B => .imp (phaseTranslate δ f q A) (phaseTranslate δ f q B)
  | .box A => .box (phaseTranslate δ f (δ q) A)


/-- Encode every atom together with its phase. -/
def encode (δ : Q → Q) (q : Q) (A : Formula α) : Formula (α × Q) :=
  phaseTranslate δ (fun q p => .atom (p, q)) q A

/-- Erase an atomic occurrence if its stored phase is incorrect. -/
noncomputable def decode (δ : Q → Q) (q : Q) (A : Formula (α × Q)) : Formula α := by
  classical
  exact phaseTranslate δ (fun q p => if p.2 = q then .atom p.1 else .bot) q A


end ModalDepth

namespace ModalDepth.Contracts
variable {α β Q C : Type}

theorem uniform_classification (n : ℕ) (hn : 0 < n) (c : ℕ → C) :
    UniformSigned n c ℕ ↔ SourceULI n ℕ ∧ PositivePeriodic n c := by
  sorry

theorem signed_classification (n : ℕ) (hn : 0 < n) (c : ℕ → C) :
    SignedCraig n c ℕ ↔ OrdinaryLyndon n ℕ ∧ PositivePeriodic n c := by
  sorry

theorem unsigned_classification (n : ℕ) (hn : 0 < n) (c : ℕ → C) :
    UnsignedCraig n c ℕ ↔ OrdinaryCraig n ℕ ∧ PositivePeriodic n c := by
  sorry

theorem classification_given_inputs (n : ℕ) (hn : 0 < n) (c : ℕ → C)
    (hu : OrdinaryULI n ℕ) (hl : OrdinaryLyndon n ℕ) :
    (UniformSigned n c ℕ ↔ PositivePeriodic n c) ∧
    (SignedCraig n c ℕ ↔ PositivePeriodic n c) ∧
    (UnsignedCraig n c ℕ ↔ PositivePeriodic n c) := by
  sorry

theorem residue_uniform (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    UniformSigned n (fun d => d % m) ℕ ↔ SourceULI n ℕ ∧ m ∣ n := by
  sorry

theorem residue_signed (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    SignedCraig n (fun d => d % m) ℕ ↔ OrdinaryLyndon n ℕ ∧ m ∣ n := by
  sorry

theorem residue_unsigned (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    UnsignedCraig n (fun d => d % m) ℕ ↔ OrdinaryCraig n ℕ ∧ m ∣ n := by
  sorry

theorem canonical_partition (n : ℕ) (hn : 0 < n) (c : ℕ → C) :
    PositivePeriodic n c ↔
      ∀ d e : ℕ, ((d = 0 ∧ e = 0) ∨ (0 < d ∧ 0 < e ∧ d % n = e % n)) → c d = c e := by
  sorry

theorem finite_labels (n : ℕ) (hn : 0 < n) (c : ℕ → C) (hc : PositivePeriodic n c) :
    ∃ s : Finset C, (∀ k, c k ∈ s) ∧ s.card ≤ n + 1 := by
  sorry

theorem positive_transitivity (n k : ℕ) (hk : 0 < k) (A : Formula α) :
    Provable n (.imp (A.boxes k) (A.boxes (k + n))) := by
  sorry

theorem unsigned_necessity (n : ℕ) (hn : 0 < n) (c : ℕ → C) [Nonempty α]
    (h : UnsignedCraig n c α) : PositivePeriodic n c := by
  sorry

theorem exact_depth_obstruction (n : ℕ) (hn : 0 < n) :
    ¬ UnsignedCraig n (fun d => d) ℕ := by
  sorry

theorem incompatible_modulus (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (h : ¬ m ∣ n) :
    ¬ UnsignedCraig n (fun d => d % m) ℕ := by
  sorry

theorem source_normalization (n : ℕ) :
    SourceULI n α ↔ OrdinaryULI n α ∧ OrdinaryLyndon n α := by
  sorry

theorem phase_preservation (n : ℕ) (δ : Q → Q) (f : Q → α → Formula β)
    (hδ : ∀ q, δ^[n + 1] q = δ q) (A : Formula α) (hA : Provable n A) (q : Q) :
    Provable n (phaseTranslate δ f q A) := by
  sorry

theorem decode_roundtrip (δ : Q → Q) (q : Q) (A : Formula α) :
    decode δ q (encode δ q A) = A := by
  sorry

theorem encoding_support (δ : Q → Q) (q : Q) (A : Formula α) (s : Bool) (p : α) (z : Q) :
    (encode δ q A).vocab s (p, z) ↔ A.support (fun d => δ^[d] q) s p z := by
  sorry

theorem decoding_support (δ : Q → Q) (q : Q) (A : Formula (α × Q)) (s : Bool) (p : α) (z : Q) :
    (decode δ q A).support (fun d => δ^[d] q) s p z → A.vocab s (p, z) := by
  sorry

theorem parity_with_inputs (hu : OrdinaryULI 2 ℕ) (hl : OrdinaryLyndon 2 ℕ) :
    UniformSigned 2 (fun d => d % 2) ℕ := by
  sorry

end ModalDepth.Contracts
