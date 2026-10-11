module

public import ModalDepth.Transfer

@[expose] public section

namespace ModalDepth

variable {α Q : Type}

namespace Formula

/-- Number of syntax-tree nodes; atom names have unit cost. -/
def nodeCount : Formula α → ℕ
  | .atom _ => 1
  | .bot => 1
  | .imp A B => A.nodeCount + B.nodeCount + 1
  | .box A => A.nodeCount + 1

/-- Maximum number of nested boxes, including boxes above variable-free formulas. -/
def modalDepth : Formula α → ℕ
  | .atom _ => 0
  | .bot => 0
  | .imp A B => max A.modalDepth B.modalDepth
  | .box A => A.modalDepth + 1

end Formula

/-- Phase encoding changes atom names, not the size of the syntax tree. -/
theorem encode_nodeCount (δ : Q → Q) (q : Q) (A : Formula α) :
    (encode δ q A).nodeCount = A.nodeCount := by
  induction A generalizing q with
  | atom p => rfl
  | bot => rfl
  | imp A B ihA ihB =>
    simp only [encode, phaseTranslate, Formula.nodeCount] at *
    rw [ihA, ihB]
  | box A ih =>
    simp only [encode, phaseTranslate, Formula.nodeCount] at *
    rw [ih]

/-- Phase encoding does not increase or decrease modal depth. -/
theorem encode_modalDepth (δ : Q → Q) (q : Q) (A : Formula α) :
    (encode δ q A).modalDepth = A.modalDepth := by
  induction A generalizing q with
  | atom p => rfl
  | bot => rfl
  | imp A B ihA ihB =>
    simp only [encode, phaseTranslate, Formula.modalDepth] at *
    rw [ihA, ihB]
  | box A ih =>
    simp only [encode, phaseTranslate, Formula.modalDepth] at *
    rw [ih]

/-- Decoding replaces a mismatched atom by one falsity node. -/
theorem decode_nodeCount (δ : Q → Q) (q : Q) (A : Formula (α × Q)) :
    (decode δ q A).nodeCount = A.nodeCount := by
  classical
  induction A generalizing q with
  | atom p =>
    by_cases h : p.2 = q <;> simp [decode, phaseTranslate, Formula.nodeCount, h]
  | bot => rfl
  | imp A B ihA ihB =>
    change (decode δ q A).nodeCount + (decode δ q B).nodeCount + 1 = _
    rw [ihA, ihB]
    rfl
  | box A ih =>
    change (decode δ (δ q) A).nodeCount + 1 = _
    rw [ih]
    rfl

/-- Decoding leaves all boxes and Boolean connective positions unchanged. -/
theorem decode_modalDepth (δ : Q → Q) (q : Q) (A : Formula (α × Q)) :
    (decode δ q A).modalDepth = A.modalDepth := by
  classical
  induction A generalizing q with
  | atom p =>
    by_cases h : p.2 = q <;> simp [decode, phaseTranslate, Formula.modalDepth, h]
  | bot => rfl
  | imp A B ihA ihB =>
    change max (decode δ q A).modalDepth (decode δ q B).modalDepth = _
    rw [ihA, ihB]
    rfl
  | box A ih =>
    change (decode δ (δ q) A).modalDepth + 1 = _
    rw [ih]
    rfl

/-- A given ordinary source-supported uniform interpolant can be decoded without
any syntax-tree size or modal-depth overhead. This is a witness-level transfer:
it does not assume or construct an ordinary interpolation algorithm. -/
theorem decode_uniformInterpolant (δ : Q → Q) (q : Q)
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
  refine ⟨decode δ q J, ?_, ?_, ?_, decode_nodeCount δ q J, decode_modalDepth δ q J⟩
  · intro s p z hz
    obtain ⟨ha, hw⟩ := hs s (p, z) (decode_support δ q J s p z hz)
    exact ⟨(encode_vocab_iff δ q A s p z).mp ha, hw⟩
  · have hd := decode_provable δ hδ hAJ q
    change Provable n (.imp (decode δ q (encode δ q A)) (decode δ q J)) at hd
    rwa [decode_encode] at hd
  · intro B hb hab
    have he := encode_provable δ hδ hab q
    change Provable n (.imp (encode δ q A) (encode δ q B)) at he
    have hJB := hU (encode δ q B) (by
      intro s p hp
      exact hb s p.1 p.2 ((encode_vocab_iff δ q B s p.1 p.2).mp hp)) he
    have hd := decode_provable δ hδ hJB q
    change Provable n (.imp (decode δ q J) (decode δ q (encode δ q B))) at hd
    rwa [decode_encode] at hd

end ModalDepth
