import Mathlib
set_option maxHeartbeats 0
open Classical Finset

lemma ImpliesDef (p₀ p₁ : Prop) :
  (p₀ → p₁) ↔ (p₁ ↔ (p₀ ∨ p₁)) := by
  tauto

lemma ImpliesOr (p q r : Prop) :
  (p → (q ∨ r)) ↔ ((p → q) ∨ (p → r)) := by
  tauto

lemma ImpliesAnd (p q r : Prop) :
  (p → (q ∧ r)) ↔ ((p → q) ∧ (p → r)) := by
  tauto

lemma ImpliesImplies (p q r : Prop) :
  (p → (q → r)) ↔ ((p → q) → (p → r)) := by
  tauto

lemma ImpliesIff (p q r : Prop) :
  (p → (q ↔ r)) ↔ ((p → q) ↔ (p → r)) := by
  tauto

lemma TrueImpliesOnlyTrue (p r : Prop) :
  p → ((p → r) ↔ r) := by
  tauto

lemma ImpliesReorder (p q r : Prop) :
  (p → (q → r)) ↔ (q → (p → r)) := by
  tauto

lemma ImpliesAndImplies (p q r : Prop) :
  (p → (q → r)) ↔ ((q ∧ p) → r) := by
  tauto

lemma ImpliesOrImplies (p₀ p₁ r : Prop) :
  ((p₀ → r) ∧ (p₁ → r)) ↔ ((p₀ ∨ p₁) → r) := by
  tauto

lemma ImpliesOrImplies3 (p₀ p₁ p₂ r : Prop) :
  ((p₀ → r) ∧ (p₁ → r) ∧ (p₂ → r)) ↔ ((p₀ ∨ p₁ ∨ p₂) → r) := by
  tauto

lemma ImpliesOrImplies4 (p₀ p₁ p₂ p₃ r : Prop) :
  ((p₀ → r) ∧ (p₁ → r) ∧ (p₂ → r) ∧ (p₃ → r)) ↔ ((p₀ ∨ p₁ ∨ p₂ ∨ p₃) → r) := by
  tauto

lemma ImpliesOrImpliesGeneralized (k : ℕ+) (p : ℕ → Prop) (r : Prop) :
  (∀ k₀ ∈ range k, (p k₀ → r)) ↔ ((∃ k₀ ∈ range k, p k₀) → r) := by
  aesop

lemma CombineCases (q r : Prop) :
  ((q → r) ∧ ((¬q) → r)) ↔ r := by
  tauto

lemma CombineCasesGeneralized (k : ℕ+) (p : ℕ → Prop) (r : Prop) :
  (∃ k₀ ∈ range k, p k₀) → (r ↔ (∀ k₀ ∈ range k, (p k₀ → r))) := by
  tauto

lemma SquashImplies (q r : Prop) :
  (q → (q → r)) ↔ (q → r) := by
  tauto

lemma InsightFromGeneralization (p₀ p₁ p₂ : Prop) :
  (p₀ ↔ (p₁ → p₂)) → (p₁ → (p₀ ↔ p₂)) := by
  tauto

lemma SwapNot2Of3 (p₀ p₁ p₂ : Prop) :
  (p₀ ↔ (p₁ ↔ p₂)) ↔ (p₁ ↔ (p₀ ↔ p₂)) := by
  tauto
