import Mathlib
set_option maxHeartbeats 0
open Classical Finset

theorem ImpliesDef (p₀ p₁ : Prop) :
  (p₀ → p₁) ↔ (p₁ ↔ (p₀ ∨ p₁)) := by
  tauto

theorem ImpliesOr (p q r : Prop) :
  (p → (q ∨ r)) ↔ ((p → q) ∨ (p → r)) := by
  tauto

theorem ImpliesAnd (p q r : Prop) :
  (p → (q ∧ r)) ↔ ((p → q) ∧ (p → r)) := by
  tauto

theorem ImpliesImplies (p q r : Prop) :
  (p → (q → r)) ↔ ((p → q) → (p → r)) := by
  tauto

theorem ImpliesIff (p q r : Prop) :
  (p → (q ↔ r)) ↔ ((p → q) ↔ (p → r)) := by
  tauto

theorem TrueImpliesOnlyTrue (p r : Prop) :
  p → ((p → r) ↔ r) := by
  tauto

theorem ImpliesReorder (p q r : Prop) :
  (p → (q → r)) ↔ (q → (p → r)) := by
  tauto

theorem ImpliesAndImplies (p q r : Prop) :
  (p → (q → r)) ↔ ((q ∧ p) → r) := by
  tauto

theorem ImpliesOrImplies (p₀ p₁ r : Prop) :
  ((p₀ → r) ∧ (p₁ → r)) ↔ ((p₀ ∨ p₁) → r) := by
  tauto

theorem ImpliesOrImplies3 (p₀ p₁ p₂ r : Prop) :
  ((p₀ → r) ∧ (p₁ → r) ∧ (p₂ → r)) ↔ ((p₀ ∨ p₁ ∨ p₂) → r) := by
  tauto

theorem ImpliesOrImplies4 (p₀ p₁ p₂ p₃ r : Prop) :
  ((p₀ → r) ∧ (p₁ → r) ∧ (p₂ → r) ∧ (p₃ → r)) ↔ ((p₀ ∨ p₁ ∨ p₂ ∨ p₃) → r) := by
  tauto

theorem ImpliesOrImpliesGeneralized (k : ℕ+) (p : ℕ → Prop) (r : Prop) :
  (∀ k₀ ∈ range k, (p k₀ → r)) ↔ ((∃ k₀ ∈ range k, p k₀) → r) := by
  aesop

theorem CombineCases (q r : Prop) :
  ((q → r) ∧ ((¬q) → r)) ↔ r := by
  tauto

theorem CombineCasesGeneralized (k : ℕ+) (p : ℕ → Prop) (r : Prop) :
  (∃ k₀ ∈ range k, p k₀) → (r ↔ (∀ k₀ ∈ range k, (p k₀ → r))) := by
  tauto

theorem SquashImplies (q r : Prop) :
  (q → (q → r)) ↔ (q → r) := by
  tauto

theorem InsightFromGeneralization (p₀ p₁ p₂ : Prop) :
  (p₀ ↔ (p₁ → p₂)) → (p₁ → (p₀ ↔ p₂)) := by
  tauto

theorem SwapNot2Of3 (p₀ p₁ p₂ : Prop) :
  (p₀ ↔ (p₁ ↔ p₂)) ↔ (p₁ ↔ (p₀ ↔ p₂)) := by
  tauto
