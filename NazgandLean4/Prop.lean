import Mathlib
set_option maxHeartbeats 0
open Classical Finset

lemma impliesOr (p q r : Prop) : (p → (q ∨ r)) ↔ ((p → q) ∨ (p → r)) := by
  tauto

lemma impliesAnd (p q r : Prop) : (p → (q ∧ r)) ↔ ((p → q) ∧ (p → r)) := by
  tauto

lemma impliesImplies (p q r : Prop) : (p → (q → r)) ↔ ((p → q) → (p → r)) := by
  tauto

lemma impliesIff (p q r : Prop) : (p → (q ↔ r)) ↔ ((p → q) ↔ (p → r)) := by
  tauto

lemma trueImpliesOnlyTrue (p r : Prop) : p → ((p → r) ↔ r) := by
  tauto

lemma impliesReorder (p q r : Prop) : (p → (q → r)) ↔ (q → (p → r)) := by
  tauto

lemma impliesAndImplies (p q r : Prop) : (p → (q → r)) ↔ ((q ∧ p) → r) := by
  tauto

lemma impliesOrImplies (p₀ p₁ r : Prop) : ((p₀ → r) ∧ (p₁ → r)) ↔ ((p₀ ∨ p₁) → r) := by
  tauto

lemma impliesOrImplies3 (p₀ p₁ p₂ r : Prop) : ((p₀ → r) ∧ (p₁ → r) ∧ (p₂ → r)) ↔ ((p₀ ∨ p₁ ∨ p₂) → r) := by
  tauto

lemma impliesOrImplies4 (p₀ p₁ p₂ p₃ r : Prop) : ((p₀ → r) ∧ (p₁ → r) ∧ (p₂ → r) ∧ (p₃ → r)) ↔ ((p₀ ∨ p₁ ∨ p₂ ∨ p₃) → r) := by
  tauto

lemma impliesOrImpliesGeneralized (k : ℕ+) (p : ℕ → Prop) (r : Prop) : (∀ k₀ ∈ range k, (p k₀ → r)) ↔ ((∃ k₀ ∈ range k, p k₀) → r) := by
  aesop

lemma combineCases (q r : Prop) : ((q → r) ∧ ((¬q) → r)) ↔ r := by
  tauto

lemma combineCasesGeneralized (k : ℕ+) (p : ℕ → Prop) (r : Prop) : (∃ k₀ ∈ range k, p k₀) → (r ↔ (∀ k₀ ∈ range k, (p k₀ → r))) := by
  tauto

lemma squashImplies (q r : Prop) : (q → (q → r)) ↔ (q → r) := by
  tauto

lemma insightFromGeneralization (p₀ p₁ p₂ : Prop) : (p₀ ↔ (p₁ → p₂)) → (p₁ → (p₀ ↔ p₂)) := by
  tauto
