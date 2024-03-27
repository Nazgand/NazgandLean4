import Mathlib
set_option maxHeartbeats 0
open Classical

lemma impliesOr (p q r : Prop) : (p → (q ∨ r)) ↔ ((p → q) ∨ (p → r)) := by
  exact imp_or -- I'm glad this is already in mathlib

lemma impliesAnd (p q r : Prop) : (p → (q ∧ r)) ↔ ((p → q) ∧ (p → r)) := by
  exact forall_and -- I'm glad this is already in mathlib

lemma trueImpliesOnlyTrue (p r : Prop) : p → ((p → r) ↔ r) := by
  exact fun a => forall_prop_of_true a

-- This should be in Mathlib, it is just as important as impliesOr and impliesAnd
lemma impliesImplies (p q r : Prop) : (p → (q → r)) ↔ ((p → q) → (p → r)) := by
  have h₀ : p ∨ ¬p := by exact _root_.em p
  rcases h₀ with ha | hb
  · constructor
    · exact fun a a_1 _ => a ha (a_1 ha)
    · have h₁ := trueImpliesOnlyTrue p q
      have h₂ := trueImpliesOnlyTrue p r
      have h₃ := trueImpliesOnlyTrue p (q → r)
      have h₁b : p → q ↔ q := by exact h₁ ha
      have h₂b : p → r ↔ r := by exact h₂ ha
      have h₃b : p → (q → r) ↔ (q → r) := by exact h₃ ha
      rw [h₁b, h₂b, h₃b]
      exact fun a a_1 => a a_1
  · constructor
    · exact fun a a_1 a_2 => a a_2 (a_1 a_2)
    · exact fun _ a _ => (hb a).elim

-- This should be in Mathlib, it is just as important as impliesOr and impliesAnd
lemma impliesIff (p q r : Prop) : (p → (q ↔ r)) ↔ ((p → q) ↔ (p → r)) := by
  have h₀ : p ∨ ¬p := by exact _root_.em p
  rcases h₀ with ha | hb
  · constructor
    · exact fun a => forall_congr' a
    · have h₁ := trueImpliesOnlyTrue p q
      have h₂ := trueImpliesOnlyTrue p r
      have h₃ := trueImpliesOnlyTrue p (q ↔ r)
      have h₁b : p → q ↔ q := by exact h₁ ha
      have h₂b : p → r ↔ r := by exact h₂ ha
      have h₃b : p → (q ↔ r) ↔ (q ↔ r) := by exact h₃ ha
      rw [h₁b, h₂b, h₃b]
      exact fun a => a
  · constructor
    · exact fun a => forall_congr' a
    · exact fun _ a => (hb a).elim
