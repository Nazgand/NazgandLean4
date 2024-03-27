import Mathlib
set_option maxHeartbeats 0
open Classical

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

lemma impliesOrImplies (p q r : Prop) : ((q → r) ∧ (p → r)) ↔ ((q ∨ p) → r) := by
  tauto

lemma combineCases (q r : Prop) : ((q → r) ∧ ((¬q) → r)) ↔ r := by
  tauto
