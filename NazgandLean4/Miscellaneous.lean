import Mathlib
set_option maxHeartbeats 0

theorem GeneralPigeonholePrinciple₀ (k : ℕ) (f : ℕ → ℝ) (slb : ℝ)
  (h0 : slb < (Finset.range (k + 1)).sum f) :
  ∃ m ∈ (Finset.range (k + 1)), f m > slb / (k + 1) := by
  by_contra h
  push_neg at h
  have h1 : (Finset.range (k + 1)).sum f ≤ ∑ i ∈ Finset.range (k + 1), slb / (k + 1) := by
    apply Finset.sum_le_sum
    intros i hi
    exact h i hi
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
  have h2 : (↑(k + 1) : ℝ) ≠ 0 := by
    norm_cast
  field_simp [h2] at h1
  rw [mul_comm ((Finset.range (k + 1)).sum f)] at h1
  have h3 : 0 < (↑(k + 1) : ℝ) := by norm_cast; linarith
  norm_cast at h1
  replace h1 := le_of_mul_le_mul_left h1 h3
  linarith

theorem GeneralPigeonholePrinciple₁ (k : ℕ) (f : ℕ → ℝ) (slb : ℝ)
  (h0 : slb ≤ (Finset.range (k + 1)).sum f) :
  ∃ m ∈ (Finset.range (k + 1)), f m ≥ slb / (k + 1) := by
  by_contra h
  push_neg at h
  have h1 : (Finset.range (k + 1)).sum f < ∑ i ∈ Finset.range (k + 1), slb / (k + 1) := by
    apply Finset.sum_lt_sum
    · intros i hi
      exact le_of_lt (h i hi)
    · use 0
      simp only [Finset.mem_range, Nat.zero_lt_succ, true_and]
      exact h 0 (Finset.mem_range.mpr (Nat.zero_lt_succ k))
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
  have h2 : (↑(k + 1) : ℝ) ≠ 0 := by
    norm_cast
  field_simp [h2] at h1
  rw [mul_comm ((Finset.range (k + 1)).sum f)] at h1
  have h3 : 0 < (↑(k + 1) : ℝ) := by norm_cast; linarith
  norm_cast at h1
  replace h1 := lt_of_mul_lt_mul_left h1 (le_of_lt h3)
  linarith

theorem MiscDiffEq (f : ℂ → ℂ) (h0 : Differentiable ℂ f) (z₀ : ℂ) (k : ℕ) (h1 : k > 0) :
  deriv f = (λ (z : ℂ) ↦ z₀ * (f (z / k)) ^ k) ↔
  f = (λ (z : ℂ) ↦ (f 0) * ((f 0) ^ (k - 1) * z₀ * z).exp) := by
  sorry

theorem SameInterval (db : ℕ → ℕ) (h0 : ∀(d : ℕ), db d > 1) :
  {r : ℝ | ∃(dv : ℕ → ℕ), ((∀(d : ℕ), db d > dv d) ∧
  r = tsum (λ (d : ℕ) ↦ (dv d : ℝ) / ∏ k ∈ Finset.range (d + 1), db k))}
  = {r : ℝ | r ≥ 0 ∧ r ≤ 1} := by
  sorry

theorem SummableSum (db dv : ℕ → ℕ) (h0 : ∀(d : ℕ), (db d > 1 ∧ db d > dv d)) :
  Summable (λ (d : ℕ) ↦ (dv d : ℝ) / ∏ k ∈ Finset.range (d + 1), db k) := by
  sorry
