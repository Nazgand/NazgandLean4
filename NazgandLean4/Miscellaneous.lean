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
  constructor
  · sorry
  · intro h
    rw [h]
    ext z
    rw [deriv_const_mul]
    · have h_inner : DifferentiableAt ℂ (fun z => (f 0) ^ (k - 1) * z₀ * z) z := by
        apply DifferentiableAt.mul
        · apply differentiableAt_const
        · apply differentiableAt_id
      change f 0 * deriv (Complex.exp ∘ (fun z => (f 0) ^ (k - 1) * z₀ * z)) z = _
      rw [deriv_comp z Complex.differentiableAt_exp h_inner]
      rw [deriv_const_mul _ differentiableAt_id]
      rw [Complex.deriv_exp]
      simp only [deriv_id'']
      have hk : (k : ℂ) ≠ 0 := by
        norm_cast
        exact Nat.pos_iff_ne_zero.mp h1
      rw [mul_pow, ←Complex.exp_nat_mul]
      field_simp [hk]
      ring_nf
      have h_pow : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.succ_le_of_lt h1)
      rw [←pow_succ', h_pow]
    · apply DifferentiableAt.comp
      · apply Complex.differentiableAt_exp
      · apply DifferentiableAt.mul
        · apply differentiableAt_const
        · apply differentiableAt_id

theorem SameInterval (db : ℕ → ℕ) (h0 : ∀(d : ℕ), db d > 1) :
  {r : ℝ | ∃(dv : ℕ → ℕ), ((∀(d : ℕ), db d > dv d) ∧
  r = tsum (λ (d : ℕ) ↦ (dv d : ℝ) / ∏ k ∈ Finset.range (d + 1), db k))}
  = {r : ℝ | r ≥ 0 ∧ r ≤ 1} := by
  sorry

theorem SummableSum (db dv : ℕ → ℕ) (h0 : ∀(d : ℕ), (db d > 1 ∧ db d > dv d)) :
  Summable (λ (d : ℕ) ↦ (dv d : ℝ) / ∏ k ∈ Finset.range (d + 1), db k) := by
  sorry
