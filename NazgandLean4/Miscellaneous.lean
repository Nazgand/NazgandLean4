import Mathlib
set_option maxHeartbeats 0

theorem GeneralPigeonholePrinciple₀ (k : ℕ) (f : ℕ → ℝ) (slb : ℝ)
  (h0 : slb < (Finset.range (k + 1)).sum f) :
  ∃ m ∈ (Finset.range (k + 1)), f m > slb / (k + 1) := by
  by_contra h
  push_neg at h
  have h1 : (Finset.range (k + 1)).sum f ≤ ∑ i ∈ Finset.range (k + 1),
    slb / (k + 1) := by
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
  have h1 : (Finset.range (k + 1)).sum f < ∑ i ∈ Finset.range (k + 1),
    slb / (k + 1) := by
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

theorem MiscDiffEq (f : ℂ → ℂ) (h0 : Differentiable ℂ f)
  (z₀ : ℂ) (k : ℕ) (h1 : k > 0) :
  deriv f = (λ (z : ℂ) ↦ z₀ * (f (z / k)) ^ k) ↔
  f = (λ (z : ℂ) ↦ (f 0) * ((f 0) ^ (k - 1) * z₀ * z).exp) := by
  constructor
  · sorry
  · intro h
    rw [h]
    ext z
    rw [deriv_const_mul]
    · have h_inner :
        DifferentiableAt ℂ (fun z => (f 0) ^ (k - 1) * z₀ * z) z := by
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

theorem VaryingBase.SummableSum (db dv : ℕ → ℕ) (h0 : ∀(d : ℕ), (db d > 1 ∧ db d > dv d)) :
  Summable (λ (d : ℕ) ↦ (dv d : ℝ) / ∏ k ∈ Finset.range (d + 1), db k) := by
  -- Each term is bounded by 1 / 2^d since db k ≥ 2 for all k
  have h_bound : ∀ d, (dv d : ℝ) / ∏ k ∈ Finset.range (d + 1), db k ≤ 1 / 2^d := by
    intro d
    have h_num_bound : (dv d : ℝ) ≤ db d - 1 := by
      have := (h0 d).2
      have h1 : dv d ≤ db d - 1 := Nat.le_sub_one_of_lt this
      calc (dv d : ℝ) ≤ (db d - 1 : ℕ) := Nat.cast_le.mpr h1
        _ = (db d : ℝ) - 1 := by simp [Nat.cast_sub (Nat.one_le_of_lt (h0 d).1)]
    have h_denom_bound : (2 : ℝ)^(d+1) ≤ ∏ k ∈ Finset.range (d + 1), (db k : ℝ) := by
      have h1 : (2 : ℝ)^(d+1) = ∏ _k ∈ Finset.range (d + 1), (2 : ℝ) := by
        simp [Finset.prod_const, Finset.card_range]
      rw [h1]
      apply Finset.prod_le_prod
      · intros k _
        norm_num
      · intros k _
        have := (h0 k).1
        have h2 : 2 ≤ db k := this
        exact Nat.ofNat_le_cast.mpr h2
    -- The bound: dv d / ∏_{k≤d} db(k) < 1 / ∏_{k<d} db(k) ≤ 1/2^d
    have hprod_pos : (∏ k ∈ Finset.range (d + 1), (db k : ℝ)) > 0 := by
      apply Finset.prod_pos
      intros k _
      exact Nat.cast_pos.mpr (Nat.lt_trans Nat.zero_lt_one (h0 k).1)
    have hprod_d_pos : (∏ k ∈ Finset.range d, (db k : ℝ)) > 0 := by
      apply Finset.prod_pos
      intros k _
      exact Nat.cast_pos.mpr (Nat.lt_trans Nat.zero_lt_one (h0 k).1)
    have h_prod_d_bound : (2 : ℝ)^d ≤ ∏ k ∈ Finset.range d, (db k : ℝ) := by
      have h1 : (2 : ℝ)^d = ∏ _k ∈ Finset.range d, (2 : ℝ) := by
        simp [Finset.prod_const, Finset.card_range]
      rw [h1]
      apply Finset.prod_le_prod
      · intros k _; norm_num
      · intros k _
        exact Nat.ofNat_le_cast.mpr (h0 k).1
    -- Convert ℕ product cast to ℝ product
    simp only [Nat.cast_prod]
    -- Now use: dv d / ∏_{k≤d} ≤ (db d - 1) / ∏_{k≤d} < db d / ∏_{k≤d} = 1/∏_{k<d}
    have hdb_pos : (db d : ℝ) > 0 := by
      exact Nat.cast_pos.mpr (Nat.lt_trans Nat.zero_lt_one (h0 d).1)
    have hdb_ne : (db d : ℝ) ≠ 0 := ne_of_gt hdb_pos
    apply le_of_lt
    calc (dv d : ℝ) / ∏ k ∈ Finset.range (d + 1), (db k : ℝ)
        ≤ (db d - 1) / ∏ k ∈ Finset.range (d + 1), (db k : ℝ) := by
          apply div_le_div_of_nonneg_right h_num_bound (le_of_lt hprod_pos)
      _ < (db d : ℝ) / ∏ k ∈ Finset.range (d + 1), (db k : ℝ) := by
          apply div_lt_div_of_pos_right _ hprod_pos
          have := (h0 d).1
          linarith
      _ = 1 / ∏ k ∈ Finset.range d, (db k : ℝ) := by
          rw [Finset.prod_range_succ]
          field_simp [hdb_ne, ne_of_gt hprod_d_pos]
      _ ≤ 1 / (2 : ℝ)^d := by
          apply div_le_div_of_nonneg_left _ (by positivity) h_prod_d_bound
          norm_num
  apply Summable.of_nonneg_of_le
  · intro d
    apply div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact h_bound
  · -- 1/2^d is a convergent geometric series
    have : Summable (λ d ↦ (1 : ℝ) / 2^d) := by
      convert summable_geometric_of_lt_one (r := (1/2 : ℝ)) _ _
      · simp [one_div, inv_pow]
      · norm_num
      · norm_num
    exact this

theorem VaryingBase.One (db : ℕ → ℕ) (h0 : ∀(d : ℕ), db d > 1) : 1 =
  tsum (λ (d : ℕ) ↦ ((db d) - 1 : ℝ) / ∏ k ∈ Finset.range (d + 1), db k) := by
  symm
  apply HasSum.tsum_eq
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · let S := λ n ↦ 1 - 1 / ∏ k ∈ Finset.range n, (db k : ℝ)
    apply Filter.Tendsto.congr (f₁ := S)
    · intro n
      induction n with
      | zero => simp only [one_div, Finset.range_zero, Finset.prod_empty, inv_one, sub_self,
        Nat.cast_prod, Finset.sum_empty, S]
      | succ n ih =>
        rw [Finset.sum_range_succ, ← ih]
        simp only [S]
        have hprod_pos : (∏ k ∈ Finset.range (n + 1), (db k : ℝ)) ≠ 0 := by
          apply ne_of_gt; apply Finset.prod_pos; intros k _
          exact Nat.cast_pos.mpr (Nat.lt_trans Nat.zero_lt_one (h0 k))
        have hprod_prev_pos : (∏ k ∈ Finset.range n, (db k : ℝ)) ≠ 0 := by
          apply ne_of_gt; apply Finset.prod_pos; intros k _
          exact Nat.cast_pos.mpr (Nat.lt_trans Nat.zero_lt_one (h0 k))
        have hdb_pos : (db n : ℝ) ≠ 0 := by
          apply ne_of_gt; exact Nat.cast_pos.mpr (Nat.lt_trans Nat.zero_lt_one (h0 n))
        rw [Finset.prod_range_succ, Finset.prod_range_succ]
        field_simp [hprod_pos, hprod_prev_pos, hdb_pos]
        simp only [Nat.cast_mul, Nat.cast_prod]
        ring
    · -- Limit S n -> 1
      rw [← sub_zero 1]
      apply Filter.Tendsto.sub tendsto_const_nhds
      have h_le : ∀ n, (2 : ℝ)^n ≤ ∏ k ∈ Finset.range n, (db k : ℝ) := by
        intro n
        calc (2 : ℝ)^n = ∏ _ ∈ Finset.range n, 2 := by simp
            _ ≤ ∏ k ∈ Finset.range n, (db k : ℝ) := by
              apply Finset.prod_le_prod
              · intros; norm_num
              · intros k _; exact Nat.ofNat_le_cast.mpr (h0 k)
      -- Upper bound limit (1/2)^n -> 0
      have h_geom : Filter.Tendsto (fun n => (1/2 : ℝ)^n) Filter.atTop (nhds 0) := by
        apply tendsto_pow_atTop_nhds_zero_of_lt_one
        · norm_num
        · norm_num
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds (x := 0)) h_geom
      · intro n
        simp only [one_div, inv_nonneg]
        apply Finset.prod_nonneg; intros; exact Nat.cast_nonneg _
      · intro n
        simp only [one_div, inv_pow]
        rw [inv_eq_one_div, inv_eq_one_div, one_div_le_one_div]
        · exact h_le n
        · apply Finset.prod_pos; intros
          exact Nat.cast_pos.mpr (Nat.lt_trans Nat.zero_lt_one (h0 _))
        · apply pow_pos; norm_num
  · intro i
    apply div_nonneg
    · simp only [sub_nonneg]
      norm_cast
      exact le_of_lt (h0 i)
    · rw [Nat.cast_prod]
      apply Finset.prod_nonneg; intros; exact Nat.cast_nonneg _

theorem VaryingBase.SameInterval (db : ℕ → ℕ) (h0 : ∀(d : ℕ), db d > 1) :
  {r : ℝ | ∃(dv : ℕ → ℕ), ((∀(d : ℕ), db d > dv d) ∧
  r = tsum (λ (d : ℕ) ↦ (dv d : ℝ) / ∏ k ∈ Finset.range (d + 1), db k))}
  = {r : ℝ | r ≥ 0 ∧ r ≤ 1} := by
  sorry
