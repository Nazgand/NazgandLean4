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
      simp only [Finset.mem_range, Nat.zero_lt_succ, true_and, h 0]
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
  have h_bound : ∀ d, (dv d : ℝ) / ∏ k ∈ Finset.range (d + 1), db k ≤ 1 / 2^d := by
    intro d
    have h_num_bound : (dv d : ℝ) ≤ db d - 1 := by
      have := (h0 d).2
      have h1 : dv d ≤ db d - 1 := Nat.le_sub_one_of_lt this
      calc (dv d : ℝ) ≤ (db d - 1 : ℕ) := Nat.cast_le.mpr h1
        _ = (db d : ℝ) - 1 := by simp only [Nat.cast_sub (Nat.one_le_of_lt (h0 d).1),
          Nat.cast_one]
    have h_denom_bound : (2 : ℝ)^(d+1) ≤ ∏ k ∈ Finset.range (d + 1), (db k : ℝ) := by
      have h1 : (2 : ℝ)^(d+1) = ∏ _k ∈ Finset.range (d + 1), (2 : ℝ) := by
        simp only [Finset.prod_const, Finset.card_range]
      rw [h1]
      apply Finset.prod_le_prod
      · intros k _; norm_num
      · intros k _; exact Nat.ofNat_le_cast.mpr (h0 k).1
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
        simp only [Finset.prod_const, Finset.card_range]
      rw [h1]
      apply Finset.prod_le_prod
      · intros k _; norm_num
      · intros k _; exact Nat.ofNat_le_cast.mpr (h0 k).1
    simp only [Nat.cast_prod]
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
          field_simp [ne_of_gt (Nat.cast_pos.mpr (Nat.lt_trans Nat.zero_lt_one (h0 d).1)),
            ne_of_gt hprod_d_pos]
      _ ≤ 1 / (2 : ℝ)^d := by
          apply div_le_div_of_nonneg_left _ (by positivity) h_prod_d_bound
          norm_num
  apply Summable.of_nonneg_of_le
  · intro d
    apply div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact h_bound
  · convert summable_geometric_of_lt_one (r := (1/2 : ℝ)) _ _
    · simp only [one_div, inv_pow]
    · norm_num
    · norm_num

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
        simp only [Finset.prod_range_succ, one_div, mul_inv_rev, Nat.cast_mul, Nat.cast_prod]
        field_simp [hprod_pos, hprod_prev_pos, hdb_pos]
        ring
    · rw [← sub_zero 1]
      apply Filter.Tendsto.sub tendsto_const_nhds
      have h_le : ∀ n, (2 : ℝ)^n ≤ ∏ k ∈ Finset.range n, (db k : ℝ) := by
        intro n
        calc (2 : ℝ)^n = ∏ _ ∈ Finset.range n, 2 := by simp only [Finset.prod_const,
          Finset.card_range]
          _ ≤ ∏ k ∈ Finset.range n, (db k : ℝ) := by
            apply Finset.prod_le_prod
            · intros; norm_num
            · intros k _; exact Nat.ofNat_le_cast.mpr (h0 k)
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
  ext r
  constructor
  · rintro ⟨dv, h_dv, rfl⟩
    have h_summable := VaryingBase.SummableSum db dv (λ d ↦ ⟨h0 d, h_dv d⟩)
    constructor
    · apply tsum_nonneg
      intro d
      apply div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · rw [VaryingBase.One db h0]
      apply Summable.tsum_le_tsum
      · intro b
        apply div_le_div_of_nonneg_right
        · rw [le_sub_iff_add_le]
          norm_cast
          exact h_dv b
        · rw [Nat.cast_prod]
          apply Finset.prod_nonneg; intros; exact Nat.cast_nonneg _
      · exact h_summable
      · convert VaryingBase.SummableSum db (fun d ↦ db d - 1)
          (fun d ↦ ⟨h0 d, Nat.sub_one_lt (ne_of_gt (Nat.lt_trans Nat.zero_lt_one (h0 d)))⟩) with i
        rw [Nat.cast_sub (Nat.le_of_lt (h0 i))]
        simp only [Nat.cast_one]
  · rintro ⟨h_ge_0, h_le_1⟩
    rcases lt_or_eq_of_le h_le_1 with hr_lt | rfl
    · let rem : ℕ → ℝ := Nat.rec r (λ n x ↦ Int.fract (x * db n))
      let dv : ℕ → ℕ := λ n ↦ ⌊rem n * db n⌋₊
      have h_rem_ge_0 : ∀ n, 0 ≤ rem n := by
        intro n; induction n with
        | zero => simp only [rem]; exact h_ge_0
        | succ n ih => simp only [rem]; exact Int.fract_nonneg _
      have h_rem_lt_1 : ∀ n, rem n < 1 := by
        intro n; induction n with
        | zero => simp only [rem]; exact hr_lt
        | succ n ih => simp only [rem]; exact Int.fract_lt_one _
      use dv
      constructor
      · intro d
        simp only [dv]
        rw [mul_comm, gt_iff_lt, Nat.floor_lt]
        · rw [mul_comm]
          apply mul_lt_of_lt_one_left (Nat.cast_pos.mpr (Nat.lt_trans Nat.zero_lt_one (h0 d)))
          exact h_rem_lt_1 d
        · apply mul_nonneg (Nat.cast_nonneg _) (h_rem_ge_0 d)
      · symm
        apply HasSum.tsum_eq
        rw [hasSum_iff_tendsto_nat_of_nonneg]
        · let P (n : ℕ) : ℝ := ∏ k ∈ Finset.range n, (db k : ℝ)
          let S (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, ((dv i : ℝ) / P (i + 1))
          have h_error : ∀ n, r - S n = rem n / P n := by
             intro n
             induction n with
             | zero =>
               dsimp only [Finset.range_zero, Finset.sum_empty, Nat.rec_zero, Finset.prod_empty, S,
                 P, rem]
               simp only [sub_zero, div_one]
             | succ n ih =>
               simp only [S] at *
               rw [Finset.sum_range_succ, ← sub_sub, ih]
               simp only [P]
               rw [Finset.prod_range_succ]
               have h_db_pos : (db n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (Nat.lt_trans Nat.zero_lt_one (h0 n)))
               have h_Pn_pos : P n ≠ 0 := by
                 apply Finset.prod_ne_zero_iff.mpr
                 intro k _
                 exact Nat.cast_ne_zero.mpr (ne_of_gt (Nat.lt_trans Nat.zero_lt_one (h0 k)))
               have h_Pn_db_ne_zero : P n * (db n : ℝ) ≠ 0 := mul_ne_zero h_Pn_pos h_db_pos
               rw [div_sub_div _ _ h_Pn_pos h_Pn_db_ne_zero,
                 div_eq_div_iff (mul_ne_zero h_Pn_pos h_Pn_db_ne_zero) h_Pn_db_ne_zero]
               ring_nf
               have h_rem_succ : rem (n + 1) = rem n * db n - dv n := by
                 simp only [rem, dv]
                 rw [Int.fract]
                 congr
                 rw [Int.floor_eq_iff]
                 constructor
                 · norm_cast
                   exact Nat.floor_le (mul_nonneg (h_rem_ge_0 n) (Nat.cast_nonneg _))
                 · norm_cast
                   convert Nat.lt_floor_add_one (rem n * (db n : ℝ))
                   simp only [Nat.cast_add, Nat.cast_one, rem]
               rw [add_comm 1 n, h_rem_succ]
               ring
          have h_eq : ∀ n, S n = r - (rem n / P n) := by
            intro n
            rw [← h_error n]
            ring
          apply Filter.Tendsto.congr (f₁ := fun n ↦ r - (rem n / P n))
          · intro n
            rw [← h_eq n]
            dsimp only [S, P]
            congr with i
            rw [Nat.cast_prod]
          · rw [← sub_zero r]
            refine Filter.Tendsto.sub ?_ ?_
            · simp only [sub_zero]
              apply tendsto_const_nhds
            apply tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds (x := 0))
            · apply Filter.Tendsto.comp (tendsto_inv_atTop_zero)
              apply tendsto_pow_atTop_atTop_of_one_lt (r := 2)
              norm_num
            · intro n
              apply div_nonneg (h_rem_ge_0 n)
              apply Finset.prod_nonneg; intros; exact Nat.cast_nonneg _
            · intro n
              dsimp only [Function.comp_apply]
              have h_le_P : (2 : ℝ) ^ n ≤ P n := by
                induction n with
                | zero =>
                  dsimp only [Finset.range_zero, Finset.prod_empty, P]
                  simp only [pow_zero, le_refl]
                | succ n ih =>
                  dsimp only [P]
                  rw [Finset.prod_range_succ, pow_succ]
                  apply mul_le_mul ih (Nat.cast_le.mpr (Nat.succ_le_of_lt (h0 n))) (by norm_num)
                  apply (pow_pos (by norm_num) n).le.trans ih
              have h_Pn_pos : 0 < P n := by
                apply lt_of_lt_of_le (pow_pos (by norm_num) n) h_le_P
              rw [div_eq_mul_inv]
              apply le_trans (mul_le_of_le_one_left (inv_nonneg.mpr (le_of_lt h_Pn_pos)) (le_of_lt (h_rem_lt_1 n)))
              rw [inv_eq_one_div, inv_eq_one_div]
              exact one_div_le_one_div_of_le (pow_pos (by norm_num) n) h_le_P
        · intro b
          apply div_nonneg (Nat.cast_nonneg _)
          rw [Nat.cast_prod]
          apply Finset.prod_nonneg; intros; exact Nat.cast_nonneg _
    · use (fun d ↦ db d - 1)
      constructor
      · intro d
        exact Nat.sub_one_lt (ne_of_gt (Nat.lt_trans Nat.zero_lt_one (h0 d)))
      · rw [VaryingBase.One db h0]
        congr
        funext d
        simp only [Nat.cast_sub, Nat.one_le_of_lt (h0 _), Nat.cast_one]

theorem RearrangeTsum (f : ℕ → ℂ) (b : ℕ → ℕ) (h₀ : Function.Bijective b) :
  tsum (λ (k : ℕ) ↦ f (b k)) = tsum f := ((Equiv.ofBijective b h₀).tsum_eq f)
