import Mathlib
import NazgandLean4.Calculus
import NazgandLean4.HomogeneousLinearDifferentialEquationsOfConstantCoefficients.Basic
set_option maxHeartbeats 0
open Finset Matrix

noncomputable def StandardBasisCoeffs (DE : DiffEq) (k₁ : Fin DE.Degree) (n : ℕ) : ℂ :=
  Nat.strongRecOn n fun n ih =>
    if h : n < DE.Degree then
      if n = k₁ then 1 else 0
    else
      -( (∑ (j : Fin DE.Degree), DE.Coeff (Fin.castSucc j) * ih ((n - DE.Degree) + j) (by
        rw [Nat.add_comm]
        apply Nat.add_lt_of_lt_sub
        rw [Nat.sub_sub_self (Nat.le_of_not_lt h)]
        exact j.isLt)) / DE.Coeff (Fin.last DE.Degree) )

noncomputable def DiffEq.StandardBasis (DE : DiffEq) (k₁ : Fin ↑DE.Degree) (z : ℂ) : ℂ :=
  ∑' (n : ℕ), StandardBasisCoeffs DE k₁ n * z ^ n / n.factorial

theorem StandardBasisCoeffsValBound {DE : DiffEq} (k₁ : Fin ↑DE.Degree) :
    ∃ (C : ℝ), ∀ n, ‖StandardBasisCoeffs DE k₁ n‖ ≤ C ^ n := by
  let c_ratio (j : Fin DE.Degree) : ℝ :=
    ‖DE.Coeff (Fin.castSucc j) / DE.Coeff (Fin.last DE.Degree)‖
  let C := 1 + ∑ j, c_ratio j
  use C
  have hC_ge_1 : 1 ≤ C := by
    dsimp only [C]
    apply le_add_of_nonneg_right
    apply Finset.sum_nonneg
    intro j _
    apply norm_nonneg
  have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one hC_ge_1
  intro n
  induction' n using Nat.strong_induction_on with n ih
  rw [StandardBasisCoeffs, Nat.strongRecOn, WellFounded.fix_eq]
  dsimp only
  split_ifs
  · norm_num
    exact one_le_pow₀ hC_ge_1
  · norm_num
    apply pow_nonneg (le_of_lt hC_pos)
  · let lead := DE.Coeff (Fin.last DE.Degree)
    have h_lead_ne_zero : lead ≠ 0 := by
      convert DE.LeadCoeffNonZero using 1
      simp only [lead]
      congr
      apply Fin.ext
      simp only [Fin.val_last, Fin.val_ofNat]
      rw [Nat.mod_eq_of_lt]
      exact Nat.lt_succ_self _
    simp only [norm_neg, norm_div]
    rw [div_le_iff₀ (norm_pos_iff.mpr h_lead_ne_zero)]
    apply le_trans (norm_sum_le _ _)
    trans ∑ (j : Fin ↑DE.Degree), ‖DE.Coeff (Fin.castSucc j)‖ * C ^ ((n - ↑DE.Degree) + ↑j)
    · apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      gcongr
      apply ih
      rw [Nat.add_comm]
      apply Nat.add_lt_of_lt_sub
      rw [Nat.sub_sub_self (Nat.le_of_not_lt ‹¬n < ↑DE.Degree›)]
      exact j.isLt
    · rw [← div_le_iff₀ (norm_pos_iff.mpr h_lead_ne_zero), Finset.sum_div]
      trans ∑ (j : Fin ↑DE.Degree), c_ratio j * C ^ ((n - ↑DE.Degree) + ↑j)
      · apply le_of_eq
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [c_ratio]
        rw [norm_div, div_mul_eq_mul_div]
      · have h_pow : ∀ (j : Fin ↑DE.Degree),
          C ^ ((n - (DE.Degree : ℕ)) + (j : ℕ)) = C ^ n / C ^ ((DE.Degree : ℕ) - (j : ℕ)) := by
          intro j
          have hj : (j : ℕ) < DE.Degree := j.isLt
          field_simp [hC_pos.ne.symm]
          rw [← pow_add]
          congr 1
          omega
        simp_rw [h_pow, div_eq_mul_inv]
        trans ∑ x : Fin ↑DE.Degree, c_ratio x * (C ^ ((DE.Degree : ℕ) - (x : ℕ)))⁻¹ * C ^ n
        · apply le_of_eq
          apply Finset.sum_congr rfl
          intro x _
          ring
        rw [← Finset.sum_mul]
        nth_rw 2 [← one_mul (C^n)]
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (le_of_lt hC_pos) n)
        trans ∑ j : Fin ↑DE.Degree, c_ratio j * C⁻¹
        · apply Finset.sum_le_sum
          intro j _
          apply mul_le_mul_of_nonneg_left
          · rw [inv_le_inv₀ (pow_pos hC_pos _) hC_pos]
            have hk : 1 ≤ (DE.Degree : ℕ) - (j : ℕ) := Nat.add_one_le_iff.mpr (Nat.sub_pos_of_lt j.isLt)
            rw [← Nat.sub_add_cancel hk, pow_add, pow_one, mul_comm]
            apply le_mul_of_one_le_right (le_of_lt hC_pos)
            apply one_le_pow₀ hC_ge_1
          · dsimp only [c_ratio]; apply norm_nonneg
        · rw [← Finset.sum_mul, ← div_eq_mul_inv, div_le_one hC_pos]
          dsimp only [C]
          linarith

theorem StandardBasisSummable (DE : DiffEq) (k₁ : Fin ↑DE.Degree) :
  ∀ (z : ℂ), Summable λ (n : ℕ) ↦ StandardBasisCoeffs DE k₁ n * z ^ n / n.factorial := by
  intro z
  obtain ⟨C, hC⟩ := StandardBasisCoeffsValBound k₁
  apply Summable.of_norm_bounded_eventually (Real.summable_pow_div_factorial (C * ‖z‖))
  filter_upwards
  intro n
  rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast, mul_pow]
  gcongr
  exact hC n

theorem StandardBasisInitialConditions (DE : DiffEq) (k₀ k₁ : Fin ↑DE.Degree) :
    iteratedDeriv k₀ (DE.StandardBasis k₁) 0 = if k₀ = k₁ then 1 else 0 := by
  unfold DiffEq.StandardBasis
  rw [SummablePowerSeriesIteratedDerivAt0 (↑k₀) (StandardBasisSummable DE k₁) rfl,
    StandardBasisCoeffs, Nat.strongRecOn, WellFounded.fix_eq]
  dsimp only
  rw [dif_pos k₀.isLt]
  grind only

theorem StandardBasisCoeffsRecurrence {DE : DiffEq} (k₁ : Fin ↑DE.Degree) (n : ℕ) :
    ∑ (j : Fin (DE.Degree + 1)), DE.Coeff j * StandardBasisCoeffs DE k₁ (n + j) = 0 := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  have h_ge : ¬ (n + DE.Degree) < DE.Degree := by omega
  conv_lhs =>
    arg 2
    rw [StandardBasisCoeffs, Nat.strongRecOn, WellFounded.fix_eq]
    simp only [h_ge, dif_neg, not_false_eq_true]
  have h_lead_eq : Fin.last DE.Degree = Fin.ofNat (DE.Degree + 1) DE.Degree := by
    simp only [Fin.ext_iff, Fin.val_last, Fin.val_ofNat]
    rw [Nat.mod_eq_of_lt]; exact Nat.lt_succ_self _
  have h_lead_ne : DE.Coeff (Fin.last DE.Degree) ≠ 0 := by
    rw [h_lead_eq]; exact DE.LeadCoeffNonZero
  have h_sub : n + ↑DE.Degree - ↑DE.Degree = n := Nat.add_sub_cancel n _
  simp only [mul_neg, mul_div_assoc']
  rw [h_sub]
  field_simp [h_lead_ne]
  rw [← sub_eq_add_neg, sub_eq_zero]
  apply Finset.sum_congr rfl
  intro j _
  congr 1

theorem StandardBasisIsSolution (DE : DiffEq) (k : Fin ↑DE.Degree) : DE.IsSolution (DE.StandardBasis k) := by
  have h_summable := StandardBasisSummable DE k
  constructor
  · apply SummablePowerSeriesDifferentiable h_summable rfl
  · ext z
    have h_deriv (i : Fin (DE.Degree + 1)) :
        iteratedDeriv i (DE.StandardBasis k) z = ∑' n, StandardBasisCoeffs DE k (n + i) * z ^ n / n.factorial := by
      unfold DiffEq.StandardBasis
      rw [SummablePowerSeriesIteratedDeriv i h_summable]
    unfold DiffEq.KeyDifferentialOperator
    simp_rw [h_deriv]
    let term (i : Fin (DE.Degree + 1)) (n : ℕ) := DE.Coeff i * (StandardBasisCoeffs DE k (n + i) * z ^ n / n.factorial)
    have h_summable_term (i : Fin (DE.Degree + 1)) : Summable (term i) := by
       apply Summable.mul_left
       exact SummablePowerSeriesIteratedDerivSummable i h_summable z
    simp_rw [← tsum_mul_left]
    rw [← Summable.tsum_finsetSum (fun i _ => h_summable_term i)]
    trans (∑' (n : ℕ), (0 : ℂ))
    · apply tsum_congr
      intro n
      have h0 := congrArg (λ (z₉ : ℂ) ↦ z₉ * z ^ n / ↑n.factorial) (StandardBasisCoeffsRecurrence k n)
      simp only [zero_mul, zero_div, Finset.sum_mul, Finset.sum_div] at h0
      simp only [term]
      rw [← h0]
      apply Finset.sum_congr rfl
      intro i _
      ring
    · exact tsum_zero

theorem StandardBasisIsBasis (DE : DiffEq) : DE.IsBasis (DE.StandardBasis) := by
  constructor
  · ext h; constructor
    · intro h_sol
      use fun k => iteratedDeriv k h 0
      let g := λ z => ∑ k : Fin DE.Degree, iteratedDeriv k h 0 * DE.StandardBasis k z
      have hg_sol : DE.IsSolution g := by
        convert LinearCombinationOfSolutions Finset.univ (DE.StandardBasis) (fun k => iteratedDeriv k h 0)
          (fun k _ => StandardBasisIsSolution DE k)
      have h_diff_sol : DE.IsSolution (h - g) := by
        rw [sub_eq_add_neg]
        apply DiffEq.IsSolution.Add h_sol
        have h_neg : -g = (-1 : ℂ) • g := by ext z; simp only [Pi.neg_apply, Pi.smul_apply,
          smul_eq_mul, neg_mul, one_mul]
        rw [h_neg]
        exact DiffEq.IsSolution.ConstMul (-1) hg_sol
      have h_zero_ic : ∀ k : Fin DE.Degree, iteratedDeriv k (h - g) 0 = 0 := by
        intro k
        rw [iteratedDeriv_sub ((DiffEqSolutionAnalytic h_sol).contDiff.contDiffAt.of_le le_top)
            ((DiffEqSolutionAnalytic hg_sol).contDiff.contDiffAt.of_le le_top)]
        simp only [g]
        rw [ComplexIteratedDerivSumConstMul (DE.StandardBasis) (fun i => (StandardBasisIsSolution DE i).1) (fun i => iteratedDeriv i h 0)]
        rw [Finset.sum_eq_single k]
        · rw [StandardBasisInitialConditions, if_pos rfl, mul_one, sub_self]
        · intro i _ h_ne
          rw [StandardBasisInitialConditions, if_neg h_ne.symm, mul_zero]
        · exact fun h => (h (Finset.mem_univ k)).elim
      have h_diff_zero := DiffEq_Zero_IC_Implies_Zero h_diff_sol h_zero_ic
      rw [sub_eq_zero] at h_diff_zero
      exact h_diff_zero
    · rintro ⟨b, rfl⟩
      convert LinearCombinationOfSolutions Finset.univ (DE.StandardBasis) b
          (fun k _ => StandardBasisIsSolution DE k)
  · intro b₀ b₁ h_eq
    ext k
    have h_deriv_k : iteratedDeriv k (λ z => ∑ i, b₀ i * DE.StandardBasis i z) 0 =
                      iteratedDeriv k (λ z => ∑ i, b₁ i * DE.StandardBasis i z) 0 := by rw [h_eq]
    have h_smooth : ∀ b : Fin DE.Degree → ℂ, ∀ i : Fin DE.Degree, Differentiable ℂ (fun z => b i * DE.StandardBasis i z) := by
      intro b i; apply Differentiable.const_mul; exact (StandardBasisIsSolution DE i).1
    simp_rw [ComplexIteratedDerivSum (fun i _ => h_smooth _ i),
      iteratedDeriv_const_mul ((StandardBasisIsSolution DE _).1.contDiff.contDiffAt.of_le le_top),
      StandardBasisInitialConditions] at h_deriv_k
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, ↓reduceIte] at h_deriv_k
    exact h_deriv_k

theorem SolutionStandardBasisForm (DE : DiffEq) (f : ℂ → ℂ) (hf : DE.IsSolution f) :
  f = ∑ (k : Fin DE.Degree), (iteratedDeriv k f 0) • DE.StandardBasis k := by
  change f ∈ DE.SetOfSolutions at hf
  have h_span := (StandardBasisIsBasis DE).1
  rw [h_span] at hf
  rcases hf with ⟨b, hb⟩
  have h_deriv (k : Fin DE.Degree) : iteratedDeriv k f 0 = b k := by
    rw [hb]
    rw [ComplexIteratedDerivSumConstMul (DE.StandardBasis) (fun i => (StandardBasisIsSolution DE i).1) b]
    simp_rw [StandardBasisInitialConditions]
    rw [Finset.sum_eq_single k]
    · simp only [↓reduceIte, mul_one]
    · intro j _ h_ne
      simp only [if_neg h_ne.symm, mul_zero]
    · intro h_mem
      exfalso
      exact h_mem (Finset.mem_univ k)
  simp_rw [h_deriv]
  rw [hb]
  ext
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

#print axioms SolutionStandardBasisForm
