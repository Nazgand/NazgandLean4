import Mathlib

theorem iteratedDerivOf0 (k : ℕ) : iteratedDeriv k (0 : ℂ → ℂ) = 0 := by
  induction k with
  | zero => simp only [iteratedDeriv_zero]
  | succ k ih => rw [iteratedDeriv_succ, ih]; simp only [deriv_zero]

theorem ShiftedIteratedDerivative (k : ℕ) (z₁ : ℂ) {f : ℂ → ℂ} (h₀ : Differentiable ℂ f) :
    iteratedDeriv k (fun z₀ => f (z₀ + z₁)) = (fun z₀ => iteratedDeriv k f (z₀ + z₁)) := by
  induction' k with K Kih
  · simp only [iteratedDeriv_zero]
  · rw [iteratedDeriv_succ, Kih]
    ext z
    let h₂ := iteratedDeriv K f
    let h := fun z₀ => (z₀ + z₁)
    have hh₂ : DifferentiableAt ℂ h₂ (h z) := by
      refine Differentiable.differentiableAt ?h
      exact (ContDiff.differentiable_iteratedDeriv K h₀.contDiff (WithTop.coe_lt_top (K : ℕ∞)))
    have hh : DifferentiableAt ℂ h z := by
      exact differentiableAt_id.add (differentiableAt_const z₁)
    have hcomp := deriv_comp z hh₂ hh
    have hrwh₂ : h₂ = iteratedDeriv K f := rfl
    have hrwh : h = fun z₀ => z₀ + z₁ := rfl
    rw [hrwh₂, hrwh] at hcomp
    simp only [← iteratedDeriv_succ, differentiableAt_fun_id,
      differentiableAt_const, deriv_fun_add,
      deriv_id'', deriv_const', add_zero, mul_one] at hcomp
    rw [← hcomp]
    rfl

theorem SumOfDifferentiableIsDifferentiable {k : ℕ} (g : Fin k → ℂ → ℂ)
    (hD : ∀ (m : Fin k), Differentiable ℂ (g m)) (c : Fin k → ℂ) :
    Differentiable ℂ (λ (z : ℂ) ↦ ∑ (m : Fin k), c m * g m z) := by
  convert Differentiable.sum (u := Finset.univ) (fun i _ => Differentiable.const_mul (hD i) (c i))
  simp only [Finset.sum_apply]

theorem IteratedDerivSum {𝕜 : Type u} [NontriviallyNormedField 𝕜] {F : Type v}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {ι : Type u_1}
    {u : Finset ι} {A : ι → 𝕜 → F} (k : ℕ) (h : ∀ i ∈ u, ContDiff 𝕜 k (A i)) :
    iteratedDeriv k (fun y => Finset.sum u fun i => A i y) =
    (fun y => Finset.sum u fun i => iteratedDeriv k (A i) y) := by
  induction k with
  | zero => simp only [iteratedDeriv_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have h_diff_k : ∀ i ∈ u, ContDiff 𝕜 k (A i) := fun i hi => (h i hi).of_succ
    rw [ih h_diff_k]
    ext x
    simp only [← Finset.sum_apply]
    rw [deriv_sum]
    · simp only [iteratedDeriv_succ, Finset.sum_apply]
    · intro i hi
      refine ((h i hi).differentiable_iteratedDeriv k ?_).differentiableAt
      norm_cast
      exact Nat.lt_succ_self k

theorem ComplexDifferentiableImpIteratedDerivDifferentiable {f : ℂ → ℂ} (k : ℕ) (hD : Differentiable ℂ f) :
  Differentiable ℂ (iteratedDeriv k f) := by
  exact ContDiff.differentiable_iteratedDeriv k hD.contDiff (WithTop.natCast_lt_top k)

theorem ComplexIteratedDerivSum {ι : Type u_1} {u : Finset ι} {A : ι → ℂ → ℂ}
    (h : ∀ i ∈ u, Differentiable ℂ (A i)) (k : ℕ) :
    iteratedDeriv k (fun y => Finset.sum u fun i => A i y) =
    (fun y => Finset.sum u fun i => iteratedDeriv k (A i) y) :=
  IteratedDerivSum k (λ i hi => (h i hi).contDiff)

theorem ComplexIteratedDerivSumConstMul {m : ℕ} (g : Fin m → ℂ → ℂ)
    (h : ∀ (k : Fin m), Differentiable ℂ (g k)) (C : Fin m → ℂ) (i : ℕ) (z : ℂ) :
    iteratedDeriv i (fun z₀ => ∑ (k : Fin m), C k * g k z₀) z =
    ∑ (k : Fin m), C k * iteratedDeriv i (g k) z := by
  let A := fun (k : Fin m) (z : ℂ) => C k * g k z
  have hA : ∀ k ∈ Finset.univ, Differentiable ℂ (A k) := by
    intro k _
    exact Differentiable.const_mul (h k) (C k)
  rw [ComplexIteratedDerivSum hA i]
  dsimp only
  congr with k
  rw [iteratedDeriv_const_mul (C k)]
  exact (h k).contDiff.contDiffAt

theorem iteratedDeriv_iteratedDeriv {f : ℂ → ℂ} (n k : ℕ) :
    iteratedDeriv n (iteratedDeriv k f) = iteratedDeriv (n + k) f := by
  simp_rw [iteratedDeriv_eq_iterate, Function.iterate_add_apply]

theorem SummablePowerSeriesNear0 (z : ℂ) (hz : ‖z‖ < 1) (p : ℝ) :
    Summable λ (k : ℕ) ↦ ((k : ℝ) ^ p : ℝ) * z ^ k := by
  rcases eq_or_ne z 0 with rfl | hz0
  by_cases hp : p = 0
  · simp only [hp, Real.rpow_zero, Complex.ofReal_one, one_mul, summable_geometric_iff_norm_lt_one,
    norm_zero, zero_lt_one]
  · convert summable_zero with k
    · simp only [mul_eq_zero, Complex.ofReal_eq_zero, pow_eq_zero_iff', ne_eq, true_and]
      by_cases hk : k = 0
      · simp only [hk, CharP.cast_eq_zero, Real.zero_rpow hp, not_true_eq_false, or_false]
      · simp only [hk, not_false_eq_true, or_true]
  apply summable_of_ratio_test_tendsto_lt_one hz
  · filter_upwards [Filter.eventually_gt_atTop 0] with k hk
    simp only [ne_eq, mul_eq_zero, Complex.ofReal_eq_zero, pow_eq_zero_iff', hz0,
      false_and, or_false]
    exact (Real.rpow_pos_of_pos (show 0 < ↑k by bound) p).ne.symm
  · have h_lim : Filter.Tendsto (fun k : ℕ ↦ ((k + 1 : ℝ) / k) ^ p * ‖z‖) Filter.atTop (nhds ‖z‖) := by
      have h_lim_base : Filter.Tendsto (fun k : ℕ ↦ (k + 1 : ℝ) / k) Filter.atTop (nhds 1) := by
        have h_congr : ∀ᶠ (k : ℕ) in Filter.atTop, 1 + (k : ℝ)⁻¹ = (k + 1) / k := by
          filter_upwards [Filter.eventually_gt_atTop 0] with k hk
          field_simp
        refine Filter.Tendsto.congr' h_congr ?_
        have h0 : Filter.Tendsto (fun k : ℕ ↦ (k : ℝ)⁻¹) Filter.atTop (nhds 0) :=
          tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
        nth_rw 2 [← add_zero 1]
        apply Filter.Tendsto.const_add 1 h0
      have h_pow : Filter.Tendsto (fun x : ℝ ↦ x ^ p) (nhds 1) (nhds (1 ^ p)) := by
        apply ContinuousAt.tendsto
        apply ContinuousAt.rpow_const
        · exact continuous_id.continuousAt
        · left; norm_num
      rw [Real.one_rpow] at h_pow
      convert (h_pow.comp h_lim_base).mul_const ‖z‖
      rw [one_mul]
    refine Filter.Tendsto.congr' ?_ h_lim
    filter_upwards [Filter.eventually_gt_atTop 0] with k hk
    have hkR : 0 < (k : ℝ) := by bound
    have hkSucc : 0 < ((k : ℝ) + 1) := by bound
    simp only [hkSucc.le, Nat.cast_nonneg, Real.div_rpow, Nat.cast_add, Nat.cast_one,
      Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_rpow_of_nonneg,
      abs_of_pos hkSucc, norm_pow, pow_succ' ‖z‖, Nat.abs_cast]
    field_simp

theorem SummablePowerSeriesDerivSummable {c : ℕ → ℂ}
    (hS : ∀ (z : ℂ), Summable λ (n : ℕ) ↦ c n * z ^ n / n.factorial) :
    ∀ (z : ℂ), Summable λ (n : ℕ) ↦ c (n + 1) * z ^ n / n.factorial := by
  intro z
  let R : ℝ := ‖z‖ + 1
  have hR_pos : 0 < R := by dsimp only [R]; have := norm_nonneg z; linarith
  have hR_ge_one : 1 ≤ R := by dsimp only [R]; have := norm_nonneg z; linarith
  have h_sum_R := hS (R : ℂ)
  have h_tendsto := Summable.tendsto_atTop_zero h_sum_R
  have h_bound : ∃ C, ∀ n, ‖c n * (R : ℂ) ^ n / n.factorial‖ ≤ C := by
    obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ h_tendsto).exists_norm_le
    use C
    intro n
    exact hC _ (Set.mem_range_self n)
  obtain ⟨C, hC⟩ := h_bound
  let q := ‖z‖ / R
  have hq_nonneg : 0 ≤ q := div_nonneg (norm_nonneg z) (le_of_lt hR_pos)
  have hq_lt_one : q < 1 := by
    dsimp only [q, R]
    rw [div_lt_one (by have := norm_nonneg z; linarith)]
    linarith
  have h_nq_summable : Summable (fun n : ℕ ↦ (n + 1 : ℝ) * q ^ n) := by
    have h1 : Summable (fun n : ℕ ↦ (n : ℝ) * q ^ n) := by
      have h_norm : ‖(q : ℂ)‖ < 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq_nonneg]
        exact hq_lt_one
      have h_complex := SummablePowerSeriesNear0 q h_norm 1
      have h_real_norm := h_complex.norm
      simp only [Real.rpow_one, Complex.ofReal_natCast, norm_mul, RCLike.norm_natCast, norm_pow,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq_nonneg] at h_real_norm
      exact h_real_norm
    have h2 : Summable (fun n : ℕ ↦ q ^ n) := summable_geometric_of_lt_one hq_nonneg hq_lt_one
    convert h1.add h2 using 1
    ext n
    ring
  have h_geom : Summable (fun (n : ℕ) ↦ C * ((n + 1 : ℝ) * q ^ n)) := Summable.mul_left C h_nq_summable
  apply Summable.of_norm_bounded h_geom
  intro n
  have hCn := hC (n + 1)
  simp only [norm_div, norm_mul, norm_pow, Complex.norm_natCast] at hCn ⊢
  simp only [Complex.norm_real, Real.norm_of_nonneg (le_of_lt hR_pos)] at hCn
  have hR_ne_zero : R ≠ 0 := ne_of_gt hR_pos
  have hR_pow_pos : 0 < R ^ (n + 1) := pow_pos hR_pos _
  have h_c_bound : ‖c (n + 1)‖ ≤ C * (n + 1).factorial / R ^ (n + 1) := by
    have h1 : ‖c (n + 1)‖ * R ^ (n + 1) ≤ C * (n + 1).factorial := by
      have h2 : ‖c (n + 1)‖ * R ^ (n + 1) / (n + 1).factorial ≤ C := hCn
      have h3 : (n + 1).factorial ≠ (0 : ℝ) := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      calc ‖c (n + 1)‖ * R ^ (n + 1) = ‖c (n + 1)‖ * R ^ (n + 1) / (n + 1).factorial * (n + 1).factorial := by
            field_simp
        _ ≤ C * (n + 1).factorial := by gcongr
    calc ‖c (n + 1)‖ = ‖c (n + 1)‖ * R ^ (n + 1) / R ^ (n + 1) := by field_simp
      _ ≤ C * (n + 1).factorial / R ^ (n + 1) := by gcongr
  calc ‖c (n + 1)‖ * ‖z‖ ^ n / ↑n.factorial
      ≤ C * (n + 1).factorial / R ^ (n + 1) * ‖z‖ ^ n / n.factorial := by gcongr
    _ = C * (n + 1) * (‖z‖ ^ n / R ^ (n + 1)) := by
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one n]
        field_simp [Nat.factorial_ne_zero]
    _ = C * (n + 1) * (q ^ n / R) := by
        congr 1
        dsimp only [q]
        rw [div_pow, pow_succ R n]
        field_simp
    _ ≤ C * (n + 1) * q ^ n := by
        gcongr
        · have hN0 : 0 ≤ (n : ℝ) + 1 := by
            bound
          suffices hCPos : 0 ≤ C by
            bound
          suffices hLeCPos : 0 ≤ ‖c (n + 1)‖ * R ^ (n + 1) / ↑(n + 1).factorial by
            bound
          bound
        · bound
  ring_nf
  gcongr

theorem SummablePowerSeriesIteratedDerivSummable {c : ℕ → ℂ} (k : ℕ)
    (hS : ∀ (z : ℂ), Summable λ (n : ℕ) ↦ c n * z ^ n / n.factorial) :
    ∀ (z : ℂ), Summable λ (n : ℕ) ↦ c (n + k) * z ^ n / n.factorial := by
  induction k with
  | zero =>
    simp only [add_zero, hS, implies_true]
  | succ k h0 =>
    convert SummablePowerSeriesDerivSummable h0 using 6
    ring

theorem SummablePowerSeriesDeriv {c : ℕ → ℂ}
    (hS : ∀ (z : ℂ), Summable λ (n : ℕ) ↦ c n * z ^ n / n.factorial) :
    deriv (λ (z : ℂ) ↦ ∑' (n : ℕ), c n * z ^ n / n.factorial) =
    λ (z : ℂ) ↦ ∑' (n : ℕ), c (n + 1) * z ^ n / n.factorial := by
  refine deriv_eq (fun z => ?_)
  let f : ℕ → ℂ → ℂ := fun k w ↦ c k * w ^ k / k.factorial
  let f' : ℕ → ℂ → ℂ := fun k w ↦ if k = 0 then 0 else c k * w ^ (k - 1) / (k - 1).factorial
  let R := ‖z‖ + 1
  let u : ℕ → ℝ := fun k ↦ if k = 0 then 0 else ‖c k‖ * R ^ (k - 1) / (k - 1).factorial
  have normZNonNeg := norm_nonneg z
  have h_sum_u : Summable u := by
    rw [(summable_nat_add_iff 1).symm]
    have h_eq : (fun k ↦ u (k + 1)) = (fun k ↦ ‖c (k + 1)‖ * R ^ k / k.factorial) := by
      ext k
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_tsub_cancel_right, u]
    rw [h_eq]
    convert (SummablePowerSeriesDerivSummable hS R).norm with k
    simp only [Complex.norm_div, Complex.norm_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg (by dsimp only [R]; linarith : 0 ≤ R), RCLike.norm_natCast]
  have h_deriv : ∀ k, ∀ w ∈ Metric.ball z 1, HasDerivAt (f k) (f' k w) w := by
    intros k w hw
    dsimp only [f, f']
    rcases k with - | k
    · simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one, ↓reduceIte]
      exact hasDerivAt_const w (c 0)
    · simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]
      have hk : (k + 1 : ℂ) ≠ 0 := by norm_cast
      have h := (hasDerivAt_pow (k + 1) w).const_mul (c (k + 1) / (k + 1).factorial)
      convert h using 1
      · ext y; ring
      · rw [Nat.factorial_succ, Nat.cast_mul]
        field_simp [Nat.factorial_ne_zero, hk]
        congr
  have h_bound : ∀ k w, w ∈ Metric.ball z 1 → ‖f' k w‖ ≤ u k := by
    intros k w hw
    dsimp only [f', u]
    rcases k with - | k
    · simp only [↓reduceIte, norm_zero, le_refl]
    · simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one, norm_div, norm_mul, norm_pow,
        Complex.norm_natCast]
      gcongr
      rw [Metric.mem_ball, dist_eq_norm] at hw
      calc ‖w‖ = ‖w - z + z‖ := by rw [sub_add_cancel]
            _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
            _ ≤ 1 + ‖z‖ := by linarith [hw.le]
            _ = R := by dsimp only [R]; ring
  have h_f_z : Summable (f · z) := hS z
  have h_res := hasDerivAt_tsum_of_isPreconnected h_sum_u (Metric.isOpen_ball)
    (convex_ball z 1).isPreconnected
    h_deriv h_bound (Metric.mem_ball_self (by linarith)) h_f_z (Metric.mem_ball_self (by linarith))
  convert h_res using 1
  nth_rw 2 [tsum_eq_zero_add']
  · simp only [↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, and_false, add_tsub_cancel_right,
    zero_add, f']
  · exact SummablePowerSeriesDerivSummable hS z

theorem SummablePowerSeriesDifferentiable {f : ℂ → ℂ} {c : ℕ → ℂ}
    (hS : ∀ (z : ℂ), Summable λ (n : ℕ) ↦ c n * z ^ n / n.factorial)
    (hT : f = λ (z : ℂ) ↦ ∑' (n : ℕ), c n * z ^ n / n.factorial) :
    Differentiable ℂ f := by
  intro z
  rw [hT]
  let f_term : ℕ → ℂ → ℂ := fun k w ↦ c k * w ^ k / k.factorial
  let f'_term : ℕ → ℂ → ℂ := fun k w ↦ if k = 0 then 0 else c k * w ^ (k - 1) / (k - 1).factorial
  let R := ‖z‖ + 1
  let u : ℕ → ℝ := fun k ↦ if k = 0 then 0 else ‖c k‖ * R ^ (k - 1) / (k - 1).factorial
  have h_sum_u : Summable u := by
    rw [(summable_nat_add_iff 1).symm]
    have h_eq : (fun k ↦ u (k + 1)) = (fun k ↦ ‖c (k + 1)‖ * R ^ k / k.factorial) := by
      ext k
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_tsub_cancel_right, u]
    rw [h_eq]
    convert (SummablePowerSeriesDerivSummable hS R).norm with k
    have hR_nonneg : 0 ≤ R := by dsimp only [R]; have := norm_nonneg z; linarith
    simp only [Complex.norm_div, Complex.norm_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hR_nonneg, RCLike.norm_natCast]
  have h_deriv : ∀ k, ∀ w ∈ Metric.ball z 1, HasDerivAt (f_term k) (f'_term k w) w := by
    intros k w hw
    dsimp only [f_term, f'_term]
    rcases k with - | k
    · simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one, ↓reduceIte]
      exact hasDerivAt_const w (c 0)
    · simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]
      have hk : (k + 1 : ℂ) ≠ 0 := by norm_cast
      have h := (hasDerivAt_pow (k + 1) w).const_mul (c (k + 1) / (k + 1).factorial)
      convert h using 1
      · ext y; ring
      · rw [Nat.factorial_succ, Nat.cast_mul]
        field_simp [Nat.factorial_ne_zero, hk]
        congr
  have h_bound : ∀ k w, w ∈ Metric.ball z 1 → ‖f'_term k w‖ ≤ u k := by
    intros k w hw
    dsimp only [f'_term, u]
    rcases k with - | k
    · simp only [↓reduceIte, norm_zero, le_refl]
    · simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one, norm_div, norm_mul, norm_pow,
        Complex.norm_natCast]
      gcongr
      rw [Metric.mem_ball, dist_eq_norm] at hw
      calc ‖w‖ = ‖w - z + z‖ := by rw [sub_add_cancel]
            _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
            _ ≤ 1 + ‖z‖ := by linarith [hw.le]
            _ = R := by dsimp only [R]; ring
  have h_f_z : Summable (f_term · z) := hS z
  have h_res := hasDerivAt_tsum_of_isPreconnected h_sum_u (Metric.isOpen_ball)
    (convex_ball z 1).isPreconnected
    h_deriv h_bound (Metric.mem_ball_self (by linarith)) h_f_z (Metric.mem_ball_self (by linarith))
  exact h_res.differentiableAt

theorem SummablePowerSeriesIteratedDeriv {c : ℕ → ℂ} (k : ℕ)
    (hS : ∀ (z : ℂ), Summable λ (n : ℕ) ↦ c n * z ^ n / n.factorial) :
    iteratedDeriv k (λ (z : ℂ) ↦ ∑' (n : ℕ), c n * z ^ n / n.factorial) =
    λ (z : ℂ) ↦ ∑' (n : ℕ), c (n + k) * z ^ n / n.factorial := by
  induction k with
  | zero =>
    simp only [iteratedDeriv_zero, add_zero]
  | succ k h0 =>
    have h1 := SummablePowerSeriesDeriv (SummablePowerSeriesIteratedDerivSummable k hS)
    have h2 := congrArg deriv h0
    simp only [← iteratedDeriv_succ] at h2
    rw [h2, h1]
    ext z
    congr
    ext m
    congr 3
    ring

theorem SummablePowerSeriesIteratedDerivAt0 {f : ℂ → ℂ} {c : ℕ → ℂ} (k : ℕ)
    (hS : ∀ (z : ℂ), Summable λ (n : ℕ) ↦ c n * z ^ n / n.factorial)
    (hT : f = λ (z : ℂ) ↦ ∑' (n : ℕ), c n * z ^ n / n.factorial) :
    iteratedDeriv k f 0 = c k := by
  have h_it := SummablePowerSeriesIteratedDeriv k hS
  rw [← hT] at h_it
  rw [h_it]
  simp only []
  rw [tsum_eq_single 0]
  · simp only [zero_add, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one]
  · intro n hn
    simp only [zero_pow hn, mul_zero, zero_div]
