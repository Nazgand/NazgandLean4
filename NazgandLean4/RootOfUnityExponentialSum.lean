/-
PDF document this is based on:
https://github.com/Nazgand/NazgandMathBook/blob/master/RootOfUnityExponentialSumFunction.pdf
-/
import Mathlib
set_option maxHeartbeats 0
open Complex Classical NormedSpace Finset Real

theorem ExpTsumForm (z : ℂ) : cexp z = tsum (λ (k : ℕ) => z ^ k / k.factorial) := by
  rw [exp_eq_exp_ℂ, exp_eq_tsum_div]

theorem ExpTaylorSeriesSummable (z : ℂ) : Summable (λ (k : ℕ) => z ^ k / k.factorial) := by
  exact expSeries_div_summable z

-- Rues is the Root of Unity Exponential Sum function
-- inspired by the relationship between exp and cosh
noncomputable
def Rues (n : ℕ+) (z : ℂ) : ℂ :=
  tsum (λ (k : ℕ) => z ^ (n * k) / (n * k).factorial)

theorem RuesSummable (n : ℕ+) (z : ℂ) : Summable (λ (k : ℕ) => z ^ (n * k) / (n * k).factorial) :=
  (expSeries_div_summable z).comp_injective (strictMono_mul_left_of_pos n.pos).injective

theorem RuesRealToReal (n : ℕ+) (x : ℝ) : (Rues n x).im = 0 := by
  rw [Rues]
  let h₀ := ContinuousLinearMap.map_tsum Complex.imCLM (RuesSummable n x)
  simp only [imCLM_apply] at h₀
  rw [h₀]
  suffices h₁ : ∑' (z : ℕ), (x ^ (n * z) : ℂ).im / ↑(Nat.factorial (n * z)) = ∑' (z : ℕ), 0
  · rw [tsum_zero] at h₁
    rw [← h₁]
    simp only [div_natCast_im]
  congr
  ext1 k
  norm_cast at *
  simp only [zero_div]

theorem RuesRotationallySymmetric (n : ℕ+) (z Rou : ℂ) (h : Rou ^ (n : ℕ) = 1) :
  Rues n z = Rues n (z * Rou) := by
  simp_rw [Rues]
  congr
  ext1 k
  have h₀ : (z * Rou) ^ (n * k) = z ^ (n * k) * Rou ^ (n * k) := by
    exact mul_pow z Rou (↑n * k)
  have h₁ : Rou ^ (n * k) = (Rou ^ (n : ℕ)) ^ k := by
    exact pow_mul Rou (↑n) k
  simp only [h₀, h₁, h, one_pow, mul_one]

theorem RouNot0 (n : ℕ+) (Rou : ℂ) (h : Rou ^ (n : ℕ) = 1) : Rou ≠ 0 := by
  by_contra h₁
  rw [h₁] at h
  simp only [ne_eq, PNat.ne_zero, not_false_eq_true, zero_pow, zero_ne_one] at h

-- (RuesDiff n m) is the mth derivative of (Rues n)
noncomputable
def RuesDiff (n : ℕ+) (m : ℤ) (z : ℂ) : ℂ :=
  tsum (λ (k : ℕ) => if ↑↑n ∣ (↑k + m) then z ^ k / k.factorial else 0)

theorem RuesDiffSummable (n : ℕ+) (m : ℤ) (z : ℂ) :
  Summable (λ (k : ℕ) => if ↑↑n ∣ (↑k + m) then z ^ k / k.factorial else 0) := by
  apply Summable.of_norm_bounded (Real.summable_pow_div_factorial ‖z‖)
  intro k
  split_ifs with h
  · rw [norm_div, norm_pow]
    simp only [Complex.norm_natCast, le_refl]
  · simp only [norm_zero, norm_nonneg, pow_nonneg, Nat.cast_nonneg, div_nonneg]

theorem RuesDiffHasDeriv (n : ℕ+) (m : ℤ) (z : ℂ) :
    HasDerivAt (RuesDiff n m) (RuesDiff n (m + 1) z) z := by
  let f : ℕ → ℂ → ℂ := fun k w ↦ if (n : ℤ) ∣ (k : ℤ) + m then w ^ k / k.factorial else 0
  let f' : ℕ → ℂ → ℂ := fun k w ↦ if (n : ℤ) ∣ (k : ℤ) + m then
    (if k = 0 then 0 else w ^ (k - 1) / (k - 1).factorial) else 0
  let R := ‖z‖ + 1
  let u : ℕ → ℝ := fun k ↦ if k = 0 then 0 else R ^ (k - 1) / (k - 1).factorial
  have h_sum_u : Summable u := by
    rw [(summable_nat_add_iff 1).symm]
    have h_eq : (fun k ↦ u (k + 1)) = (fun k ↦ R ^ k / k.factorial) := by
      ext k
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_tsub_cancel_right, u]
    rw [h_eq]
    exact expSeries_div_summable R
  have h_deriv : ∀ k, ∀ w ∈ Metric.ball z 1, HasDerivAt (f k) (f' k w) w := by
    intros k w hw
    dsimp only [f, f']
    split_ifs with h_div
    · rcases k with - | k
      · simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
        exact hasDerivAt_const w 1
      · contradiction
    · rename_i h_k0
      have h0 : (k : ℂ) ≠ 0 := by norm_cast
      convert (hasDerivAt_pow k w).div_const (Nat.factorial k : ℂ) using 1
      rw [← Nat.mul_factorial_pred h_k0, Nat.cast_mul]
      field_simp [Nat.factorial_ne_zero, h0]
    · exact hasDerivAt_const w (0 : ℂ)
  have h_bound : ∀ k w, w ∈ Metric.ball z 1 → ‖f' k w‖ ≤ u k := by
    intros k w hw
    dsimp only [f', u]
    split_ifs with h_div
    · rcases k with - | k <;> simp only [norm_zero, le_refl]
    · simp only [norm_div, norm_pow, _root_.norm_natCast]
      gcongr
      rw [Metric.mem_ball, dist_eq_norm] at hw
      calc ‖w‖ = ‖w - z + z‖ := by rw [sub_add_cancel]
            _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
            _ ≤ 1 + ‖z‖ := by linarith [hw.le]
            _ = R := by dsimp only [R]; ring
    · simp only [norm_zero, le_refl]
    · simp only [norm_zero]
      positivity
  have h_f_z : Summable (f · z) := RuesDiffSummable n m z
  have h_res := hasDerivAt_tsum_of_isPreconnected h_sum_u (Metric.isOpen_ball)
    (convex_ball z 1).isPreconnected
    h_deriv h_bound (Metric.mem_ball_self (by linarith)) h_f_z (Metric.mem_ball_self (by linarith))
  convert h_res using 1
  rw [tsum_eq_zero_add']
  · dsimp only [RuesDiff, CharP.cast_eq_zero, zero_add, Int.cast_ofNat_Int, ↓dreduceIte,
    Nat.cast_add, Nat.cast_one, Int.natCast_add, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    Nat.add_one_sub_one, f']
    simp only [zero_add, ite_self]
    refine tsum_congr (fun k ↦ ?_)
    congr 1
    ring_nf
  · simp only [Nat.cast_add, Nat.cast_one, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
    add_tsub_cancel_right, f']
    refine Summable.of_norm_bounded (Real.summable_pow_div_factorial ‖z‖) (fun k ↦ ?_)
    split_ifs with h
    · simp only [norm_div, norm_pow, Complex.norm_natCast]
      gcongr
    · simp only [norm_zero]
      positivity

theorem RuesDiffDeriv (n : ℕ+) (m : ℤ) :
  deriv (RuesDiff n m) = (RuesDiff n (m + 1)) := by
  refine deriv_eq ?h
  exact fun x => RuesDiffHasDeriv n m x

theorem RuesDiffIteratedDeriv (k : ℕ) (n : ℕ+) (m : ℤ) :
  iteratedDeriv k (RuesDiff n m) = RuesDiff n (k + m) := by
  induction' k with K Kih
  · simp only [iteratedDeriv_zero, CharP.cast_eq_zero, zero_add]
  · have h₀ := congrArg deriv Kih
    rw [iteratedDeriv_succ, h₀, RuesDiffDeriv]
    have h₁ : ↑K + m + 1 = ↑(Nat.succ K) + m := by
      simp only [Nat.cast_succ]
      ring
    rw [h₁]

theorem TsumMulIte {α} [TopologicalSpace α] [T2Space α] [AddCommMonoid α] (f : ℕ → α) {n : ℕ+} :
  ∑' (k : ℕ), f (n * k) = ∑' (k : ℕ), ite ((n : ℤ) ∣ k) (f k) 0 := by
  have h₀ : (n : ℕ) ≠ 0 := PNat.ne_zero n
  let nMul : ℕ → ℕ := (λ (m : ℕ) => (n : ℕ) * m)
  have hnMulInj := mul_right_injective₀ h₀
  have h₁ : ∑' (k : ℕ), f (↑n * k) = ∑' (k : ℕ), f (nMul k) := by exact rfl
  have h₂ : ∑' (k : ℕ), f (nMul k) = ∑' (a : Set.range nMul), f ↑a := by
    exact Eq.symm (tsum_range f hnMulInj)
  rw [h₁, h₂, _root_.tsum_subtype (Set.range nMul) f]
  have h₃ : ∀ (k : ℕ), (Set.range nMul).indicator f k = if (↑n : ℤ) ∣ ↑k then f k else 0 := by
    intros k
    simp only [Set.indicator, Set.mem_range, eq_comm, Dvd.dvd, nMul]
    congr 1
    rw [← iff_eq_eq]
    constructor
    · intros h₀
      rcases h₀ with ⟨w, hw⟩
      have h₁ : ∃ (w₂ : ℕ), w = w₂ := by
        refine Int.eq_ofNat_of_zero_le ?_
        by_contra h₆
        simp only [not_le] at h₆
        have h₃ : (n : ℤ) > 0 := by
          refine Int.natCast_pos.mpr ?_
          exact PNat.pos n
        have h₄ : ((n : ℤ) * w) < 0 := by
          exact Int.mul_neg_of_pos_of_neg h₃ h₆
        linarith
      rcases h₁ with ⟨w₂, hw₂⟩
      use w₂
      rw [hw₂] at hw
      exact Int.ofNat_inj.mp hw
    · intros h₄
      rcases h₄ with ⟨w, hw⟩
      use w
      simp only [Nat.cast_mul, hw]
  exact tsum_congr (h₃)

theorem NeedZeroCoeff (f : ℕ → ℂ) (n : ℕ+) :
  ∑' (k : ℕ), f (n * k) = ∑' (k : ℕ), ite ((n : ℤ) ∣ k) (f k) 0 := by
  exact TsumMulIte _

theorem RuesDiffM0EqualsRues (n : ℕ+) : RuesDiff n 0 = Rues n := by
  ext1 z
  rw [Rues, RuesDiff]
  simp only [add_zero]
  rw [NeedZeroCoeff (λ (k : ℕ) => z ^ k / (Nat.factorial k)) n]

theorem RuesDiffRotationallySymmetric (n : ℕ+) (m : ℤ) (z Rou : ℂ) (h : Rou ^ (n : ℕ) = 1) :
  RuesDiff n m (z * Rou) = Rou ^ (-m) * RuesDiff n m z := by
  simp_rw [RuesDiff, ← tsum_mul_left]
  congr
  ext1 k
  simp only [zpow_neg, mul_ite, mul_zero]
  have h₀ := Classical.em (↑↑n ∣ ↑k + m)
  rcases h₀ with h₀a | h₀b
  · simp_rw [if_pos h₀a]
    rw [mul_pow z Rou k]
    have h₁ : Rou ^ k = (Rou ^ m)⁻¹ := by
      obtain ⟨k₂, kmDiv⟩ := h₀a
      have h₂ : Rou ^ (↑k + m) = 1 := by
        rw [kmDiv, zpow_mul]
        simp only [zpow_natCast, h, one_zpow]
      have h₃ := congrArg (λ (z₀ : ℂ) => z₀ * (Rou ^ m)⁻¹) h₂
      simp only [one_mul] at h₃
      have h₄ := RouNot0 n Rou h
      rw [zpow_add₀ h₄ ↑k m] at h₃
      rw [← h₃]
      have h₅ : Rou ^ m ≠ 0 := by
        exact zpow_ne_zero m h₄
      field_simp
      exact rfl
    rw [h₁]
    ring
  · simp_rw [if_neg h₀b]

theorem RuesDiffMPeriodic (n : ℕ+) (m k : ℤ) : RuesDiff n m = RuesDiff n (m + k * n) := by
  ext1 z
  simp_rw [RuesDiff]
  congr
  ext1 K
  congr 1
  have DvdAddMultiple (n m k : ℤ) : (n ∣ m) ↔ (n ∣ m + k * n) :=
    Iff.symm Int.dvd_add_mul_self
  rw [DvdAddMultiple (↑↑n) (↑K + m) k]
  ring_nf

theorem RuesDiffSumOfRuesDiff (n k : ℕ+) (m : ℤ) (z : ℂ) : RuesDiff n m z = ∑ k₀ ∈ range k,
  RuesDiff (n * k) (n * k₀ + m) z := by
  simp_rw [RuesDiff]
  have h₀ : ∀ x ∈ range k,
    Summable (λ (k_1 : ℕ) => if ↑↑(n * k) ∣ ↑k_1 + (↑↑n * ↑x + m) then z ^ k_1 / ↑k_1.factorial else 0) := by
    intros x _
    exact RuesDiffSummable (n * k) _ z
  rw [← Summable.tsum_finsetSum h₀]
  clear h₀
  congr
  ext1 x
  let f₀ : ℕ → Prop := (λ (i : ℕ) => ↑↑(n * k) ∣ ↑x + (↑↑n * ↑i + m))
  have h₁ : ∀ i ∈ range ↑k, ∀ j ∈ range ↑k, f₀ i → f₀ j → i = j := by
    intros i hir j hjr hi hj
    simp only [PNat.mul_coe, Nat.cast_mul, f₀] at hi hj
    simp only [mem_range] at hir hjr
    clear f₀ z
    rw [← Int.modEq_zero_iff_dvd] at hi hj
    have h₀ := Int.ModEq.sub hi hj
    simp only [add_sub_add_left_eq_sub, add_sub_add_right_eq_sub, sub_self] at h₀
    clear hi hj
    rw [Int.modEq_zero_iff_dvd, (show (↑↑n * ↑i - ↑↑n * ↑j : ℤ) = ↑↑n * (↑i - ↑j) by ring)] at h₀
    have h₁ : (n : ℤ) ≠ 0 := by
      exact Ne.symm (NeZero.ne' (n : ℤ))
    have h₂ : (k : ℤ) ∣ ↑i - ↑j := by exact (mul_dvd_mul_iff_left h₁).mp h₀
    obtain ⟨y, h₃⟩ := h₂
    have h₄ : k * y < k := by
      linarith
    have h₅ : -k < k * y := by
      linarith
    have h₆ : (k : ℤ) > 0 := by
      linarith
    have h₇ : y < 1 := by
      exact (mul_lt_iff_lt_one_right h₆).mp h₄
    nth_rw 1 [(show -(k : ℤ) = ↑↑k * -1 by ring)] at h₅
    have h₈ : -1 < y := by
      exact (Int.mul_lt_mul_left h₆).mp h₅
    have h₉ : y = 0 := by
      linarith
    rw [h₉] at h₃
    simp only [mul_zero] at h₃
    clear n hir hjr m h₀ h₁ h₄ h₅ h₆ h₇ h₈ h₉ y x k
    refine Int.ofNat_inj.mp ?intro.a
    have h₀ := congrArg (λ (k : ℤ) => k + j) h₃
    simp only [sub_add_cancel, zero_add] at h₀
    exact h₀
  have h₂ := Finset.sum_ite_zero (range ↑k) f₀ h₁ (z ^ x / ↑x.factorial)
  clear h₁
  simp only [PNat.mul_coe, Nat.cast_mul, mem_range, f₀] at h₂ ⊢
  rw [h₂]
  clear h₂ f₀
  congr
  rw [← iff_eq_eq]
  constructor
  · intros h₀
    obtain ⟨w, h₁⟩ := h₀
    have h₂ : ∀ (i : ℕ), ↑x + (↑↑n * ↑i + m) = ↑x + m + (↑↑n * ↑i) := by
      intros i
      ring_nf
    simp_rw [h₂, h₁]
    use ((-w) % k).toNat
    constructor
    · refine (Int.toNat_lt' ?h.left.hn).mpr ?h.left.a
      · exact PNat.pos k
      · refine Int.emod_lt_of_pos (-w) ?h.left.a.H
        refine Int.natCast_pos.mpr ?h.left.a.H.a
        exact PNat.pos k
    · have h₃ : ↑(-w % ↑↑k).toNat = (-w % ↑↑k) := by
        refine Int.toNat_of_nonneg ?_
        refine Int.emod_nonneg (-w) ?_
        exact Ne.symm (NeZero.ne' (k : ℤ))
      rw [h₃]
      clear h₁ h₂ h₃ m z x
      suffices h₀ : ↑↑k ∣ w + (-w % ↑↑k)
      · have h₁ := mul_dvd_mul_left (n : ℤ) h₀
        ring_nf at *
        exact h₁
      · refine Int.dvd_of_emod_eq_zero ?h₀.H
        have h₀ : (0 : ℤ) = 0 % k := by
          exact rfl
        rw [h₀]
        refine Eq.symm (Int.ModEq.eq ?h₀.H.a)
        have h₁ : -w % ↑↑k ≡ -w [ZMOD ↑↑k] := by
          exact Int.mod_modEq (-w) ↑↑k
        have h₂ : w ≡ w [ZMOD ↑↑k] := by exact rfl
        have h₃ := Int.ModEq.add h₂ h₁
        simp only [add_neg_cancel] at h₃
        exact h₃.symm
  · intros h₀
    obtain ⟨w, _, h₂⟩ := h₀
    have h₃ := dvd_of_mul_right_dvd h₂
    have h₄ : (n : ℤ) ∣ ↑↑n * ↑w := by exact Int.dvd_mul_right (↑n) w
    rw [(show ↑x + (↑↑n * ↑w + m) = ↑↑n * ↑w + ↑(x + m) by ring_nf)] at h₃
    exact (Int.dvd_iff_dvd_of_dvd_add h₃).mp h₄

theorem RuesDiffNthIteratedDeriv (n : ℕ+) (m : ℤ) :
  iteratedDeriv n (RuesDiff n m) = RuesDiff n m := by
  rw [RuesDiffIteratedDeriv, RuesDiffMPeriodic n m 1]
  simp only [one_mul]
  ring_nf

theorem RouGeometricSumEqIte (n : ℕ+) (k : ℤ): ∑ x ∈ range ↑n,
  cexp (2 * ↑π * ((k * ↑x / ↑↑n) * I)) = (if ↑↑n ∣ k then ↑↑n else 0) := by
  have h₀ : ∀ (x : ℕ), (2 * ↑π * (↑k * ↑x / ↑↑n * I)) = ↑x * (2 * ↑π * (↑k / ↑↑n * I)) := by
    intros x
    ring_nf
  simp_rw [h₀, Complex.exp_nat_mul]
  clear h₀
  have hem := Classical.em (↑↑n ∣ k)
  have h₂ : (n : ℂ) ≠ 0 := by exact Ne.symm (NeZero.ne' (n : ℂ))
  rcases hem with hemt | hemf
  · have h₁ : ∑ x ∈ range ↑n, cexp (2 * ↑π * (↑k / ↑↑n * I)) ^ x = ∑ x ∈ range ↑n,
    1 := by
      congr
      ext1 x
      obtain ⟨k₂, kDiv⟩ := hemt
      rw [kDiv]
      field_simp
      simp only [Int.cast_mul, Int.cast_natCast]
      suffices h₃ : cexp (2 * ↑π * (↑k₂ * I)) = 1
      · rw [(show 2 * ↑π * (↑↑n * ↑k₂) * I / ↑↑n = 2 * ↑π * (↑k₂ * I) by field_simp [h₂])]
        rw [h₃]
        simp only [one_pow]
      · refine Complex.exp_eq_one_iff.mpr ?h₃.a
        use k₂
        ring_nf
    rw [h₁, if_pos hemt]
    simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
  · rw [if_neg hemf]
    have h₀ : cexp (2 * ↑π * (↑k / ↑↑n * I)) ≠ 1 := by
      by_contra h
      rw [Complex.exp_eq_one_iff] at h
      obtain ⟨m, h⟩ := h
      rw [(show 2 * ↑π * (↑k / ↑↑n * I) = (↑k / ↑↑n) * (2 * ↑π * I) by ring)] at h
      have h₃ := mul_right_cancel₀ Complex.two_pi_I_ne_zero h
      field_simp at h₃
      rw [mul_comm] at h₃
      have h₄ : k = m * n := by
        exact mod_cast h₃
      have h₅ : (n : ℤ) ∣ k := by
        exact Dvd.intro_left m (id (Eq.symm h₄))
      apply hemf
      exact h₅
    rw [geom_sum_eq h₀]
    suffices h₁ : cexp (2 * ↑π * (↑k / ↑↑n * I)) ^ (n : ℕ) = 1
    · rw [h₁]
      simp only [sub_self, zero_div]
    · rw [(Complex.exp_nat_mul _ n).symm]
      refine Complex.exp_eq_one_iff.mpr ?h₁.a
      use k
      field_simp

theorem RuesDiffEqualsExpSum (n : ℕ+) (m : ℤ) (z : ℂ) : RuesDiff n m z = (∑ k₀ ∈ range n,
  cexp (z * cexp (2 * π * (k₀ / n) * I) + m * 2 * π * (k₀ / n) * I)) / n := by
  simp_rw [Complex.exp_add]
  have h₀ : ∀ (k : ℕ), cexp (z * cexp (2 * ↑π * (↑k / ↑↑n) * I)) =
    ∑' (k_1 : ℕ), (z * cexp (2 * ↑π * (↑k / ↑↑n) * I)) ^ k_1 / ↑(Nat.factorial k_1) := by
    intros k
    exact ExpTsumForm (z * cexp (2 * ↑π * (↑k / ↑↑n) * I))
  simp_rw [h₀]
  clear h₀
  simp_rw [← tsum_mul_right]
  have h₁ : ∀ x ∈ range ↑n, Summable (λ (x_1 : ℕ) =>
    (z * cexp (2 * ↑π * (↑x / ↑↑n) * I)) ^ x_1 /
    ↑(Nat.factorial x_1) * cexp (↑m * 2 * ↑π * (↑x / ↑↑n) * I)) := by
    intros k _
    exact Summable.smul_const (ExpTaylorSeriesSummable (z * cexp (2 * ↑π * (↑k / ↑↑n) * I))) _
  have h₂ := (Summable.tsum_finsetSum h₁).symm
  clear h₁
  simp_rw [h₂]
  clear h₂
  simp_rw [mul_pow, ← Complex.exp_nat_mul]
  have h₃ : ∀ (b x : ℕ), z ^ b * cexp (↑b * (2 * ↑π * (↑x / ↑↑n) * I)) /
    ↑(Nat.factorial b) * cexp (↑m * 2 * ↑π * (↑x / ↑↑n) * I) =
    (z ^ b / ↑(Nat.factorial b)) * (cexp (↑b * (2 * ↑π * (↑x / ↑↑n) * I)) *
    cexp (↑m * 2 * ↑π * (↑x / ↑↑n) * I)) := by
    intros b x
    ring_nf
  simp_rw [h₃, ← Finset.mul_sum, ← Complex.exp_add, ← tsum_div_const, RuesDiff]
  clear h₃
  congr
  ext1 k
  have h₄ : ∀ (x : ℕ), ↑k * (2 * ↑π * (↑x / ↑↑n) * I) + ↑m * 2 * ↑π * (↑x / ↑↑n) * I =
    (2 * ↑π * ((↑k + ↑m) * ↑x / ↑↑n) * I) := by
    intros x
    ring_nf
  simp_rw [h₄]
  clear h₄
  have h₅ := RouGeometricSumEqIte n (↑k + m)
  have h₆ : ∀ (x : ℕ), (2 * ↑π * ((↑k + ↑m) * ↑x / ↑↑n) * I) =
    (2 * ↑π * (↑(↑k + m) * ↑x / ↑↑n * I)) := by
    intros x
    simp only [Int.cast_add, Int.cast_natCast]
    ring_nf
  simp_rw [h₆, h₅, mul_ite, mul_zero]
  have hem := Classical.em (↑↑n ∣ ↑k + m)
  rcases hem with hemt | hemf
  · simp only [if_pos hemt, isUnit_iff_ne_zero, ne_eq, Nat.cast_eq_zero, PNat.ne_zero,
    not_false_eq_true, IsUnit.mul_div_cancel_right]
  · simp only [if_neg hemf, zero_div]

theorem RuesNMthIteratedDeriv (n m : ℕ+) : iteratedDeriv m (Rues n) = RuesDiff n m := by
  rw [← RuesDiffM0EqualsRues, RuesDiffIteratedDeriv]
  simp only [add_zero]

theorem RuesDiffMod (n : ℕ+) (m : ℤ) : RuesDiff n m = RuesDiff n (m % n) := by
  rw [RuesDiffMPeriodic n (m % n) (m / n)]
  nth_rw 1 [← Int.ediv_mul_add_emod m n]
  suffices h₀ : m / ↑↑n * ↑↑n + m % ↑↑n = m % ↑↑n + m / ↑↑n * ↑↑n
  exact congrArg (RuesDiff n) h₀
  ring_nf

-- RuesDiffZMod is the `ZMod n` version of RuesDiff
noncomputable
def RuesDiffZMod (n : ℕ+) (m : ZMod n) (z : ℂ) : ℂ := RuesDiff n m.val z

theorem RuesDiffZModEqRuesDiff (n : ℕ+) (m : ℤ) : RuesDiff n m = RuesDiffZMod n ↑m := by
  ext1 z
  rw [RuesDiffZMod, RuesDiffMod]
  congr
  exact Eq.symm (ZMod.val_intCast m)

theorem ExpPiMulIHalf : cexp (↑(π / 2) * I) = I := by
  rw [exp_mul_I]
  simp only [ofReal_div, ofReal_ofNat, Complex.cos_pi_div_two, Complex.sin_pi_div_two, one_mul,
    zero_add]

theorem ExpToNatPowersOfI (k : ℕ): cexp (↑π * I * k / 2) = I ^ k := by
  induction' k with K Kih
  · simp only [CharP.cast_eq_zero, mul_zero, zero_div, Complex.exp_zero, pow_zero]
  · simp_rw [Nat.cast_succ]
    have h₀ : ↑π * I * (↑K + 1) / 2 = ↑π * I * ↑K / 2 + ↑(π / 2) * I := by
      simp only [ofReal_div, ofReal_ofNat]
      ring_nf
    rw [h₀]
    clear h₀
    rw [Complex.exp_add, Kih, ExpPiMulIHalf]
    have h₂ := zpow_add₀ I_ne_zero K 1
    simp only [zpow_natCast, zpow_one] at h₂
    rw [← h₂]
    exact rfl

theorem RuesNEqualsExpSum (n : ℕ+) (z : ℂ) : Rues n z = (∑ m ∈ range n,
  cexp (z * cexp (2 * π * (m / n) * I))) / n := by
  rw [← RuesDiffM0EqualsRues, RuesDiffEqualsExpSum]
  congr
  ext1 k
  simp only [Int.cast_zero, zero_mul, add_zero]

theorem RuesZ0Equals1 (n : ℕ+) : Rues n 0 = 1 := by
  rw [RuesNEqualsExpSum]
  simp only [zero_mul, Complex.exp_zero, sum_const, card_range, nsmul_eq_mul, mul_one, ne_eq,
    Nat.cast_eq_zero, PNat.ne_zero, not_false_eq_true, div_self]

theorem RuesN1EqualsExp : Rues 1 = cexp := by
  ext1 z
  rw [Rues, ExpTsumForm]
  simp only [PNat.one_coe, one_mul]

theorem RuesN2EqualsCosh : Rues 2 = Complex.cosh := by
  ext1 z
  rw [RuesNEqualsExpSum, Complex.cosh]
  have h₀ : range (2 : ℕ+) = {0, 1} := by
    rfl
  simp_rw [h₀, Finset.sum]
  simp only [insert_val, singleton_val, Multiset.mem_singleton, zero_ne_one, not_false_eq_true,
    Multiset.ndinsert_of_notMem, PNat.val_ofNat, Nat.cast_ofNat, Multiset.map_cons,
    CharP.cast_eq_zero, zero_div, mul_zero, zero_mul, Complex.exp_zero, mul_one,
    Multiset.map_singleton, Nat.cast_one, one_div, Multiset.sum_cons, Multiset.sum_singleton]
  have h₁ : cexp (2 * ↑π * (↑↑(2 : ℕ+))⁻¹ * I) = -1 := by
    have h₂ : 2 * (π : ℂ) * (↑↑(2 : ℕ+))⁻¹ = π := by
      simp only [PNat.val_ofNat, Nat.cast_ofNat]
      field_simp
    rw [h₂]
    simp only [exp_pi_mul_I]
  simp only [PNat.val_ofNat, Nat.cast_ofNat] at h₁
  simp_rw [h₁]
  simp only [mul_neg, mul_one]

theorem RuesN4EqualsCoshCosh (z : ℂ) : Rues 4 z = cosh (z / (1 + I)) * cosh (z / (1 - I)) := by
  rw [RuesNEqualsExpSum, Complex.cosh, Complex.cosh]
  have h₀ : (4 : ℕ+) = (4 : ℕ) := by
    rfl
  simp_rw [h₀, Finset.sum]
  clear h₀
  simp only [range_val, Multiset.range_succ, Multiset.range_zero, Multiset.cons_zero,
    Nat.cast_ofNat, Multiset.map_cons, Nat.cast_one, one_div, Multiset.map_singleton,
    CharP.cast_eq_zero, zero_div, mul_zero, zero_mul, Complex.exp_zero, mul_one, Multiset.sum_cons,
    Multiset.sum_singleton]
  ring_nf
  simp only [one_div, exp_pi_mul_I, mul_neg, mul_one]
  have h₁ : cexp (↑π * I * (3 / 2)) = -I := by
    have h₁b := ExpToNatPowersOfI 3
    simp only [Nat.cast_ofNat] at h₁b
    have h₁b₁ : ↑π * I * 3 / 2 = ↑π * I * (3 / 2) := by
      ring
    rw [h₁b₁] at h₁b
    rw [h₁b]
    clear h₁b h₁b₁
    have h₅ : I ^ (3 : ℕ) = I ^ (3 : ℤ) := by
      exact rfl
    rw [h₅]
    clear h₅
    have h₆ : (3 : ℤ) = 2 + 1 := by
      exact rfl
    rw [h₆]
    clear h₆
    rw [zpow_add₀ I_ne_zero]
    have h₇ : (2 : ℤ) = 1 + 1 := by
      exact rfl
    rw [h₇]
    clear h₇
    rw [zpow_add₀ I_ne_zero]
    simp only [zpow_one, I_mul_I, neg_mul, one_mul]
  rw [h₁]
  clear h₁
  have h₂ : cexp (↑π * I * 2⁻¹) = I := by
    nth_rw 2 [← ExpPiMulIHalf]
    congr 1
    simp only [ofReal_div, ofReal_ofNat]
    ring_nf
  rw [h₂]
  clear h₂
  have h₃ : (1 + I)⁻¹ = (1 - I) / 2 := by
    rw [Inv.inv, Complex.instInv, normSq]
    simp only [MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, ofReal_inv, ofReal_add, ofReal_mul,
      map_add, map_one, conj_I, add_re, one_re, I_re, add_zero, ofReal_one, mul_one, add_im, one_im,
      I_im, zero_add]
    ring_nf
  rw [h₃]
  clear h₃
  have h₄ : (1 - I)⁻¹ = (1 + I) / 2 := by
    rw [Inv.inv, Complex.instInv, normSq]
    simp only [MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, ofReal_inv, ofReal_add, ofReal_mul,
      map_sub, map_one, conj_I, sub_neg_eq_add, sub_re, one_re, I_re, sub_zero, ofReal_one, mul_one,
      sub_im, one_im, I_im, zero_sub, ofReal_neg, mul_neg, neg_neg]
    ring_nf
  simp only [h₄, ← Complex.exp_add]
  ring_nf

theorem ExpSumOfRuesDiff (k : ℕ+) (z : ℂ) : cexp z = ∑ k₀ ∈ range k, RuesDiff k k₀ z := by
  rw [← RuesN1EqualsExp, ← RuesDiffM0EqualsRues]
  have h₀ := RuesDiffSumOfRuesDiff 1 k 0 z
  simp only [one_mul, PNat.val_ofNat, Nat.cast_one, add_zero] at h₀
  assumption

theorem RouForm (n : ℕ+) (x : ℕ) : cexp (2 * ↑π * (↑x / ↑↑n) * I) ^ (n : ℕ) = 1 := by
  rw [(Complex.exp_nat_mul _ n).symm, Complex.exp_eq_one_iff]
  use x
  field_simp
  exact rfl

theorem Sum3Cycle {M α β γ : Type*} [AddCommMonoid M]
  {s : Finset α} {t : Finset β} {u : Finset γ} {f : α → β → γ → M} :
  ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c = ∑ b ∈ t, ∑ c ∈ u, ∑ a ∈ s, f a b c := by
  rw [sum_comm]
  simp_rw [@sum_comm _ _ γ]

theorem SumOfSumEqSum {α β : Type} [Ring β] {n : ℕ} (m : ℤ) (z₀ z₁ : α) (f : ZMod n → α → β) :
  (∑ i ∈ range n, ∑ j ∈ range n, if ↑n ∣ m - i - j then f i z₀ * f j z₁ else 0) =
  ∑ k ∈ range n, f k z₀ * f (m - k) z₁ := by
  obtain rfl | hn := eq_or_ne n 0
  · simp only [range_zero, CharP.cast_eq_zero, zero_dvd_iff, sum_empty, sum_const_zero]
  refine sum_congr rfl ?_
  intros k hk
  haveI : NeZero n := ⟨hn⟩
  let j_sol := ((m - k : ZMod n).val)
  rw [Finset.sum_eq_single j_sol]
  · have h_cast : (j_sol : ZMod n) = m - k := by
      dsimp only [j_sol]
      apply ZMod.val_injective n
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (ZMod.val_lt _)]
    have h_div : ↑n ∣ m - ↑k - ↑j_sol := by
      simp only [← CharP.intCast_eq_zero_iff (ZMod n) n,
        Int.cast_sub, Int.cast_natCast, j_sol, h_cast, sub_self]
    simp only [if_pos h_div]
    congr
  · intros b hb_range hb_ne
    rw [if_neg]
    intro h_div
    apply hb_ne
    simp only [← CharP.intCast_eq_zero_iff (ZMod n) n,
      Int.cast_sub, Int.cast_natCast, sub_eq_zero] at h_div
    have h_cast : (j_sol : ZMod n) = m - k := by
      dsimp only [j_sol]
      apply ZMod.val_injective n
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (ZMod.val_lt _)]
    have h_eq : (b : ZMod n) = (j_sol : ZMod n) := by
      rw [← h_div]
      exact h_cast.symm
    replace h_eq := congrArg ZMod.val h_eq
    rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp hb_range),
      Nat.mod_eq_of_lt (ZMod.val_lt _)] at h_eq
    exact h_eq
  · intro h
    exfalso
    exact h (mem_range.mpr (ZMod.val_lt (m - k : ZMod n)))

theorem RuesDiffArgumentSumRule (n : ℕ+) (m : ℤ) (z₀ z₁ : ℂ) : RuesDiff n m (z₀ + z₁) =
  ∑ k ∈ range n, (RuesDiff n k z₀ * RuesDiff n (m - k) z₁) := by
  rw [RuesDiffEqualsExpSum]
  simp_rw [RightDistribClass.right_distrib, Complex.exp_add, ExpSumOfRuesDiff n (z₀ * _),
    ExpSumOfRuesDiff n (z₁ * _), RuesDiffRotationallySymmetric n _ _ _ (RouForm n _),
    Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, ← Complex.exp_int_mul]
  rw [Sum3Cycle]
  have h₀ : ∀ (a b c : ℕ), cexp (↑(-(b : ℤ)) * (2 * ↑π * (↑a / ↑↑n) * I)) * RuesDiff n (↑b) z₀ *
      (cexp (↑(-(c : ℤ)) * (2 * ↑π * (↑a / ↑↑n) * I)) * RuesDiff n (↑c) z₁) * cexp (↑m * 2 * ↑π * (↑a / ↑↑n) * I) =
      RuesDiff n (↑b) z₀ * RuesDiff n (↑c) z₁ * (cexp (↑(-(b : ℤ)) * (2 * ↑π * (↑a / ↑↑n) * I)) *
      (cexp (↑(-(c : ℤ)) * (2 * ↑π * (↑a / ↑↑n) * I))) * cexp (↑m * 2 * ↑π * (↑a / ↑↑n) * I)) := by
    intros a b c
    ring_nf
  simp_rw [h₀, ← Complex.exp_add, ← Finset.mul_sum, Int.cast_neg, Int.cast_natCast, neg_mul]
  have h₁ : ∀ (x x_1 x_2 : ℕ), -(↑x * (2 * ↑π * (↑x_2 / ↑↑n) * I)) + -(↑x_1 * (2 * ↑π * (↑x_2 / ↑↑n) * I)) +
      ↑m * 2 * ↑π * (↑x_2 / ↑↑n) * I = (2 * ↑π * (((↑m - ↑x - ↑x_1) * ↑x_2 / ↑↑n) * I)) := by
    intros x x_1 x_2
    ring_nf
  simp_rw [h₁]
  clear h₁
  have h₂ : ∀ (x x_1 : ℕ), (m : ℂ) - (x : ℂ) - (x_1 : ℂ) =
    @Int.cast ℂ Ring.toIntCast (m - (x : ℤ) - (x_1 : ℤ)) := by
    intros x x_1
    norm_cast
  simp only [h₂, RouGeometricSumEqIte, mul_ite, mul_zero, sum_div, RuesDiffZModEqRuesDiff]
  calc
    _ = (∑ x ∈ range ↑n, ∑ x_1 ∈ range ↑n, if ↑↑n ∣ m - ↑x - ↑x_1 then
      RuesDiff n (↑x) z₀ * RuesDiff n (↑x_1) z₁ else 0) := by
      congr! 2 with x _ x_1 _; split_ifs
      · simp only [Int.cast_natCast, isUnit_iff_ne_zero, ne_eq, Nat.cast_eq_zero, PNat.ne_zero,
        not_false_eq_true, IsUnit.mul_div_cancel_right, RuesDiffZModEqRuesDiff]
      · simp only [zero_div]
    _ = _ := by
      have h := SumOfSumEqSum m z₀ z₁ (RuesDiffZMod n)
      norm_cast at h ⊢
      simp_rw [← h, RuesDiffZModEqRuesDiff]
      congr
      norm_cast

#print axioms RuesDiffArgumentSumRule

theorem RuesArgumentSumRule (n : ℕ+) (z₀ z₁ : ℂ) : Rues n (z₀ + z₁) = ∑ k ∈ range n,
  (RuesDiff n k z₀ * RuesDiff n (n - k) z₁) := by
  rw [← RuesDiffM0EqualsRues, RuesDiffArgumentSumRule]
  congr
  ext k
  congr 1
  rw [RuesDiffMPeriodic n (0 - ↑k) 1]
  congr 1
  ring_nf

theorem RuesDiffZ0EqualsIte (n : ℕ+) (m : ℤ) : RuesDiff n m 0 = ite ((n : ℤ) ∣ m) 1 0  := by
  rw [RuesDiff, tsum_eq_single 0]
  · simp only [Nat.cast_zero, zero_add, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  · intros b hb
    split_ifs
    · rw [zero_pow hb, zero_div]
    · rfl

theorem EqualsNthDerivRuesDiffSum (f : ℂ → ℂ) (n : ℕ+) (df : Differentiable ℂ f) :
  (f = iteratedDeriv n f) ↔ (f = ∑ k ∈ range n,
    (λ (_ : ℂ) => iteratedDeriv k f 0) * (RuesDiff n (-k))) := by
  let g := ∑ k ∈ range n, (λ (z : ℂ) => iteratedDeriv k f 0) * (RuesDiff n (-k))
  have h_lin_g : ∀ (m : ℕ), iteratedDeriv m g =
    ∑ k ∈ range n, (λ (z : ℂ) => iteratedDeriv k f 0) * iteratedDeriv m (RuesDiff n (-k)) := by
    intro m
    induction m with
    | zero =>
      dsimp only [g]
      rfl
    | succ m ih =>
      rw [iteratedDeriv_succ, ih]
      ext z
      rw [deriv_sum]
      · simp_rw [Finset.sum_apply]
        apply sum_congr rfl
        intros x hx
        simp only [Pi.mul_apply]
        rw [show ((fun z => iteratedDeriv x f 0) * iteratedDeriv m (RuesDiff n (-↑x))) =
                 (fun z => iteratedDeriv x f 0 * iteratedDeriv m (RuesDiff n (-↑x)) z) by rfl]
        rw [deriv_const_mul]
        · rw [iteratedDeriv_succ]
        · rw [RuesDiffIteratedDeriv]
          apply HasDerivAt.differentiableAt (RuesDiffHasDeriv _ _ _)
      · intros x hx
        apply DifferentiableAt.const_mul
        rw [RuesDiffIteratedDeriv]
        apply HasDerivAt.differentiableAt (RuesDiffHasDeriv _ _ _)
  have hg_sol : g = iteratedDeriv n g := by
    nth_rewrite 1 [h_lin_g n]
    apply sum_congr rfl
    intros k hk
    rw [RuesDiffIteratedDeriv]
    rw [RuesDiffMPeriodic n (-k) 1]
    ring_nf
  constructor
  · intro h
    have h_init : ∀ k ∈ range n, iteratedDeriv k g 0 = iteratedDeriv k f 0 := by
      intros k hk
      rw [h_lin_g k]
      simp only [sum_apply, Pi.mul_apply]
      rw [Finset.sum_eq_single k]
      · rw [RuesDiffIteratedDeriv, RuesDiffZ0EqualsIte]
        simp only [add_neg_cancel, dvd_zero, ↓reduceIte, mul_one]
      · intros b hb_range hb_ne
        rw [RuesDiffIteratedDeriv, RuesDiffZ0EqualsIte]
        simp only [mul_ite, mul_one, mul_zero, ite_eq_right_iff]
        have h_ndiv : ¬ (n : ℤ) ∣ ↑k + -↑b := by
          rw [Int.add_neg_eq_sub, ← Int.modEq_iff_dvd]
          intro h_eq
          apply hb_ne
          apply Nat.ModEq.eq_of_lt_of_lt
          · exact Int.natCast_modEq_iff.mp h_eq
          · exact mem_range.mp hb_range
          · exact mem_range.mp hk
        simp only [h_ndiv, IsEmpty.forall_iff]
      · intro h_nmem
        exfalso
        exact h_nmem hk
    ext z
    have h_all_derivs : ∀ k, iteratedDeriv k f 0 = iteratedDeriv k g 0 := by
      intro k
      let q := k / n
      let r := k % n
      have hk_eq : k = q * n + r := by
        nth_rewrite 1 [← Nat.div_add_mod k n]
        ring
      rw [hk_eq]
      have hf_per : iteratedDeriv (q * n + r) f = iteratedDeriv r f := by
        induction q with
        | zero => simp only [zero_mul, zero_add]
        | succ q ih =>
          rw [show (q + 1) * ↑n + r = ↑n + (q * ↑n + r) by ring]
          simp only [iteratedDeriv_eq_iterate] at h ih ⊢
          rw [Function.iterate_add_apply, ih]
          nth_rewrite 1 [← Function.iterate_add_apply, add_comm _ (r : ℕ), Function.iterate_add_apply, h.symm]
          rfl
      have hg_per : iteratedDeriv (q * n + r) g = iteratedDeriv r g := by
         induction q with
        | zero => simp only [zero_mul, zero_add]
        | succ q ih =>
          rw [show (q + 1) * ↑n + r = ↑n + (q * ↑n + r) by ring]
          simp only [iteratedDeriv_eq_iterate] at hg_sol ih ⊢
          rw [Function.iterate_add_apply, ih]
          nth_rewrite 1 [← Function.iterate_add_apply, add_comm _ (r : ℕ), Function.iterate_add_apply, hg_sol.symm]
          rfl
      rw [hf_per, hg_per]
      rw [h_init]
      exact mem_range.mpr (Nat.mod_lt k n.pos)
    have hg_diff : Differentiable ℂ g := by
       dsimp only [g]
       apply Differentiable.sum
       intro k _
       apply Differentiable.mul
       <;> intro z
       · apply differentiableAt_const
       · apply (RuesDiffHasDeriv n (-↑k : ℤ) z).differentiableAt
    have hf_ana : ∀ z, AnalyticAt ℂ f z := fun z => df.analyticAt z
    have hg_ana : ∀ z, AnalyticAt ℂ g z := fun z => hg_diff.analyticAt z
    have h_eq : f = g := by
      apply AnalyticOnNhd.eq_of_eventuallyEq (𝕜 := ℂ)
      · intros x _; exact hf_ana x
      · intros x _; exact hg_ana x
      · have hf_ser := (hf_ana 0).hasFPowerSeriesAt
        have hg_ser := (hg_ana 0).hasFPowerSeriesAt
        have h_ser_eq : (FormalMultilinearSeries.ofScalars ℂ (fun n ↦ iteratedDeriv n f 0 / n.factorial)) =
                        (FormalMultilinearSeries.ofScalars ℂ (fun n ↦ iteratedDeriv n g 0 / n.factorial)) := by
          ext n
          simp only [h_all_derivs, FormalMultilinearSeries.apply_eq_prod_smul_coeff, prod_const_one,
            FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, one_mul]
        have h_sub_ser := hf_ser.sub hg_ser
        rw [h_ser_eq, sub_self] at h_sub_ser
        have h_sub_ev := h_sub_ser.eventually_eq_zero
        filter_upwards [h_sub_ev] with x hx
        simp only [Pi.sub_apply, sub_eq_zero] at hx
        exact hx
    exact congr_fun h_eq z
  · intro h
    exact h.trans (hg_sol.trans (congr_arg (iteratedDeriv (↑n)) h).symm)

#print axioms EqualsNthDerivRuesDiffSum

theorem RuesDiffSumEqRuesDiff (n : ℕ+) (m : ℤ) (z₀ z₁ : ℂ) :
  ∑ k ∈ range n, RuesDiff n k z₀ * RuesDiff n (m - k) (z₁ - z₀) = RuesDiff n m z₁ := by
  rw [← RuesDiffArgumentSumRule, add_sub_cancel]

theorem RuesDiffSumIdentity (n : ℕ+) (m : ℤ) (z : ℂ) :
  ∑ k ∈ range n, RuesDiff n k z * RuesDiff n (m - k) (-z) = ite ((n : ℤ) ∣ m) 1 0 := by
  rw [← RuesDiffZ0EqualsIte n m, ← RuesDiffSumEqRuesDiff n m z 0, zero_sub]

theorem ExpOfMulRouEqRuesDiffSum (n : ℕ+) (z Rou : ℂ) (hu : Rou ^ (n : ℕ) = 1) :
    cexp (z * Rou) = ∑ k ∈ range n, Rou⁻¹ ^ k * RuesDiff n k z := by
  rw [ExpSumOfRuesDiff n (z * Rou)]
  congr
  ext k
  rw [RuesDiffRotationallySymmetric n k z Rou hu, zpow_neg, zpow_natCast, inv_pow]
