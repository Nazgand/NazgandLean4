-- PDF document this is based on: https://github.com/Nazgand/NazgandMathBook/blob/master/RootOfUnityExponentialSumFunction.pdf
-- LEAN 3 code for this: https://github.com/Nazgand/NazgandMathBook/blob/master/NazgandLean3/src/RootOfUnityExponentialSum.lean
import Mathlib
set_option maxHeartbeats 0
open Complex Classical NormedSpace BigOperators Finset Real

lemma ExpTsumForm (z : ℂ) : cexp z = tsum (λ (k : ℕ) => z ^ k / k.factorial) := by
  rw [exp_eq_exp_ℂ, exp_eq_tsum_div]

lemma ExpTaylorSeriesSummable (z : ℂ) : Summable (λ (k : ℕ) => z ^ k / k.factorial) := by
  exact expSeries_div_summable ℂ z

-- Rues is the Root of Unity Exponential Sum function
-- inspired by the relationship between exp and cosh
noncomputable
def Rues (n : ℕ+) (z : ℂ) : ℂ :=
  tsum (λ (k : ℕ) => z ^ (n * k) / (n * k).factorial)

lemma RuesSummable (n : ℕ+) (z : ℂ) : Summable (λ (k : ℕ) => z ^ (n * k) / (n * k).factorial) :=
  (expSeries_div_summable ℂ z).comp_injective (strictMono_mul_left_of_pos n.pos).injective

lemma RuesRealToReal (n : ℕ+) (x : ℝ) : (Rues n x).im = 0 := by
  rw [Rues]
  let h₀ := ContinuousLinearMap.map_tsum Complex.imCLM (RuesSummable n x)
  simp only [imCLM_apply] at h₀
  rw [h₀]
  suffices h₁ : ∑' (z : ℕ), (x ^ (n * z) : ℂ).im / ↑(Nat.factorial (n * z)) = ∑' (z : ℕ), 0
  · rw [tsum_zero] at h₁
    rw [←h₁]
    simp only [div_natCast_im]
  congr
  ext1 k
  norm_cast at *
  simp only [zero_div]

lemma RuesRotationallySymmetric (n : ℕ+) (z rou : ℂ) (h : rou ^ (n : ℕ) = 1) : Rues n z = Rues n (z * rou) := by
  simp_rw [Rues]
  congr
  ext1 k
  have h₀ : (z * rou) ^ (n * k) = z ^ (n * k) * rou ^ (n * k) := by
    exact mul_pow z rou (↑n * k)
  have h₁ : rou ^ (n * k) = (rou ^ (n : ℕ)) ^ k := by
    exact pow_mul rou (↑n) k
  simp only [h₀, h₁, h, one_pow, mul_one]

lemma RouNot0 (n : ℕ+) (rou : ℂ) (h : rou ^ (n : ℕ) = 1) : rou ≠ 0 := by
  by_contra h₁
  rw [h₁] at h
  simp only [ne_eq, PNat.ne_zero, not_false_eq_true, zero_pow, zero_ne_one] at h

-- (RuesDiff n m) is the mth derivative of (Rues n)
noncomputable
def RuesDiff (n : ℕ+) (m : ℤ) (z : ℂ) : ℂ :=
  tsum (λ (k : ℕ) => if ↑↑n ∣ (↑k + m) then z ^ k / k.factorial else 0)

lemma RuesDiffSummable (n : ℕ+) (m : ℤ) (z : ℂ) : Summable (λ (k : ℕ) => if ↑↑n ∣ (↑k + m) then z ^ k / k.factorial else 0) := by
  sorry

lemma RuesDiffHasDeriv (n : ℕ+) (m : ℤ) (z : ℂ) : HasDerivAt (RuesDiff n m) (RuesDiff n (m + 1) z) z := by
  sorry

lemma RuesDiffDeriv (n : ℕ+) (m : ℤ) : deriv (RuesDiff n m) = (RuesDiff n (m + 1)) := by
  sorry

lemma RuesDiffIteratedDeriv (k : ℕ) (n : ℕ+) (m : ℤ) : iteratedDeriv k (RuesDiff n m) = RuesDiff n (k + m) := by
  induction' k with K Kih
  · simp only [Nat.zero_eq, iteratedDeriv_zero, CharP.cast_eq_zero, zero_add]
  · have h₀ := congrArg deriv Kih
    rw [iteratedDeriv_succ, h₀, RuesDiffDeriv]
    have h₁ : ↑K + m + 1 = ↑(Nat.succ K) + m := by
      simp only [Nat.cast_succ]
      ring
    rw [h₁]

lemma TsumMulIte {α} [TopologicalSpace α] [T2Space α] [AddCommMonoid α] (f : ℕ → α) {n : ℕ+} :
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
    rw [←iff_eq_eq]
    constructor
    · intros h₀
      rcases h₀ with ⟨w, hw⟩
      have h₁ : ∃ (w₂ : ℕ), w = w₂ := by
        refine Int.eq_ofNat_of_zero_le ?_
        by_contra h₆
        simp only [not_le] at h₆
        have h₃ : (n : ℤ) > 0 := by
          refine Int.ofNat_pos.mpr ?_
          exact PNat.pos n
        have h₄ : ((n : ℤ) * w) < 0 := by
          exact Int.mul_neg_of_pos_of_neg h₃ h₆
        linarith
      rcases h₁ with ⟨w₂, hw₂⟩
      use w₂
      rw [hw₂] at hw
      exact Int.ofNat_inj.mp hw
    · intros h₄
      rcases h₄ with ⟨w,hw⟩
      use w
      simp only [Nat.cast_mul, hw]
  exact tsum_congr (h₃)

lemma NeedZeroCoeff (f : ℕ → ℂ) (n : ℕ+) : ∑' (k : ℕ), f (n * k) = ∑' (k : ℕ), ite ((n : ℤ) ∣ k) (f k) 0 := by
  exact TsumMulIte _

lemma RuesDiffM0EqualsRues (n : ℕ+) : RuesDiff n 0 = Rues n := by
  ext1 z
  rw [Rues, RuesDiff]
  simp only [add_zero]
  rw [NeedZeroCoeff (λ (k : ℕ) => z ^ k / (Nat.factorial k)) n]

lemma RuesDiffRotationallySymmetric (n : ℕ+) (m : ℤ) (z rou : ℂ) (h : rou ^ (n : ℕ) = 1) : RuesDiff n m (z * rou) = rou ^ (-m) * RuesDiff n m z := by
  simp_rw [RuesDiff, ←tsum_mul_left]
  congr
  ext1 k
  simp only [zpow_neg, mul_ite, mul_zero]
  have h₀ := Classical.em (↑↑n ∣ ↑k + m)
  rcases h₀ with h₀a | h₀b
  · simp_rw [if_pos h₀a]
    rw [mul_pow z rou k]
    have h₁ : rou ^ k = (rou ^ m)⁻¹ := by
      obtain ⟨k₂, kmDiv⟩ := h₀a
      have h₂ : rou ^ (↑k + m) = 1 := by
        rw [kmDiv, zpow_mul]
        simp only [zpow_natCast, h, one_zpow]
      have h₃ := congrArg (λ (z₀ : ℂ) => z₀ * (rou ^ m)⁻¹) h₂
      simp only [one_mul, ne_eq, inv_eq_zero] at h₃
      have h₄ := RouNot0 n rou h
      rw [zpow_add₀ h₄ ↑k m] at h₃
      rw [←h₃]
      have h₅ : rou ^ m ≠ 0 := by
        exact zpow_ne_zero m h₄
      field_simp
    rw [h₁]
    ring
  · simp_rw [if_neg h₀b]

lemma Dvd.dvd.addMultiple (n m k : ℤ): (n ∣ m) ↔ (n ∣ m + k * n) := by
  have h₁ : n ∣ (k * n) := by
    exact Int.dvd_mul_left k n
  constructor
  · intros h₀
    exact Dvd.dvd.add h₀ h₁
  · intros h₂
    exact (Int.dvd_add_left h₁).mp h₂

lemma RuesDiffMPeriodic (n : ℕ+) (m k : ℤ) : RuesDiff n m = RuesDiff n (m + k * n) := by
  ext1 z
  simp_rw [RuesDiff]
  congr
  ext1 K
  congr 1
  rw [Dvd.dvd.addMultiple (↑↑n) (↑K + m) k]
  ring_nf

lemma RuesDiffSumOfRuesDiff (n k : ℕ+) (m : ℤ) (z : ℂ) : RuesDiff n m z = ∑ k₀ in range k, RuesDiff (n * k) (n * k₀ + m) z := by
  simp_rw [RuesDiff]
  have h₀ : ∀ x ∈ range k, Summable (λ (k_1 : ℕ) => if ↑↑(n * k) ∣ ↑k_1 + (↑↑n * ↑x + m) then z ^ k_1 / ↑k_1.factorial else 0) := by
    intros x _
    exact RuesDiffSummable (n * k) _ z
  rw [← tsum_sum h₀]
  clear h₀
  congr
  ext1 x
  let f₀ : ℕ → Prop := (λ (i : ℕ) => ↑↑(n * k) ∣ ↑x + (↑↑n * ↑i + m))
  have h₁ : ∀ i ∈ range ↑k, ∀ j ∈ range ↑k, f₀ i → f₀ j → i = j := by
    intros i hir j hjr hi hj
    simp [f₀] at hi hj
    simp only [mem_range] at hir hjr
    clear f₀ z
    rw [←Int.modEq_zero_iff_dvd] at hi hj
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
      exact (mul_lt_mul_left h₆).mp h₅
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
  rw [←iff_eq_eq]
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
      · exact PNat.ne_zero k
      · refine Int.emod_lt_of_pos (-w) ?h.left.a.H
        refine Int.ofNat_pos.mpr ?h.left.a.H.a
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
        simp only [add_right_neg] at h₃
        exact h₃.symm
  · intros h₀
    obtain ⟨w, _, h₂⟩ := h₀
    have h₃ := dvd_of_mul_right_dvd h₂
    have h₄ : (n : ℤ) ∣ ↑↑n * ↑w := by exact Int.dvd_mul_right (↑n) w
    rw [(show ↑x + (↑↑n * ↑w + m) = ↑↑n * ↑w + ↑(x + m) by ring_nf)] at h₃
    exact (Int.dvd_iff_dvd_of_dvd_add h₃).mp h₄

lemma RuesArgumentSumRule (n : ℕ+) (z₀ z₁ : ℂ) : Rues n (z₀ + z₁) = ∑ k in range n, (RuesDiff n k z₀ * RuesDiff n (n - k) z₁) := by
  sorry

lemma RuesDiffNthIteratedDeriv (n : ℕ+) (m : ℤ) : iteratedDeriv n (RuesDiff n m) = RuesDiff n m := by
  rw [RuesDiffIteratedDeriv, RuesDiffMPeriodic n m 1]
  simp only [one_mul]
  ring_nf

lemma RouGeometricSumEqIte (n : ℕ+) (k : ℤ): ∑ x in range ↑n, cexp (2 * ↑π * ((k * ↑x / ↑↑n) * I)) = (if ↑↑n ∣ k then ↑↑n else 0) := by
  have h₀ : ∀ (x : ℕ), (2 * ↑π * (↑k * ↑x / ↑↑n * I)) = ↑x * (2 * ↑π * (↑k / ↑↑n * I)) := by
    intros x
    ring_nf
  simp_rw [h₀, Complex.exp_nat_mul]
  clear h₀
  have hem := Classical.em (↑↑n ∣ k)
  have h₂ : (n : ℂ) ≠ 0 := by exact Ne.symm (NeZero.ne' (n : ℂ))
  rcases hem with hemt | hemf
  · have h₁ : ∑ x in range ↑n, cexp (2 * ↑π * (↑k / ↑↑n * I)) ^ x = ∑ x in range ↑n, 1 := by
      congr
      ext1 x
      obtain ⟨k₂, kDiv⟩ := hemt
      rw [kDiv]
      field_simp
      suffices h₃ : cexp (2 * ↑π * (↑k₂ * I)) = 1
      · rw [h₃]
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
      ring_nf

lemma RuesDiffEqualsExpSum (n : ℕ+) (m : ℤ) (z : ℂ) : RuesDiff n m z = (∑ k₀ in range n, cexp (z * cexp (2 * π * (k₀ / n) * I) + m * 2 * π * (k₀ / n) * I)) / n := by
  simp_rw [Complex.exp_add]
  have h₀ : ∀ (k : ℕ), cexp (z * cexp (2 * ↑π * (↑k / ↑↑n) * I)) = ∑' (k_1 : ℕ), (z * cexp (2 * ↑π * (↑k / ↑↑n) * I)) ^ k_1 / ↑(Nat.factorial k_1) := by
    intros k
    exact ExpTsumForm (z * cexp (2 * ↑π * (↑k / ↑↑n) * I))
  simp_rw [h₀]
  clear h₀
  simp_rw [←tsum_mul_right]
  have h₁ : ∀ x ∈ range ↑n, Summable (λ (x_1 : ℕ) => (z * cexp (2 * ↑π * (↑x / ↑↑n) * I)) ^ x_1 / ↑(Nat.factorial x_1) * cexp (↑m * 2 * ↑π * (↑x / ↑↑n) * I)) := by
    intros k _
    exact Summable.smul_const (ExpTaylorSeriesSummable (z * cexp (2 * ↑π * (↑k / ↑↑n) * I))) _
  have h₂ := (tsum_sum h₁).symm
  clear h₁
  simp_rw [h₂]
  clear h₂
  simp_rw [mul_pow, ←Complex.exp_nat_mul]
  have h₃ : ∀ (b x : ℕ), z ^ b * cexp (↑b * (2 * ↑π * (↑x / ↑↑n) * I)) / ↑(Nat.factorial b) * cexp (↑m * 2 * ↑π * (↑x / ↑↑n) * I) =
            (z ^ b / ↑(Nat.factorial b)) * (cexp (↑b * (2 * ↑π * (↑x / ↑↑n) * I)) * cexp (↑m * 2 * ↑π * (↑x / ↑↑n) * I)) := by
    intros b x
    ring_nf
  simp_rw [h₃, ←Finset.mul_sum, ←Complex.exp_add, ←tsum_div_const, RuesDiff]
  clear h₃
  congr
  ext1 k
  have h₄ : ∀ (x : ℕ), ↑k * (2 * ↑π * (↑x / ↑↑n) * I) + ↑m * 2 * ↑π * (↑x / ↑↑n) * I = (2 * ↑π * ((↑k + ↑m) * ↑x / ↑↑n) * I) := by
    intros x
    ring_nf
  simp_rw [h₄]
  clear h₄
  have h₅ := RouGeometricSumEqIte n (↑k + m)
  have h₆ : ∀ (x : ℕ), (2 * ↑π * ((↑k + ↑m) * ↑x / ↑↑n) * I) = (2 * ↑π * (↑(↑k + m) * ↑x / ↑↑n * I)) := by
    intros x
    simp only [Int.cast_add, Int.cast_natCast]
    ring_nf
  simp_rw [h₆, h₅]
  simp only [mul_ite, mul_zero]
  have hem := Classical.em (↑↑n ∣ ↑k + m)
  rcases hem with hemt | hemf
  · simp_rw [if_pos hemt]
    ring_nf
    simp only [ne_eq, Nat.cast_eq_zero, PNat.ne_zero, not_false_eq_true, mul_inv_cancel_right₀]
  · simp_rw [if_neg hemf]
    simp only [zero_div]

lemma RuesDiffZ0EqualsIte (n : ℕ+) (m : ℤ) : RuesDiff n m 0 = ite ((n : ℤ) ∣ m) 1 0  := by
  sorry

lemma EqualsNthDerivRuesDiffSum (f : ℂ → ℂ) (n : ℕ+) : (f = iteratedDeriv n f) ↔ (f = ∑ k in range n, (λ(z : ℂ) => iteratedDeriv k f 0) * (RuesDiff n (-k))) := by
  sorry

lemma RuesNMthIteratedDeriv (n m : ℕ+) : iteratedDeriv m (Rues n) = RuesDiff n m := by
  rw [←RuesDiffM0EqualsRues, RuesDiffIteratedDeriv]
  simp only [add_zero]

lemma RuesDiffMod (n : ℕ+) (m : ℤ) : RuesDiff n m = RuesDiff n (m % n) := by
  rw [RuesDiffMPeriodic n (m % n) (m / n)]
  nth_rw 1 [←Int.ediv_add_emod' m n]
  suffices h₀ : m / ↑↑n * ↑↑n + m % ↑↑n = m % ↑↑n + m / ↑↑n * ↑↑n
  exact congrArg (RuesDiff n) h₀
  ring_nf

lemma ExpPiMulIHalf : cexp (↑(π / 2) * I) = I := by
  rw [exp_mul_I]
  simp only [ofReal_div, ofReal_ofNat, Complex.cos_pi_div_two, Complex.sin_pi_div_two, one_mul,
    zero_add]

lemma ExpToNatPowersOfI (k : ℕ): exp (↑π * I * k / 2) = I ^ k := by
  induction' k with K Kih
  · simp only [Nat.zero_eq, CharP.cast_eq_zero, mul_zero, zero_div, Complex.exp_zero, pow_zero]
  · simp_rw [Nat.cast_succ]
    have h₀ : ↑π * I * (↑K + 1) / 2 = ↑π * I * ↑K / 2 + ↑(π / 2) * I := by
      simp only [ofReal_div, ofReal_ofNat]
      ring_nf
    rw [h₀]
    clear h₀
    rw [Complex.exp_add, Kih, ExpPiMulIHalf]
    have h₂ := zpow_add₀ I_ne_zero K 1
    simp only [zpow_natCast, zpow_one] at h₂
    rw [←h₂]
    exact rfl

lemma RuesNEqualsExpSum (n : ℕ+) (z : ℂ) : Rues n z = (∑ m in range n, cexp (z * cexp (2 * π * (m / n) * I))) / n := by
  rw [←RuesDiffM0EqualsRues, RuesDiffEqualsExpSum]
  congr
  ext1 k
  simp only [Int.cast_zero, zero_mul, add_zero]

lemma RuesZ0Equals1 (n : ℕ+) : Rues n 0 = 1 := by
  rw [RuesNEqualsExpSum]
  simp only [zero_mul, Complex.exp_zero, sum_const, card_range, nsmul_eq_mul, mul_one, ne_eq,
    Nat.cast_eq_zero, PNat.ne_zero, not_false_eq_true, div_self]

lemma RuesN1EqualsExp : Rues 1 = cexp := by
  ext1 z
  rw [Rues, ExpTsumForm]
  simp only [PNat.one_coe, one_mul]

lemma RuesN2EqualsCosh : Rues 2 = Complex.cosh := by
  ext1 z
  rw [RuesNEqualsExpSum, Complex.cosh]
  have h₀ : range (2 : ℕ+) = {0, 1} := by
    rfl
  simp_rw [h₀, Finset.sum]
  simp only [mem_singleton, insert_val, singleton_val, Multiset.mem_singleton, not_false_eq_true,
    Multiset.ndinsert_of_not_mem, Multiset.map_cons, CharP.cast_eq_zero, zero_div, mul_zero,
    zero_mul, Complex.exp_zero, mul_one, Multiset.map_singleton, Nat.cast_one, one_div,
    Multiset.sum_cons, Multiset.sum_singleton]
  have h₁ : cexp (2 * ↑π * (↑↑(2 : ℕ+))⁻¹ * I) = -1 := by
    have h₂ : 2 * (π : ℂ) * (↑↑(2 : ℕ+))⁻¹ = π := by
      field_simp
    rw [h₂]
    simp only [exp_pi_mul_I]
  simp_rw [h₁]
  simp only [mul_neg, mul_one]
  congr

lemma RuesN4EqualsCoshCosh (z : ℂ) : Rues 4 z = cosh (z / (1 + I)) * cosh (z / (1 - I)) := by
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
    nth_rw 2 [←ExpPiMulIHalf]
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
  rw [h₄]
  clear h₄
  ring_nf
  simp only [Int.ofNat_eq_coe, Nat.cast_one, Int.cast_one, Nat.cast_ofNat, one_div,
    Int.cast_negOfNat, mul_neg, mul_one, neg_mul]
  simp_rw [Complex.exp_add]
  ring_nf
  simp only [Int.ofNat_eq_coe, Nat.cast_one, Int.cast_one, Nat.cast_ofNat, one_div,
    Int.cast_negOfNat, mul_neg, mul_one, neg_mul]
  simp_rw [←Complex.exp_nat_mul, ←Complex.exp_add]
  ring_nf

lemma ExpSumOfRuesDiff (k : ℕ+) (z : ℂ) : exp z = ∑ k₀ in range k, RuesDiff k k₀ z := by
  rw [←RuesN1EqualsExp, ←RuesDiffM0EqualsRues]
  have h₀ := RuesDiffSumOfRuesDiff 1 k 0 z
  simp only [one_mul, PNat.val_ofNat, Nat.cast_one, add_zero] at h₀
  assumption

lemma RouForm (n : ℕ+) (x : ℕ) : cexp (2 * ↑π * (↑x / ↑↑n) * I) ^ (n : ℕ) = 1 := by
  rw [(Complex.exp_nat_mul _ n).symm, Complex.exp_eq_one_iff]
  use x
  field_simp
  ring_nf

lemma RuesDiffArgumentSumRule (n : ℕ+) (m : ℤ) (z₀ z₁ : ℂ) : RuesDiff n m (z₀ + z₁) = ∑ k in range n, (RuesDiff n k z₀ * RuesDiff n (m - k) z₁) := by
  rw [RuesDiffEqualsExpSum]
  simp_rw [Complex.exp_add, RightDistribClass.right_distrib, Complex.exp_add, ExpSumOfRuesDiff n (z₀ * _), ExpSumOfRuesDiff n (z₁ * _)]
  simp_rw [RuesDiffRotationallySymmetric n _ _ _ (RouForm n _)]
  sorry
