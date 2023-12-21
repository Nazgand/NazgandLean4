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
  let h₀ := ContinuousLinearMap.map_tsum Complex.imClm (RuesSummable n x)
  simp only [imClm_apply, div_nat_cast_im] at h₀
  rw [h₀]
  suffices h₁ : ∑' (z : ℕ), (x ^ (n * z) : ℂ).im / ↑(Nat.factorial (n * z)) = ∑' (z : ℕ), 0
  · rw [tsum_zero] at h₁
    rw [←h₁]
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
  simp only [ne_eq, PNat.ne_zero, not_false_eq_true, zero_pow', zero_ne_one] at h

-- (RuesDiff n m) is the mth derivative of (Rues n)
noncomputable
def RuesDiff (n : ℕ+) (m : ℤ) (z : ℂ) : ℂ :=
  tsum (λ (k : ℕ) => if ((k : ℤ) + m) % n = 0 then z ^ k / k.factorial else 0)

lemma RuesDiffSummable (n : ℕ+) (m : ℤ) (z : ℂ) : Summable (λ (k : ℕ) => if ((k : ℤ) + m) % n = 0 then z ^ k / k.factorial else 0) := by
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

lemma RuesDiffM0EqualsRues (n : ℕ+) : RuesDiff n 0 = Rues n := by
  sorry

lemma RuesDiffRotationallySymmetric (n : ℕ+) (m : ℤ) (z rou : ℂ) (h : rou ^ (n : ℕ) = 1) : RuesDiff n m (z * rou) = rou ^ (-m) * RuesDiff n m z := by
  simp_rw [RuesDiff, ←tsum_mul_left]
  congr
  ext1 k
  simp only [EuclideanDomain.mod_eq_zero, zpow_neg, mul_ite, mul_zero]
  have h₀ := Classical.em (↑↑n ∣ ↑k + m)
  rcases h₀ with h₀a | h₀b
  · simp_rw [if_pos h₀a]
    rw [mul_pow z rou k]
    have h₁ : rou ^ k = (rou ^ m)⁻¹ := by
      obtain ⟨k₂, kmDiv⟩ := h₀a
      have h₂ : rou ^ (↑k + m) = 1 := by
        rw [kmDiv, zpow_mul]
        simp only [zpow_coe_nat, h, one_zpow]
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

lemma RuesDiffMPeriodic (n : ℕ+) (m k : ℤ) : RuesDiff n m = RuesDiff n (m + k * n) := by
  ext1 z
  simp_rw [RuesDiff]
  congr
  ext1 K
  have h₀ : (↑K + m) % ↑↑n = (↑K + (m + k * ↑↑n)) % ↑↑n := by
    have h₁ : ↑K + (m + k * ↑↑n) = (↑K + m) + k * ↑↑n := by
      ring
    rw [h₁, Int.add_mul_emod_self]
  rw [h₀]

lemma RuesDiffSumOfRuesDiff (n k : ℕ+) (m : ℤ) (z : ℂ) : RuesDiff n m z = ∑ k₀ in range k, RuesDiff (n * k) (n * k₀ + m) z := by
  sorry

lemma ExpSumOfRuesDiff (k : ℕ+) (z : ℂ) : exp z = ∑ k₀ in range k, RuesDiff k k₀ z := by
  sorry

lemma RuesArgumentSumRule (n : ℕ+) (z₀ z₁ : ℂ) : Rues n (z₀ + z₁) = ∑ k in range n, (RuesDiff n k z₀ * RuesDiff n (n - k) z₁) := by
  sorry

lemma RuesDiffNthIteratedDeriv (n : ℕ+) (m : ℤ) : iteratedDeriv n (RuesDiff n m) = RuesDiff n m := by
  sorry

lemma RuesDiffEqualsExpSum (n : ℕ+) (m : ℤ) (z : ℂ) : RuesDiff n m z = (∑ k₀ in range n, cexp (z * cexp (2 * π * (k₀ / n) * I) + m * 2 * π * (k₀ / n) * I)) / n := by
  simp_rw [Complex.exp_add]
  have h₀ : ∀ (k : ℕ), cexp (z * cexp (2 * ↑π * (↑k / ↑↑n) * I)) = ∑' (k_1 : ℕ), (z * cexp (2 * ↑π * (↑k / ↑↑n) * I)) ^ k_1 / ↑(Nat.factorial k_1) := by
    intros k
    exact ExpTsumForm (z * cexp (2 * ↑π * (↑k / ↑↑n) * I))
  simp_rw [h₀]
  clear h₀
  simp_rw [←tsum_mul_right]
  have h₁ : ∀ x ∈ range ↑n, Summable (λ (x_1 : ℕ) => (z * cexp (2 * ↑π * (↑x / ↑↑n) * I)) ^ x_1 / ↑(Nat.factorial x_1) * cexp (↑m * 2 * ↑π * (↑x / ↑↑n) * I)) := by
    intros k kr
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
  have h₄ : ∀ (x : ℕ), ↑k * (2 * ↑π * (↑x / ↑↑n) * I) + ↑m * 2 * ↑π * (↑x / ↑↑n) * I =
            (2 * ↑π * ((↑k + ↑m) * ↑x / ↑↑n) * I) := by
    intros x
    ring_nf
  simp_rw [h₄]
  clear h₄
  sorry

lemma RuesDiffZ0EqualsIte (n : ℕ+) (m : ℤ) : RuesDiff n m 0 = ite ((n : ℤ) ∣ m) 1 0  := by
  sorry

lemma EqualsNthDerivRuesDiffSum (f : ℂ → ℂ) (n : ℕ+) : (f = iteratedDeriv n f) ↔ (f = ∑ k in range n, (λ(z : ℂ) => iteratedDeriv k f 0) * (RuesDiff n (-k))) := by
  sorry

lemma RuesNMthIteratedDeriv (n m : ℕ+) : iteratedDeriv m (Rues n) = RuesDiff n m := by
  rw [←RuesDiffM0EqualsRues, RuesDiffIteratedDeriv]
  simp only [add_zero]

lemma RuesDiffMod (n : ℕ+) (m : ℤ) : RuesDiff n m = RuesDiff n (m % n) := by
  sorry

lemma RuesDiffArgumentSumRule (n : ℕ+) (m : ℤ) (z₀ z₁ : ℂ) : RuesDiff n m (z₀ + z₁) = ∑ k in range n, (RuesDiff n k z₀ * RuesDiff n (m - k) z₁) := by
  sorry

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
    have h₁ : Nat.succ K = K + 1 := by
      exact rfl
    rw [h₁]
    have h₂ := zpow_add₀ I_ne_zero K 1
    simp only [zpow_coe_nat, zpow_one] at h₂
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
      ring
      congr
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
  simp only [Int.ofNat_eq_coe, Nat.cast_ofNat, Int.int_cast_ofNat, Nat.cast_one, Int.cast_one,
    one_div, exp_pi_mul_I, mul_neg, mul_one]
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
    rw [Inv.inv, instInvComplex, normSq]
    simp only [MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, ofReal_inv, ofReal_add, ofReal_mul,
      map_add, map_one, conj_I, add_re, one_re, I_re, add_zero, ofReal_one, mul_one, add_im, one_im,
      I_im, zero_add]
    ring_nf
  rw [h₃]
  clear h₃
  have h₄ : (1 - I)⁻¹ = (1 + I) / 2 := by
    rw [Inv.inv, instInvComplex, normSq]
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
  ring
