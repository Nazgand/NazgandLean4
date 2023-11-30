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

lemma RuesNEqualsExpSum (n : ℕ+) (z : ℂ) : Rues n z = (∑ m in range n, cexp (z * cexp (2 * π * (m / n) * I))) / n := by
  sorry

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
  sorry

lemma RuesN4EqualsCoshCosh (z : ℂ) : Rues 4 z = cosh (z / (1 + I)) * cosh (z / (1 - I)) := by
  sorry

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
  sorry

lemma RuesDiffMPeriodic (n : ℕ+) (m k : ℤ) : RuesDiff n m = RuesDiff n (m + k * n) := by
  sorry

lemma RuesDiffSumOfRuesDiff (n k : ℕ+) (m : ℤ) (z : ℂ) : RuesDiff n m z = ∑ k₀ in range k, RuesDiff (n * k) (n * k₀ + m) z := by
  sorry

lemma ExpSumOfRuesDiff (k : ℕ+) (z : ℂ) : exp z = ∑ k₀ in range k, RuesDiff k k₀ z := by
  sorry

lemma RuesArgumentSumRule (n : ℕ+) (z₀ z₁ : ℂ) : Rues n (z₀ + z₁) = ∑ k in range n, (RuesDiff n k z₀ * RuesDiff n (n - k) z₁) := by
  sorry

lemma RuesDiffNthIteratedDeriv (n : ℕ+) (m : ℤ) : iteratedDeriv n (RuesDiff n m) = RuesDiff n m := by
  sorry

lemma RuesDiffEqualsExpSum (n : ℕ+) (m : ℤ) (z : ℂ) : RuesDiff n m z = (∑ k₀ in range n, cexp (z * cexp (2 * π * (k₀ / n) * I) + m * 2 * π * (k₀ / n) * I)) / n := by
  sorry

lemma RuesDiffZ0EqualsIte (n : ℕ+) (m : ℤ) : RuesDiff n m 0 = ite ((n : ℤ) ∣ m) 1 0  := by
  sorry

lemma EqualsNthDerivRuesDiffSum (f : ℂ → ℂ) (n : ℕ+) : (f = iteratedDeriv n f) ↔ (f = ∑ k in range n, (λ(z : ℂ) => iteratedDeriv k f 0) * (RuesDiff n (-k))) := by
  sorry

lemma RuesNMthIteratedDeriv (n m : ℕ+) : iteratedDeriv m (Rues n) = RuesDiff n m := by
  sorry

lemma RuesDiffMod (n : ℕ+) (m : ℤ) : RuesDiff n m = RuesDiff n (m % n) := by
  sorry

lemma RuesDiffArgumentSumRule (n : ℕ+) (m : ℤ) (z₀ z₁ : ℂ) : RuesDiff n m (z₀ + z₁) = ∑ k in range n, (RuesDiff n k z₀ * RuesDiff n (m - k) z₁) := by
  sorry
