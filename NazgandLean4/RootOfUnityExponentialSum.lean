import Mathlib
set_option maxHeartbeats 0
open Complex Classical NormedSpace

lemma ExpTsumForm (z : ℂ) : exp z = tsum (λ (k : ℕ) => z ^ k / k.factorial) := by
  rw [exp_eq_exp_ℂ, exp_eq_tsum_div]

lemma ExpTaylorSeriesSummable (z : ℂ) : Summable (λ (k : ℕ) => z ^ k / k.factorial) := by
  exact expSeries_div_summable ℂ z

-- rues is the Root of Unity Exponential Sum function
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
