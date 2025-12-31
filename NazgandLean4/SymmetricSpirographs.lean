import Mathlib
import NazgandLean4.IntegerInduction
set_option maxHeartbeats 0
open Complex Classical Real

-- Example Mathematica code to show a table of spirographs with 9-fold symmetry and 5 winding speed
-- g[t_,m_]:=FullSimplify[Sum[Exp[I*(9*k+5)*t]*1.5^-k ,{k,0,m}]]
-- Table[ParametricPlot[{Re[g[u,m]],Im[g[u,m]]}, {u, 0, 2 Pi}],{m,0,15}]

--declare a Set Of Complex Spirograph functions with k-fold symmetry with m winding speed.
def SetSpiro (k : ℕ+) (m : ℤ) :
  Set (ℂ → ℂ) := {f : (ℂ → ℂ) | ∀ (t : ℂ), f (t + 2 * π / k) = exp (I * 2 * m * π / k) * f t}

lemma SpiroLinearCombination {f₀ f₁} (k : ℕ+) (m : ℤ) (h₀ : f₀ ∈ SetSpiro k m) (h₁ : f₁ ∈ SetSpiro k m)
  (w₀ w₁ : ℂ) : (λ (t : ℂ) => w₀ * f₀ t + w₁ * f₁ t) ∈ SetSpiro k m := by
  simp [SetSpiro] at *
  intros t
  simp only [h₀, h₁]
  ring

lemma SpiroOffset {f₀} (k : ℕ+) (m : ℤ) (h₀ : f₀ ∈ SetSpiro k m)
  (o : ℂ) : (λ (t : ℂ) => f₀ (t + o)) ∈ SetSpiro k m := by
  simp [SetSpiro] at *
  intros t
  rw [(show t + 2 * ↑π / ↑↑k + o = (t + o) + 2 * ↑π / ↑↑k by ring), h₀]

lemma SpiroPseudoPeriodic {f₀} (k : ℕ+) (m : ℤ) (h₀ : f₀ ∈ SetSpiro k m)
  : ∀ (n : ℤ) (t : ℂ), f₀ (t + 2 * n * π / k) = exp (I * 2 * n * m * π / k) * f₀ t := by
  rw [IntegerInduction]
  simp [SetSpiro] at *
  constructor
  · use 0
    simp only [Int.cast_zero, mul_zero, zero_mul, zero_div, add_zero, Complex.exp_zero, one_mul,
      implies_true]
  · intros m₁
    constructor
    · intros h₁ t
      rw [(show t + 2 * (↑m₁ + 1) * ↑π / ↑↑k = t + 2 * ↑m₁ * ↑π / ↑↑k + 2 * ↑π / ↑↑k by ring), h₀, h₁]
      rw [(show (I * 2 * ↑m * ↑π / ↑↑k).exp * ((I * 2 * ↑m₁ * ↑m * ↑π / ↑↑k).exp * f₀ t) =
        (I * 2 * ↑m * ↑π / ↑↑k).exp * (I * 2 * ↑m₁ * ↑m * ↑π / ↑↑k).exp * f₀ t by ring), ←Complex.exp_add]
      ring_nf
    · intros h₁ t
      rw [(show t + 2 * ↑m₁ * ↑π / ↑↑k = (t - 2 * ↑π / ↑↑k) + 2 * (↑m₁ + 1) * ↑π / ↑↑k by ring), h₁]
      rw [(show f₀ t = f₀ ((t - 2 * ↑π / ↑↑k) + 2 * ↑π / ↑↑k) by ring_nf), h₀]
      rw [(show (I * 2 * ↑m₁ * ↑m * ↑π / ↑↑k).exp * ((I * 2 * ↑m * ↑π / ↑↑k).exp * f₀ (t - 2 * ↑π / ↑↑k)) =
        (I * 2 * ↑m₁ * ↑m * ↑π / ↑↑k).exp * (I * 2 * ↑m * ↑π / ↑↑k).exp * f₀ (t - 2 * ↑π / ↑↑k) by ring_nf), ←Complex.exp_add]
      ring_nf

lemma SpiroPeriodic {f₀} (k : ℕ+) (m : ℤ) (h₀ : f₀ ∈ SetSpiro k m) : ∀ (t : ℂ), f₀ (t + 2 * π) = f₀ t := by
  intros t
  have h₁ := SpiroPseudoPeriodic k m h₀ k t
  have h₂ : (2 : ℂ) * ↑↑↑k * ↑π / ↑↑k = 2 * ↑π := by
    field_simp
  simp only [Int.cast_natCast] at *
  rw [h₂] at h₁
  rw [h₁]
  have h₃ : I * 2 * ↑↑k * ↑m * ↑π / ↑↑k = ↑m * 2 * ↑π * I := by
    field_simp
  rw [h₃]
  have h₄ : (↑m * 2 * ↑π * I).exp = 1 := by
    rw [Complex.exp_eq_one_iff]
    use m
    ring
  rw [h₄]
  simp only [one_mul]

lemma SpiroPeriodic2 {f₀} (k : ℕ+) (m : ℤ) (h₀ : f₀ ∈ SetSpiro k m) : ∀ (t : ℂ), f₀ (t + 2 * π / (Int.gcd m k)) = f₀ t := by
  have h₂ : ↑(Int.gcd m k) ∣ (k : ℤ) := Int.gcd_dvd_right m ↑↑k
  obtain ⟨w, hw⟩ := h₂
  have h₁ := SpiroPseudoPeriodic k m h₀ w
  intros t
  specialize h₁ t
  have h₄ : (m.gcd ↑↑k : ℂ) ≠ 0 := by
    by_contra h₁₀
    simp only [Nat.cast_eq_zero] at h₁₀
    rw [Int.gcd_eq_zero_iff] at h₁₀
    obtain ⟨_, h₁₂⟩ := h₁₀
    simp only [Nat.cast_eq_zero, PNat.ne_zero] at h₁₂
  have h₃ : (w : ℂ) = ↑(k : ℤ) / ↑(m.gcd ↑↑k) := by
    nth_rw 1 [hw]
    simp only [Int.cast_mul, Int.cast_natCast]
    field_simp
  rw [h₃] at h₁
  simp only [Int.cast_natCast] at h₁
  have h₅ : (2 : ℂ) * (↑↑k / ↑(m.gcd ↑↑k)) * ↑π / ↑↑k = 2 * ↑π / ↑(m.gcd ↑↑k) := by
    field_simp
  rw [h₅] at h₁
  rw [h₁]
  have h₆ : (I * 2 * (↑↑k / ↑(m.gcd ↑↑k)) * ↑m * ↑π / ↑↑k) = (I * 2 * ↑m * ↑π / ↑(m.gcd ↑↑k)) := by
    field_simp
  rw [h₆]
  have h₇ : ↑(Int.gcd m k) ∣ m := Int.gcd_dvd_left m ↑↑k
  obtain ⟨w₂, hw₂⟩ := h₇
  nth_rw 1 [hw₂]
  have h₈ : I * 2 * ↑(↑(m.gcd ↑↑k) * w₂) * ↑π / ↑(m.gcd ↑↑k) = I * 2 * ↑π * ↑w₂ := by
    field_simp
    ring_nf
    simp only [Int.cast_mul, Int.cast_natCast]
  rw [h₈]
  suffices h₉ : (I * 2 * ↑π * ↑w₂).exp = 1
  rw [h₉]
  simp only [one_mul]
  rw [Complex.exp_eq_one_iff]
  use w₂
  ring_nf

lemma SimpleGeneralSpiro (k : ℕ+) (m : ℤ) (g : ℂ → ℂ)
  : (λ (t : ℂ) => exp (I * t * m) * g (exp (I * t * k))) ∈ SetSpiro k m := by
  simp [SetSpiro] at *
  intros t
  rw [(show I * (t + 2 * ↑π / ↑↑k) * ↑m = (I * 2 * ↑m * ↑π / ↑↑k) + (I * t * ↑m) by ring), Complex.exp_add]
  field_simp
  have h₀ : (I * (t * ↑↑k + 2 * ↑π)).exp = (I * t * ↑↑k).exp := by
    rw [(show I * (t * ↑↑k + 2 * ↑π) = I * t * ↑↑k + 2 * ↑π * I by ring), Complex.exp_add, Complex.exp_two_pi_mul_I]
    simp only [mul_one]
  rw [h₀]
  ring

lemma SetSpiroRelated {f₀} (k₀ k₁ : ℕ+) (m : ℤ) (h₀ : f₀ ∈ SetSpiro k₀ m) :
  (λ (t : ℂ) => (f₀ (t * k₁ / k₀)) ^ (k₀ : ℕ)) ∈ SetSpiro k₁ (m * k₁) := by
  simp [SetSpiro] at *
  intros t
  field_simp
  rw [(show (t * ↑↑k₁ + 2 * ↑π) / ↑↑k₀ = t * ↑↑k₁ / ↑↑k₀ + 2 * ↑π / ↑↑k₀ by ring), h₀, mul_pow, ←Complex.exp_nat_mul]
  congr 1
  congr 1
  ring_nf
  congr 1
  field_simp

lemma SetSpiroRelated2 {f₀} (k: ℕ+) (m₀ m₁ : ℤ) (h₀ : f₀ ∈ SetSpiro k m₀) :
  (λ (t : ℂ) => exp (I * t * (m₁ - m₀)) * (f₀ t)) ∈ SetSpiro k m₁ := by
  simp [SetSpiro] at *
  intros t
  rw [h₀]
  ring_nf
  rw [←Complex.exp_add, (show f₀ t * (I * ↑π * (↑↑k)⁻¹ * ↑m₁ * 2).exp * (I * t * ↑m₁ - I * t * ↑m₀).exp =
    f₀ t * ((I * ↑π * (↑↑k)⁻¹ * ↑m₁ * 2).exp * (I * t * ↑m₁ - I * t * ↑m₀).exp) by ring), ←Complex.exp_add]
  ring_nf
