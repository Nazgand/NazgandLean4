import Mathlib
import NazgandLean4.IntegerInduction
set_option maxHeartbeats 0
open Complex Classical Real

-- Example Mathematica code to show a table of spirographs with 9-fold symmetry and 5 winding speed
-- g[t_,m_]:=FullSimplify[Sum[Exp[I*(9*k+5)*t]*1.5^-k ,{k,0,m}]]
-- Table[ParametricPlot[{Re[g[u,m]],Im[g[u,m]]}, {u, 0, 2 Pi}],{m,0,15}]

--declare a Set Of Complex Spirograph functions with k-fold symmetry with m winding speed
def SetSpiro (k : ℕ+) (m : ℤ) (h : Int.gcd m k = 1) :
  Set (ℂ → ℂ) := {f : (ℂ → ℂ) | ∀ (t : ℂ), f (t + 2 * π / k) = exp (I * 2 * m * π / k) * f t}

lemma SpiroLinearCombination (k : ℕ+) (m : ℤ) (h : Int.gcd m k = 1) (h₀ : f₀ ∈ SetSpiro k m h) (h₁ : f₁ ∈ SetSpiro k m h)
  (w₀ w₁ : ℂ) : (λ (t : ℂ) => w₀ * f₀ t + w₁ * f₁ t) ∈ SetSpiro k m h := by
  simp [SetSpiro] at *
  intros t
  simp only [h₀, h₁]
  ring

lemma SpiroOffset (k : ℕ+) (m : ℤ) (h : Int.gcd m k = 1) (h₀ : f₀ ∈ SetSpiro k m h)
  (o : ℂ) : (λ (t : ℂ) => f₀ (t + o)) ∈ SetSpiro k m h := by
  simp [SetSpiro] at *
  intros t
  rw [(show t + 2 * ↑π / ↑↑k + o = (t + o) + 2 * ↑π / ↑↑k by ring), h₀]

lemma SpiroPseudoPeriodic (k : ℕ+) (m : ℤ) (h : Int.gcd m k = 1) (h₀ : f₀ ∈ SetSpiro k m h)
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

lemma SpiroPeriodic (k : ℕ+) (m : ℤ) (h : Int.gcd m k = 1) (h₀ : f₀ ∈ SetSpiro k m h) : ∀ (t : ℂ), f₀ (t + 2 * π) = f₀ t := by
  intros t
  have h₁ := SpiroPseudoPeriodic k m h h₀ k t
  have h₂ : (2 : ℂ) * ↑↑↑k * ↑π / ↑↑k = 2 * ↑π := by
    field_simp
    ring
  simp only [Int.cast_natCast] at *
  rw [h₂] at h₁
  rw [h₁]
  have h₃ : I * 2 * ↑↑k * ↑m * ↑π / ↑↑k = ↑m * 2 * ↑π * I := by
    field_simp
    ring
  rw [h₃]
  have h₄ : (↑m * 2 * ↑π * I).exp = 1 := by
    rw [Complex.exp_eq_one_iff]
    use m
    ring
  rw [h₄]
  simp only [one_mul]

lemma SimpleGeneralSpiro (k : ℕ+) (m : ℤ) (h : Int.gcd m k = 1) (g : ℂ → ℂ)
  : (λ (t : ℂ) => exp (I * t * m) * g (exp (I * t * k))) ∈ SetSpiro k m h := by
  simp [SetSpiro] at *
  intros t
  rw [(show I * (t + 2 * ↑π / ↑↑k) * ↑m = (I * 2 * ↑m * ↑π / ↑↑k) + (I * t * ↑m) by ring), Complex.exp_add]
  field_simp
  have h₀ : (I * (t * ↑↑k + 2 * ↑π)).exp = (I * t * ↑↑k).exp := by
    rw [(show I * (t * ↑↑k + 2 * ↑π) = I * t * ↑↑k + 2 * ↑π * I by ring), Complex.exp_add, Complex.exp_two_pi_mul_I]
    simp only [mul_one]
  rw [h₀]
  ring
