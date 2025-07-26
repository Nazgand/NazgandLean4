import Mathlib
set_option maxHeartbeats 0

def VandermondeMatrix {k : ℕ} (r : Fin k → ℂ)
  := Matrix.of (λ (y : Fin k) (x : Fin k) ↦ (r y) ^ x.val)

theorem InvertableVandermondeMatrix {k : ℕ} (h0 : k > 0) (r : Fin k → ℂ)
  (h1 : r.Injective) : (VandermondeMatrix r).det ≠ 0 := by
  sorry

noncomputable def PolynomialFromRoots {k : ℕ} (r : Fin k → ℂ) : Polynomial ℂ :=
  ∏ (k₀ : Fin k), (Polynomial.monomial 1 1 - Polynomial.monomial 0 (r k₀))

noncomputable def PolynomialFromCoeffs {k : ℕ} (c : Fin k → ℂ) : Polynomial ℂ :=
  ∑ (k₀ : Fin k), Polynomial.monomial k₀.val (c k₀)

def PolynomialFingerprintFromRoots {k : ℕ} (r : Fin k → ℂ) (p : Polynomial ℂ) :=
  Matrix.of (λ (y : Fin k) (_ : Fin 1) ↦ p.eval (r y))

theorem ModPolynomialFingerprintEqPolynomialFingerprint {k : ℕ} (r : Fin k → ℂ) (p : Polynomial ℂ) :
  PolynomialFingerprintFromRoots r (p.mod (PolynomialFromRoots r)) = PolynomialFingerprintFromRoots r p := by
  sorry

theorem ModPolynomialFromFingerprint {k : ℕ} (h0 : k > 0) (r : Fin k → ℂ) (h1 : r.Injective) (p : Polynomial ℂ) :
  p.mod (PolynomialFromRoots r) =
  PolynomialFromCoeffs (λ (k₀ : Fin k) ↦ ((VandermondeMatrix r)⁻¹ * PolynomialFingerprintFromRoots r p) k₀ (0 : Fin 1)) := by
  sorry
