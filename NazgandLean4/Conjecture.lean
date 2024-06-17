-- Formalization of this conjecture https://github.com/Nazgand/NazgandMathBook/blob/master/ArgumentSumRulesFromHomogeneousLinearDifferentialEquationsOfConstantCoefficientsConjecture.pdf
import Mathlib
set_option maxHeartbeats 0
open Complex Classical BigOperators Finset Matrix

-- throughout this file we have reused variable names
-- (n : ℕ+) -- n is the degree of the differential equation
-- (DiffEqCoeff : (Fin (n + 1)) → ℂ) -- coefficients of the differential equation

def LeadCoeffNonZero {n : ℕ+} (DiffEqCoeff : (Fin (n + 1)) → ℂ) : Prop := DiffEqCoeff n ≠ 0 -- needed to keep the degree equal to n

def IsDifferentiableEverywhere (f : ℂ → ℂ) : Prop := --checks whether a given function Is Differentiable Everywhere
  ∀ (z : ℂ), ∃ (f' : ℂ), HasDerivAt f f' z

def IsDifferentialEquationSolution {n : ℕ+} (DiffEqCoeff : (Fin (n + 1)) → ℂ) (f : ℂ → ℂ) : Prop := --checks whether a given function is a solution
  IsDifferentiableEverywhere f ∧ ∀ (z : ℂ), 0 = ∑ k in range ↑(n + 1), (DiffEqCoeff k) * (iteratedDeriv k f z)

def SetOfSolutions {n : ℕ+} (DiffEqCoeff : (Fin (n + 1)) → ℂ) : Set (ℂ → ℂ) := {h : ℂ → ℂ | IsDifferentialEquationSolution DiffEqCoeff h}

-- the n different g functions span the set of solutions (and thus are a basis of the set of solutions)
def GSpan {n : ℕ+} (DiffEqCoeff : (Fin (n + 1)) → ℂ) (g : (Fin n) → ℂ → ℂ) : Prop := SetOfSolutions DiffEqCoeff = {h : ℂ → ℂ | ∃ (b : (Fin n) → ℂ), h = λ (z : ℂ) => ∑ k in range ↑n, b k * g k z}

-- the column vector of the functions in g
def v {n : ℕ+} (g : (Fin n) → ℂ → ℂ) (z : ℂ) : Matrix (Fin n) (Fin 1) ℂ := of λ (y : Fin n) (_ : Fin 1) => g y z

-- This lemma will be useful to help solve the conjecture by allowing one to transform the arbitrary basis to a basis of one's choice
-- Note the matric C is invertable because this lemma goes both from g₀ to g₁ and from g₁ to g₀.
lemma SpanMatrixImageOfSpan {n : ℕ+} {DiffEqCoeff : (Fin (n + 1)) → ℂ} (h₀ : LeadCoeffNonZero DiffEqCoeff) (g₀ g₁ : (Fin n) → ℂ → ℂ) (h₁ : GSpan DiffEqCoeff g₀) (h₂ : GSpan DiffEqCoeff g₁) :
    ∃ (C : Matrix (Fin n) (Fin n) ℂ), (∀ z : ℂ, v g₀ z = C * v g₁ z) := sorry

-- the actual conjecture
theorem ArgumentSumConjecture {n : ℕ+} {DiffEqCoeff : (Fin (n + 1)) → ℂ} (h₀ : LeadCoeffNonZero DiffEqCoeff) {f : ℂ → ℂ} (h₁ : IsDifferentialEquationSolution DiffEqCoeff f) (g : (Fin n) → ℂ → ℂ) (h₂ : GSpan DiffEqCoeff g) :
    ∃ (A : Matrix (Fin n) (Fin n) ℂ), ∀ (z₀ z₁ : ℂ), (f (z₀ + z₁) = ((transpose (v g z₀)) * A * (v g z₁)) 0 0 ∧ A = transpose A) :=
  sorry
