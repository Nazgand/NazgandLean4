-- Formalization of this conjecture https://github.com/Nazgand/NazgandMathBook/blob/master/ArgumentSumRulesFromHomogeneousLinearDifferentialEquationsOfConstantCoefficientsConjecture.pdf
import Mathlib
set_option maxHeartbeats 0
open Complex Classical BigOperators Finset Matrix

variable (n : ℕ+) -- n is the degree of the differential equation
variable (a : (Fin (n + 1)) → ℂ) -- coefficients of the differential equation
def anNonZero : Prop := a n ≠ 0 -- needed to keep the degree equal to n

def IsDifferentiableEverywhere (f : ℂ → ℂ) : Prop := --checks whether a given function Is Differentiable Everywhere
  ∀ (z : ℂ), ∃ (f' : ℂ), HasDerivAt f f' z

def IsDifferentialEquationSolution (f : ℂ → ℂ) : Prop := --checks whether a given function is a solution
  IsDifferentiableEverywhere f ∧ ∀ (z : ℂ), 0 = ∑ k in range ↑(n + 1), (a k) * (iteratedDeriv k f z)

def SetOfSolutions : Set (ℂ → ℂ) := {h : ℂ → ℂ | IsDifferentialEquationSolution n a h}

variable (g : (Fin n) → ℂ → ℂ)
-- the n different g functions span the set of solutions
def GSpan : Prop := SetOfSolutions n a = {h : ℂ → ℂ | ∃ (b : (Fin n) → ℂ), h = λ (z : ℂ) => ∑ k in range ↑n, b k * g k z}

-- the column vector of the basis
def v (z : ℂ) : Matrix (Fin n) (Fin 1) ℂ := of λ (y : Fin n) (_ : Fin 1) => g y z

theorem ArgumentSumConjecture {f : ℂ → ℂ} (h₀ : anNonZero n a) (h₁ : IsDifferentialEquationSolution n a f) (h₂ : GSpan n a g) :
    ∃ (A : Matrix (Fin n) (Fin n) ℂ), ∀ (z₀ z₁ : ℂ), (f (z₀ + z₁) = ((transpose (v n g z₀)) * A * (v n g z₁)) 0 0 ∧ A = transpose A) :=
  sorry
