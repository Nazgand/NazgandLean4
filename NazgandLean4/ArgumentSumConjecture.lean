-- Formalization of this conjecture https://github.com/Nazgand/NazgandMathBook/blob/master/ArgumentSumRulesFromHomogeneousLinearDifferentialEquationsOfConstantCoefficientsConjecture.pdf
import Mathlib
set_option maxHeartbeats 0
set_option diagnostics true
open Complex Classical BigOperators Finset Matrix Polynomial

-- throughout this file we have reused variable names
-- (n : ℕ+) -- n is the degree of the differential equation
-- (DiffEqCoeff : (Fin (n + 1)) → ℂ) -- coefficients of the differential equation

def LeadCoeffNonZero {n : ℕ+} (DiffEqCoeff : (Fin (n + 1)) → ℂ) : Prop := DiffEqCoeff n ≠ 0 -- needed to keep the degree equal to n

def IsDifferentialEquationSolution {n : ℕ+} (DiffEqCoeff : (Fin (n + 1)) → ℂ) (f : ℂ → ℂ) : Prop := --checks whether a given function is a solution
  ContDiff ℂ ⊤ f ∧ ∀ (z : ℂ), 0 = ∑ k in range ↑(n + 1), (DiffEqCoeff k) * (iteratedDeriv k f z)

def SetOfSolutions {n : ℕ+} (DiffEqCoeff : (Fin (n + 1)) → ℂ) : Set (ℂ → ℂ) := {h : ℂ → ℂ | IsDifferentialEquationSolution DiffEqCoeff h}

-- the n different g functions are a basis of the set of solutions
def GBasis {n : ℕ+} (DiffEqCoeff : (Fin (n + 1)) → ℂ) (g : (Fin n) → ℂ → ℂ) : Prop := SetOfSolutions DiffEqCoeff = {h : ℂ → ℂ | ∃ (b : (Fin n) → ℂ), h = λ (z : ℂ) => ∑ k in range ↑n, b k * g k z}

-- the column vector of the functions in g
def v {n : ℕ+} (g : (Fin n) → ℂ → ℂ) (z : ℂ) : Matrix (Fin n) (Fin 1) ℂ := of λ (y : Fin n) (_ : Fin 1) => g y z

-- simplify the shifted iterated derivative
lemma ShiftedIteratedDerivative (k : ℕ) (z₁ : ℂ) {f : ℂ → ℂ} (h₀ : ContDiff ℂ ⊤ f) : iteratedDeriv k (fun z₀ => f (z₀ + z₁)) = (fun z₀ => iteratedDeriv k f (z₀ + z₁)) := by
  induction' k with K Kih
  · simp only [iteratedDeriv_zero]
  · rw [iteratedDeriv_succ, Kih]
    ext z
    let h₂ := iteratedDeriv K f
    let h := fun z₀ => (z₀ + z₁)
    have hh₂ : DifferentiableAt ℂ h₂ (h z) := by
      refine Differentiable.differentiableAt ?h
      refine ContDiff.differentiable_iteratedDeriv' ?h.hf
      have hktop : (↑K + 1 : ℕ∞) ≤ ⊤ := by
        sorry
      exact ContDiff.of_le h₀ hktop
    have hh : DifferentiableAt ℂ h z := by
      refine DifferentiableAt.add_const ?hf z₁
      exact differentiableAt_id'
    have hcomp := deriv.comp z hh₂ hh
    have hrwh₂ : h₂ = iteratedDeriv K f := by exact rfl
    have hrwh : h = fun z₀ => z₀ + z₁ := by exact rfl
    rw [hrwh₂, hrwh] at hcomp
    simp only [differentiableAt_id', differentiableAt_const, deriv_add, deriv_id'', deriv_const',
      add_zero, mul_one, ←iteratedDeriv_succ] at hcomp
    rw [←hcomp]
    rfl

-- A solution with input shifted by a constant z₁ is still a solution
lemma ShiftedSolution {n : ℕ+} {DiffEqCoeff : (Fin (n + 1)) → ℂ} {f : ℂ → ℂ} (z₁ : ℂ) (h₀ : f ∈ SetOfSolutions DiffEqCoeff) :
  (λ (z₀ : ℂ) => f (z₀ + z₁)) ∈ SetOfSolutions DiffEqCoeff := by
  unfold SetOfSolutions
  unfold SetOfSolutions at h₀
  simp only [Set.mem_setOf_eq]
  simp only [Set.mem_setOf_eq] at h₀
  unfold IsDifferentialEquationSolution
  unfold IsDifferentialEquationSolution at h₀
  rcases h₀ with ⟨h₁, h₂⟩
  constructor
  · refine Differentiable.contDiff ?left.hf
    unfold Differentiable
    sorry
  · sorry

-- This lemma will be useful to help solve the conjecture by allowing one to transform the arbitrary basis to a basis of one's choice
-- Note the matric C is invertable because this lemma goes both from g₀ to g₁ and from g₁ to g₀.
lemma BasisMatrixImageOfBasis {n : ℕ+} {DiffEqCoeff : (Fin (n + 1)) → ℂ} (h₀ : LeadCoeffNonZero DiffEqCoeff) (g₀ g₁ : (Fin n) → ℂ → ℂ) (h₁ : GBasis DiffEqCoeff g₀) (h₂ : GBasis DiffEqCoeff g₁) :
    ∃ (C : Matrix (Fin n) (Fin n) ℂ), (∀ z : ℂ, v g₀ z = C * v g₁ z) := by
  have h₃ : ∀ k : Fin ↑n, g₀ k ∈ SetOfSolutions DiffEqCoeff := by
    intros k
    rw [h₁]
    simp only [Set.mem_setOf_eq]
    use (λ k₀ : Fin ↑n => if k = k₀ then (1 : ℂ) else (0 : ℂ))
    simp only [ite_mul, one_mul, zero_mul]
    ext1 z
    simp only [sum_range, Fin.cast_val_eq_self, sum_ite_eq, mem_univ, ↓reduceIte]
  rw [h₂] at h₃
  simp only [Set.mem_setOf_eq] at h₃
  choose b hb using h₃
  use of λ (y : Fin n) (x : Fin n) => b y x
  intros z
  unfold v
  clear h₁ h₂ DiffEqCoeff h₀
  ext i j
  simp only [hb, ← Fin.sum_univ_eq_sum_range, Fin.cast_val_eq_self, of_apply, mul_apply]

-- Define the characteristic polynomial for the differential equation
noncomputable def CharacteristicPolynomial (n : ℕ+) (DiffEqCoeff : Fin (n + 1) → ℂ) : Polynomial ℂ :=
  ∑ k in range (n + 1), (C (DiffEqCoeff k)) * X^k

-- Define the set of roots of the characteristic polynomial
noncomputable def RootsOfCharacteristicPoly (n : ℕ+) (DiffEqCoeff : Fin (n + 1) → ℂ) : Multiset ℂ :=
  (CharacteristicPolynomial n DiffEqCoeff).roots

-- the simplified single basis asymmetric conjecture
theorem Asymm1BasisArgumentSumConjecture {n : ℕ+} {DiffEqCoeff : (Fin (n + 1)) → ℂ} (h₀ : LeadCoeffNonZero DiffEqCoeff) {f : ℂ → ℂ} (h₁ : IsDifferentialEquationSolution DiffEqCoeff f) :
    ∃ (g : (Fin n) → ℂ → ℂ) (A : Matrix (Fin n) (Fin n) ℂ), (GBasis DiffEqCoeff g) ∧ ∀ (z₀ z₁ : ℂ), ((of λ (_ _ : Fin 1) => f (z₀ + z₁)) = ((transpose (v g z₀)) * A * (v g z₁))) :=
  sorry

-- the simplified asymmetric conjecture
theorem AsymmArgumentSumConjecture {n : ℕ+} {DiffEqCoeff : (Fin (n + 1)) → ℂ} (h₀ : LeadCoeffNonZero DiffEqCoeff) {f : ℂ → ℂ} (h₁ : IsDifferentialEquationSolution DiffEqCoeff f) (g : (Fin n) → ℂ → ℂ) (h₂ : GBasis DiffEqCoeff g) :
    ∃ (A : Matrix (Fin n) (Fin n) ℂ), ∀ (z₀ z₁ : ℂ), ((of λ (_ _ : Fin 1) => f (z₀ + z₁)) = ((transpose (v g z₀)) * A * (v g z₁))) := by
  choose g₀ A₀ h₃ h₄ using Asymm1BasisArgumentSumConjecture h₀ h₁
  choose C hC using BasisMatrixImageOfBasis h₀ g₀ g h₃ h₂
  use Cᵀ * A₀ * C
  intros z₀ z₁
  rw [h₄, ←Matrix.mul_assoc, ←Matrix.mul_assoc]
  have h₅ := congrArg (λ B : Matrix (Fin ↑n) (Fin 1) ℂ => Bᵀ) (hC z₀)
  simp only [transpose_mul] at h₅
  rw [←h₅, Matrix.mul_assoc, Matrix.mul_assoc, hC z₁]
  simp only [Matrix.mul_assoc]

-- the full symmetric conjecture
theorem ArgumentSumConjecture {n : ℕ+} {DiffEqCoeff : (Fin (n + 1)) → ℂ} (h₀ : LeadCoeffNonZero DiffEqCoeff) {f : ℂ → ℂ} (h₁ : IsDifferentialEquationSolution DiffEqCoeff f) (g : (Fin n) → ℂ → ℂ) (h₂ : GBasis DiffEqCoeff g) :
    ∃ (A : Matrix (Fin n) (Fin n) ℂ), A = transpose A ∧ ∀ (z₀ z₁ : ℂ), ((of λ (_ _ : Fin 1) => f (z₀ + z₁)) = ((transpose (v g z₀)) * A * (v g z₁))) := by
  choose A₀ hA₀ using AsymmArgumentSumConjecture h₀ h₁ g h₂
  use (1 / 2 : ℂ) • (A₀ + (transpose A₀))
  constructor
  · ext i j
    simp only [one_div, smul_apply, add_apply, transpose_apply, smul_eq_mul, smul_add]
    ring
  · have hA₀2 : ∀ (z₀ z₁ : ℂ), (of fun _ _ => f (z₀ + z₁)) = (v g z₀)ᵀ * A₀ᵀ * v g z₁ := by
      intros z₁ z₀
      have h₃ := congrArg (λ B => Bᵀ) (hA₀ z₀ z₁)
      simp only [transpose_mul, transpose_transpose] at h₃
      have h₄ : (of fun (_ _ : Fin 1) => f (z₀ + z₁))ᵀ = (of fun _ _ => f (z₀ + z₁)) := by
        ext _ _
        simp only [transpose_apply, of_apply]
      rw [h₄] at h₃
      rw [(show z₁ + z₀ = z₀ + z₁ by ring), h₃]
      exact Eq.symm (Matrix.mul_assoc (v g z₁)ᵀ A₀ᵀ (v g z₀))
    have hA₀3 : ∀ (z₀ z₁ : ℂ), 2 • (of fun _ _ => f (z₀ + z₁)) = (v g z₀)ᵀ * (A₀ + A₀ᵀ) * v g z₁ := by
      intros z₀ z₁
      have h₃ := Mathlib.Tactic.LinearCombination.add_pf (hA₀ z₀ z₁) (hA₀2 z₀ z₁)
      have h₄ : (of fun _ _ => f (z₀ + z₁)) + (of fun _ _ => f (z₀ + z₁)) = 2 • (of fun (_ _ : Fin 1) => f (z₀ + z₁)) := by
        ext i j
        simp only [add_apply, of_apply, smul_apply, nsmul_eq_mul, Nat.cast_ofNat]
        ring
      rw [h₄] at h₃
      rw [h₃]
      have h₅ : (v g z₀)ᵀ * (A₀ + A₀ᵀ) = (v g z₀)ᵀ * A₀ + (v g z₀)ᵀ * A₀ᵀ := by
        exact Matrix.mul_add (v g z₀)ᵀ A₀ A₀ᵀ
      rw [h₅]
      exact Eq.symm (Matrix.add_mul ((v g z₀)ᵀ * A₀) ((v g z₀)ᵀ * A₀ᵀ) (v g z₁))
    have hA₀4 : ∀ (z₀ z₁ : ℂ), (of fun _ _ => f (z₀ + z₁)) = (1 / 2 : ℂ) • (v g z₀)ᵀ * (A₀ + A₀ᵀ) * v g z₁ := by
      intros z₀ z₁
      have h₃ := congrArg (λ (B : Matrix (Fin 1) (Fin 1) ℂ) => (1 / 2 : ℂ) • B) (hA₀3 z₀ z₁)
      simp only [one_div, smul_of, nsmul_eq_mul, Nat.cast_ofNat] at h₃
      have h₄ : (of ((2 : ℂ)⁻¹ • (2 * fun (_ _ : Fin 1) => f (z₀ + z₁)))) = (of fun _ _ => f (z₀ + z₁)) := by
        ext _ _
        simp only [of_apply, Pi.smul_apply, Pi.mul_apply, Pi.ofNat_apply, Nat.cast_ofNat,
          smul_eq_mul, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          IsUnit.inv_mul_cancel_left]
      rw [h₄] at h₃
      rw [h₃]
      simp only [one_div, smul_mul]
    intros z₀ z₁
    rw [hA₀4]
    congr 1
    rw [Matrix.mul_smul, Matrix.smul_mul]
