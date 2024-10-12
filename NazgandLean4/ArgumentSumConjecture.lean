-- Formalization of this conjecture https://github.com/Nazgand/NazgandMathBook/blob/master/ArgumentSumRulesFromHomogeneousLinearDifferentialEquationsOfConstantCoefficientsConjecture.pdf
import Mathlib
set_option maxHeartbeats 0
set_option pp.proofs true
open Complex Classical BigOperators Finset Matrix Polynomial

structure DiffEq where
  Degree : ℕ+
  Coeff : (Fin (Degree + 1)) → ℂ
  LeadCoeffNonZero : Coeff Degree ≠ 0

def DiffEq.IsSolution (de : DiffEq) (f : ℂ → ℂ) : Prop :=
  ContDiff ℂ ⊤ f ∧ ∀ (z : ℂ), 0 = ∑ k in range ↑(de.Degree + 1), (de.Coeff k) * (iteratedDeriv k f z)

def DiffEq.SetOfSolutions (de : DiffEq) : Set (ℂ → ℂ) := {h : ℂ → ℂ | de.IsSolution h}

def DiffEq.IsVectorBasis (de : DiffEq) (g : (Fin de.Degree) → ℂ → ℂ) : Prop :=
  (de.SetOfSolutions = {h : ℂ → ℂ | ∃ (b : (Fin de.Degree) → ℂ), h = λ (z : ℂ) => ∑ k in range de.Degree, b k * g k z} ∧
  ∀ m ∈ range de.Degree, ¬ (g m ∈ {h : ℂ → ℂ | ∃ (b : (Fin de.Degree) → ℂ), h = λ (z : ℂ) => ∑ k in (range de.Degree \ {m}), b k * g k z}))

-- the column vector of the functions in g
def v {n : ℕ+} (g : (Fin n) → ℂ → ℂ) (z : ℂ) : Matrix (Fin n) (Fin 1) ℂ := of λ (y : Fin n) (_ : Fin 1) => g y z

-- simplify the shifted iterated derivative
lemma ShiftedIteratedDerivative (k : ℕ) (z₁ : ℂ) {f : ℂ → ℂ} (h₀ : ContDiff ℂ ⊤ f) :
  iteratedDeriv k (fun z₀ => f (z₀ + z₁)) = (fun z₀ => iteratedDeriv k f (z₀ + z₁)) := by
  induction' k with K Kih
  · simp only [iteratedDeriv_zero]
  · rw [iteratedDeriv_succ, Kih]
    ext z
    let h₂ := iteratedDeriv K f
    let h := fun z₀ => (z₀ + z₁)
    have hh₂ : DifferentiableAt ℂ h₂ (h z) := by
      refine Differentiable.differentiableAt ?h
      refine ContDiff.differentiable_iteratedDeriv' ?h.hf
      exact ContDiff.of_le h₀ (OrderTop.le_top (↑K + 1 : ℕ∞))
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
lemma ShiftedSolution {de : DiffEq} {f : ℂ → ℂ} (z₁ : ℂ) (h₀ : f ∈ de.SetOfSolutions) :
  (λ (z₀ : ℂ) => f (z₀ + z₁)) ∈ de.SetOfSolutions := by
  unfold DiffEq.SetOfSolutions
  unfold DiffEq.SetOfSolutions at h₀
  simp only [Set.mem_setOf_eq]
  simp only [Set.mem_setOf_eq] at h₀
  unfold DiffEq.IsSolution
  unfold DiffEq.IsSolution at h₀
  rcases h₀ with ⟨h₁, h₂⟩
  constructor
  · refine Differentiable.contDiff ?left.hf
    refine Differentiable.comp' ?left.hf.hg ?left.hf.hf
    · have h1LeTop : (1 : ℕ∞) ≤ ⊤ := by exact OrderTop.le_top 1
      exact ContDiff.differentiable h₁ h1LeTop
    · refine (differentiable_add_const_iff z₁).mpr ?left.hf.hf.a
      exact differentiable_id'
  · have hShID : ∀ (k : ℕ), (iteratedDeriv k fun z₀ => f (z₀ + z₁)) = fun z₀ => iteratedDeriv k f (z₀ + z₁) := by
      intros k
      rw [ShiftedIteratedDerivative k z₁ h₁]
    simp_rw [hShID]
    intros z₀
    exact h₂ (z₀ + z₁)

noncomputable def ExtractedFunctionExists {de : DiffEq} {f : ℂ → ℂ} (h₁ : f ∈ de.SetOfSolutions)
  (g : (Fin de.Degree) → ℂ → ℂ) (h₂ : de.IsVectorBasis g) (z₁ : ℂ) :
  ∃ b : (Fin de.Degree → ℂ), (fun z₀ => f (z₀ + z₁)) = fun z => ∑ k ∈ range de.Degree, b ↑k * g (↑k) z := by
  have h₃ := ShiftedSolution z₁ h₁
  unfold DiffEq.IsVectorBasis at h₂
  rw [h₂.left] at h₃
  simp only [Set.mem_setOf_eq] at h₃
  exact h₃

noncomputable def ExtractedFunctions {de : DiffEq} {f : ℂ → ℂ} (h₁ : f ∈ de.SetOfSolutions)
  (g : (Fin de.Degree) → ℂ → ℂ) (h₂ : de.IsVectorBasis g) (k : Fin de.Degree) (z₁ : ℂ) : ℂ := by
  exact Classical.choose (ExtractedFunctionExists h₁ g h₂ z₁) ↑k

-- The convenient to define one
lemma ExtractedFunctionsUse0 {de : DiffEq} {f : ℂ → ℂ} (h₁ : f ∈ de.SetOfSolutions) (g : (Fin de.Degree) → ℂ → ℂ) (h₂ : de.IsVectorBasis g) (z₁ : ℂ) :
  (fun z₀ => f (z₀ + z₁)) = fun z₀ => ∑ k ∈ range ↑de.Degree, (ExtractedFunctions h₁ g h₂ ↑k z₁) * g (↑k) z₀ := by
  unfold ExtractedFunctions
  exact Classical.choose_spec (ExtractedFunctionExists h₁ g h₂ z₁)

-- The one we actually need
lemma ExtractedFunctionsUse1 {de : DiffEq} {f : ℂ → ℂ} (h₁ : f ∈ de.SetOfSolutions) (g : (Fin de.Degree) → ℂ → ℂ) (h₂ : de.IsVectorBasis g) (z₀ : ℂ) :
  (fun z₁ => f (z₀ + z₁)) = fun z₁ => ∑ k ∈ range de.Degree, (ExtractedFunctions h₁ g h₂ ↑k z₁) * g (↑k) z₀ := by
  ext z₁
  exact congrFun (ExtractedFunctionsUse0 h₁ g h₂ z₁) z₀
