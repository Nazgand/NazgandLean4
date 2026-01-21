import Mathlib
set_option maxHeartbeats 0
open Finset Matrix

-- HomogeneousLinearDifferentialEquationsOfConstantCoefficients
structure DiffEq where
  Degree : ℕ+
  Coeff : (Fin (Degree + 1)) → ℂ
  LeadCoeffNonZero : Coeff (Fin.ofNat (Degree + 1) Degree) ≠ 0

def DiffEq.IsSolution (DE : DiffEq) (f : ℂ → ℂ) : Prop :=
  ContDiff ℂ ⊤ f ∧ ∀ (z : ℂ), 0 =
  ∑ (k : (Fin (DE.Degree + 1))), (DE.Coeff k) * (iteratedDeriv k f z)

def DiffEq.SetOfSolutions (DE : DiffEq) : Set (ℂ → ℂ) := {h : ℂ → ℂ | DE.IsSolution h}

def DiffEq.IsBasis (DE : DiffEq) (g : (Fin ↑DE.Degree) → ℂ → ℂ) : Prop :=
  (DE.SetOfSolutions =
    {h : ℂ → ℂ | ∃ (b : (Fin ↑DE.Degree) → ℂ),
      h = λ (z : ℂ) => ∑ (k : (Fin ↑DE.Degree)), b k * g k z} ∧
    (∀ (b₀ b₁ : (Fin ↑DE.Degree) → ℂ),
      (λ (z : ℂ) => ∑ (k : (Fin ↑DE.Degree)), b₀ k * g k z) =
      (λ (z : ℂ) => ∑ (k : (Fin ↑DE.Degree)), b₁ k * g k z) → b₀ = b₁))

-- simplify the shifted iterated derivative
theorem ShiftedIteratedDerivative (k : ℕ) (z₁ : ℂ) {f : ℂ → ℂ} (h₀ : ContDiff ℂ ⊤ f) :
    iteratedDeriv k (fun z₀ => f (z₀ + z₁)) = (fun z₀ => iteratedDeriv k f (z₀ + z₁)) := by
  induction' k with K Kih
  · simp only [iteratedDeriv_zero]
  · rw [iteratedDeriv_succ, Kih]
    ext z
    let h₂ := iteratedDeriv K f
    let h := fun z₀ => (z₀ + z₁)
    have hh₂ : DifferentiableAt ℂ h₂ (h z) := by
      refine Differentiable.differentiableAt ?h
      exact (ContDiff.differentiable_iteratedDeriv K h₀ (WithTop.coe_lt_top (K : ℕ∞)))
    have hh : DifferentiableAt ℂ h z := by
      exact differentiableAt_id.add (differentiableAt_const z₁)
    have hcomp := deriv_comp z hh₂ hh
    have hrwh₂ : h₂ = iteratedDeriv K f := rfl
    have hrwh : h = fun z₀ => z₀ + z₁ := rfl
    rw [hrwh₂, hrwh] at hcomp
    simp only [← iteratedDeriv_succ, differentiableAt_fun_id,
      differentiableAt_const, deriv_fun_add,
      deriv_id'', deriv_const', add_zero, mul_one] at hcomp
    rw [←hcomp]
    rfl

-- A solution with input shifted by a constant z₁ is still a solution
theorem ShiftedSolution {DE : DiffEq} {f : ℂ → ℂ} (z₁ : ℂ) (hf : f ∈ DE.SetOfSolutions) :
  (λ (z₀ : ℂ) => f (z₀ + z₁)) ∈ DE.SetOfSolutions := by
  unfold DiffEq.SetOfSolutions at ⊢ hf
  simp only [Set.mem_setOf_eq] at ⊢ hf
  unfold DiffEq.IsSolution at ⊢ hf
  rcases hf with ⟨h₁, h₂⟩
  constructor
  · refine Differentiable.contDiff ?left.hf
    exact (h₁.differentiable (by simp)).comp (differentiable_id.add (differentiable_const z₁))
  · have hShID : ∀ (k : ℕ), (iteratedDeriv k fun z₀ => f (z₀ + z₁)) =
      fun z₀ => iteratedDeriv k f (z₀ + z₁) := by
      intros k
      rw [ShiftedIteratedDerivative k z₁ h₁]
    simp_rw [hShID]
    intros z₀
    exact h₂ (z₀ + z₁)

theorem BasisInSetOfSolutions {DE : DiffEq} (g : (Fin ↑DE.Degree) → ℂ → ℂ) (hg : DE.IsBasis g) :
    ∀ j, g j ∈ DE.SetOfSolutions := by
  unfold DiffEq.IsBasis at hg
  rw [hg.1]
  intro j
  use fun k => if k = j then 1 else 0
  simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ↓reduceIte]
