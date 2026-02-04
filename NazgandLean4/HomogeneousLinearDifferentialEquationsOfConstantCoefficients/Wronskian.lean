import Mathlib
import NazgandLean4.Calculus
import NazgandLean4.HomogeneousLinearDifferentialEquationsOfConstantCoefficients.Basic
open Finset Matrix

theorem Wronskian_Invertible {DE : DiffEq} (g : (Fin ↑DE.Degree) → ℂ → ℂ) (hg : DE.IsBasis g) :
    IsUnit (Matrix.of (fun (i j : Fin ↑DE.Degree) => iteratedDeriv i (g j) 0)) := by
  let W : Matrix (Fin ↑DE.Degree) (Fin ↑DE.Degree) ℂ :=
    Matrix.of (fun (i j : Fin ↑DE.Degree) => iteratedDeriv i (g j) 0)
  rw [isUnit_iff_isUnit_det]
  by_contra h_not_unit
  have h_det_zero : Matrix.det W = 0 := by
    rwa [isUnit_iff_ne_zero, not_not] at h_not_unit
  obtain ⟨v, hv_ne, hv_eq⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h_det_zero
  let f_zero := fun z => ∑ k, v k * g k z
  have h_sol_g : ∀ j : Fin ↑DE.Degree, g j ∈ DE.SetOfSolutions := by
    unfold DiffEq.IsBasis at hg
    rw [hg.1]
    intro j
    simp only [Set.mem_setOf_eq]
    use (fun i => if i = j then 1 else 0)
    ext z
    simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ↓reduceIte]
  have h_f_zero_contdiff : Differentiable ℂ f_zero := by
    dsimp only [f_zero]
    exact SumOfDifferentiableIsDifferentiable g (λ k ↦ (h_sol_g k).1) v
  have h_f_zero_ode : ∀ z : ℂ, 0 = ∑ (k_1 : Fin (DE.Degree + 1)), DE.Coeff k_1 * iteratedDeriv k_1 f_zero z := by
    intro z
    dsimp only [f_zero]
    have h_smooth : ∀ i ∈ Finset.univ, Differentiable ℂ (fun z => v i * g i z) :=
      fun i _ => Differentiable.const_mul (h_sol_g i).1 (v i)
    simp only [ComplexIteratedDerivSum (fun i hi => h_smooth i hi)]
    have h_comm : ∀ (n : ℕ) (i : Fin ↑DE.Degree) z,
        iteratedDeriv n (fun z => v i * g i z) z = v i * iteratedDeriv n (g i) z := by
      intro n i z
      exact iteratedDeriv_const_mul ((h_sol_g i).1.contDiff.of_le le_top).contDiffAt (v i)
    simp_rw [h_comm, Finset.mul_sum]
    rw [Finset.sum_comm]
    symm
    apply sum_eq_zero
    intro j hj
    simp_rw [← mul_assoc, mul_comm _ (v j), mul_assoc]
    rw [← Finset.mul_sum]
    have h_op : DE.KeyDifferentialOperator (g j) z = 0 := congr_fun (h_sol_g j).2 z
    change v j * DE.KeyDifferentialOperator (g j) z = 0
    rw [h_op, mul_zero]
  have h_sol : DE.IsSolution f_zero := ⟨h_f_zero_contdiff, funext fun z => (h_f_zero_ode z).symm⟩
  have h_ic : ∀ k : Fin ↑DE.Degree, iteratedDeriv k f_zero 0 = 0 := by
    intro k
    dsimp only [f_zero]
    have h_smooth : ∀ i ∈ Finset.univ, Differentiable ℂ (fun z => v i * g i z) :=
      fun i _ => Differentiable.const_mul (h_sol_g i).1 (v i)
    rw [ComplexIteratedDerivSum (fun i hi => h_smooth i hi)]
    simp_rw [iteratedDeriv_const_mul ((h_sol_g _).1.contDiff.of_le le_top).contDiffAt (v _), mul_comm (v _) _]
    exact congr_fun hv_eq k
  have h_fz : f_zero = 0 := DiffEq_Zero_IC_Implies_Zero h_sol h_ic
  rw [DiffEq.IsBasis] at hg
  have h_span := hg.2 (fun _ => 0) v
  have h_lhs_zero : (fun z => ∑ k : Fin ↑DE.Degree, (0 : ℂ) * g k z) = (fun z => 0) := by
    ext z
    simp only [zero_mul, sum_const_zero]
  have h_rhs_f_zero : (fun z => ∑ k : Fin ↑DE.Degree, v k * g k z) = f_zero := rfl
  rw [h_lhs_zero, h_rhs_f_zero, h_fz] at h_span
  have h_v_zero : v = 0 := Eq.symm (h_span rfl)
  contradiction
