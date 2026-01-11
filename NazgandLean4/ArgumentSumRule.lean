/-
Formalization of this theorem (previously a conjecture)
https://github.com/Nazgand/NazgandMathBook/blob/master/ArgumentSumRulesFromHomogeneousLinearDifferentialEquationsOfConstantCoefficientsConjecture.pdf
-/
import Mathlib
set_option maxHeartbeats 0
open Finset Matrix

structure DiffEq where
  Degree : ℕ+
  Coeff : (Fin (Degree + 1)) → ℂ
  LeadCoeffNonZero : Coeff (Fin.ofNat (Degree + 1) Degree) ≠ 0

def DiffEq.IsSolution (DE : DiffEq) (f : ℂ → ℂ) : Prop :=
  ContDiff ℂ ⊤ f ∧ ∀ (z : ℂ), 0 =
  ∑ (k : (Fin (DE.Degree + 1))), (DE.Coeff k) * (iteratedDeriv k f z)

def DiffEq.SetOfSolutions (DE : DiffEq) : Set (ℂ → ℂ) := {h : ℂ → ℂ | DE.IsSolution h}

def DiffEq.IsVectorBasis (DE : DiffEq) (g : (Fin ↑DE.Degree) → ℂ → ℂ) : Prop :=
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

noncomputable def KeyDifferentialOperator (DE : DiffEq) (f : ℂ → ℂ) : ℂ → ℂ :=
  λ (z: ℂ) => ∑ (k : (Fin (DE.Degree + 1))), (DE.Coeff k) * (iteratedDeriv k f z)

theorem iteratedDerivSum {𝕜 : Type u} [NontriviallyNormedField 𝕜] {F : Type v}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {ι : Type u_1}
  {u : Finset ι} {A : ι → 𝕜 → F} (h : ∀ i ∈ u, ContDiff 𝕜 ⊤ (A i)) (k : ℕ) :
  iteratedDeriv k (fun y => Finset.sum u fun i => A i y) =
  (fun y => Finset.sum u fun i => iteratedDeriv k (A i) y) := by
  induction' k with K Kih
  · simp only [iteratedDeriv_zero]
  · have h₀ := congrArg deriv Kih
    rw [iteratedDeriv_succ, h₀]
    clear h₀
    ext x
    have h₁ : (1 : ℕ∞) ≤ ⊤ := OrderTop.le_top 1
    have h₂ : ∀ i ∈ u, DifferentiableAt 𝕜 (iteratedDeriv K (A i)) x := by
      intros i ih
      exact (ContDiff.differentiable_iteratedDeriv K (h i ih) (WithTop.coe_lt_top (K : ℕ∞))) x
    simp_rw [← Finset.sum_apply]
    rw [deriv_sum h₂]
    simp only [iteratedDeriv_succ, Finset.sum_apply]

theorem DiffEq_Solution_Analytic {DE : DiffEq} {f : ℂ → ℂ} (h : DE.IsSolution f) :
  AnalyticOnNhd ℂ f Set.univ := by
  rw [DiffEq.IsSolution] at h
  exact ContDiff.analyticOnNhd h.1

theorem DiffEq_Zero_IC_Implies_Zero {DE : DiffEq} {h : ℂ → ℂ} (h_sol : DE.IsSolution h)
    (h_ic : ∀ k : Fin ↑DE.Degree, iteratedDeriv k h 0 = 0) : h = 0 := by
  have h_ana : AnalyticAt ℂ h 0 := (DiffEq_Solution_Analytic h_sol) 0 trivial
  have h_derivs : ∀ k, iteratedDeriv k h 0 = 0 := by
    intro k
    induction' k using Nat.strong_induction_on with k ih
    if hk : k < DE.Degree then
      exact h_ic ⟨k, hk⟩
    else
      let m := k - DE.Degree
      have hm : m + DE.Degree = k := Nat.sub_add_cancel (Nat.le_of_not_lt hk)
      have h_ode := funext h_sol.2
      have h_diff_ode :
        iteratedDeriv m (fun z => ∑ j : Fin (DE.Degree + 1), DE.Coeff j * iteratedDeriv j h z) 0 = 0 := by
        rw [← h_ode]
        simp only [iteratedDeriv_const, ite_self]
      have h_smooth : ContDiff ℂ ⊤ h := by
        rw [← contDiffOn_univ]
        exact (DiffEq_Solution_Analytic h_sol).analyticOn.contDiffOn uniqueDiffOn_univ
      have h_iter_sum : iteratedDeriv m (fun z ↦ ∑ j : Fin (DE.Degree + 1), DE.Coeff j * iteratedDeriv j h z) =
                        fun z ↦ ∑ j : Fin (DE.Degree + 1), DE.Coeff j * iteratedDeriv (m + j) h z := by
        induction m with
        | zero =>
          ext z
          simp only [iteratedDeriv_zero, zero_add]
        | succ m₂ ih₂ =>
          ext z
          simp only [iteratedDeriv_succ]
          rw [ih₂]
          have h_diff : ∀ j, Differentiable ℂ (fun (w : ℂ) => DE.Coeff j * iteratedDeriv (m₂ + ↑j) h w) := by
            intro j
            apply Differentiable.const_mul
            apply h_smooth.differentiable_iteratedDeriv _ (WithTop.coe_lt_top _)
          have h_sum_eq : (fun z => ∑ j, DE.Coeff j * iteratedDeriv (m₂ + ↑j) h z) =
            ∑ j, (fun z => DE.Coeff j * iteratedDeriv (m₂ + ↑j) h z) := by
            ext
            simp only [Finset.sum_apply]
          rw [h_sum_eq, deriv_sum (fun j _ => (h_diff j).differentiableAt)]
          apply Finset.sum_congr rfl
          intro j _
          rw [deriv_const_mul]
          · congr 1
            simp only [add_right_comm, iteratedDeriv_succ]
          · apply (h_smooth.differentiable_iteratedDeriv _ (WithTop.coe_lt_top _)).differentiableAt
      have h_diff_ode' : ∑ j : Fin (DE.Degree + 1), DE.Coeff j * iteratedDeriv (m + j) h 0 = 0 := by
        rw [h_iter_sum] at h_diff_ode
        exact h_diff_ode
      rw [Fin.sum_univ_castSucc] at h_diff_ode'
      have h_lower : ∑ x : Fin ↑DE.Degree, DE.Coeff (Fin.castSucc x) * iteratedDeriv (m + x) h 0 = 0 := by
        apply Finset.sum_eq_zero
        intro x _
        apply mul_eq_zero_of_right
        apply ih
        rw [←hm]
        apply Nat.add_lt_add_left x.isLt
      simp only [Fin.val_castSucc, h_lower, Fin.val_last, zero_add] at h_diff_ode'
      rw [hm] at h_diff_ode'
      refine eq_zero_of_ne_zero_of_mul_left_eq_zero ?_ h_diff_ode'
      convert DE.LeadCoeffNonZero
      simp only [Fin.ofNat_eq_cast, Fin.natCast_eq_last]
  have h_ana_at : AnalyticAt ℂ h 0 := (DiffEq_Solution_Analytic h_sol) 0 trivial
  have hf_ser := h_ana_at.hasFPowerSeriesAt
  have h_ser_zero : FormalMultilinearSeries.ofScalars ℂ (fun n ↦ iteratedDeriv n h 0 / n.factorial) = 0 := by
    ext n
    simp only [h_derivs n, zero_div, FormalMultilinearSeries.ofScalars_eq_zero_of_scalar_zero,
      ContinuousMultilinearMap.zero_apply, FormalMultilinearSeries.zero_apply]
  have h_loc : h =ᶠ[nhds 0] 0 := by
    rw [h_ser_zero] at hf_ser
    exact hf_ser.eventually_eq_zero
  apply AnalyticOnNhd.eq_of_eventuallyEq (DiffEq_Solution_Analytic h_sol)
  exact analyticOnNhd_const
  exact h_loc

theorem BasisInSetOfSolutions {DE : DiffEq} (g : (Fin ↑DE.Degree) → ℂ → ℂ) (hg : DE.IsVectorBasis g) :
    ∀ j, g j ∈ DE.SetOfSolutions := by
  unfold DiffEq.IsVectorBasis at hg
  rw [hg.1]
  intro j
  use fun k => if k = j then 1 else 0
  simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ↓reduceIte]

theorem Wronskian_Invertible {DE : DiffEq} (g : (Fin ↑DE.Degree) → ℂ → ℂ) (hg : DE.IsVectorBasis g) :
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
    unfold DiffEq.IsVectorBasis at hg
    rw [hg.1]
    intro j
    simp only [Set.mem_setOf_eq]
    use (fun i => if i = j then 1 else 0)
    ext z
    simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ↓reduceIte]
  have h_f_zero_contdiff : ContDiff ℂ ⊤ f_zero := by
    apply ContDiff.sum
    intro i hi
    apply ContDiff.smul
    · exact contDiff_const
    · exact (h_sol_g i).1
  have h_f_zero_ode : ∀ z : ℂ, 0 = ∑ (k_1 : Fin (DE.Degree + 1)), DE.Coeff k_1 * iteratedDeriv k_1 f_zero z := by
    intro z
    dsimp only [f_zero]
    have h_smooth : ∀ i ∈ Finset.univ, ContDiff ℂ ⊤ (fun z => v i * g i z) :=
      fun i _ => ContDiff.mul contDiff_const (h_sol_g i).1
    simp only [iteratedDerivSum h_smooth]
    have h_comm : ∀ (n : ℕ) (i : Fin ↑DE.Degree) z,
        iteratedDeriv n (fun z => v i * g i z) z = v i * iteratedDeriv n (g i) z := by
      intro n i z
      exact iteratedDeriv_const_mul ((h_sol_g i).1.of_le le_top).contDiffAt (v i)
    simp_rw [h_comm, Finset.mul_sum]
    rw [Finset.sum_comm]
    symm
    apply sum_eq_zero
    intro j hj
    simp_rw [← mul_assoc, mul_comm _ (v j), mul_assoc]
    rw [← Finset.mul_sum]
    rw [← (h_sol_g j).2 z]
    simp only [mul_zero]
  have h_sol : DE.IsSolution f_zero := ⟨h_f_zero_contdiff, h_f_zero_ode⟩
  have h_ic : ∀ k : Fin ↑DE.Degree, iteratedDeriv k f_zero 0 = 0 := by
    intro k
    dsimp only [f_zero]
    have h_smooth : ∀ i ∈ Finset.univ, ContDiff ℂ ⊤ (fun z => v i * g i z) :=
      fun i _ => ContDiff.mul contDiff_const (h_sol_g i).1
    rw [iteratedDerivSum h_smooth]
    simp_rw [iteratedDeriv_const_mul ((h_sol_g _).1.of_le le_top).contDiffAt (v _), mul_comm (v _) _]
    exact congr_fun hv_eq k
  have h_fz : f_zero = 0 := DiffEq_Zero_IC_Implies_Zero h_sol h_ic
  rw [DiffEq.IsVectorBasis] at hg
  have h_span := hg.2 (fun _ => 0) v
  have h_lhs_zero : (fun z => ∑ k : Fin ↑DE.Degree, (0 : ℂ) * g k z) = (fun z => 0) := by
    ext z
    simp only [zero_mul, sum_const_zero]
  have h_rhs_f_zero : (fun z => ∑ k : Fin ↑DE.Degree, v k * g k z) = f_zero := rfl
  rw [h_lhs_zero, h_rhs_f_zero, h_fz] at h_span
  have h_v_zero : v = 0 := Eq.symm (h_span rfl)
  contradiction

noncomputable def ExtractedFunctions {DE : DiffEq} {f : ℂ → ℂ}
  (_ : f ∈ DE.SetOfSolutions) (g : (Fin ↑DE.Degree) → ℂ → ℂ) (_ : DE.IsVectorBasis g)
  (k : Fin ↑DE.Degree) (z₁ : ℂ) : ℂ :=
  let W : Matrix (Fin ↑DE.Degree) (Fin ↑DE.Degree) ℂ := Matrix.of fun i j => iteratedDeriv i (g j) 0
  let F : Fin ↑DE.Degree → ℂ := fun i => iteratedDeriv i f z₁
  (W⁻¹ *ᵥ F) k

theorem ExtractedFunctionsSpec {DE : DiffEq} {f : ℂ → ℂ} (hf : f ∈ DE.SetOfSolutions)
  (g : (Fin ↑DE.Degree) → ℂ → ℂ) (hg : DE.IsVectorBasis g) (z₀ z₁ : ℂ) :
  f (z₀ + z₁) = ∑ (k : (Fin ↑DE.Degree)), (ExtractedFunctions hf g hg k z₁) * g k z₀ := by
  let W : Matrix (Fin ↑DE.Degree) (Fin ↑DE.Degree) ℂ := Matrix.of fun i j => iteratedDeriv i (g j) 0
  let hW : IsUnit W.det := (isUnit_iff_isUnit_det W).mp (Wronskian_Invertible g hg)
  let F : Fin ↑DE.Degree → ℂ := fun i => iteratedDeriv i f z₁
  let C := fun k => ExtractedFunctions hf g hg k z₁
  have h_sys : W *ᵥ C = F := by
     dsimp only [C, ExtractedFunctions]
     rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv W hW, Matrix.one_mulVec]
  let h_rhs := fun z => ∑ k, C k * g k z
  have h_rhs_sol : h_rhs ∈ DE.SetOfSolutions := by
    rw [hg.1]
    simp only [Set.mem_setOf_eq]
    use C
  have h_lhs_sol : (fun z => f (z + z₁)) ∈ DE.SetOfSolutions := ShiftedSolution z₁ hf
  let Diff := (fun z => f (z + z₁)) - h_rhs
  have h_Diff_sol : Diff ∈ DE.SetOfSolutions := by
    rw [hg.1] at h_rhs_sol h_lhs_sol ⊢
    obtain ⟨b₁, hb₁⟩ := h_rhs_sol
    obtain ⟨b₂, hb₂⟩ := h_lhs_sol
    use b₂ - b₁
    ext z
    simp only [Pi.sub_apply, hb₁, hb₂, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, Diff]
  have h_Diff_IC : ∀ k : Fin ↑DE.Degree, iteratedDeriv k Diff 0 = 0 := by
    intro i
    dsimp only [Diff]
    rw [iteratedDeriv_sub ((ShiftedSolution z₁ hf).1.contDiffAt.of_le le_top) ((h_rhs_sol.1.contDiffAt).of_le le_top)]
    simp only [sub_eq_zero]
    rw [ShiftedIteratedDerivative i z₁ hf.1]
    dsimp only [h_rhs]
    simp only [zero_add]
    have h_iter_sum : iteratedDeriv i (fun z => ∑ k, C k * g k z) 0 =
        ∑ k, C k * iteratedDeriv i (g k) 0 := by
      have h_smooth : ∀ j ∈ Finset.univ, ContDiff ℂ ⊤ (fun z => C j * g j z) := by
        intro j _
        exact ContDiff.const_smul (C j) (BasisInSetOfSolutions g hg j).1
      rw [iteratedDerivSum h_smooth]
      apply Finset.sum_congr rfl
      intro k _
      exact iteratedDeriv_const_mul ((BasisInSetOfSolutions g hg k).1.of_le le_top).contDiffAt (C k)
    rw [h_iter_sum]
    have h_mat_mul : (W *ᵥ C) i = ∑ k, W i k * C k := rfl
    have h_lhs : iteratedDeriv i f z₁ = (W *ᵥ C) i := by rw [h_sys]
    rw [h_lhs, h_mat_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring_nf
    rw [mul_comm]
    congr
  have h_Diff_eq_zero := DiffEq_Zero_IC_Implies_Zero h_Diff_sol h_Diff_IC
  exact sub_eq_zero.mp (congrFun h_Diff_eq_zero z₀)

theorem ExtractedFunctionsDifferentiable {DE : DiffEq} {f : ℂ → ℂ}
  (hf : f ∈ DE.SetOfSolutions) (g : (Fin ↑DE.Degree) → ℂ → ℂ) (hg : DE.IsVectorBasis g)
  : ∀ (k : (Fin ↑DE.Degree)), Differentiable ℂ (ExtractedFunctions hf g hg k) := by
  let W : Matrix (Fin ↑DE.Degree) (Fin ↑DE.Degree) ℂ := Matrix.of fun i j => iteratedDeriv i (g j) 0
  have hW : IsUnit W := Wronskian_Invertible g hg
  rw [isUnit_iff_isUnit_det] at hW
  let W_inv := W.nonsingInvUnit hW
  have h_sol_g : ∀ j : Fin ↑DE.Degree, g j ∈ DE.SetOfSolutions := by
    unfold DiffEq.IsVectorBasis at hg
    rw [hg.1]
    intro j
    simp only [Set.mem_setOf_eq]
    use (fun k => if k = j then 1 else 0)
    simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ↓reduceIte]
  have h_lin_sys : ∀ z, W.mulVec (fun k => ExtractedFunctions hf g hg k z) =
    fun (j : Fin ↑DE.Degree) => iteratedDeriv (j : ℕ) f z := by
    intro z
    ext j
    have h_deriv := congr_fun (congr_arg (iteratedDeriv j)
      (funext (fun z₀ => ExtractedFunctionsSpec hf g hg z₀ z))) 0
    rw [ShiftedIteratedDerivative j z hf.1] at h_deriv
    simp only [zero_add] at h_deriv
    rw [h_deriv]
    rw [iteratedDerivSum]
    · dsimp only [mulVec]
      apply Finset.sum_congr rfl
      intro x _
      rw [iteratedDeriv_const_mul ((h_sol_g x).1.of_le le_top).contDiffAt]
      ring_nf
      exact CommMonoid.mul_comm (W j x) (ExtractedFunctions hf g hg x z)
    · intro i _
      apply ContDiff.smul
      · exact contDiff_const
      · exact (h_sol_g i).1
  intro k
  let f_vec := fun z (j : Fin ↑DE.Degree) => iteratedDeriv (j : ℕ) f z
  have h_diff_f_vec : ∀ j, Differentiable ℂ (fun z => f_vec z j) := by
    intro j
    exact hf.1.differentiable_iteratedDeriv j (WithTop.coe_lt_top _)
  have h_sol : (ExtractedFunctions hf g hg k) = fun z => ((W_inv⁻¹ : Units _).val.mulVec (f_vec z)) k := by
    ext z
    dsimp only [f_vec]
    rw [← h_lin_sys z]
    simp only [Matrix.mulVec_mulVec]
    have h0 : (W_inv⁻¹ : Units (Matrix (Fin ↑DE.Degree) (Fin ↑DE.Degree) ℂ)).val * W = 1 := by
      change (W_inv⁻¹ * W_inv).val = 1
      simp only [inv_mul_cancel, Units.val_one]
    rw [h0, Matrix.one_mulVec]
  rw [h_sol]
  dsimp only [mulVec, dotProduct]
  fun_prop

theorem AppliedDifferentialOperator {DE : DiffEq} {f : ℂ → ℂ}
  (hf : f ∈ DE.SetOfSolutions) (g : (Fin ↑DE.Degree) → ℂ → ℂ) (hg : DE.IsVectorBasis g) :
  ∀ (z₀ z₁ : ℂ), 0 = ∑ (k : (Fin ↑DE.Degree)),
  (KeyDifferentialOperator DE (ExtractedFunctions hf g hg k) z₁ * g k z₀) := by
  intros z₀ z₁
  have h₀ : 0 = KeyDifferentialOperator DE (fun z₁ => ∑ (k : (Fin ↑DE.Degree)),
    (ExtractedFunctions hf g hg k z₁) * g k z₀) z₁ := by
    have h₉ := congrArg (KeyDifferentialOperator DE) (funext (fun z₁ => ExtractedFunctionsSpec hf g hg z₀ z₁))
    unfold KeyDifferentialOperator at h₉ ⊢
    rw [show (fun z₁ => f (z₀ + z₁)) = (fun z₁ => f (z₁ + z₀)) by ring_nf] at h₉
    rw [← (congrFun h₉ z₁)]
    have h₅ := ShiftedSolution z₀ hf
    unfold DiffEq.SetOfSolutions DiffEq.IsSolution at h₅
    simp only [Set.mem_setOf_eq] at h₅
    exact h₅.2 z₁
  unfold KeyDifferentialOperator at h₀ ⊢
  have h_smooth : ∀ i ∈ Finset.univ, ContDiff ℂ ⊤ (fun z => ExtractedFunctions hf g hg i z * g i z₀) := by
    intro i _
    exact Differentiable.contDiff (Differentiable.mul_const
      (ExtractedFunctionsDifferentiable hf g hg i) (g i z₀))
  have h_iter_sum : ∀ (n : ℕ), iteratedDeriv n (fun z => ∑ k, ExtractedFunctions hf g hg k z * g k z₀) =
      fun z => ∑ k, iteratedDeriv n (fun z => ExtractedFunctions hf g hg k z * g k z₀) z := by
    intro n
    exact iteratedDerivSum (by
      intro i _
      exact Differentiable.contDiff
        (Differentiable.mul_const (ExtractedFunctionsDifferentiable hf g hg i) (g i z₀))) n
  simp_rw [h_iter_sum] at h₀
  have h_iter_const_mul : ∀ (n : ℕ) (k : Fin ↑DE.Degree),
      iteratedDeriv n (fun z => ExtractedFunctions hf g hg k z * g k z₀) =
      fun z => iteratedDeriv n (ExtractedFunctions hf g hg k) z * g k z₀ := by
    intro n k
    have h1 : (fun z => ExtractedFunctions hf g hg k z * g k z₀) =
              (fun z => g k z₀ * ExtractedFunctions hf g hg k z) := by
      ext z; ring
    rw [h1]
    ext z
    rw [iteratedDeriv_const_mul (((
      ExtractedFunctionsDifferentiable hf g hg k).contDiff.of_le le_top).contDiffAt (x := z))]
    ring
  simp_rw [h_iter_const_mul, Finset.sum_mul, Finset.mul_sum] at h₀ ⊢
  rw [Finset.sum_comm] at h₀
  convert h₀ using 2
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem ExtractedFunctionsAreSolutions {DE : DiffEq} {f : ℂ → ℂ} (hf : f ∈ DE.SetOfSolutions)
  (g : (Fin ↑DE.Degree) → ℂ → ℂ) (hg : DE.IsVectorBasis g) :
  ∀ (k : (Fin ↑DE.Degree)), (ExtractedFunctions hf g hg k) ∈ DE.SetOfSolutions := by
  intros k
  constructor
  · have h0 := ExtractedFunctionsDifferentiable hf g hg k
    exact Differentiable.contDiff h0
  · intros z
    have h1 : 0 = KeyDifferentialOperator DE (ExtractedFunctions hf g hg k) z := by
      have h0 := hg.2 (λ (k : (Fin ↑DE.Degree)) => 0)
        (λ (k : (Fin ↑DE.Degree)) => KeyDifferentialOperator DE (ExtractedFunctions hf g hg k) z)
      simp only [zero_mul, sum_const_zero] at h0
      have h1 : ((fun z₂ => 0) = fun z₂ => ∑ k : Fin ↑DE.Degree,
        KeyDifferentialOperator DE (ExtractedFunctions hf g hg k) z * g k z₂) := by
        ext z₀
        exact AppliedDifferentialOperator hf g hg z₀ z
      exact congrFun (h0 h1) k
    rw [KeyDifferentialOperator] at h1
    exact h1

noncomputable def MatrixEntries {DE : DiffEq} {f : ℂ → ℂ} (hf : f ∈ DE.SetOfSolutions)
  (g : (Fin ↑DE.Degree) → ℂ → ℂ) (hg : DE.IsVectorBasis g) (k : (Fin ↑DE.Degree)) :
  (Fin ↑DE.Degree) → ℂ :=
  let W : Matrix (Fin ↑DE.Degree) (Fin ↑DE.Degree) ℂ := Matrix.of fun i j => iteratedDeriv i (g j) 0
  let ek : Fin ↑DE.Degree → ℂ := fun i => iteratedDeriv i (ExtractedFunctions hf g hg k) 0
  (W⁻¹ *ᵥ ek)

theorem MatrixEntriesUse {DE : DiffEq} {f : ℂ → ℂ} (hf : f ∈ DE.SetOfSolutions)
  (g : (Fin ↑DE.Degree) → ℂ → ℂ) (hg : DE.IsVectorBasis g) (k : (Fin ↑DE.Degree)) :
  ExtractedFunctions hf g hg k = fun z₁ =>
  ∑ (k_1 : (Fin ↑DE.Degree)), (MatrixEntries hf g hg k) k_1 * g k_1 z₁ := by
  have hEk := ExtractedFunctionsAreSolutions hf g hg k
  ext z₁
  have h := ExtractedFunctionsSpec hEk g hg z₁ 0
  simp only [add_zero] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro j _
  congr 1

noncomputable def ArgumentSumRule2Matrix {DE : DiffEq} {f : ℂ → ℂ} (hf : f ∈ DE.SetOfSolutions)
  (g : (Fin ↑DE.Degree) → ℂ → ℂ) (hg : DE.IsVectorBasis g) :
  Matrix (Fin ↑DE.Degree) (Fin ↑DE.Degree) ℂ :=
  of λ (y : Fin ↑DE.Degree) (x : Fin ↑DE.Degree) => MatrixEntries hf g hg x y

-- the column vector of the functions in g
def Vec {n : ℕ+} (g : (Fin n) → ℂ → ℂ) (z : ℂ) :
  Matrix (Fin n) (Fin 1) ℂ := of λ (y : Fin n) (_ : Fin 1) => g y z

theorem ExistsUniqueArgumentSumRuleMatrix {DE : DiffEq} {f : ℂ → ℂ} (hf : f ∈ DE.SetOfSolutions)
  (g : (Fin ↑DE.Degree) → ℂ → ℂ) (hg : DE.IsVectorBasis g)
  (A : Matrix (Fin ↑DE.Degree) (Fin ↑DE.Degree) ℂ) : A = ArgumentSumRule2Matrix hf g hg ↔
  (∀ (z₀ z₁ : ℂ), ((of λ (_ _ : Fin 1) => f (z₀ + z₁)) =
    ((transpose (Vec g z₀)) * A * (Vec g z₁)))) := by
  have hExists : ∀ (z₀ z₁ : ℂ), ((of λ (_ _ : Fin 1) => f (z₀ + z₁)) =
    ((transpose (Vec g z₀)) * (ArgumentSumRule2Matrix hf g hg) * (Vec g z₁))) := by
    unfold ArgumentSumRule2Matrix
    intros z₀ z₁
    ext x y
    rw [Fin.fin_one_eq_zero y, Fin.fin_one_eq_zero x, Matrix.mul_apply, Vec, Vec]
    simp only [Fin.isValue, of_apply, mul_apply, transpose_apply]
    have h2 : f (z₀ + z₁) = ∑ (k : (Fin ↑DE.Degree)), ∑ (k_1 : (Fin ↑DE.Degree)),
      MatrixEntries hf g hg k k_1 * g k_1 z₀ * g k z₁ := by
      rw [add_comm]
      simp_rw [ExtractedFunctionsSpec hf g hg, MatrixEntriesUse, sum_mul]
    simp_rw [h2, Finset.sum_mul, mul_comm]
  constructor
  · intro hA
    simp only [hExists, hA, implies_true]
  · intro hA
    let B := ArgumentSumRule2Matrix hf g hg
    ext i j
    have h_bilinear_eq : ∀ z₀ z₁, ∑ k, ∑ l, g k z₀ * A k l * g l z₁ =
                                  ∑ k, ∑ l, g k z₀ * B k l * g l z₁ := by
      intros z₀ z₁
      have hA' := congr_fun (congr_fun (hA z₀ z₁) 0) 0
      have hB' := congr_fun (congr_fun (hExists z₀ z₁) 0) 0
      simp only [Fin.isValue, of_apply, Vec, mul_apply, transpose_apply, sum_mul] at hA' hB'
      rw [sum_comm, ← hA', sum_comm, ← hB']
    have h_inner_eq : ∀ k z₁, ∑ l, A k l * g l z₁ = ∑ l, B k l * g l z₁ := by
      intros k z₁
      have h := hg.2 (fun k' => ∑ l, A k' l * g l z₁) (fun k' => ∑ l, B k' l * g l z₁)
      have h_func_eq : (fun z₀ => ∑ k', (∑ l, A k' l * g l z₁) * g k' z₀) =
                       (fun z₀ => ∑ k', (∑ l, B k' l * g l z₁) * g k' z₀) := by
        ext z₀
        simp only [sum_mul]
        convert h_bilinear_eq z₀ z₁ using 2
        <;> (congr; exact (mul_rotate _ _ _).symm)
      exact congr_fun (h h_func_eq) k
    have h_entry_eq := hg.2 (fun l => A i l) (fun l => B i l) (by ext z₁; exact h_inner_eq i z₁)
    exact congr_fun h_entry_eq j

#print axioms ExistsUniqueArgumentSumRuleMatrix

theorem SymmetricArgumentSumRuleMatrix {DE : DiffEq} {f : ℂ → ℂ} (hf : f ∈ DE.SetOfSolutions)
  (g : (Fin ↑DE.Degree) → ℂ → ℂ) (hg : DE.IsVectorBasis g)
  (A : Matrix (Fin ↑DE.Degree) (Fin ↑DE.Degree) ℂ) : A = ArgumentSumRule2Matrix hf g hg →
  A = Aᵀ := by
  intro hA
  rw [hA]
  symm
  apply (ExistsUniqueArgumentSumRuleMatrix hf g hg (ArgumentSumRule2Matrix hf g hg)ᵀ).mpr
  intro z₀ z₁
  have hSwap := congrArg transpose
    ((ExistsUniqueArgumentSumRuleMatrix hf g hg (ArgumentSumRule2Matrix hf g hg)).mp (by rfl) z₁ z₀)
  have h1x1Transpose : ∀ (M : Matrix (Fin 1) (Fin 1) ℂ), M = Mᵀ := by
    intro M
    exact ext_iff_trace_mul_left.mpr (congrFun rfl)
  rw [← h1x1Transpose (of fun x x_1 => f (z₁ + z₀)), add_comm] at hSwap
  simp only [hSwap, Matrix.mul_assoc, transpose_mul, transpose_transpose]

#print axioms SymmetricArgumentSumRuleMatrix

theorem TensorProductBasisLinearIndependence (Dim : ℕ) {DE : DiffEq}
    (g : (Fin ↑DE.Degree) → ℂ → ℂ) (hg : DE.IsVectorBasis g)
    (c : (Fin Dim → Fin ↑DE.Degree) → ℂ)
    (hc : ∀ z : Fin Dim → ℂ, ∑ k, c k * ∏ j, g (k j) (z j) = 0) : c = 0 := by
  induction Dim with
  | zero =>
    ext k
    have hk : k = (fun i => i.elim0) := by ext i; exact i.elim0
    specialize hc (fun i => i.elim0)
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one] at hc
    have h_singleton : (Finset.univ : Finset (Fin 0 → Fin ↑DE.Degree)) = {fun i => i.elim0} := by
      ext x
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      ext i; exact i.elim0
    rw [h_singleton, Finset.sum_singleton] at hc
    rw [hk]
    exact hc
  | succ Dim₀ ih =>
    ext k
    have hk_decomp : k = Fin.cons (k 0) (k ∘ Fin.succ) := by
      ext j
      simp only [Fin.cons]
      cases j using Fin.cases with
      | zero => exact Fin.val_eq_of_eq rfl
      | succ j' => exact Fin.val_eq_of_eq rfl
    let c' : Fin ↑DE.Degree → (Fin Dim₀ → Fin ↑DE.Degree) → ℂ := fun i₀ k' => c (Fin.cons i₀ k')
    have h_decomp : ∀ w : Fin Dim₀ → ℂ, ∀ z₀ : ℂ,
        ∑ i, (∑ k', c' i k' * ∏ j', g (k' j') (w j')) * g i z₀ = 0 := by
      intro w z₀
      have hc_w := hc (Fin.cons z₀ w)
      have h_prod : ∀ k : Fin (Dim₀ + 1) → Fin ↑DE.Degree,
          ∏ j, g (k j) ((Fin.cons z₀ w : Fin (Dim₀ + 1) → ℂ) j) = g (k 0) z₀ * ∏ j', g (k (Fin.succ j')) (w j') := by
        intro k
        simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      have h_rearr : ∑ k, c k * (g (k 0) z₀ * ∏ j', g (k (Fin.succ j')) (w j')) =
                     ∑ k, (c k * ∏ j', g (k (Fin.succ j')) (w j')) * g (k 0) z₀ := by
        grind only
      let E : (Fin (Dim₀ + 1) → Fin ↑DE.Degree) ≃ Fin ↑DE.Degree × (Fin Dim₀ → Fin ↑DE.Degree) :=
        (Fin.consEquiv (fun _ => Fin ↑DE.Degree)).symm
      simp only [h_prod, h_rearr, ← Equiv.sum_comp E.symm, Equiv.symm_symm, Fin.consEquiv_apply,
        Fin.cons_succ, Fin.cons_zero, Fintype.sum_prod_type, E, ← Finset.sum_mul] at hc_w
      convert hc_w using 3
    have h_coeff_zero : ∀ i : Fin ↑DE.Degree, ∀ w : Fin Dim₀ → ℂ, ∑ k', c' i k' * ∏ j', g (k' j') (w j') = 0 := by
      intro i w
      have h_func_eq : (fun z => ∑ j, (∑ k', c' j k' * ∏ j', g (k' j') (w j')) * g j z) =
                       (fun z => ∑ j, (0 : ℂ) * g j z) := by
        simp only [zero_mul, Finset.sum_const_zero, h_decomp w]
      exact congrFun (hg.2 (fun j => ∑ k', c' j k' * ∏ j', g (k' j') (w j')) (fun _ => 0) h_func_eq) i
    have h_c'_zero : ∀ i : Fin ↑DE.Degree, c' i = 0 := by
      simp only [ih (c' _) (h_coeff_zero _), implies_true]
    simp only [c'] at h_c'_zero
    rw [hk_decomp]
    exact congrFun (h_c'_zero (k 0)) (k ∘ Fin.succ)

def PermuteFunctionsByReorderingInputs {α : Type} (Perm : Equiv.Perm α) (β : Type) :
  Equiv.Perm (α → β) := Perm.symm.arrowCongr (Equiv.refl β)

def IsArgumentSumRuleTensor (Dim : ℕ) {DE : DiffEq} {f : ℂ → ℂ} (_ : f ∈ DE.SetOfSolutions)
  (g : (Fin ↑DE.Degree) → ℂ → ℂ) (_ : DE.IsVectorBasis g)
  (Tensor : (Fin Dim → Fin ↑DE.Degree) → ℂ) : Prop :=
  (∀ (z : Fin Dim → ℂ), f (∑ (j : Fin Dim), (z j)) =
    ∑ (k : Fin Dim → Fin ↑DE.Degree), (Tensor k * ∏ (j : Fin Dim), (g (k j) (z j))))

noncomputable def ArgumentSumRuleTensor (Dim : ℕ) {DE : DiffEq} {f : ℂ → ℂ} (hf : f ∈ DE.SetOfSolutions)
    (g : (Fin ↑DE.Degree) → ℂ → ℂ) (hg : DE.IsVectorBasis g) : (Fin Dim → Fin ↑DE.Degree) → ℂ :=
  match Dim with
  | 0 => fun _ => f 0
  | Dim' + 1 =>
    let A := ArgumentSumRule2Matrix hf g hg
    let c_basis (j : Fin ↑DE.Degree) := ArgumentSumRuleTensor Dim' (BasisInSetOfSolutions g hg j) g hg
    fun k => ∑ j : Fin ↑DE.Degree, A (k (Fin.last Dim')) j * c_basis j (Fin.init k)

theorem ExistsUniqueArgumentSumRuleTensor (Dim : ℕ) {DE : DiffEq} {f : ℂ → ℂ} (hf : f ∈ DE.SetOfSolutions)
  (g : (Fin ↑DE.Degree) → ℂ → ℂ) (hg : DE.IsVectorBasis g) (T₀ : (Fin Dim → Fin ↑DE.Degree) → ℂ) :
  IsArgumentSumRuleTensor Dim hf g hg T₀ ↔ T₀ = ArgumentSumRuleTensor Dim hf g hg := by
  have hExist : IsArgumentSumRuleTensor Dim hf g hg (ArgumentSumRuleTensor Dim hf g hg) := by
    induction Dim generalizing f hf with
    | zero =>
      intro z
      simp only [ArgumentSumRuleTensor, Fin.sum_univ_zero, Fin.prod_univ_zero, mul_one, Fintype.sum_unique]
    | succ LowerDim IH =>
      unfold ArgumentSumRuleTensor
      intro z
      let A := (ArgumentSumRule2Matrix hf g hg)
      have h_scalar : ∀ z₀ z₁, f (z₀ + z₁) = ((Vec g z₀)ᵀ * A * Vec g z₁) 0 0 := by
        intros z₀ z₁
        exact congr_fun (congr_fun ((ExistsUniqueArgumentSumRuleMatrix hf g hg (ArgumentSumRule2Matrix hf g hg)).mp (by rfl) z₀ z₁) 0) 0
      let c_basis (j : Fin ↑DE.Degree) := ArgumentSumRuleTensor LowerDim (BasisInSetOfSolutions g hg j) g hg
      calc f (∑ i : Fin (LowerDim + 1), z i)
        = f ((∑ j : Fin LowerDim, z (Fin.castSucc j)) + z (Fin.last LowerDim)) := by
            rw [Fin.sum_univ_castSucc]
        _ = ((Vec g (z (Fin.last LowerDim)))ᵀ * A * Vec g (∑ j, z (Fin.castSucc j))) 0 0 := by
              rw [add_comm, h_scalar]
        _ = ∑ p, ∑ q, g p (z (Fin.last LowerDim)) * A p q * g q (∑ j, z (Fin.castSucc j)) := by
             simp only [Vec, Fin.isValue, mul_apply, transpose_apply, of_apply, sum_mul]
             exact sum_comm
        _ = ∑ p : Fin ↑DE.Degree, ∑ q : Fin ↑DE.Degree,
            g p (z (Fin.last LowerDim)) * A p q *
            (∑ k : Fin LowerDim → Fin ↑DE.Degree, c_basis q k * ∏ i, g (k i) (z (Fin.castSucc i))) := by
              apply Finset.sum_congr rfl
              intro p _
              apply Finset.sum_congr rfl
              intro q _
              rw [IH (BasisInSetOfSolutions g hg q) (c_basis q)]
        _ = ∑ k : Fin (LowerDim + 1) → Fin ↑DE.Degree,
            (∑ j : Fin ↑DE.Degree, A (k (Fin.last LowerDim)) j * c_basis j (Fin.init k)) *
            ∏ i : Fin (LowerDim + 1), g (k i) (z i) := by
              simp only [Finset.mul_sum]
              trans ∑ p : Fin ↑DE.Degree, ∑ k : Fin LowerDim → Fin ↑DE.Degree, ∑ q : Fin ↑DE.Degree,
                    g p (z (Fin.last LowerDim)) * A p q *
                    (c_basis q k * ∏ i : Fin LowerDim, g (k i) (z (Fin.castSucc i)))
              · apply Finset.sum_congr rfl
                intro p _
                rw [Finset.sum_comm]
              rw [Finset.sum_comm, ← Finset.sum_product']
              let e := @Fin.snocEquiv LowerDim (fun _ => Fin ↑DE.Degree)
              simp only [univ_product_univ]
              apply Finset.sum_bij (fun x _ => e (x.2, x.1))
              · simp only [mem_univ, imp_self, implies_true]
              · simp only [mem_univ, EmbeddingLike.apply_eq_iff_eq,
                Prod.mk.injEq, and_imp, forall_const, Prod.forall, forall_eq', Prod.mk.eta]
              · simp only [mem_univ, exists_const, Prod.exists, forall_const]
                intro Position
                let preimage := e.symm Position
                use preimage.2, preimage.1
                grind only [= Equiv.apply_symm_apply]
              · intro x _
                simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fin.snoc_last, Fin.init_snoc,
                  Fin.prod_univ_castSucc, Fin.snoc_castSucc, sum_mul, e]
                congr
                ext Edge
                ring
  have hUnique : ∀ (T₃ T₁ : (Fin Dim → Fin ↑DE.Degree) → ℂ)
  (hT₃ : IsArgumentSumRuleTensor Dim hf g hg T₃) (hT₁ : IsArgumentSumRuleTensor Dim hf g hg T₁), T₃ = T₁ := by
    intro T₃ T₁ hT₃ hT₁
    let c := T₃ - T₁
    have h_diff : ∀ z : Fin Dim → ℂ, ∑ k, c k * ∏ j, g (k j) (z j) = 0 := by
      intro z
      simp only [Pi.sub_apply, sub_mul, sum_sub_distrib, ← hT₃ z, ← hT₁ z, sub_self, c]
    have hc : c = 0 := TensorProductBasisLinearIndependence Dim g hg c h_diff
    grind only
  grind only

#print axioms ExistsUniqueArgumentSumRuleTensor

def SymmetricTensor {α : Type} {Dim Edge : ℕ} (Tensor : (Fin Dim → Fin Edge) → α) : Prop :=
    (∀ (Perm : Equiv.Perm (Fin Dim)) (Position : (Fin Dim → Fin Edge)),
     Tensor ((PermuteFunctionsByReorderingInputs Perm (Fin Edge)) Position) = Tensor Position)

theorem SymmetricArgumentSumRuleTensor (Dim : ℕ) {DE : DiffEq} {f : ℂ → ℂ} (hf : f ∈ DE.SetOfSolutions)
  (g : (Fin ↑DE.Degree) → ℂ → ℂ) (hg : DE.IsVectorBasis g) :
  SymmetricTensor (ArgumentSumRuleTensor Dim hf g hg) := by
  let PermutePositions := λ (PermuteAxes : Equiv.Perm (Fin Dim)) ↦
    (PermuteFunctionsByReorderingInputs PermuteAxes (Fin ↑DE.Degree))
  let SymmetryOfArgumentSumRuleTensor := λ (PermuteAxes : Equiv.Perm (Fin Dim)) ↦
    (PermuteFunctionsByReorderingInputs (PermutePositions PermuteAxes) ℂ) (ArgumentSumRuleTensor Dim hf g hg)
  have hSymmetryOfArgumentSumRuleTensorIsArgumentSumRuleTensor : ∀ (PermuteAxes : Equiv.Perm (Fin Dim)),
    SymmetryOfArgumentSumRuleTensor PermuteAxes = (ArgumentSumRuleTensor Dim hf g hg) := by
    intro PermuteAxes
    rw [← (ExistsUniqueArgumentSumRuleTensor Dim hf g hg (SymmetryOfArgumentSumRuleTensor PermuteAxes)),
      IsArgumentSumRuleTensor]
    intro z
    have hSpec : IsArgumentSumRuleTensor Dim hf g hg (ArgumentSumRuleTensor Dim hf g hg) := by
      grind only [ExistsUniqueArgumentSumRuleTensor]
    rw [IsArgumentSumRuleTensor] at hSpec
    specialize hSpec ((PermuteFunctionsByReorderingInputs PermuteAxes ℂ) z)
    have h0 : (∑ j, (PermuteFunctionsByReorderingInputs PermuteAxes ℂ) z j) = (∑ j, z j) := by
      rw [← Equiv.sum_comp PermuteAxes z]
      rfl
    rw [← h0, hSpec]
    simp_rw [SymmetryOfArgumentSumRuleTensor]
    rw [← Equiv.sum_comp (PermutePositions PermuteAxes)]
    congr
    ext Pos
    simp only [← Equiv.prod_comp PermuteAxes (λ (j : Fin Dim) ↦ g (Pos j) (z j))]
    rfl
  intro PermuteAxes Position
  nth_rw 2 [← hSymmetryOfArgumentSumRuleTensorIsArgumentSumRuleTensor PermuteAxes]
  rfl

#print axioms SymmetricArgumentSumRuleTensor
