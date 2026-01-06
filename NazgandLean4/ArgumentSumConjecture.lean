-- Formalization of this conjecture https://github.com/Nazgand/NazgandMathBook/blob/master/ArgumentSumRulesFromHomogeneousLinearDifferentialEquationsOfConstantCoefficientsConjecture.pdf
import Mathlib
set_option maxHeartbeats 0
set_option pp.proofs true
open Complex Classical BigOperators Finset Matrix Polynomial

structure DiffEq where
  Degree : ℕ+
  Coeff : (Fin (Degree + 1)) → ℂ
  LeadCoeffNonZero : Coeff (Fin.ofNat (Degree + 1) Degree) ≠ 0

def DiffEq.IsSolution (de : DiffEq) (f : ℂ → ℂ) : Prop :=
  ContDiff ℂ ⊤ f ∧ ∀ (z : ℂ), 0 =
  ∑ (k : (Fin (de.Degree + 1))), (de.Coeff k) * (iteratedDeriv k f z)

def DiffEq.SetOfSolutions (de : DiffEq) : Set (ℂ → ℂ) := {h : ℂ → ℂ | de.IsSolution h}

def DiffEq.IsVectorBasis (de : DiffEq) (g : (Fin de.Degree) → ℂ → ℂ) : Prop :=
  (de.SetOfSolutions =
    {h : ℂ → ℂ | ∃ (b : (Fin de.Degree) → ℂ),
      h = λ (z : ℂ) => ∑ (k : (Fin de.Degree)), b k * g k z} ∧
    (∀ (b₀ b₁ : (Fin de.Degree) → ℂ),
      (λ (z : ℂ) => ∑ (k : (Fin de.Degree)), b₀ k * g k z) =
      (λ (z : ℂ) => ∑ (k : (Fin de.Degree)), b₁ k * g k z) → b₀ = b₁))

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
theorem ShiftedSolution {de : DiffEq} {f : ℂ → ℂ} (z₁ : ℂ) (h₀ : f ∈ de.SetOfSolutions) :
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
    exact (h₁.differentiable (by simp)).comp (differentiable_id.add (differentiable_const z₁))
  · have hShID : ∀ (k : ℕ), (iteratedDeriv k fun z₀ => f (z₀ + z₁)) =
      fun z₀ => iteratedDeriv k f (z₀ + z₁) := by
      intros k
      rw [ShiftedIteratedDerivative k z₁ h₁]
    simp_rw [hShID]
    intros z₀
    exact h₂ (z₀ + z₁)

theorem ExtractedFunctionExists {de : DiffEq} {f : ℂ → ℂ} (h₁ : f ∈ de.SetOfSolutions)
  (g : (Fin de.Degree) → ℂ → ℂ) (h₂ : de.IsVectorBasis g) (z₁ : ℂ) :
  ∃ b : (Fin de.Degree → ℂ), (fun z₀ => f (z₀ + z₁)) =
  fun z => ∑ (k : (Fin de.Degree)), b k * g k z := by
  have h₃ := ShiftedSolution z₁ h₁
  unfold DiffEq.IsVectorBasis at h₂
  rw [h₂.left] at h₃
  simp only [Set.mem_setOf_eq] at h₃
  exact h₃

noncomputable def ExtractedFunctions {de : DiffEq} {f : ℂ → ℂ}
  (h₁ : f ∈ de.SetOfSolutions) (g : (Fin de.Degree) → ℂ → ℂ) (h₂ : de.IsVectorBasis g)
  (k : Fin de.Degree) (z₁ : ℂ) : ℂ := by
  exact Classical.choose (ExtractedFunctionExists h₁ g h₂ z₁) k

-- The convenient to define one
theorem ExtractedFunctionsUse0 {de : DiffEq} {f : ℂ → ℂ} (h₁ : f ∈ de.SetOfSolutions)
  (g : (Fin de.Degree) → ℂ → ℂ) (h₂ : de.IsVectorBasis g) (z₁ : ℂ) :
  (fun z₀ => f (z₀ + z₁)) = fun z₀ => ∑ (k : (Fin de.Degree)),
   (ExtractedFunctions h₁ g h₂ k z₁) * g k z₀ := by
  exact Classical.choose_spec (ExtractedFunctionExists h₁ g h₂ z₁)

-- The one we actually need
theorem ExtractedFunctionsUse1 {de : DiffEq} {f : ℂ → ℂ} (h₁ : f ∈ de.SetOfSolutions)
  (g : (Fin de.Degree) → ℂ → ℂ) (h₂ : de.IsVectorBasis g) (z₀ : ℂ) :
  (fun z₁ => f (z₀ + z₁)) = fun z₁ => ∑ (k : (Fin de.Degree)),
   (ExtractedFunctions h₁ g h₂ k z₁) * g k z₀ := by
  ext z₁
  exact congrFun (ExtractedFunctionsUse0 h₁ g h₂ z₁) z₀

noncomputable def KeyDifferentialOperator (de : DiffEq) (f : ℂ → ℂ) : ℂ → ℂ :=
  λ (z: ℂ) => ∑ (k : (Fin (de.Degree + 1))), (de.Coeff k) * (iteratedDeriv k f z)

theorem AppliedDifferentialOperator0 {de : DiffEq} {f : ℂ → ℂ}
  (h₁ : f ∈ de.SetOfSolutions) (g : (Fin de.Degree) → ℂ → ℂ) (h₂ : de.IsVectorBasis g) :
  ∀ (z₀ z₁ : ℂ), 0 = KeyDifferentialOperator de (fun z₁ => ∑ (k : (Fin de.Degree)),
   (ExtractedFunctions h₁ g h₂ k z₁) * g k z₀) z₁ := by
  intros z₀ z₁
  have h₀ := congrArg (KeyDifferentialOperator de) (ExtractedFunctionsUse1 h₁ g h₂ z₀)
  unfold KeyDifferentialOperator at h₀
  have h₃ : (fun z₁ => f (z₀ + z₁)) = (fun z₁ => f (z₁ + z₀)) := by
    ext z₂
    ring_nf
  rw [h₃] at h₀
  clear h₃
  have h₄ := congrFun h₀ z₁
  clear h₀
  unfold KeyDifferentialOperator
  rw [←h₄]
  clear h₄
  have h₅ := ShiftedSolution z₀ h₁
  unfold DiffEq.SetOfSolutions at h₅
  unfold DiffEq.IsSolution at h₅
  simp only [Set.mem_setOf_eq] at h₅
  exact h₅.right z₁

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

theorem DiffEq_Solution_Analytic {de : DiffEq} {f : ℂ → ℂ} (h : de.IsSolution f) : AnalyticOnNhd ℂ f Set.univ := by
  rw [DiffEq.IsSolution] at h
  exact ContDiff.analyticOnNhd h.1

theorem DiffEq_Zero_IC_Implies_Zero {de : DiffEq} {h : ℂ → ℂ} (h_sol : de.IsSolution h)
    (h_ic : ∀ k : Fin de.Degree, iteratedDeriv k h 0 = 0) : h = 0 := by
  have h_ana : AnalyticAt ℂ h 0 := (DiffEq_Solution_Analytic h_sol) 0 trivial
  have h_derivs : ∀ k, iteratedDeriv k h 0 = 0 := by
    intro k
    induction' k using Nat.strong_induction_on with k ih
    if hk : k < de.Degree then
      exact h_ic ⟨k, hk⟩
    else
      let m := k - de.Degree
      have hm : m + de.Degree = k := Nat.sub_add_cancel (Nat.le_of_not_lt hk)
      have h_ode := funext h_sol.2
      have h_diff_ode : iteratedDeriv m (fun z => ∑ j : Fin (de.Degree + 1), de.Coeff j * iteratedDeriv j h z) 0 = 0 := by
        rw [← h_ode]
        simp only [iteratedDeriv_const, ite_self]
      have h_smooth : ContDiff ℂ ⊤ h := by
        rw [← contDiffOn_univ]
        exact (DiffEq_Solution_Analytic h_sol).analyticOn.contDiffOn uniqueDiffOn_univ
      have h_iter_sum : iteratedDeriv m (fun z ↦ ∑ j : Fin (de.Degree + 1), de.Coeff j * iteratedDeriv j h z) =
                        fun z ↦ ∑ j : Fin (de.Degree + 1), de.Coeff j * iteratedDeriv (m + j) h z := by
        induction m with
        | zero =>
          ext z
          simp only [iteratedDeriv_zero, zero_add]
        | succ m₂ ih₂ =>
          ext z
          simp only [iteratedDeriv_succ]
          rw [ih₂]
          have h_diff : ∀ j, Differentiable ℂ (fun (w : ℂ) => de.Coeff j * iteratedDeriv (m₂ + ↑j) h w) := by
            intro j
            apply Differentiable.const_mul
            apply h_smooth.differentiable_iteratedDeriv _ (WithTop.coe_lt_top _)
          have h_sum_eq : (fun z => ∑ j, de.Coeff j * iteratedDeriv (m₂ + ↑j) h z) = ∑ j, (fun z => de.Coeff j * iteratedDeriv (m₂ + ↑j) h z) := by
             ext
             simp only [Finset.sum_apply]
          rw [h_sum_eq, deriv_sum (fun j _ => (h_diff j).differentiableAt)]
          apply Finset.sum_congr rfl
          intro j _
          rw [deriv_const_mul]
          · congr 1
            simp only [add_right_comm, iteratedDeriv_succ]
          · apply (h_smooth.differentiable_iteratedDeriv _ (WithTop.coe_lt_top _)).differentiableAt
      have h_diff_ode' : ∑ j : Fin (de.Degree + 1), de.Coeff j * iteratedDeriv (m + j) h 0 = 0 := by
        rw [h_iter_sum] at h_diff_ode
        exact h_diff_ode
      rw [Fin.sum_univ_castSucc] at h_diff_ode'
      have h_lower : ∑ x : Fin de.Degree, de.Coeff (Fin.castSucc x) * iteratedDeriv (m + x) h 0 = 0 := by
        apply Finset.sum_eq_zero
        intro x _
        apply mul_eq_zero_of_right
        apply ih
        rw [←hm]
        apply Nat.add_lt_add_left x.isLt
      simp only [Fin.val_castSucc, h_lower, Fin.val_last, zero_add] at h_diff_ode'
      rw [hm] at h_diff_ode'
      refine eq_zero_of_ne_zero_of_mul_left_eq_zero ?_ h_diff_ode'
      convert de.LeadCoeffNonZero
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

theorem Wronskian_Invertible {de : DiffEq} (g : (Fin de.Degree) → ℂ → ℂ) (h_basis : de.IsVectorBasis g) :
    IsUnit (Matrix.of (fun (i j : Fin de.Degree) => iteratedDeriv i (g j) 0)) := by
  let W : Matrix (Fin de.Degree) (Fin de.Degree) ℂ :=
    Matrix.of (fun (i j : Fin de.Degree) => iteratedDeriv i (g j) 0)
  rw [isUnit_iff_isUnit_det]
  by_contra h_not_unit
  -- In a field, not IsUnit means zero determinant
  have h_det_zero : Matrix.det W = 0 := by
    rwa [isUnit_iff_ne_zero, not_not] at h_not_unit
  -- If the determinant is zero, there exists a non-zero vector v such that W * v = 0
  obtain ⟨v, hv_ne, hv_eq⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h_det_zero
  let f_zero := fun z => ∑ k, v k * g k z
  have h_sol_g : ∀ j : Fin de.Degree, g j ∈ de.SetOfSolutions := by
    unfold DiffEq.IsVectorBasis at h_basis
    rw [h_basis.left]
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
  have h_f_zero_ode : ∀ z : ℂ, 0 = ∑ (k_1 : Fin (de.Degree + 1)), de.Coeff k_1 * iteratedDeriv k_1 f_zero z := by
    intro z
    dsimp only [f_zero]
    have h_smooth : ∀ i ∈ Finset.univ, ContDiff ℂ ⊤ (fun z => v i * g i z) :=
      fun i _ => ContDiff.mul contDiff_const (h_sol_g i).1
    simp only [iteratedDerivSum h_smooth]
    have h_comm : ∀ (n : ℕ) (i : Fin de.Degree) z,
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
  have h_sol : de.IsSolution f_zero := ⟨h_f_zero_contdiff, h_f_zero_ode⟩
  have h_ic : ∀ k : Fin de.Degree, iteratedDeriv k f_zero 0 = 0 := by
    intro k
    dsimp only [f_zero]
    have h_smooth : ∀ i ∈ Finset.univ, ContDiff ℂ ⊤ (fun z => v i * g i z) :=
      fun i _ => ContDiff.mul contDiff_const (h_sol_g i).1
    rw [iteratedDerivSum h_smooth]
    simp_rw [iteratedDeriv_const_mul ((h_sol_g _).1.of_le le_top).contDiffAt (v _), mul_comm (v _) _]
    exact congr_fun hv_eq k
  have h_fz : f_zero = 0 := DiffEq_Zero_IC_Implies_Zero h_sol h_ic
  rw [DiffEq.IsVectorBasis] at h_basis
  have h_span := h_basis.2 (fun _ => 0) v
  have h_lhs_zero : (fun z => ∑ k : Fin de.Degree, (0 : ℂ) * g k z) = (fun z => 0) := by
    ext z
    simp only [zero_mul, sum_const_zero]
  have h_rhs_f_zero : (fun z => ∑ k : Fin de.Degree, v k * g k z) = f_zero := rfl
  rw [h_lhs_zero, h_rhs_f_zero, h_fz] at h_span
  have h_v_zero : v = 0 := Eq.symm (h_span rfl)
  contradiction

theorem ExtractedFunctionsDifferentiable0 {de : DiffEq} {f : ℂ → ℂ}
  (h₁ : f ∈ de.SetOfSolutions) (g : (Fin de.Degree) → ℂ → ℂ) (h₂ : de.IsVectorBasis g)
  : ∀ (k : (Fin de.Degree)), Differentiable ℂ (ExtractedFunctions h₁ g h₂ k) := by
  let W : Matrix (Fin de.Degree) (Fin de.Degree) ℂ := Matrix.of fun i j => iteratedDeriv i (g j) 0
  have hW : IsUnit W := Wronskian_Invertible g h₂
  rw [isUnit_iff_isUnit_det] at hW
  let W_inv := W.nonsingInvUnit hW
  have h_sol_g : ∀ j : Fin de.Degree, g j ∈ de.SetOfSolutions := by
    unfold DiffEq.IsVectorBasis at h₂
    rw [h₂.left]
    intro j
    simp only [Set.mem_setOf_eq]
    use (fun k => if k = j then 1 else 0)
    simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ↓reduceIte]
  have h_lin_sys : ∀ z, W.mulVec (fun k => ExtractedFunctions h₁ g h₂ k z) = fun (j : Fin de.Degree) => iteratedDeriv (j : ℕ) f z := by
    intro z
    ext j
    have h_eq := ExtractedFunctionsUse0 h₁ g h₂ z
    have h_deriv := congr_fun (congr_arg (iteratedDeriv j) h_eq) 0
    rw [ShiftedIteratedDerivative j z h₁.1] at h_deriv
    simp only [zero_add] at h_deriv
    rw [h_deriv]
    rw [iteratedDerivSum]
    · dsimp only [mulVec]
      apply Finset.sum_congr rfl
      intro x _
      rw [iteratedDeriv_const_mul ((h_sol_g x).1.of_le le_top).contDiffAt]
      ring_nf
      exact CommMonoid.mul_comm (W j x) (ExtractedFunctions h₁ g h₂ x z)
    · intro i _
      apply ContDiff.smul
      · exact contDiff_const
      · exact (h_sol_g i).1
  intro k
  let f_vec := fun z (j : Fin de.Degree) => iteratedDeriv (j : ℕ) f z
  have h_diff_f_vec : ∀ j, Differentiable ℂ (fun z => f_vec z j) := by
    intro j
    have h_smooth : ContDiff ℂ ⊤ f := h₁.1
    exact h_smooth.differentiable_iteratedDeriv j (WithTop.coe_lt_top _)
  have h_sol : (ExtractedFunctions h₁ g h₂ k) = fun z => ((W_inv⁻¹ : Units _).val.mulVec (f_vec z)) k := by
    ext z
    dsimp only [f_vec]
    rw [← h_lin_sys z]
    simp only [Matrix.mulVec_mulVec]
    have : (W_inv⁻¹ : Units (Matrix (Fin de.Degree) (Fin de.Degree) ℂ)).val * W = 1 := by
      change (W_inv⁻¹ * W_inv).val = 1
      simp only [inv_mul_cancel, Units.val_one]
    rw [this, Matrix.one_mulVec]
  rw [h_sol]
  dsimp only [mulVec, dotProduct]
  fun_prop

theorem ExtractedFunctionsDifferentiable1 {de : DiffEq} {f : ℂ → ℂ}
  (h₁ : f ∈ de.SetOfSolutions) (g : (Fin de.Degree) → ℂ → ℂ) (h₂ : de.IsVectorBasis g)
  (z₀ : ℂ) : ∀ (k : (Fin de.Degree)),
  ContDiff ℂ ⊤ (λ (z₁ : ℂ) => ((ExtractedFunctions h₁ g h₂ k z₁) * g k z₀)) := by
  intros k
  have h₀ := Differentiable.mul_const
    (ExtractedFunctionsDifferentiable0 h₁ g h₂ k) (g k z₀)
  exact Differentiable.contDiff h₀

theorem AppliedDifferentialOperator1 {de : DiffEq} {f : ℂ → ℂ}
  (h₁ : f ∈ de.SetOfSolutions) (g : (Fin de.Degree) → ℂ → ℂ) (h₂ : de.IsVectorBasis g) :
  ∀ (z₀ z₁ : ℂ), 0 = ∑ (k : (Fin de.Degree)),
  (KeyDifferentialOperator de (ExtractedFunctions h₁ g h₂ k) z₁ * g k z₀) := by
  sorry

theorem ExtractedFunctionsAreSolutions0 {de : DiffEq} {f : ℂ → ℂ}
  (h₁ : f ∈ de.SetOfSolutions) (g : (Fin de.Degree) → ℂ → ℂ) (h₂ : de.IsVectorBasis g) :
  ∀ (z₁ : ℂ) (k : (Fin de.Degree)),
  0 = KeyDifferentialOperator de (ExtractedFunctions h₁ g h₂ k) z₁ := by
  intros z₁ k
  have h0 := h₂.right (λ (k : (Fin de.Degree)) => 0)
    (λ (k : (Fin de.Degree)) => KeyDifferentialOperator de (ExtractedFunctions h₁ g h₂ k) z₁)
  simp only [zero_mul, sum_const_zero] at h0
  have h1 : ((fun z => 0) = fun z => ∑ k : Fin ↑de.Degree,
    KeyDifferentialOperator de (ExtractedFunctions h₁ g h₂ k) z₁ * g k z) := by
    ext z₀
    exact AppliedDifferentialOperator1 h₁ g h₂ z₀ z₁
  exact congrFun (h0 h1) k

theorem ExtractedFunctionsAreSolutions1 {de : DiffEq} {f : ℂ → ℂ} (h₁ : f ∈ de.SetOfSolutions)
  (g : (Fin de.Degree) → ℂ → ℂ) (h₂ : de.IsVectorBasis g) :
  ∀ (k : (Fin de.Degree)), (ExtractedFunctions h₁ g h₂ k) ∈ de.SetOfSolutions := by
  intros k
  rw [DiffEq.SetOfSolutions]
  simp only [Set.mem_setOf_eq]
  rw [DiffEq.IsSolution]
  constructor
  · have h0 := ExtractedFunctionsDifferentiable0 h₁ g h₂ k
    exact Differentiable.contDiff h0
  · intros z
    have h1 := ExtractedFunctionsAreSolutions0 h₁ g h₂ z k
    rw [KeyDifferentialOperator] at h1
    exact h1

theorem MatrixEntriesExist {de : DiffEq} {f : ℂ → ℂ} (h₁ : f ∈ de.SetOfSolutions)
  (g : (Fin de.Degree) → ℂ → ℂ) (h₂ : de.IsVectorBasis g) :
  ∀ (k : (Fin de.Degree)), ∃ (b : (Fin de.Degree) → ℂ),
  (ExtractedFunctions h₁ g h₂ k) = λ (z : ℂ) => ∑ (k : (Fin de.Degree)), b k * g k z := by
  intros k
  have h0 := ExtractedFunctionsAreSolutions1 h₁ g h₂ k
  have h1 := h₂
  rw [DiffEq.IsVectorBasis] at h1
  rw [h1.left] at h0
  simp only [Set.mem_setOf_eq] at h0
  exact h0

noncomputable def MatrixEntries {de : DiffEq} {f : ℂ → ℂ} (h₁ : f ∈ de.SetOfSolutions)
  (g : (Fin de.Degree) → ℂ → ℂ) (h₂ : de.IsVectorBasis g) (k : (Fin de.Degree)) :
  (Fin de.Degree) → ℂ := by
  exact Classical.choose (MatrixEntriesExist h₁ g h₂ k)

theorem MatrixEntriesUse {de : DiffEq} {f : ℂ → ℂ} (h₁ : f ∈ de.SetOfSolutions)
  (g : (Fin de.Degree) → ℂ → ℂ) (h₂ : de.IsVectorBasis g) (k : (Fin de.Degree)) :
  ExtractedFunctions h₁ g h₂ k = fun z₁ =>
  ∑ (k_1 : (Fin de.Degree)), (MatrixEntries h₁ g h₂ k) k_1 * g k_1 z₁ := by
  exact Classical.choose_spec (MatrixEntriesExist h₁ g h₂ k)

theorem ArgumentSumSumForm {de : DiffEq} {f : ℂ → ℂ} (h₁ : f ∈ de.SetOfSolutions)
  (g : (Fin de.Degree) → ℂ → ℂ) (h₂ : de.IsVectorBasis g) (z₀ z₁ : ℂ) :
  f (z₀ + z₁) = ∑ (k : (Fin de.Degree)), ∑ (k_1 : (Fin de.Degree)),
  MatrixEntries h₁ g h₂ k k_1 * g k_1 z₁ * g k z₀ := by
  have h0 := congrFun (ExtractedFunctionsUse1 h₁ g h₂ z₀) z₁
  rw [h0]
  congr
  ext k
  rw [MatrixEntriesUse h₁ g h₂ k]
  simp only
  exact sum_mul univ (fun i => MatrixEntries h₁ g h₂ k i * g i z₁) (g k z₀)

-- the column vector of the functions in g
def Vec {n : ℕ+} (g : (Fin n) → ℂ → ℂ) (z : ℂ) :
  Matrix (Fin n) (Fin 1) ℂ := of λ (y : Fin n) (_ : Fin 1) => g y z

theorem ArgumentSumMatrixForm {de : DiffEq} {f : ℂ → ℂ} (h₁ : f ∈ de.SetOfSolutions)
  (g : (Fin de.Degree) → ℂ → ℂ) (h₂ : de.IsVectorBasis g) :
  ∃ (A : Matrix (Fin de.Degree) (Fin de.Degree) ℂ),
  ∀ (z₀ z₁ : ℂ), ((of λ (_ _ : Fin 1) => f (z₀ + z₁)) =
    ((transpose (Vec g z₀)) * A * (Vec g z₁))) := by
  use of λ (y : Fin de.Degree) (x : Fin de.Degree) => MatrixEntries h₁ g h₂ x y
  intros z₀ z₁
  ext x y
  simp only [of_apply]
  have h0 : x = 0 := Fin.fin_one_eq_zero x
  have h1 : y = 0 := Fin.fin_one_eq_zero y
  rw [h1, h0, Matrix.mul_apply]
  simp_rw [Matrix.mul_apply]
  simp only [Fin.isValue, transpose_apply, of_apply]
  rw [Vec, Vec]
  simp only [Fin.isValue, of_apply]
  have h2 := ArgumentSumSumForm h₁ g h₂ z₁ z₀
  have h3 : (z₁ + z₀) = (z₀ + z₁) := AddCommMagma.add_comm z₁ z₀
  rw [h3] at h2
  rw [h2]
  congr
  ext k
  rw [Finset.sum_mul]
  congr
  ext m
  ring_nf

theorem ArgumentSumSymmetricMatrixForm {de : DiffEq} {f : ℂ → ℂ} (h₁ : f ∈ de.SetOfSolutions)
  (g : (Fin de.Degree) → ℂ → ℂ) (h₂ : de.IsVectorBasis g) :
  ∃ (A : Matrix (Fin de.Degree) (Fin de.Degree) ℂ), (A = transpose A ∧
    ∀ (z₀ z₁ : ℂ), ((of λ (_ _ : Fin 1) => f (z₀ + z₁)) =
    ((transpose (Vec g z₀)) * A * (Vec g z₁)))) := by
  sorry
