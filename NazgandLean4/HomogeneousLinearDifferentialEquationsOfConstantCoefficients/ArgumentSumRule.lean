/-
Formalization of this theorem (previously a conjecture)
https://GitHub.Com/Nazgand/NazgandMathBook/blob/master/PDFs/ArgumentSumRulesFromHomogeneousLinearDifferentialEquationsOfConstantCoefficients.pdf
-/
import Mathlib
import NazgandLean4.Calculus
import NazgandLean4.HomogeneousLinearDifferentialEquationsOfConstantCoefficients.Basic
import NazgandLean4.HomogeneousLinearDifferentialEquationsOfConstantCoefficients.Wronskian
set_option maxHeartbeats 0
open Finset Matrix

noncomputable def ExtractedFunctions {DE : DiffEq} {f : ℂ → ℂ}
  (_ : f ∈ DE.SetOfSolutions) (g : (Fin ↑DE.Degree) → ℂ → ℂ) (_ : DE.IsBasis g)
  (k : Fin ↑DE.Degree) (z₁ : ℂ) : ℂ :=
  let W : Matrix (Fin ↑DE.Degree) (Fin ↑DE.Degree) ℂ := Matrix.of fun i j => iteratedDeriv i (g j) 0
  let F : Fin ↑DE.Degree → ℂ := fun i => iteratedDeriv i f z₁
  (W⁻¹ *ᵥ F) k

theorem ExtractedFunctionsSpec {DE : DiffEq} {f : ℂ → ℂ} (hf : f ∈ DE.SetOfSolutions)
  (g : (Fin ↑DE.Degree) → ℂ → ℂ) (hg : DE.IsBasis g) (z₀ z₁ : ℂ) :
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
    rw [iteratedDeriv_sub ((ShiftedSolution z₁ hf).1.contDiff.contDiffAt) (h_rhs_sol.1.contDiff.contDiffAt)]
    simp only [sub_eq_zero]
    rw [ShiftedIteratedDerivative i z₁ hf.1]
    dsimp only [h_rhs]
    simp only [zero_add]
    have h_iter_sum : iteratedDeriv i (fun z => ∑ k, C k * g k z) 0 =
        ∑ k, C k * iteratedDeriv i (g k) 0 :=
      ComplexIteratedDerivSumConstMul g (fun k => (BasisInSetOfSolutions g hg k).1) C i 0
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
  (hf : f ∈ DE.SetOfSolutions) (g : (Fin ↑DE.Degree) → ℂ → ℂ) (hg : DE.IsBasis g)
  : ∀ (k : (Fin ↑DE.Degree)), Differentiable ℂ (ExtractedFunctions hf g hg k) := by
  let W : Matrix (Fin ↑DE.Degree) (Fin ↑DE.Degree) ℂ := Matrix.of fun i j => iteratedDeriv i (g j) 0
  have hW : IsUnit W := Wronskian_Invertible g hg
  rw [isUnit_iff_isUnit_det] at hW
  let W_inv := W.nonsingInvUnit hW
  have h_sol_g : ∀ j : Fin ↑DE.Degree, g j ∈ DE.SetOfSolutions := by
    unfold DiffEq.IsBasis at hg
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
    rw [ComplexIteratedDerivSumConstMul g (fun k => (h_sol_g k).1) (fun k => ExtractedFunctions hf g hg k z) j 0]
    dsimp only [mulVec, of_apply, W]
    apply Finset.sum_congr rfl
    intro x _
    ring
  intro k
  let f_vec := fun (j : Fin ↑DE.Degree) (z : ℂ) => iteratedDeriv (j : ℕ) f z
  have h_diff_f_vec : ∀ j, Differentiable ℂ (f_vec j) := by
    intro j
    have h_cont_diff : ContDiff ℂ ((j : ℕ) + 1) f := (DiffEqSolutionAnalytic hf).contDiff.of_le le_top
    exact h_cont_diff.differentiable_iteratedDeriv (j : ℕ) (Nat.cast_lt.mpr (Nat.lt_succ_self j))
  have h_sol : (ExtractedFunctions hf g hg k) = fun z => ((W_inv⁻¹ : Units _).val.mulVec (fun j => f_vec j z)) k := by
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
  exact SumOfDifferentiableIsDifferentiable f_vec h_diff_f_vec (fun i => (W_inv⁻¹ : Units _).val k i)

theorem AppliedDifferentialOperator {DE : DiffEq} {f : ℂ → ℂ}
  (hf : f ∈ DE.SetOfSolutions) (g : (Fin ↑DE.Degree) → ℂ → ℂ) (hg : DE.IsBasis g) :
  ∀ (z₀ z₁ : ℂ), 0 = ∑ (k : (Fin ↑DE.Degree)),
  (DE.KeyDifferentialOperator (ExtractedFunctions hf g hg k) z₁ * g k z₀) := by
  intros z₀ z₁
  have h₀ : 0 = DE.KeyDifferentialOperator (fun z₁ => ∑ (k : (Fin ↑DE.Degree)),
    (ExtractedFunctions hf g hg k z₁) * g k z₀) z₁ := by
    have h₉ := congrArg DE.KeyDifferentialOperator (funext (fun z₁ => ExtractedFunctionsSpec hf g hg z₀ z₁))
    unfold DiffEq.KeyDifferentialOperator at h₉ ⊢
    rw [show (fun z₁ => f (z₀ + z₁)) = (fun z₁ => f (z₁ + z₀)) by ring_nf] at h₉
    rw [← (congrFun h₉ z₁)]
    have h₅ := ShiftedSolution z₀ hf
    unfold DiffEq.SetOfSolutions DiffEq.IsSolution at h₅
    simp only [Set.mem_setOf_eq] at h₅
    unfold DiffEq.KeyDifferentialOperator at h₅
    exact (congr_fun h₅.2 z₁).symm
  unfold DiffEq.KeyDifferentialOperator at h₀ ⊢
  simp_rw [mul_comm (ExtractedFunctions hf g hg _ _) _, ComplexIteratedDerivSumConstMul (ExtractedFunctions hf g hg)
    (ExtractedFunctionsDifferentiable hf g hg) (fun k => g k z₀)] at h₀
  simp_rw [Finset.mul_sum, Finset.sum_mul] at h₀ ⊢
  rw [Finset.sum_comm] at h₀
  convert h₀ using 2
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem ExtractedFunctionsAreSolutions {DE : DiffEq} {f : ℂ → ℂ} (hf : f ∈ DE.SetOfSolutions)
  (g : (Fin ↑DE.Degree) → ℂ → ℂ) (hg : DE.IsBasis g) :
  ∀ (k : (Fin ↑DE.Degree)), (ExtractedFunctions hf g hg k) ∈ DE.SetOfSolutions := by
  intros k
  constructor
  · exact ExtractedFunctionsDifferentiable hf g hg k
  · ext z
    have h1 : 0 = DE.KeyDifferentialOperator (ExtractedFunctions hf g hg k) z := by
      have h0 := hg.2 (λ (k : (Fin ↑DE.Degree)) => 0)
        (λ (k : (Fin ↑DE.Degree)) => DE.KeyDifferentialOperator (ExtractedFunctions hf g hg k) z)
      simp only [zero_mul, sum_const_zero] at h0
      have h1 : ((fun z₂ => 0) = fun z₂ => ∑ k : Fin ↑DE.Degree,
        DE.KeyDifferentialOperator (ExtractedFunctions hf g hg k) z * g k z₂) := by
        ext z₀
        exact AppliedDifferentialOperator hf g hg z₀ z
      exact congrFun (h0 h1) k
    exact h1.symm

noncomputable def MatrixEntries {DE : DiffEq} {f : ℂ → ℂ} (hf : f ∈ DE.SetOfSolutions)
  (g : (Fin ↑DE.Degree) → ℂ → ℂ) (hg : DE.IsBasis g) (k : (Fin ↑DE.Degree)) :
  (Fin ↑DE.Degree) → ℂ :=
  let W : Matrix (Fin ↑DE.Degree) (Fin ↑DE.Degree) ℂ := Matrix.of fun i j => iteratedDeriv i (g j) 0
  let ek : Fin ↑DE.Degree → ℂ := fun i => iteratedDeriv i (ExtractedFunctions hf g hg k) 0
  (W⁻¹ *ᵥ ek)

theorem MatrixEntriesUse {DE : DiffEq} {f : ℂ → ℂ} (hf : f ∈ DE.SetOfSolutions)
  (g : (Fin ↑DE.Degree) → ℂ → ℂ) (hg : DE.IsBasis g) (k : (Fin ↑DE.Degree)) :
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
  (g : (Fin ↑DE.Degree) → ℂ → ℂ) (hg : DE.IsBasis g) :
  Matrix (Fin ↑DE.Degree) (Fin ↑DE.Degree) ℂ :=
  of λ (y : Fin ↑DE.Degree) (x : Fin ↑DE.Degree) => MatrixEntries hf g hg x y

theorem ExistsUniqueArgumentSumRuleMatrix {DE : DiffEq} {f : ℂ → ℂ} (hf : f ∈ DE.SetOfSolutions)
  (g : (Fin ↑DE.Degree) → ℂ → ℂ) (hg : DE.IsBasis g)
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
  (g : (Fin ↑DE.Degree) → ℂ → ℂ) (hg : DE.IsBasis g)
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
    (g : (Fin ↑DE.Degree) → ℂ → ℂ) (hg : DE.IsBasis g)
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
  (g : (Fin ↑DE.Degree) → ℂ → ℂ) (_ : DE.IsBasis g)
  (Tensor : (Fin Dim → Fin ↑DE.Degree) → ℂ) : Prop :=
  (∀ (z : Fin Dim → ℂ), f (∑ (j : Fin Dim), (z j)) =
    ∑ (k : Fin Dim → Fin ↑DE.Degree), (Tensor k * ∏ (j : Fin Dim), (g (k j) (z j))))

noncomputable def ArgumentSumRuleTensor (Dim : ℕ) {DE : DiffEq} {f : ℂ → ℂ} (hf : f ∈ DE.SetOfSolutions)
    (g : (Fin ↑DE.Degree) → ℂ → ℂ) (hg : DE.IsBasis g) : (Fin Dim → Fin ↑DE.Degree) → ℂ :=
  match Dim with
  | 0 => fun _ => f 0
  | Dim' + 1 =>
    let A := ArgumentSumRule2Matrix hf g hg
    let c_basis (j : Fin ↑DE.Degree) := ArgumentSumRuleTensor Dim' (BasisInSetOfSolutions g hg j) g hg
    fun k => ∑ j : Fin ↑DE.Degree, A (k (Fin.last Dim')) j * c_basis j (Fin.init k)

theorem ExistsUniqueArgumentSumRuleTensor (Dim : ℕ) {DE : DiffEq} {f : ℂ → ℂ} (hf : f ∈ DE.SetOfSolutions)
  (g : (Fin ↑DE.Degree) → ℂ → ℂ) (hg : DE.IsBasis g) (T₀ : (Fin Dim → Fin ↑DE.Degree) → ℂ) :
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
              · simp only [mem_univ, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, and_imp,
                forall_const, Prod.forall, forall_eq', Prod.mk.eta, implies_true]
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
  (g : (Fin ↑DE.Degree) → ℂ → ℂ) (hg : DE.IsBasis g) :
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
