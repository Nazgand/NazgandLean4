import Mathlib
import NazgandLean4.Calculus
set_option maxHeartbeats 0
open Finset Matrix

-- HomogeneousLinearDifferentialEquationsOfConstantCoefficients
structure DiffEq where
  Degree : ℕ
  Coeff : (Fin (Degree + 1)) → ℂ
  LeadCoeffNonZero : Coeff (Fin.ofNat (Degree + 1) Degree) ≠ 0

noncomputable def DiffEq.KeyDifferentialOperator (DE : DiffEq) (f : ℂ → ℂ) : ℂ → ℂ :=
  λ (z: ℂ) => ∑ (k : (Fin (DE.Degree + 1))), (DE.Coeff k) * (iteratedDeriv k f z)

def DiffEq.IsSolution (DE : DiffEq) (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ DE.KeyDifferentialOperator f = 0

def DiffEq.SetOfSolutions (DE : DiffEq) : Set (ℂ → ℂ) := {h : ℂ → ℂ | DE.IsSolution h}

def DiffEq.IsBasis (DE : DiffEq) (g : (Fin ↑DE.Degree) → ℂ → ℂ) : Prop :=
  (DE.SetOfSolutions =
    {h : ℂ → ℂ | ∃ (b : (Fin ↑DE.Degree) → ℂ),
      h = λ (z : ℂ) => ∑ (k : (Fin ↑DE.Degree)), b k * g k z} ∧
    (∀ (b₀ b₁ : (Fin ↑DE.Degree) → ℂ),
      (λ (z : ℂ) => ∑ (k : (Fin ↑DE.Degree)), b₀ k * g k z) =
      (λ (z : ℂ) => ∑ (k : (Fin ↑DE.Degree)), b₁ k * g k z) → b₀ = b₁))

-- the column vector of the functions in g
def Vec {n : ℕ} (g : (Fin n) → ℂ → ℂ) (z : ℂ) :
  Matrix (Fin n) (Fin 1) ℂ := of λ (y : Fin n) (_ : Fin 1) => g y z

theorem DiffEqSolutionAnalytic {DE : DiffEq} {f : ℂ → ℂ} (h : DE.IsSolution f) :
  AnalyticOnNhd ℂ f Set.univ := by
  rw [DiffEq.IsSolution] at h
  exact ContDiff.analyticOnNhd h.1.contDiff

namespace DiffEq

theorem KeyDifferentialOperator.Add {DE : DiffEq} {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) :
    DE.KeyDifferentialOperator (f + g) = DE.KeyDifferentialOperator f + DE.KeyDifferentialOperator g := by
  ext z
  simp only [DiffEq.KeyDifferentialOperator, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [iteratedDeriv_add (hf.contDiff.contDiffAt.of_le le_top) (hg.contDiff.contDiffAt.of_le le_top)]
  ring

theorem KeyDifferentialOperator.ConstMul {DE : DiffEq} {f : ℂ → ℂ} (c : ℂ)
    (hf : Differentiable ℂ f) :
    DE.KeyDifferentialOperator (c • f) = c • DE.KeyDifferentialOperator f := by
  ext z
  simp only [DiffEq.KeyDifferentialOperator, Pi.smul_apply, smul_eq_mul]
  trans ∑ k, c * (DE.Coeff k * iteratedDeriv k f z)
  · apply Finset.sum_congr rfl
    intro k _
    have h_smul : c • f = fun z => c * f z := by ext; simp only [Pi.smul_apply, smul_eq_mul]
    rw [h_smul,
      iteratedDeriv_const_mul (hf.contDiff.contDiffAt.of_le le_top)]
    ring
  · rw [Finset.mul_sum]

theorem IsSolution.Add {DE : DiffEq} {f g : ℂ → ℂ}
    (hf : DE.IsSolution f) (hg : DE.IsSolution g) : DE.IsSolution (f + g) := by
  constructor
  · apply Differentiable.add hf.1 hg.1
  · rw [KeyDifferentialOperator.Add hf.1 hg.1, hf.2, hg.2, add_zero]

theorem IsSolution.ConstMul {DE : DiffEq} {f : ℂ → ℂ} (c : ℂ)
    (hf : DE.IsSolution f) : DE.IsSolution (c • f) := by
  constructor
  · apply Differentiable.const_mul hf.1
  · rw [KeyDifferentialOperator.ConstMul c hf.1, hf.2, smul_zero]

theorem IsSolution.Zero {DE : DiffEq} : DE.IsSolution 0 := by
  constructor
  · apply differentiable_const
  · ext z
    simp only [DiffEq.KeyDifferentialOperator, iteratedDerivOf0, mul_zero, Finset.sum_const_zero, Pi.zero_apply]

end DiffEq

theorem LinearCombinationOfSolutions {DE : DiffEq} {ι : Type*} (s : Finset ι)
    (f : ι → ℂ → ℂ) (c : ι → ℂ) (hf : ∀ i ∈ s, DE.IsSolution (f i)) :
    DE.IsSolution (λ z ↦ ∑ i ∈ s, c i * f i z) := by
  induction s using Finset.cons_induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact DiffEq.IsSolution.Zero
  | cons a s ha ih =>
    simp only [Finset.sum_cons]
    apply DiffEq.IsSolution.Add
    · apply DiffEq.IsSolution.ConstMul
      exact hf a (Finset.mem_cons_self _ _)
    · apply ih
      intro i hi
      exact hf i (Finset.mem_cons_of_mem hi)

-- A solution with input shifted by a constant z₁ is still a solution
theorem ShiftedSolution {DE : DiffEq} {f : ℂ → ℂ} (z₁ : ℂ) (hf : f ∈ DE.SetOfSolutions) :
  (λ (z₀ : ℂ) => f (z₀ + z₁)) ∈ DE.SetOfSolutions := by
  unfold DiffEq.SetOfSolutions at ⊢ hf
  simp only [Set.mem_setOf_eq] at ⊢ hf
  unfold DiffEq.IsSolution at ⊢ hf
  rcases hf with ⟨h₁, h₂⟩
  constructor
  · exact h₁.comp (differentiable_id.add (differentiable_const z₁))
  · have hShID : ∀ (k : ℕ), (iteratedDeriv k fun z₀ => f (z₀ + z₁)) =
      fun z₀ => iteratedDeriv k f (z₀ + z₁) := by
      intros k
      rw [ShiftedIteratedDerivative k z₁ h₁]
    ext z₀
    unfold DiffEq.KeyDifferentialOperator
    simp_rw [hShID]
    have h_sol_z := congr_fun h₂ (z₀ + z₁)
    unfold DiffEq.KeyDifferentialOperator at h_sol_z
    exact h_sol_z

theorem BasisInSetOfSolutions {DE : DiffEq} (g : (Fin ↑DE.Degree) → ℂ → ℂ) (hg : DE.IsBasis g) :
    ∀ j, g j ∈ DE.SetOfSolutions := by
  unfold DiffEq.IsBasis at hg
  rw [hg.1]
  intro j
  use fun k => if k = j then 1 else 0
  simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ↓reduceIte]

theorem InvertibleMatrixMulBasisIsBasis {DE : DiffEq} (g : (Fin ↑DE.Degree) → ℂ → ℂ)
    (hg : DE.IsBasis g) (C : Matrix (Fin ↑DE.Degree) (Fin ↑DE.Degree) ℂ) (hC : IsUnit C) :
     DE.IsBasis (λ (k : Fin DE.Degree) (z : ℂ) ↦ (C * Vec g z) k 0) := by
  let n := DE.Degree
  let g' := λ (k : Fin n) (z : ℂ) ↦ (C * Vec g z) k 0
  have hg'_eq : ∀ z, Vec g' z = C * Vec g z := by
    intro z
    ext i j
    simp only [g', Vec, of_apply, Matrix.mul_apply, Matrix.of_apply]
  unfold DiffEq.IsBasis at hg ⊢
  rcases hg with ⟨h_span, h_indep⟩
  constructor
  · rw [h_span]
    ext h
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨b, rfl⟩
      let b_vec : Matrix (Fin 1) (Fin n) ℂ := of (λ _ j => b j)
      let C_inv := hC.unit.inv
      let b' := λ k => (b_vec * C_inv) 0 k
      use b'
      ext z
      have h1 : (∑ k : Fin n, b k * g k z) = (b_vec * Vec g z) 0 0 := by
        simp only [Vec, Fin.isValue, mul_apply, of_apply, b_vec]
      rw [h1]
      have h2 : (∑ k : Fin n, b' k * g' k z) = ((of (λ _ : Fin 1 => b') : Matrix (Fin 1) (Fin n) ℂ) * Vec g' z) 0 0 := by
         simp only [Vec, Fin.isValue, mul_apply, of_apply]
      rw [h2]
      simp only [hg'_eq]
      have h_b' : (of (λ _ : Fin 1 => b') : Matrix (Fin 1) (Fin n) ℂ) = b_vec * C_inv := by
        ext i j
        simp only [Fin.isValue, of_apply, b', b_vec]
        congr
      have h_mat_eq : b_vec * Vec g z = (of (λ _ : Fin 1 => b') : Matrix (Fin 1) (Fin n) ℂ) * (C * Vec g z) := by
        rw [h_b', Matrix.mul_assoc]
        congr
        rw [← Matrix.mul_assoc, ← hC.unit_spec]
        unfold C_inv
        rw [hC.unit.inv_val, Matrix.one_mul]
      rw [h_mat_eq]
    · rintro ⟨b, rfl⟩
      let b_vec : Matrix (Fin 1) (Fin n) ℂ := of (λ _ j => b j)
      let b_new := λ k => (b_vec * C) 0 k
      use b_new
      ext z
      have h1 : (∑ k : Fin n, b k * g' k z) = (b_vec * Vec g' z) 0 0 := by
        simp only [Vec, Fin.isValue, mul_apply, of_apply, b_vec]
      rw [h1]
      have h2 : (∑ k : Fin n, b_new k * g k z) = ((of (λ _ : Fin 1 => b_new) : Matrix (Fin 1) (Fin n) ℂ) * Vec g z) 0 0 := by
         simp only [Vec, Fin.isValue, mul_apply, of_apply]
      rw [h2]
      simp only [hg'_eq]
      have h_b_new : (of (λ _ : Fin 1 => b_new) : Matrix (Fin 1) (Fin n) ℂ) = b_vec * C := by
        ext i j
        simp only [Fin.isValue, of_apply, b_new, b_vec]
        congr
      have h_mat_eq : b_vec * (C * Vec g z) = ((of (λ _ : Fin 1 => b_new) : Matrix (Fin 1) (Fin n) ℂ) * Vec g z) := by
        rw [h_b_new, Matrix.mul_assoc]
      rw [h_mat_eq]
  · intros b₀ b₁ h_eq
    let b₀_vec : Matrix (Fin 1) (Fin n) ℂ := of (λ _ j => b₀ j)
    let b₁_vec : Matrix (Fin 1) (Fin n) ℂ := of (λ _ j => b₁ j)
    have h_eq_mat : ∀ z, (b₀_vec * Vec g' z) 0 0 = (b₁_vec * Vec g' z) 0 0 := by
      intro z
      have h0 : (b₀_vec * Vec g' z) 0 0 = ∑ k, b₀ k * g' k z := by
        simp only [Vec, Fin.isValue, mul_apply, of_apply, b₀_vec]
        rfl
      rw [h0]
      have h1 : (b₁_vec * Vec g' z) 0 0 = ∑ k, b₁ k * g' k z := by
        simp only [Vec, Fin.isValue, mul_apply, of_apply, b₁_vec]
        rfl
      rw [h1]
      exact congr_fun h_eq z
    simp only [hg'_eq] at h_eq_mat
    have h_assoc : ∀ (b_vec : Matrix (Fin 1) (Fin n) ℂ) z, (b_vec * (C * Vec g z)) 0 0 = ((b_vec * C) * Vec g z) 0 0 := by
      intros
      rw [Matrix.mul_assoc]
    simp_rw [h_assoc] at h_eq_mat
    let b0_C := λ k => (b₀_vec * C) 0 k
    let b1_C := λ k => (b₁_vec * C) 0 k
    have h_sums_eq : (fun z => ∑ k, b0_C k * g k z) = (fun z => ∑ k, b1_C k * g k z) := by
       ext z
       specialize h_eq_mat z
       have h0 : (∑ k, b0_C k * g k z) = ((b₀_vec * C) * Vec g z) 0 0 := by
         simp only [Fin.isValue, mul_apply, Vec, of_apply, b0_C]
       rw [h0]
       have h1 : (∑ k, b1_C k * g k z) = ((b₁_vec * C) * Vec g z) 0 0 := by
         simp only [Fin.isValue, mul_apply, Vec, of_apply, b1_C]
       rw [h1]
       exact h_eq_mat
    have h_coeffs_eq := h_indep b0_C b1_C h_sums_eq
    funext k
    have mat_eq : b₀_vec * C = b₁_vec * C := by
      ext i j
      simp only [Fin.isValue, b0_C, b1_C] at h_coeffs_eq
      convert congr_fun h_coeffs_eq j using 1
    have mat_b_eq : b₀_vec = b₁_vec := by
      rw [← Matrix.mul_one b₀_vec, ← hC.unit.val_inv, ← Matrix.mul_assoc, hC.unit_spec,
         mat_eq, Matrix.mul_assoc]
      nth_rw 1 [← hC.unit_spec]
      rw [hC.unit.val_inv, Matrix.mul_one]
    replace mat_b_eq := congr_fun (congr_fun mat_b_eq 0) k
    simp only [b₀_vec, b₁_vec, of_apply] at mat_b_eq
    exact mat_b_eq

theorem ExistInvertibleMatrixMulBasis0ToGetBasis1 {DE : DiffEq} (g₀ g₁ : (Fin ↑DE.Degree) → ℂ → ℂ)
    (hg₀ : DE.IsBasis g₀) (hg₁ : DE.IsBasis g₁) :
    ∃ (C : Matrix (Fin ↑DE.Degree) (Fin ↑DE.Degree) ℂ), (IsUnit C ∧ ∀ z : ℂ, C * Vec g₀ z = Vec g₁ z) := by
  let n := DE.Degree
  have g1_in_sol : ∀ k, g₁ k ∈ DE.SetOfSolutions := BasisInSetOfSolutions g₁ hg₁
  have exists_C : ∃ C : Matrix (Fin n) (Fin n) ℂ, ∀ z, Vec g₁ z = C * Vec g₀ z := by
     rw [hg₀.1] at g1_in_sol
     have h_basis_rep : ∀ k, ∃ (b : Fin DE.Degree → ℂ), g₁ k = fun z => ∑ j, b j * g₀ j z := by
       intro k
       specialize g1_in_sol k
       simp at g1_in_sol
       exact g1_in_sol
     choose b hb using h_basis_rep
     let C := of (fun i j => b i j)
     use C
     intro z
     ext i j
     simp only [Vec, of_apply, mul_apply]
     rw [hb i]
     rfl
  rcases exists_C with ⟨C, hC_eq⟩
  have g0_in_sol : ∀ k, g₀ k ∈ DE.SetOfSolutions := BasisInSetOfSolutions g₀ hg₀
  have exists_D : ∃ D : Matrix (Fin n) (Fin n) ℂ, ∀ z, Vec g₀ z = D * Vec g₁ z := by
     rw [hg₁.1] at g0_in_sol
     have h_basis_rep : ∀ k, ∃ (b : Fin DE.Degree → ℂ), g₀ k = fun z => ∑ j, b j * g₁ j z := by
       intro k
       specialize g0_in_sol k
       simp at g0_in_sol
       exact g0_in_sol
     choose b hb using h_basis_rep
     let D := of (fun i j => b i j)
     use D
     intro z
     ext i j
     simp only [Vec, of_apply, mul_apply]
     rw [hb i]
     rfl
  rcases exists_D with ⟨D, hD_eq⟩
  have h_id : C * D = 1 := by
    apply Matrix.ext
    intros i j
    let row_vec := λ k => (C * D - 1) i k
    have h_lin_comb : (fun z => ∑ k, row_vec k * g₁ k z) = 0 := by
      ext z
      have h0 : (((C * D - 1) * Vec g₁ z) : Matrix (Fin n) (Fin 1) ℂ) i 0 = ∑ k, (C * D - 1) i k * g₁ k z := by
         simp only [Vec, Fin.isValue, mul_apply, sub_apply, of_apply]
      rw [← h0]
      simp only [Matrix.sub_mul, Matrix.one_mul]
      rw [Matrix.mul_assoc, ← hD_eq z, ← hC_eq z]
      simp only [Fin.isValue, sub_apply, sub_self, Pi.zero_apply]
    have h_coeffs_zero := hg₁.2 row_vec 0 (by rw [h_lin_comb]; simp; exact Pi.zero_def)
    have h_eq := congr_fun h_coeffs_zero j
    simp only [sub_apply, Pi.zero_apply, row_vec] at h_eq
    exact eq_of_sub_eq_zero h_eq
  have h_id2 : D * C = 1 := by
     apply Matrix.ext
     intros i j
     let row_vec := λ k => (D * C - 1) i k
     have h_lin_comb : (fun z => ∑ k, row_vec k * g₀ k z) = 0 := by
       ext z
       have h0 : (((D * C - 1) * Vec g₀ z) : Matrix (Fin n) (Fin 1) ℂ) i 0 = ∑ k, (D * C - 1) i k * g₀ k z := by
          simp only [Vec, Fin.isValue, mul_apply, sub_apply, of_apply]
       rw [← h0]
       simp only [Matrix.sub_mul, Matrix.one_mul]
       rw [Matrix.mul_assoc, ← hC_eq z, ← hD_eq z]
       simp only [Fin.isValue, sub_apply, sub_self, Pi.zero_apply]
     have h_coeffs_zero := hg₀.2 row_vec 0 (by rw [h_lin_comb]; simp; exact Pi.zero_def)
     have h_eq := congr_fun h_coeffs_zero j
     simp only [sub_apply, Pi.zero_apply, row_vec] at h_eq
     exact eq_of_sub_eq_zero h_eq
  use C
  constructor
  · let u : (Matrix (Fin DE.Degree) (Fin DE.Degree) ℂ)ˣ := {
      val := C
      inv := D
      val_inv := h_id
      inv_val := h_id2
    }
    use u
  · intro z
    exact (hC_eq z).symm

theorem DiffEq_Zero_IC_Implies_Zero {DE : DiffEq} {h : ℂ → ℂ} (h_sol : DE.IsSolution h)
    (h_ic : ∀ k : Fin ↑DE.Degree, iteratedDeriv k h 0 = 0) : h = 0 := by
  have h_ana : AnalyticAt ℂ h 0 := (DiffEqSolutionAnalytic h_sol) 0 trivial
  have h_derivs : ∀ k, iteratedDeriv k h 0 = 0 := by
    intro k
    induction' k using Nat.strong_induction_on with k ih
    if hk : k < DE.Degree then
      exact h_ic ⟨k, hk⟩
    else
      let m := k - DE.Degree
      have hm : m + DE.Degree = k := Nat.sub_add_cancel (Nat.le_of_not_lt hk)
      have hm : m + DE.Degree = k := Nat.sub_add_cancel (Nat.le_of_not_lt hk)
      have h_diff_ode :
        iteratedDeriv m (fun z => ∑ j : Fin (DE.Degree + 1), DE.Coeff j * iteratedDeriv j h z) 0 = 0 := by
        change iteratedDeriv m (DE.KeyDifferentialOperator h) 0 = 0
        rw [h_sol.2, iteratedDerivOf0]
        rfl
      have h_smooth : ∀ n, Differentiable ℂ (iteratedDeriv n h) := by
        intro n
        exact ((DiffEqSolutionAnalytic h_sol).contDiff.of_le le_top).differentiable_iteratedDeriv n (Nat.cast_lt.mpr (Nat.lt_succ_self n))
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
            exact h_smooth _
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
          · exact (h_smooth _).differentiableAt
      have h_diff_ode' : ∑ j : Fin (DE.Degree + 1), DE.Coeff j * iteratedDeriv (m + j) h 0 = 0 := by
        rw [h_iter_sum] at h_diff_ode
        exact h_diff_ode
      rw [Fin.sum_univ_castSucc] at h_diff_ode'
      have h_lower : ∑ x : Fin ↑DE.Degree, DE.Coeff (Fin.castSucc x) * iteratedDeriv (m + x) h 0 = 0 := by
        apply Finset.sum_eq_zero
        intro x _
        apply mul_eq_zero_of_right
        apply ih
        rw [← hm]
        apply Nat.add_lt_add_left x.isLt
      simp only [Fin.val_castSucc, h_lower, Fin.val_last, zero_add] at h_diff_ode'
      rw [hm] at h_diff_ode'
      refine eq_zero_of_ne_zero_of_mul_left_eq_zero ?_ h_diff_ode'
      convert DE.LeadCoeffNonZero
      simp only [Fin.ofNat_eq_cast, Fin.natCast_eq_last]
  have h_ana_at : AnalyticAt ℂ h 0 := (DiffEqSolutionAnalytic h_sol) 0 trivial
  have hf_ser := h_ana_at.hasFPowerSeriesAt
  have h_ser_zero : FormalMultilinearSeries.ofScalars ℂ (fun n ↦ iteratedDeriv n h 0 / n.factorial) = 0 := by
    ext n
    simp only [h_derivs n, zero_div, FormalMultilinearSeries.ofScalars_eq_zero_of_scalar_zero,
      ContinuousMultilinearMap.zero_apply, FormalMultilinearSeries.zero_apply]
  have h_loc : h =ᶠ[nhds 0] 0 := by
    rw [h_ser_zero] at hf_ser
    exact hf_ser.eventually_eq_zero
  apply AnalyticOnNhd.eq_of_eventuallyEq (DiffEqSolutionAnalytic h_sol)
  exact analyticOnNhd_const
  exact h_loc
