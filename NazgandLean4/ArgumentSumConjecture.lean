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
      sorry
    have hh : DifferentiableAt ℂ h z := by
      sorry
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
    sorry
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
      sorry
    sorry

theorem ExtractedFunctionsDifferentiable0 {de : DiffEq} {f : ℂ → ℂ}
  (h₁ : f ∈ de.SetOfSolutions) (g : (Fin de.Degree) → ℂ → ℂ) (h₂ : de.IsVectorBasis g)
  : ∀ (k : (Fin de.Degree)), Differentiable ℂ (ExtractedFunctions h₁ g h₂ k) := by
  sorry

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
