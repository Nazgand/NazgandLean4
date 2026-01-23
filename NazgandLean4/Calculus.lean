import Mathlib

theorem SumOfDifferentiableIsDifferentiable {k : ℕ} (g : Fin k → ℂ → ℂ)
  (hD : ∀ (m : Fin k), Differentiable ℂ (g m)) (c : Fin k → ℂ) :
  Differentiable ℂ (λ (z : ℂ) ↦ ∑ (m : Fin k), c m * g m z) := by
  convert Differentiable.sum (u := Finset.univ) (fun i _ => Differentiable.const_mul (hD i) (c i))
  simp [Finset.sum_apply]

theorem IteratedDerivSum {𝕜 : Type u} [NontriviallyNormedField 𝕜] {F : Type v}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {ι : Type u_1}
  {u : Finset ι} {A : ι → 𝕜 → F} (k : ℕ) (h : ∀ i ∈ u, ContDiff 𝕜 k (A i)) :
  iteratedDeriv k (fun y => Finset.sum u fun i => A i y) =
  (fun y => Finset.sum u fun i => iteratedDeriv k (A i) y) := by
  induction k with
  | zero => simp only [iteratedDeriv_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have h_diff_k : ∀ i ∈ u, ContDiff 𝕜 k (A i) := fun i hi => (h i hi).of_succ
    rw [ih h_diff_k]
    ext x
    simp only [← Finset.sum_apply]
    rw [deriv_sum]
    · simp only [iteratedDeriv_succ, Finset.sum_apply]
    · intro i hi
      refine ((h i hi).differentiable_iteratedDeriv k ?_).differentiableAt
      norm_cast
      exact Nat.lt_succ_self k

theorem ComplexIteratedDerivSum {ι : Type u_1} {u : Finset ι} {A : ι → ℂ → ℂ}
  (h : ∀ i ∈ u, Differentiable ℂ (A i)) (k : ℕ) :
  iteratedDeriv k (fun y => Finset.sum u fun i => A i y) =
  (fun y => Finset.sum u fun i => iteratedDeriv k (A i) y) :=
  IteratedDerivSum k (λ i hi => (h i hi).contDiff)

theorem ComplexIteratedDerivSumConstMul {m : ℕ} (g : Fin m → ℂ → ℂ)
  (h : ∀ (k : Fin m), Differentiable ℂ (g k)) (C : Fin m → ℂ) (i : ℕ) (z : ℂ) :
  iteratedDeriv i (fun z₀ => ∑ (k : Fin m), C k * g k z₀) z =
  ∑ (k : Fin m), C k * iteratedDeriv i (g k) z := by
  let A := fun (k : Fin m) (z : ℂ) => C k * g k z
  have hA : ∀ k ∈ Finset.univ, Differentiable ℂ (A k) := by
    intro k _
    exact Differentiable.const_mul (h k) (C k)
  rw [ComplexIteratedDerivSum hA i]
  dsimp
  congr with k
  rw [iteratedDeriv_const_mul]
  exact (h k).contDiff.contDiffAt
