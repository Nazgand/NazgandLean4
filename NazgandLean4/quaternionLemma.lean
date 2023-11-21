import Mathlib
set_option maxHeartbeats 0
open Quaternion Classical

--declare a Set Of Quaternions That Square To Negative 1
def Soqtstn1₀ : Set ℍ[ℝ] := {q₀ : ℍ[ℝ] | -1 = q₀ * q₀}
def Soqtstn1₁ : Set ℍ[ℝ] := {q₁ : ℍ[ℝ] | ∃ (rx ry rz : ℝ), (q₁ = ⟨0, rx, ry, rz⟩ ∧ rx*rx + ry*ry + rz*rz = 1)}
def Soqtstn1₂ : Set ℍ[ℝ] := {q₂ : ℍ[ℝ] | ‖q₂‖ = 1 ∧ q₂.re = 0}

lemma EqualSetsSoqtstn1₀AndSoqtstn1₁ : Soqtstn1₀ = Soqtstn1₁ := by
  ext ⟨r, x, y, z⟩
  dsimp [Soqtstn1₀, Soqtstn1₁]
  simp only [ext_iff, neg_re, QuaternionAlgebra.one_re, mul_re, neg_imI, QuaternionAlgebra.one_imI,
    neg_zero, mul_imI, neg_imJ, QuaternionAlgebra.one_imJ, mul_imJ, neg_imK,
    QuaternionAlgebra.one_imK, mul_imK]
  constructor
  · intros ha
    use x
    use y
    use z
    simp only [and_self, and_true]
    rcases ha with ⟨hSphere3,h0x,h0y,h0z⟩
    ring_nf at h0x
    ring_nf at h0y
    ring_nf at h0z
    simp only [zero_eq_mul, mul_eq_zero, OfNat.ofNat_ne_zero, or_false] at h0x
    simp only [zero_eq_mul, mul_eq_zero, OfNat.ofNat_ne_zero, or_false] at h0y
    simp only [zero_eq_mul, mul_eq_zero, OfNat.ofNat_ne_zero, or_false] at h0z
    have hr₀ : (¬ r = 0) → False := by
      intros hrn0
      let hrn0₂ := Iff.mpr iff_false_iff hrn0
      simp only [hrn0₂, false_or] at h0x
      simp only [hrn0₂, false_or] at h0y
      simp only [hrn0₂, false_or] at h0z
      simp_rw [h0x, h0y, h0z] at hSphere3
      simp only [mul_zero, sub_zero] at hSphere3
      have hrnn := mul_self_nonneg r
      rw [←hSphere3] at hrnn
      linarith
    have hr : r = 0 := by_contra hr₀
    constructor
    · exact hr
    · rw [hr] at hSphere3
      let hSphere4 := congrArg (λ (xk : ℝ) => -xk) hSphere3
      simp only [neg_neg, mul_zero, zero_sub, neg_sub] at hSphere4
      rw [hSphere4]
      ring_nf
  · intros h₀
    ring_nf
    rcases h₀ with ⟨rx,ry,rz,hx⟩
    rcases hx with ⟨hx₀,hSphere⟩
    rcases hx₀ with ⟨hr,hrx,hry,hrz⟩
    simp_rw [hr]
    simp only [ne_eq, zero_pow', zero_sub, zero_mul, and_self, and_true]
    simp_rw [hrx,hry,hrz]
    let hSphere2 := congrArg (λ (xk : ℝ) => -xk) hSphere
    simp only [neg_add_rev] at hSphere2
    rw [←hSphere2]
    ring

lemma EqualSetsSoqtstn1₁AndSoqtstn1₂ : Soqtstn1₁ = Soqtstn1₂ := by
  ext ⟨r, x, y, z⟩
  dsimp [Soqtstn1₁, Soqtstn1₂]
  simp only [ext_iff]
  constructor
  · intros h
    rcases h with ⟨rx,ry,rz,hx,hSphere⟩
    rcases hx with ⟨hr0, hxrx, hyry, hzrz⟩
    simp_rw [hr0]
    simp only [and_true]
    simp_rw [←hxrx, ←hyry, ←hzrz] at hSphere
    let hNorm1 := congrArg Real.sqrt hSphere
    simp only [Real.sqrt_one] at hNorm1
    simp_rw [←hNorm1]
    let hSqrtNormSquare := congrArg Real.sqrt (Quaternion.normSq_eq_norm_mul_self (@QuaternionAlgebra.mk ℝ (-1) (-1) 0 x y z))
    simp only [norm_nonneg, Real.sqrt_mul_self] at hSqrtNormSquare
    simp_rw [←hSqrtNormSquare, Quaternion.normSq_def']
    ring_nf
  · intros h₀
    rcases h₀ with ⟨hNorm1, hr0⟩
    use x
    use y
    use z
    simp only [hr0, and_self, true_and]
    let hNormSquare1 := congrArg (λ (r₀ : ℝ)=>r₀*r₀) hNorm1
    simp only [mul_one] at hNormSquare1
    rw [←Quaternion.normSq_eq_norm_mul_self, hr0, Quaternion.normSq_def'] at hNormSquare1
    rw [←hNormSquare1]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow', zero_add]
    ring_nf

--declare a Set Of Quaternions q That Square To q Minus 1
def Soqqtstqm1₀ : Set ℍ[ℝ] := {q₀ : ℍ[ℝ] | q₀ - 1 = q₀ * q₀}
def Soqqtstqm1₁ : Set ℍ[ℝ] := {q₁ : ℍ[ℝ] | ∃ (rx ry rz : ℝ), (q₁ = ⟨1/2, rx, ry, rz⟩ ∧ rx*rx + ry*ry + rz*rz = 3/4)}
def Soqqtstqm1₂ : Set ℍ[ℝ] := {q₂ : ℍ[ℝ] | ‖q₂‖ = 1 ∧ q₂.re = 1/2}
def Soqqtstqm1₃ : Set ℍ[ℝ] := {q₃ : ℍ[ℝ] | ∃ (qim : ℍ[ℝ]), (qim ∈ Soqtstn1₁ ∧ q₃ = 1/2 + qim * (Real.sqrt 3) / 2)}

lemma EqualSetsSoqqtstqm1₀AndSoqqtstqm1₁ : Soqqtstqm1₀ = Soqqtstqm1₁ := by
  ext ⟨r, x, y, z⟩
  dsimp [Soqqtstqm1₀, Soqqtstqm1₁]
  simp only [ext_iff, sub_re, QuaternionAlgebra.one_re, mul_re, sub_imI, QuaternionAlgebra.one_imI,
    sub_zero, mul_imI, sub_imJ, QuaternionAlgebra.one_imJ, mul_imJ, sub_imK,
    QuaternionAlgebra.one_imK, mul_imK, one_div]
  ring_nf
  simp only [Int.ofNat_eq_coe, Nat.cast_one, Int.cast_one, Nat.cast_ofNat, one_div,
    Int.int_cast_ofNat]
  constructor
  · intros h₀
    use x
    use y
    use z
    simp only [and_self, and_true]
    rcases h₀ with ⟨h₁,hx,hy,hz⟩
    have hr₀ : (¬ r = 1/2) → False := by
      intros hrn0
      sorry
    have hr₁ : r = 1/2 := by_contra hr₀
    rw [hr₁]
    simp only [one_div, true_and]
    rw [hr₁] at h₁
    let hSphere := congrArg (λ (x₀ : ℝ) => 1/4 - x₀) h₁
    ring_nf at hSphere
    rw [←hSphere]
    simp only [Int.ofNat_eq_coe, Nat.cast_ofNat, Int.int_cast_ofNat]
  · intros h₀
    rcases h₀ with ⟨rx,ry,rz,hx,hSphere⟩
    rcases hx with ⟨hr,hx,hy,hz⟩
    simp_rw [hr]
    ring_nf
    simp only [Int.cast_negOfNat, Nat.cast_one, Int.ofNat_eq_coe, Int.cast_one, Nat.cast_ofNat,
      one_div, neg_mul, one_mul, and_self, and_true]
    rw [←hx, ←hy, ←hz] at hSphere
    let hXSquare := congrArg (λ (x₀ : ℝ) => x₀ - y ^ 2 - z ^ 2) hSphere
    ring_nf at hXSquare
    rw [hXSquare]
    ring

lemma EqualSetsSoqqtstqm1₁AndSoqqtstqm1₂ : Soqqtstqm1₁ = Soqqtstqm1₂ := by
  sorry

lemma EqualSetsSoqqtstqm1₁AndSoqqtstqm1₃ : Soqqtstqm1₁ = Soqqtstqm1₃ := by
  sorry
