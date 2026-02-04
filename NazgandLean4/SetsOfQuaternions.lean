import Mathlib
set_option maxHeartbeats 0
open Quaternion Classical

theorem InvQuaternionOfReal (x : ℝ) : (x : ℍ)⁻¹ = ↑(x⁻¹ : ℝ) := Eq.symm (coe_inv x)

theorem InvTwo : (2 : ℍ)⁻¹ = ↑(1/2 : ℝ) := by
  rw [(show (2 : ℍ) = ↑(2 : ℝ) by rfl), InvQuaternionOfReal 2]
  norm_num

macro "quat_simp" : tactic => `(tactic| simp only [inv_def, normSq_def, re_mul,
  re_star, imI_star, neg_zero, mul_zero, sub_zero,
  imJ_star, imK_star, mul_inv_rev, re_smul, smul_eq_mul, ne_eq, OfNat.ofNat_ne_zero,
  not_false_eq_true, inv_mul_cancel_right₀, div_eq_mul_inv, Algebra.mul_smul_comm, re_coe,
  zero_mul, imI_coe, sub_self, imJ_coe, imK_coe, imI_mul, Nat.ofNat_nonneg,
  Real.sqrt_eq_zero, zero_add, add_zero, imJ_mul, imK_mul, imI_smul, imJ_smul,
  imK_smul, one_div, re_sub, imI_sub, imJ_sub, imK_sub, re_add, imI_add, imJ_add, imK_add,
  re_neg, imI_neg, imJ_neg, imK_neg, re_one, imI_one, imJ_one, imK_one, Quaternion.ext_iff])

-- Declare a Set Of Quaternions That Square To Negative 1
def Soqtstn1₀ : Set ℍ[ℝ] := {q₀ : ℍ[ℝ] | -1 = q₀ * q₀}
def Soqtstn1₁ : Set ℍ[ℝ] := {q₁ : ℍ[ℝ] | ∃ (rx ry rz : ℝ),
  (q₁ = ⟨0, rx, ry, rz⟩ ∧ rx * rx + ry * ry + rz * rz = 1)}
def Soqtstn1₂ : Set ℍ[ℝ] := {q₂ : ℍ[ℝ] | ‖q₂‖ = 1 ∧ q₂.re = 0}

theorem EqualSetsSoqtstn1₀AndSoqtstn1₁ : Soqtstn1₀ = Soqtstn1₁ := by
  ext ⟨r, x, y, z⟩
  dsimp only [Soqtstn1₀, Set.mem_setOf_eq, Soqtstn1₁]
  quat_simp
  constructor
  · intros ha
    use x
    use y
    use z
    simp only [and_self, and_true]
    rcases ha with ⟨hSphere3, h0x, h0y, h0z⟩
    ring_nf at h0x h0y h0z
    simp only [zero_eq_mul, mul_eq_zero, OfNat.ofNat_ne_zero, or_false] at h0x h0y h0z
    have hr₀ : (¬ r = 0) → False := by
      intros hrn0
      simp only [hrn0, false_or] at h0x h0y h0z
      simp_rw [h0x, h0y, h0z] at hSphere3
      simp only [mul_zero, sub_zero] at hSphere3
      have hrnn := mul_self_nonneg r
      rw [← hSphere3] at hrnn
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
    rcases h₀ with ⟨rx, ry, rz, hx⟩
    rcases hx with ⟨hx₀, hSphere⟩
    rcases hx₀ with ⟨hr, hrx, hry, hrz⟩
    simp_rw [hr]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_sub, zero_mul,
      and_self, and_true]
    simp_rw [hrx, hry, hrz]
    let hSphere2 := congrArg (λ (xk : ℝ) => -xk) hSphere
    simp only [neg_add_rev] at hSphere2
    rw [← hSphere2]
    ring

theorem EqualSetsSoqtstn1₁AndSoqtstn1₂ : Soqtstn1₁ = Soqtstn1₂ := by
  ext ⟨r, x, y, z⟩
  dsimp only [Soqtstn1₁, Set.mem_setOf_eq, Soqtstn1₂]
  simp only [Quaternion.ext_iff]
  constructor
  · intros h
    rcases h with ⟨rx, ry, rz, hx, hSphere⟩
    rcases hx with ⟨hr0, hxrx, hyry, hzrz⟩
    simp_rw [hr0]
    simp only [and_true]
    simp_rw [← hxrx, ← hyry, ← hzrz] at hSphere
    let hNorm1 := congrArg Real.sqrt hSphere
    simp only [Real.sqrt_one] at hNorm1
    simp_rw [← hNorm1]
    let hSqrtNormSquare :=
      congrArg Real.sqrt (Quaternion.normSq_eq_norm_mul_self (QuaternionAlgebra.mk 0 x y z))
    simp only [norm_nonneg, Real.sqrt_mul_self] at hSqrtNormSquare
    simp_rw [← hSqrtNormSquare, Quaternion.normSq_def']
    ring_nf
  · intros h₀
    rcases h₀ with ⟨hNorm1, hr0⟩
    use x
    use y
    use z
    simp only [hr0, and_self, true_and]
    let hNormSquare1 := congrArg (λ (r₀ : ℝ) => r₀ * r₀) hNorm1
    simp only [mul_one] at hNormSquare1
    rw [← Quaternion.normSq_eq_norm_mul_self, hr0, Quaternion.normSq_def'] at hNormSquare1
    rw [← hNormSquare1]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
    ring_nf

-- Declare a Set Of Quaternions q That Square To q Minus 1
def Soqqtstqm1₀ : Set ℍ[ℝ] := {q₀ : ℍ[ℝ] | q₀ - 1 = q₀ * q₀}
def Soqqtstqm1₁ : Set ℍ[ℝ] := {q₁ : ℍ[ℝ] | ∃ (rx ry rz : ℝ),
  (q₁ = ⟨1 / 2, rx, ry, rz⟩ ∧ rx * rx + ry * ry + rz * rz = 3 / 4)}
def Soqqtstqm1₂ : Set ℍ[ℝ] := {q₂ : ℍ[ℝ] | ‖q₂‖ = 1 ∧ q₂.re = 1 / 2}
def Soqqtstqm1₃ : Set ℍ[ℝ] := {q₃ : ℍ[ℝ] | ∃ (qim : ℍ[ℝ]),
  (qim ∈ Soqtstn1₁ ∧ q₃ = 1/2 + qim * (Real.sqrt 3) / 2)}

theorem EqualSetsSoqqtstqm1₀AndSoqqtstqm1₁ : Soqqtstqm1₀ = Soqqtstqm1₁ := by
  ext ⟨r, x, y, z⟩
  dsimp only [Soqqtstqm1₀, Set.mem_setOf_eq, Soqqtstqm1₁]
  quat_simp
  ring_nf
  simp only [one_div]
  constructor
  · intros h₀
    use x
    use y
    use z
    simp only [and_self, and_true]
    rcases h₀ with ⟨h₁, hx, hy, hz⟩
    have EqSplit : ∀ (x₀ : ℝ), x₀ = r * x₀ * 2 → (x₀ = 0 ∨ r = 1 / 2) := by
      intro x₀ h
      have hFactored : x₀ * (1 - r * 2) = 0 := by linarith
      simp only [mul_eq_zero] at hFactored
      apply hFactored.imp_right
      intro h
      field_simp
      linarith
    let hx₂ := EqSplit x hx
    let hy₂ := EqSplit y hy
    let hz₂ := EqSplit z hz
    have hr₀ : (¬ r = 1/2) → False := by
      intros hrn0
      simp only [one_div] at hrn0
      simp only [one_div, hrn0, or_false] at hx₂ hy₂ hz₂
      simp only [hx₂, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, hy₂,
        neg_zero, hz₂, sub_self, add_zero] at h₁
      let h₂ := congrArg (λ (x₀ : ℝ) => x₀ - r + 1) h₁
      simp only [add_sub_cancel_right, neg_add_cancel] at h₂
      have hSquareNn := mul_self_nonneg (r - 1 / 2)
      linarith
    have hr₁ : r = 1/2 := by_contra hr₀
    rw [hr₁]
    simp only [one_div, true_and]
    rw [hr₁] at h₁
    let hSphere := congrArg (λ (x₀ : ℝ) => 1 / 4 - x₀) h₁
    ring_nf at hSphere
    rw [← hSphere]
  · intros h₀
    rcases h₀ with ⟨rx, ry, rz, hx, hSphere⟩
    rcases hx with ⟨hr, hx, hy, hz⟩
    simp_rw [hr]
    ring_nf
    simp only [one_div, and_self, and_true]
    rw [← hx, ← hy, ← hz] at hSphere
    let hXSquare := congrArg (λ (x₀ : ℝ) => x₀ - y ^ 2 - z ^ 2) hSphere
    ring_nf at hXSquare
    rw [hXSquare]
    ring

theorem EqualSetsSoqqtstqm1₁AndSoqqtstqm1₂ : Soqqtstqm1₁ = Soqqtstqm1₂ := by
  ext ⟨r, x, y, z⟩
  dsimp only [Soqqtstqm1₁, Set.mem_setOf_eq, Soqqtstqm1₂]
  simp only [one_div, Quaternion.ext_iff]
  constructor
  · intros h₀
    rcases h₀ with ⟨rx, ry, rz, hx, hSphere⟩
    rcases hx with ⟨hr, hx, hy, hz⟩
    rw [← hx, ← hy, ← hz] at hSphere
    have hrSquare := congrArg (λ (x₀ : ℝ) => x₀ ^ 2) hr
    simp only [inv_pow] at hrSquare
    have hNormSq := congrArg (λ (x₀ : ℝ) => x₀ + r ^ 2) hSphere
    nth_rewrite 2 [hrSquare] at hNormSq
    simp only at hNormSq
    ring_nf at hNormSq
    let hSqrtNormSquare := congrArg Real.sqrt (Quaternion.normSq_eq_norm_mul_self (QuaternionAlgebra.mk r x y z))
    simp only [norm_nonneg, Real.sqrt_mul_self] at hSqrtNormSquare
    rw [← hSqrtNormSquare, Quaternion.normSq_def']
    simp only [Real.sqrt_eq_one]
    constructor
    · rw [← hNormSq]
      ring_nf
    · exact hr
  · intros h₀
    use x
    use y
    use z
    rcases h₀ with ⟨hNorm, hr⟩
    simp only [hr, and_self, true_and]
    have hNormSqMr := congrArg (λ (x₀ : ℝ) => x₀ * x₀ - 1 / 4) hNorm
    simp only [hr, ← normSq_eq_norm_mul_self, normSq_def', inv_pow, one_div, mul_one] at hNormSqMr
    ring_nf at hNormSqMr ⊢
    rw [hNormSqMr]

theorem EqualSetsSoqqtstqm1₁AndSoqqtstqm1₃ : Soqqtstqm1₁ = Soqqtstqm1₃ := by
  ext ⟨r, x, y, z⟩
  dsimp only [Soqqtstqm1₁, Set.mem_setOf_eq, Soqqtstqm1₃, Soqtstn1₁]
  simp only [one_div, Quaternion.ext_iff, re_add, imI_add, imJ_add, imK_add]
  constructor
  · intros h₀
    rcases h₀ with ⟨rx, ry, rz, hx, hSphere⟩
    rcases hx with ⟨hr, hx, hy, hz⟩
    use (QuaternionAlgebra.mk 0 (rx * 2 / Real.sqrt 3) (ry * 2 / Real.sqrt 3) (rz * 2 / Real.sqrt 3))
    simp only [true_and]
    constructor
    · use rx * 2 / Real.sqrt 3
      use ry * 2 / Real.sqrt 3
      use rz * 2 / Real.sqrt 3
      constructor
      · simp only [and_self]
      · ring_nf
        have h3g0 : (0 : ℝ) ≤ 3 := by linarith
        simp only [inv_pow, Real.sq_sqrt h3g0]
        have hSphere₂ := congrArg (λ (x₀ : ℝ) => x₀ * 4 / 3) hSphere
        simp only at hSphere₂
        norm_num at hSphere₂
        rw [← hSphere₂]
        ring
    · have h2 : (2 : ℍ) = ↑(2 : ℝ) := rfl
      constructor
      · rw [hr, h2]
        quat_simp
      · constructor
        · rw [hx, h2]
          quat_simp
          ring
        · constructor
          · rw [hy, h2]
            quat_simp
            ring
          · rw [hz, h2]
            quat_simp
            ring
  · intros h₀
    rcases h₀ with ⟨qim, hx₁, hx₂⟩
    rcases hx₁ with ⟨rx, ry, rz, hQim, hSphere⟩
    rcases hx₂ with ⟨hr, hx, hy, hz⟩
    rcases hQim with ⟨hQimR, hQimI, hQimJ, hQimK⟩
    use x
    use y
    use z
    simp only [and_self, and_true]
    have h2 : (2 : ℍ) = ↑(2 : ℝ) := rfl
    constructor
    · rw [hr, h2]
      quat_simp
      simp only [hQimR, zero_mul, mul_zero, add_zero]
    · rw [hx, hy, hz, h2]
      quat_simp
      simp only [hQimI, hQimJ, hQimK]
      ring_nf
      have h3 : (0 : ℝ) ≤ 3 := by linarith
      simp only [Real.sq_sqrt h3]
      nlinarith [hSphere]

-- Declare a Set Of Quaternions Whose 4th Power Is Negative 1
def Soqw4pin1₀ : Set ℍ[ℝ] := {q₀ : ℍ[ℝ] | -1 = q₀ ^ 4}
def Soqw4pin1₁ : Set ℍ[ℝ] := {q₁ : ℍ[ℝ] | ∃ (rx ry rz Pm1 : ℝ),
  ((Pm1 ^ 2 = 1) ∧ q₁ * (Real.sqrt 2) = ⟨Pm1, rx, ry, rz⟩ ∧
  rx * rx + ry * ry + rz * rz = 1)}
def Soqw4pin1₂ : Set ℍ[ℝ] := {q₂ : ℍ[ℝ] | ‖q₂‖ = 1 ∧ (q₂.re ^ 2 = 1 / 2)}
def Soqw4pin1₃ : Set ℍ[ℝ] := {q₃ : ℍ[ℝ] | ∃ (qim : ℍ[ℝ]) (Pm1 : ℝ),
  ((Pm1 ^ 2 = 1) ∧ qim ∈ Soqtstn1₁ ∧ q₃ * (Real.sqrt 2) = Pm1 + qim)}

theorem EqualSetsSoqw4pin1₀AndSoqw4pin1₂ : Soqw4pin1₀ = Soqw4pin1₂ := by
  ext q
  dsimp only [Soqw4pin1₀, Set.mem_setOf_eq, Soqw4pin1₂]
  simp only [one_div]
  constructor
  · intros h
    have hNormSq : ‖q‖ = 1 := by
      have hNormPow4 : ‖q‖ ^ 4 = 1 := by
        rw [← norm_pow, ← h]
        simp only [norm_neg, one_mem, CStarRing.norm_of_mem_unitary]
      have hNormPos : 0 ≤ ‖q‖ := norm_nonneg q
      rw [pow_eq_one_iff_of_nonneg hNormPos (by norm_num : 4 ≠ 0)] at hNormPow4
      exact hNormPow4
    constructor
    · exact hNormSq
    · let q2 := q * q
      have hq2 : q2 * q2 = -1 := by
        rw [← pow_two]
        convert h
        ring_nf
        dsimp only [q2]
        rw [← pow_two, ← pow_mul]
        norm_num
        exact h.symm
      have hq2Re : q2.re = 0 := by
        have hRe : (q2 * q2).re = -1 := by rw [hq2]; rfl
        rw [re_mul] at hRe
        have hNormSqQ2 : ‖q2‖ = 1 := by
          rw [norm_mul, hNormSq]
          norm_num
        have hImSq : ‖q2.im‖ ^ 2 = 1 - q2.re ^ 2 := by
          have h : ‖q2‖ ^ 2 = q2.re ^ 2 + ‖q2.im‖ ^ 2 := by
            rw [pow_two ‖q2‖, ← normSq_eq_norm_mul_self]
            rw [pow_two ‖q2.im‖, ← normSq_eq_norm_mul_self]
            simp only [normSq_def, re_mul, re_star, imI_star, mul_neg, sub_neg_eq_add, imJ_star,
              imK_star, im, QuaternionAlgebra.re_im, mul_zero, QuaternionAlgebra.imI_im, zero_add,
              QuaternionAlgebra.imJ_im, QuaternionAlgebra.imK_im]
            ring
          rw [hNormSqQ2] at h
          norm_num at h
          linarith
        ring_nf at hRe
        rw [pow_two, ← normSq_eq_norm_mul_self, Quaternion.normSq_def] at hImSq
        simp only [im, re_mul, QuaternionAlgebra.re_im, re_star, mul_zero, QuaternionAlgebra.imI_im,
          imI_star, mul_neg, sub_neg_eq_add, zero_add, QuaternionAlgebra.imJ_im, imJ_star,
          QuaternionAlgebra.imK_im, imK_star] at hImSq
        ring_nf at hImSq
        have hReSub : q2.re ^ 2 - (1 - q2.re ^ 2) = -1 := by
          convert hRe using 1
          rw [← hImSq]
          ring
        have hReZero : 2 * q2.re ^ 2 = 0 := by linarith
        simp only [mul_eq_zero, OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, pow_eq_zero_iff,
          false_or] at hReZero
        exact hReZero
      have hReSimple : q2.re = 2 * q.re ^ 2 - ‖q‖ ^ 2 := by
        rw [re_mul, pow_two ‖q‖, ← normSq_eq_norm_mul_self]
        simp only [normSq, re_mul, re_star, imI_star, mul_neg, sub_neg_eq_add, imJ_star, imK_star,
          MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
        ring
      rw [hq2Re, hNormSq] at hReSimple
      linarith
  · intros h
    rcases h with ⟨hNorm, hRe⟩
    have hq2Re : (q * q).re = 0 := by
      rw [re_mul]
      have hNormSq : ‖q‖ ^ 2 = 1 := by rw [hNorm]; norm_num
      have hNormSqSplit : q.re ^ 2 + ‖q.im‖ ^ 2 = 1 := by
        have h : ‖q‖ ^ 2 = q.re ^ 2 + ‖q.im‖ ^ 2 := by
          rw [pow_two ‖q‖, ← normSq_eq_norm_mul_self, pow_two ‖q.im‖, ← normSq_eq_norm_mul_self]
          simp only [normSq_def, re_mul, re_star, imI_star, mul_neg, sub_neg_eq_add, imJ_star,
            imK_star, im, QuaternionAlgebra.re_im, mul_zero, QuaternionAlgebra.imI_im, zero_add,
            QuaternionAlgebra.imJ_im, QuaternionAlgebra.imK_im]
          ring
        rw [← h, hNormSq]
      have hImVecSq : ‖q.im‖ ^ 2 = 1 - q.re ^ 2 := by linarith
      have h_re_eq : q.re * q.re - q.imI * q.imI - q.imJ * q.imJ - q.imK * q.imK = q.re ^ 2 - ‖q.im‖ ^ 2 := by
        rw [pow_two ‖q.im‖, ← normSq_eq_norm_mul_self, Quaternion.normSq_def]
        simp only [im, re_mul, QuaternionAlgebra.re_im, re_star, mul_zero, QuaternionAlgebra.imI_im,
          imI_star, mul_neg, sub_neg_eq_add, zero_add, QuaternionAlgebra.imJ_im, imJ_star,
          QuaternionAlgebra.imK_im, imK_star]
        ring
      rw [h_re_eq, hImVecSq, hRe]
      norm_num
    have hq2Norm : ‖q * q‖ = 1 := by
      rw [norm_mul, hNorm]
      norm_num
    have hq2Sq : (q * q) * (q * q) = -1 := by
      apply ext
      · rw [re_mul]
        have hImVecSq : ‖(q * q).im‖ ^ 2 = 1 := by
          have h : ‖q * q‖ ^ 2 = (q * q).re ^ 2 + ‖(q * q).im‖ ^ 2 := by
            rw [pow_two ‖q * q‖, ← normSq_eq_norm_mul_self, Quaternion.normSq_def', pow_two ‖(q * q).im‖]
            simp only [re_mul, imI_mul, imJ_mul, imK_mul, im, ← normSq_eq_norm_mul_self, normSq_def,
              QuaternionAlgebra.re_im, re_star, mul_zero, QuaternionAlgebra.imI_im, imI_star,
              neg_sub, zero_sub, QuaternionAlgebra.imJ_im, imJ_star, neg_add_rev,
              QuaternionAlgebra.imK_im, imK_star]
            ring
          rw [hq2Norm, hq2Re] at h
          simp only [one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
            zero_add] at h
          exact h.symm
        rw [hq2Re]
        simp only [mul_zero, zero_sub, re_neg, QuaternionAlgebra.re_one]
        have hSum : (q * q).imI * (q * q).imI + (q * q).imJ * (q * q).imJ +
          (q * q).imK * (q * q).imK = ‖(q * q).im‖ ^ 2 := by
          rw [pow_two, ← normSq_eq_norm_mul_self, Quaternion.normSq_def]
          simp only [imI_mul, imJ_mul, imK_mul, im, re_mul, QuaternionAlgebra.re_im, re_star,
            mul_zero, QuaternionAlgebra.imI_im, imI_star, neg_sub, zero_sub,
            QuaternionAlgebra.imJ_im, imJ_star, neg_add_rev, QuaternionAlgebra.imK_im, imK_star]
          ring
        trans -((q * q).imI * (q * q).imI + (q * q).imJ * (q * q).imJ + (q * q).imK * (q * q).imK)
        · ring
        rw [hSum, hImVecSq]
      · simp only [imI_mul, hq2Re, zero_mul, mul_zero, add_zero, imJ_mul, imK_mul, zero_add,
        imI_neg, QuaternionAlgebra.imI_one, neg_zero]
        ring
      · simp only [imJ_mul, hq2Re, zero_mul, imI_mul, imK_mul, zero_sub, mul_zero, add_zero,
        imJ_neg, QuaternionAlgebra.imJ_one, neg_zero]
        ring
      · simp only [imK_mul, hq2Re, zero_mul, imI_mul, imJ_mul, zero_add, mul_zero, add_zero,
        imK_neg, QuaternionAlgebra.imK_one, neg_zero]
        ring
    rw [← hq2Sq]
    simp only [mul_assoc, pow_succ, pow_zero, one_mul]

theorem EqualSetsSoqw4pin1₀AndSoqw4pin1₁ : Soqw4pin1₀ = Soqw4pin1₁ := by
  ext ⟨r, x, y, z⟩
  dsimp only [Soqw4pin1₀, Set.mem_setOf_eq, Soqw4pin1₁]
  constructor
  · intro h
    have hMem : ⟨r, x, y, z⟩ ∈ Soqw4pin1₂ := by
      rw [← EqualSetsSoqw4pin1₀AndSoqw4pin1₂]
      exact h
    simp only [Soqw4pin1₂, Set.mem_setOf_eq, one_div] at hMem
    rcases hMem with ⟨hNorm, hReSq⟩
    use x * Real.sqrt 2
    use y * Real.sqrt 2
    use z * Real.sqrt 2
    use r * Real.sqrt 2
    constructor
    · have h2pos : (0 : ℝ) < 2 := by norm_num
      rw [pow_two, mul_mul_mul_comm]
      rw [Real.mul_self_sqrt (le_of_lt h2pos)]
      rw [mul_comm, ← pow_two]
      rw [hReSq]
      norm_num
    constructor
    · have h2 : (Real.sqrt 2 : ℍ) = ↑(Real.sqrt 2 : ℝ) := rfl
      rw [h2]
      ext <;> simp only [re_mul, re_coe, imI_coe, imJ_coe, imK_coe, sub_zero, imI_mul, mul_zero,
        add_zero, imJ_mul, imK_mul] <;> ring
    · have h2pos : (0 : ℝ) < 2 := by norm_num
      have hSqrt2Sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (le_of_lt h2pos)
      have hNormSq : r ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 1 := by
        have h1 := congrArg (fun n => n * n) hNorm
        simp only [one_mul] at h1
        rw [← normSq_eq_norm_mul_self, normSq_def'] at h1
        linarith
      have hReSq' : r ^ 2 = (2 : ℝ)⁻¹ := hReSq
      calc (x * Real.sqrt 2) * (x * Real.sqrt 2) + (y * Real.sqrt 2) * (y * Real.sqrt 2) +
              (z * Real.sqrt 2) * (z * Real.sqrt 2)
        = (x ^ 2 + y ^ 2 + z ^ 2) * (Real.sqrt 2 ^ 2) := by ring
      _ = (x ^ 2 + y ^ 2 + z ^ 2) * 2 := by rw [hSqrt2Sq]
      _ = (1 - r ^ 2) * 2 := by linarith
      _ = 1 := by rw [hReSq']; norm_num
  · intro h
    rcases h with ⟨rx, ry, rz, Pm1, hPm1Sq, hq, hSphere⟩
    have hMem : ⟨r, x, y, z⟩ ∈ Soqw4pin1₂ := by
      simp only [Soqw4pin1₂, Set.mem_setOf_eq, one_div]
      have h2 : (Real.sqrt 2 : ℍ) = ↑(Real.sqrt 2 : ℝ) := rfl
      rw [h2] at hq
      have hqExt := hq
      simp only [Quaternion.ext_iff, re_mul, re_coe, imI_coe, sub_zero, imI_mul, mul_zero, add_zero,
        imJ_mul, imJ_coe, imK_mul, imK_coe] at hqExt
      rcases hqExt with ⟨hr, hx, hy, hz⟩
      constructor
      · have h2pos : (0 : ℝ) < 2 := by norm_num
        have hSqrt2Ne0 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr h2pos
        have hr' : r = Pm1 / Real.sqrt 2 := by field_simp at hr ⊢; linarith
        have hx' : x = rx / Real.sqrt 2 := by field_simp at hx ⊢; linarith
        have hy' : y = ry / Real.sqrt 2 := by field_simp at hy ⊢; linarith
        have hz' : z = rz / Real.sqrt 2 := by field_simp at hz ⊢; linarith
        rw [hr', hx', hy', hz']
        have hSqrt2Sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (le_of_lt h2pos)
        have hPm1Sq' : Pm1 ^ 2 = 1 := hPm1Sq
        have hSpherePow : rx ^ 2 + ry ^ 2 + rz ^ 2 = 1 := by
          calc rx ^ 2 + ry ^ 2 + rz ^ 2 = rx * rx + ry * ry + rz * rz := by ring
          _ = 1 := hSphere
        have hNormSqVal : (Pm1 / Real.sqrt 2) ^ 2 + (rx / Real.sqrt 2) ^ 2 +
            (ry / Real.sqrt 2) ^ 2 + (rz / Real.sqrt 2) ^ 2 = 1 := by
          field_simp
          rw [hSqrt2Sq]
          have h1 : Pm1 ^ 2 + rx ^ 2 + ry ^ 2 + rz ^ 2 = 2 := by linarith
          linarith
        let q' : ℍ[ℝ] := ⟨Pm1 / Real.sqrt 2, rx / Real.sqrt 2, ry / Real.sqrt 2, rz / Real.sqrt 2⟩
        have hNormMulSelf : ‖q'‖ * ‖q'‖ = 1 := by
          rw [← normSq_eq_norm_mul_self, normSq_def']
          exact hNormSqVal
        have hNormNonneg : 0 ≤ ‖q'‖ := norm_nonneg _
        nlinarith [sq_nonneg ‖q'‖]
      · have h2pos : (0 : ℝ) < 2 := by norm_num
        have hSqrt2Ne0 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr h2pos
        have hr' : r = Pm1 / Real.sqrt 2 := by field_simp at hr ⊢; linarith
        simp only [hr', pow_two, div_mul_div_comm]
        rw [Real.mul_self_sqrt (le_of_lt h2pos)]
        have hPm1Sq' : Pm1 * Pm1 = 1 := by rw [← pow_two]; exact hPm1Sq
        rw [hPm1Sq']
        norm_num
    have hGoal : ⟨r, x, y, z⟩ ∈ Soqw4pin1₀ := by
      rw [EqualSetsSoqw4pin1₀AndSoqw4pin1₂]
      exact hMem
    exact hGoal

theorem EqualSetsSoqw4pin1₁AndSoqw4pin1₃ : Soqw4pin1₁ = Soqw4pin1₃ := by
  ext ⟨r, x, y, z⟩
  dsimp only [Soqw4pin1₁, Set.mem_setOf_eq, Soqw4pin1₃, Soqtstn1₁]
  constructor
  · intro ⟨rx, ry, rz, Pm1, hPm1Sq, hq, hSphere⟩
    use ⟨0, rx, ry, rz⟩
    use Pm1
    constructor
    · exact hPm1Sq
    constructor
    · use rx, ry, rz
    · rw [hq]
      ext
      · simp only [re_add, re_coe, add_zero]
      · simp only [imI_add, imI_coe, zero_add]
      · simp only [imJ_add, imJ_coe, zero_add]
      · simp only [imK_add, imK_coe, zero_add]
  · intro ⟨qim, Pm1, hPm1Sq, hQim, hq⟩
    rcases hQim with ⟨rx, ry, rz, hQimEq, hSphere⟩
    use rx, ry, rz, Pm1
    constructor
    · exact hPm1Sq
    constructor
    · rw [hq, hQimEq]
      ext
      · simp only [re_add, re_coe, add_zero]
      · simp only [imI_add, imI_coe, zero_add]
      · simp only [imJ_add, imJ_coe, zero_add]
      · simp only [imK_add, imK_coe, zero_add]
    · exact hSphere
