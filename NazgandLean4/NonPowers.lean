import Mathlib
set_option maxHeartbeats 0

def PosNat : Set ℕ := {k : ℕ | k > 0}
def OverUnityNat : Set ℕ := {k : ℕ | k > 1}
def NonPowerNat : Set ℕ := {k : ℕ | ¬(∃ a b : ℕ, k = a ^ b ∧ b > 1)}

-- the greatest common divisor of the prime exponents in the factorization of k
def PrimeExponentsGcd (k : ℕ) : ℕ := k.factorization.support.gcd k.factorization

theorem PrimeExponentsGcdOfPower (a b : ℕ) :
  PrimeExponentsGcd (a ^ b) = b * PrimeExponentsGcd a := by
  unfold PrimeExponentsGcd
  by_cases hb : b = 0
  · rw [hb, pow_zero, Nat.zero_mul, Nat.factorization_one, Finsupp.support_zero, Finset.gcd_empty]
  · have h_supp : (b • a.factorization).support = a.factorization.support := by
      ext x
      simp only [Finsupp.mem_support_iff, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [mul_ne_zero_iff, and_iff_right hb]
    have h_coe : ⇑(b • a.factorization) = fun x => b * a.factorization x := by
      ext
      simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [Nat.factorization_pow, h_coe, Finset.gcd_mul_left, h_supp, normalize_eq,
      Nat.support_factorization]

theorem NonPowerNatPrimeExponentsGcdEq1 :
  NonPowerNat = {k : ℕ | 1 = PrimeExponentsGcd k} := by
  ext k
  simp only [NonPowerNat, Set.mem_setOf_eq]
  constructor
  · intro h_np
    by_contra h_g
    let g := PrimeExponentsGcd k
    have hg_ne_1 : g ≠ 1 := by exact Ne.symm (Ne.intro h_g)
    by_cases hg0 : g = 0
    · have : k = 0 ∨ k = 1 := by
        simp only [g, PrimeExponentsGcd] at hg0
        by_cases hk : k = 0; · left; exact hk
        right
        rw [← Nat.factorization_prod_pow_eq_self hk]
        rw [Finset.gcd_eq_zero_iff] at hg0
        apply Finset.prod_eq_one
        intro p hp
        exfalso
        exact (Finsupp.mem_support_iff.mp hp) (hg0 p hp)
      rcases this with rfl | rfl
      · apply h_np; use 0, 2; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        gt_iff_lt, Nat.one_lt_ofNat, and_self]
      · apply h_np; use 1, 2; simp only [one_pow, gt_iff_lt, Nat.one_lt_ofNat, and_self]
    · have hk0 : k ≠ 0 := by
        intro hk
        simp only [PrimeExponentsGcd, hk, Nat.factorization_zero, Finsupp.support_zero,
          Finsupp.coe_zero, Finset.gcd_empty, not_true_eq_false, g] at hg0
      have hg_gt_1 : g > 1 :=
        Nat.lt_of_le_of_ne (Nat.pos_of_ne_zero hg0) hg_ne_1.symm
      let root := k.factorization.support.prod (λ p => p ^ (k.factorization p / g))
      have hk : k = root ^ g := by
        rw [← Finset.prod_pow]
        nth_rw 1 [← Nat.factorization_prod_pow_eq_self hk0]
        refine Finset.prod_congr rfl (λ p hp => ?_)
        rw [← Nat.pow_mul]
        congr 1
        have h_div : g ∣ k.factorization p := Finset.gcd_dvd hp
        exact (Nat.div_mul_cancel h_div).symm
      apply h_np
      use root, g
  · intro h_gcd ⟨a, b, hk, hb⟩
    rw [hk, PrimeExponentsGcdOfPower] at h_gcd
    have hb_eq_1 : b = 1 := Nat.eq_one_of_dvd_one (Dvd.intro _ h_gcd.symm)
    linarith

theorem OverUnityNatUniqueNonPowerNatBase (k : ℕ) (h : k ∈ OverUnityNat) :
  ∃! (a : ℕ), (a ∈ NonPowerNat ∧ ∃ (b : ℕ), k = a ^ b) := by
  sorry

theorem OverUnityNatEqNonPowerNatToThePowerOfPosNat :
  OverUnityNat = {k : ℕ | ∃ a b : ℕ, a ∈ NonPowerNat ∧ b ∈ PosNat ∧ k = a ^ b} :=
  sorry

theorem NonPowerNatToThePowerOfPosNatUniqueRepresentation (a₀ b₀ a₁ b₁ : ℕ)
  (h0 : a₀ ∈ NonPowerNat) (h1 : b₀ ∈ PosNat)
  (h2 : a₁ ∈ NonPowerNat) (h3 : b₁ ∈ PosNat)
  (h4 : a₀ ^ b₀ = a₁ ^ b₁) : a₀ = a₁ ∧ b₀ = b₁ :=
  sorry

def PowerTower (list : List ℕ) : ℕ :=
  match list with
  | [] => 1
  | h :: t => h ^ PowerTower t

def ListOfNonPowers (list : List ℕ) : Prop :=
  match list with
  | [] => true
  | h :: t => (h ∈ NonPowerNat) ∧ ListOfNonPowers t

theorem PosNatExistsUniqueNonPowerPowerTower (k : ℕ) (h0 : k ∈ PosNat) :
  ∃! (list : List ℕ), ListOfNonPowers list ∧ PowerTower list = k :=
  sorry
