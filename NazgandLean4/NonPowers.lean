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
  have hk0 : k ≠ 0 := by
    intro hk
    rw [OverUnityNat, hk] at h
    simp only [gt_iff_lt, Set.mem_setOf_eq, not_lt_zero] at h
  let g := PrimeExponentsGcd k
  have hg_pos : g > 0 := by
    rw [gt_iff_lt, Nat.pos_iff_ne_zero, Ne]
    intro hg0
    simp only [g, PrimeExponentsGcd] at hg0
    rw [Finset.gcd_eq_zero_iff] at hg0
    have : k = 1 := by
       rw [← Nat.factorization_prod_pow_eq_self hk0]
       apply Finset.prod_eq_one
       intro p hp
       simp only [hg0 p hp, pow_zero]
    subst this
    simp only [OverUnityNat, gt_iff_lt, Set.mem_setOf_eq, lt_self_iff_false] at h
  let a := k.factorization.support.prod (λ p => p ^ (k.factorization p / g))
  have hk_eq : k = a ^ g := by
    rw [← Finset.prod_pow]
    nth_rw 1 [← Nat.factorization_prod_pow_eq_self hk0]
    refine Finset.prod_congr rfl (λ p hp => ?_)
    rw [← Nat.pow_mul]
    congr 1
    exact (Nat.div_mul_cancel (Finset.gcd_dvd hp)).symm
  use a
  constructor
  · constructor
    · rw [NonPowerNatPrimeExponentsGcdEq1]
      simp only [Set.mem_setOf_eq]
      have hg : g = g * PrimeExponentsGcd a := by
         conv_lhs => simp only [g]
         rw [hk_eq, PrimeExponentsGcdOfPower]
      nth_rw 1 [← mul_one g] at hg
      exact Nat.mul_left_cancel hg_pos hg
    · use g
  · intro a' ⟨ha', ⟨b', h_eq⟩⟩
    rw [NonPowerNatPrimeExponentsGcdEq1] at ha'
    simp only [Set.mem_setOf_eq] at ha'
    have hb' : b' = g := by
      simp only [g]
      rw [h_eq, PrimeExponentsGcdOfPower, ha'.symm, mul_one]
    subst hb'
    rw [h_eq] at hk_eq
    have h_ne_zero : g ≠ 0 := Nat.pos_iff_ne_zero.mp hg_pos
    exact (Nat.pow_left_inj h_ne_zero).mp hk_eq

theorem OverUnityNatEqNonPowerNatToThePowerOfPosNat :
  OverUnityNat = {k : ℕ | ∃ a b : ℕ, a ∈ NonPowerNat ∧ b ∈ PosNat ∧ k = a ^ b} := by
  ext k
  constructor
  · intro hk
    obtain ⟨a, ha, b, rfl⟩ := (OverUnityNatUniqueNonPowerNatBase k hk).exists
    use a, b
    refine ⟨ha, ?_, rfl⟩
    by_contra hb
    simp only [PosNat, Set.mem_setOf_eq, not_lt, Nat.le_zero_eq] at hb
    rw [hb, pow_zero] at hk
    simp only [OverUnityNat, gt_iff_lt, Set.mem_setOf_eq, lt_self_iff_false] at hk
  · rintro ⟨a, b, ha, hb, rfl⟩
    simp only [OverUnityNat, gt_iff_lt, Set.mem_setOf_eq]
    simp only [PosNat, gt_iff_lt, Set.mem_setOf_eq] at hb
    simp only [NonPowerNat, gt_iff_lt, not_exists, not_and, not_lt, Set.mem_setOf_eq] at ha
    have ha_gt_1 : a > 1 := by
      by_contra ha_le
      simp only [not_lt] at ha_le
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha_le with rfl | rfl
      · specialize ha 0 2 (by simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow]); linarith
      · specialize ha 1 2 (by simp only [one_pow]); linarith
    exact Nat.one_lt_pow (Nat.ne_zero_of_lt hb) ha_gt_1

theorem NonPowerNatToThePowerOfPosNatUniqueRepresentation (a₀ b₀ a₁ b₁ : ℕ)
  (h0 : a₀ ∈ NonPowerNat) (h1 : b₀ ∈ PosNat)
  (h2 : a₁ ∈ NonPowerNat) (h4 : a₀ ^ b₀ = a₁ ^ b₁) : a₀ = a₁ ∧ b₀ = b₁ := by
  have ha0_gt_1 : a₀ > 1 := by
    by_contra ha
    simp only [not_lt] at ha
    simp only [NonPowerNat, gt_iff_lt, not_exists, not_and, not_lt, Set.mem_setOf_eq] at h0
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl
    · specialize h0 0 2 (by simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow])
      linarith
    · specialize h0 1 2 (by simp only [one_pow]); linarith
  have hk_gt_1 : a₀ ^ b₀ > 1 := Nat.one_lt_pow (Nat.ne_of_gt h1) ha0_gt_1
  have h_unique := OverUnityNatUniqueNonPowerNatBase (a₀ ^ b₀) hk_gt_1
  obtain ⟨a, _, h_uniq⟩ := h_unique
  have ha0_eq : a₀ = a := h_uniq a₀ ⟨h0, b₀, rfl⟩
  have ha1_eq : a₁ = a := h_uniq a₁ ⟨h2, b₁, h4⟩
  subst ha0_eq ha1_eq
  refine ⟨rfl, ?_⟩
  apply Nat.pow_right_injective ha0_gt_1 h4

def PowerTower (list : List ℕ) : ℕ :=
  match list with
  | [] => 1
  | h :: t => h ^ PowerTower t

def ListOfNonPowers (list : List ℕ) : Prop :=
  match list with
  | [] => true
  | h :: t => (h ∈ NonPowerNat) ∧ ListOfNonPowers t

theorem PosNatExistsUniqueNonPowerPowerTower (k : ℕ) (h0 : k ∈ PosNat) :
  ∃! (list : List ℕ), ListOfNonPowers list ∧ PowerTower list = k := by
  have PosNonPowerPowerTower : ∀ (l : List ℕ), ListOfNonPowers l → 0 < PowerTower l := by
    intro l hl
    induction l with
    | nil => simp only [PowerTower, zero_lt_one]
    | cons h t ih =>
      rw [ListOfNonPowers] at hl
      simp only [PowerTower]
      have h_gt_0 : h > 0 := by
        have h9 := hl.1
        simp only [NonPowerNat, gt_iff_lt, not_exists, not_and, not_lt, Set.mem_setOf_eq] at h9
        by_contra hz
        simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero] at hz
        subst hz
        specialize h9 0 2 (by simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow])
        linarith
      apply Nat.pow_pos h_gt_0
  induction k using Nat.strong_induction_on with | h k ih =>
  by_cases h1 : k = 1
  · subst h1
    use []
    simp only [ListOfNonPowers, PowerTower, true_and]
    rintro list ⟨hl, hp⟩
    match list with
    | [] => rfl
    | h :: t =>
      exfalso
      have h_np : h ∈ NonPowerNat := hl.1
      have h_gt_1 : h > 1 := by
        by_contra h_le
        simp only [not_lt] at h_le
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h_le with rfl | rfl
        · simp only [NonPowerNat, gt_iff_lt, not_exists, not_and, not_lt, Set.mem_setOf_eq] at h_np
          specialize h_np 0 2 (by simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
            zero_pow]); linarith
        · simp only [NonPowerNat, gt_iff_lt, not_exists, not_and, not_lt, Set.mem_setOf_eq] at h_np
          specialize h_np 1 2 (by simp only [one_pow]); linarith
      simp only [PowerTower, pow_eq_one_iff] at hp
      have : PowerTower t = 0 := by
        by_contra h_nz
        have t_pos : PowerTower t > 0 := Nat.pos_of_ne_zero h_nz
        have h_pow_gt : h ^ PowerTower t > 1 := Nat.one_lt_pow (ne_of_gt t_pos) h_gt_1
        grind only
      have pt_pos : PowerTower t > 0 := PosNonPowerPowerTower t hl.2
      linarith
  · have k_gt_1 : k > 1 := Nat.lt_of_le_of_ne (h0) (Ne.symm h1)
    have h_unique := OverUnityNatUniqueNonPowerNatBase k k_gt_1
    obtain ⟨a, ⟨ha, b, rfl⟩, h_uniq_base⟩ := h_unique
    have b_pos : b ∈ PosNat := by
       by_contra hb
       simp only [PosNat, gt_iff_lt, Set.mem_setOf_eq, not_lt, nonpos_iff_eq_zero] at hb
       have : b = 0 := by linarith
       subst this
       rw [pow_zero] at h1
       exact h1 rfl
    have b_lt_k : b < a ^ b := by
       apply Nat.lt_pow_self
       by_contra ha_le
       simp only [not_lt] at ha_le
       rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha_le with rfl | rfl
       · simp only [NonPowerNat, gt_iff_lt, not_exists, not_and, not_lt, Set.mem_setOf_eq] at ha
         specialize ha 0 2 (by simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow])
         linarith
       · simp only [NonPowerNat, gt_iff_lt, not_exists, not_and, not_lt, Set.mem_setOf_eq] at ha
         specialize ha 1 2 (by simp only [one_pow]); linarith
    obtain ⟨tl, htl_prop, htl_uniq⟩ := ih b b_lt_k b_pos
    use a :: tl
    constructor
    · simp only [ListOfNonPowers, PowerTower]
      constructor
      · simp only [ha, htl_prop, and_self]
      · simp only [htl_prop]
    · intro l' ⟨hl', hp'⟩
      match l' with
      | [] =>
        simp only [PowerTower] at hp'
        rw [hp'] at k_gt_1
        linarith
      | h' :: t' =>
        simp only [ListOfNonPowers, PowerTower] at hl' hp'
        have pt_pos : PowerTower t' ∈ PosNat := PosNonPowerPowerTower t' hl'.2
        have h4 : a ^ b = h' ^ PowerTower t' := by rw [hp']
        have h_base_eq : a = h' ∧ b = PowerTower t' :=
           NonPowerNatToThePowerOfPosNatUniqueRepresentation a b h' (PowerTower t') ha b_pos hl'.1 h4
        rcases h_base_eq with ⟨rfl, rfl⟩
        congr
        apply htl_uniq t'
        exact ⟨hl'.2, rfl⟩
