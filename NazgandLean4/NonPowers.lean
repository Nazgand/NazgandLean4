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
  sorry

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
