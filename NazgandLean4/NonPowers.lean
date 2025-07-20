import Mathlib
set_option maxHeartbeats 0

def PosNat : Set ℕ := {k : ℕ | k > 0}
def OverUnityNat : Set ℕ := {k : ℕ | k > 1}
def NonPowerNat : Set ℕ := {k : ℕ | ¬(∃ a b : ℕ, k = a ^ b ∧ b > 1)}

-- the greatest common divisor of the prime exponents in the factorization of k
def PrimeExponentsGcd (k : ℕ) : ℕ := k.factorization.support.gcd k.factorization

theorem PrimeExponentsGcdOfPower (a b : ℕ) : PrimeExponentsGcd (a ^ b) = b * PrimeExponentsGcd a := by
  sorry

theorem NonPowerNatPrimeExponentsGcdEq1 : NonPowerNat = {k : ℕ | 1 = PrimeExponentsGcd k} := by
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
