import Mathlib
set_option maxHeartbeats 0

def PosNat : Set ℕ := {k : ℕ | k > 0}
def OverUnityNat : Set ℕ := {k : ℕ | k > 1}
def PowerNat : Set ℕ := {k : ℕ | ∃ a b : ℕ, k = a ^ b ∧ b > 1}
def NonPowerNat : Set ℕ := {k : ℕ | ¬ k ∈ PowerNat}

def NonPowerPowerTowerHeightNeg1 : Set ℕ := {k : ℕ | k = 0}
def NonPowerPowerTower (height : ℕ) : Set ℕ :=
  if height = 0 then
    {k : ℕ | ∃ a b : ℕ, a ∈ NonPowerNat ∧ b ∈ NonPowerPowerTowerHeightNeg1
    ∧ k = a ^ b}
  else
    {k : ℕ | ∃ a b : ℕ, a ∈ NonPowerNat ∧ b ∈ NonPowerPowerTower (height - 1)
    ∧ k = a ^ b}

lemma OverUnityNatEqNonPowerNatToThePowerOfPosNat :
  OverUnityNat = {k : ℕ | ∃ a b : ℕ, a ∈ NonPowerNat ∧ b ∈ PosNat ∧ k = a ^ b} :=
  sorry

lemma NonPowerNatToThePowerOfPosNatUniqueRepresentation (a₀ b₀ a₁ b₁ : ℕ)
  (h0 : a₀ ∈ NonPowerNat) (h1 : b₀ ∈ PosNat)
  (h2 : a₁ ∈ NonPowerNat) (h3 : b₁ ∈ PosNat)
  (h4 : a₀ ^ b₀ = a₁ ^ b₁) : a₀ = a₁ ∧ b₀ = b₁ :=
  sorry

lemma NonPowerPowerTower1EqNonPowerNat :
  NonPowerPowerTower 1 = NonPowerNat :=
  sorry

lemma NonPowerPowerTowerUniqueHeight (k h₀ h₁ : ℕ)
  (h0 : k ∈ NonPowerPowerTower h₀) (h1 : k ∈ NonPowerPowerTower h₁) :
  h₀ = h₁ :=
  sorry

lemma PosNatHasNonPowerPowerTower (k : ℕ) (h0 : k ∈ PosNat) :
  ∃ h : ℕ, k ∈ NonPowerPowerTower h :=
  sorry
