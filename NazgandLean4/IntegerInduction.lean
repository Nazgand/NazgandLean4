import Mathlib
set_option maxHeartbeats 0
open Classical Finset Nat

lemma IntegerInduction (p : ℤ → Prop) :
  (∀ (n : ℤ), p n) ↔ ((∃ (k : ℤ), p k) ∧ (∀ (m : ℤ), p m ↔ p (m + 1))) := by
  constructor
  · intros h₀
    constructor
    · use 391547
      exact h₀ 391547
    · intros m
      simp only [h₀ m, h₀ (m + 1)]
  · intros h₀
    obtain ⟨he, hi⟩ := h₀
    obtain ⟨k, hk⟩ := he
    exact fun n => (fun hsucc a b => (Succ.rec_linear hsucc a b).mpr) hi n k hk

lemma WavelengthRestate (p : ℤ → Prop) (k : ℤ) :
  (∀ (m : ℤ), p m ↔ p (m + k)) ↔ (∀ (m k₀ : ℤ), p m ↔ p (m + k₀ * k)) := by
  constructor
  · intros h
    rw [forall_swap, IntegerInduction]
    constructor
    · use 0
      simp only [zero_mul, add_zero, forall_const]
    · intros m
      constructor
      · intros h₀ k₀
        rw [h₀ k₀, h]
        ring_nf
      · intros h₀ k₀
        rw [h₀ k₀, h (k₀ + m * k)]
        ring_nf
  · intros h m
    have h₀ := h m 1
    simp only [one_mul] at h₀
    exact h₀

lemma WavelengthGCD (p : ℤ → Prop) (k₀ k₁ : ℕ+) : (∀ (m : ℤ), p m ↔ p (m + (Nat.gcd k₀ k₁))) ↔
  ((∀ (m : ℤ), p m ↔ p (m + k₀)) ∧ (∀ (m : ℤ), p m ↔ p (m + k₁))) := by
  constructor
  · intros h₀
    constructor
    · sorry
    · sorry
  · intros h₀
    obtain ⟨h₁, h₂⟩ := h₀
    sorry
