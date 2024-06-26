import Mathlib
set_option maxHeartbeats 0
open Classical Finset

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
    exact fun n => (Succ.rec_linear hi n k).mpr hk

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

lemma associated_gcd_gcd (a b : ℤ) : Associated (IsBezout.gcd a b) (GCDMonoid.gcd a b) := by
  exact IsBezout.associated_gcd_gcd ℤ

lemma GcdLinearCombination (k₀ k₁ : ℤ) : (∃ (m₀ m₁ : ℤ), (Int.gcd k₀ k₁ = m₀ * k₀ + m₁ * k₁)) := by
  obtain ⟨m, n, h⟩ := IsBezout.gcd_eq_sum k₀ k₁
  have := associated_gcd_gcd k₀ k₁
  rw [Int.associated_iff] at this
  cases this with
  | inl h' =>
    use m, n
    rw [h, Int.coe_gcd, h']
  | inr h' =>
    use -m, -n
    rw [Int.coe_gcd]
    linarith

lemma WavelengthGcd (p : ℤ → Prop) (k₀ k₁ : ℤ) : (∀ (m : ℤ), p m ↔ p (m + (Int.gcd k₀ k₁))) ↔
  ((∀ (m : ℤ), p m ↔ p (m + k₀)) ∧ (∀ (m : ℤ), p m ↔ p (m + k₁))) := by
  constructor
  · intros h₀
    rw [WavelengthRestate] at h₀
    rw [WavelengthRestate]
    constructor
    · have h₁ : ↑(k₀.gcd k₁) ∣ k₀ := Int.gcd_dvd_left
      obtain ⟨w, hw⟩ := h₁
      intros m k
      rw [h₀ m (w * k)]
      nth_rw 2 [hw]
      ring_nf
    · have h₁ : ↑(k₀.gcd k₁) ∣ k₁ := Int.gcd_dvd_right
      obtain ⟨w, hw⟩ := h₁
      rw [WavelengthRestate]
      intros m k
      rw [h₀ m (w * k)]
      nth_rw 2 [hw]
      ring_nf
  · intros h₀
    obtain ⟨h₁, h₂⟩ := h₀
    rw [WavelengthRestate] at *
    intros m j
    obtain ⟨w₀, w₁, h₃⟩ := GcdLinearCombination k₀ k₁
    rw [h₃, h₁ m (j * w₀), h₂ (m + j * w₀ * k₀) (j * w₁)]
    ring_nf
