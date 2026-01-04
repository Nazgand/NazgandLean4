import Mathlib
set_option maxHeartbeats 0

-- Extends Mersenne Numbers to bases other than 2.

def ExtendedMersenne (b k : ℕ) : ℕ :=
  (Finset.range k).sum (λ (m : ℕ) ↦ b ^ m)

theorem ExtendedMersenneMulPredB (b k : ℕ) :
  (ExtendedMersenne b k) * (b - 1) = (b ^ k) - 1 := by
  induction k with
  | zero =>
    simp only [ExtendedMersenne, Finset.range_zero, Finset.sum_empty, zero_mul, pow_zero, tsub_self]
  | succ n ih =>
    rw [ExtendedMersenne, Finset.sum_range_succ]
    have h : (Finset.range n).sum (fun m ↦ b ^ m) = ExtendedMersenne b n := rfl
    rw [h, add_mul, ih]
    cases b with
    | zero =>
      simp only [zero_tsub, mul_zero, add_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        not_false_eq_true, zero_pow]
      cases n <;> simp only [pow_zero, tsub_self, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        not_false_eq_true, zero_pow, zero_tsub]
    | succ m =>
      simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
      have h_le : 1 ≤ (m + 1) ^ n := Nat.one_le_pow n (m + 1) (Nat.succ_pos m)
      have h_comm : (m + 1) ^ n - 1 + (m + 1) ^ n * m = (m + 1) ^ n + (m + 1) ^ n * m - 1 :=
        (Nat.sub_add_comm h_le).symm
      rw [h_comm]
      rw [mul_comm ((m + 1) ^ n)]
      nth_rw 1 [← one_mul ((m + 1) ^ n)]
      rw [← add_mul, add_comm 1 m, mul_comm, ← pow_succ]

theorem ExtendedMersenneFactorableK (b k₀ k₁ : ℕ) :
  ExtendedMersenne b (k₀ * k₁) = (ExtendedMersenne b k₀) * (ExtendedMersenne (b ^ k₀) k₁) := by
  induction k₁ with
  | zero =>
    simp only [ExtendedMersenne, mul_zero, Finset.range_zero, Finset.sum_empty]
  | succ n ih =>
    simp only [ExtendedMersenne] at ih ⊢
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ, mul_add]
    congr 1
    simp only [pow_add, pow_mul]
    rw [mul_comm, Finset.mul_sum]

theorem ExtendedMersennePrimeImp (b k : ℕ) :
  Nat.Prime (ExtendedMersenne b k) → Nat.Prime k := by
  cases b with
  | zero =>
    simp only [ExtendedMersenne, zero_geom_sum]
    intro h
    cases k with
    | zero => cases (Nat.not_prime_zero h)
    | succ k => cases (Nat.not_prime_one h)
  | succ m =>
    intro hp
    have hk : k ≥ 2 := by
      cases k with
      | zero => simp only [ExtendedMersenne, Finset.range_zero, Finset.sum_empty] at hp; cases (Nat.not_prime_zero hp)
      | succ k' =>
        cases k' with
        | zero => simp only [ExtendedMersenne, zero_add, Finset.range_one, Finset.sum_singleton,
          pow_zero] at hp; cases (Nat.not_prime_one hp)
        | succ k'' => apply Nat.le_add_left
    by_contra hnp
    rcases Nat.exists_dvd_of_not_prime2 hk hnp with ⟨x, ⟨y, rfl⟩, hx, hy⟩
    have h_prod : ExtendedMersenne (m + 1) x * ExtendedMersenne ((m + 1) ^ x) y = ExtendedMersenne (m + 1) (x * y) :=
      (ExtendedMersenneFactorableK (m + 1) x y).symm
    rw [← h_prod] at hp
    have hx2 : x ≥ 2 := hx
    have hy2 : y ≥ 2 := by
      by_contra hy_lt
      rw [not_le] at hy_lt
      have : y = 1 := by
        cases y with
        | zero =>
           simp only [mul_zero, not_lt_zero] at hy
        | succ y' =>
           cases y'
           · rfl
           · simp_all only [ge_iff_le, Nat.add_eq_right, Nat.add_eq_zero_iff, one_ne_zero,
             and_false]; linarith
      subst this
      simp only [mul_one, lt_self_iff_false] at hy
    have h1 : ExtendedMersenne (m + 1) x > 1 := by
      calc ExtendedMersenne (m + 1) x
        _ ≥ (Finset.range 2).sum (fun i ↦ (m + 1) ^ i) :=
             Finset.sum_le_sum_of_subset_of_nonneg
               (fun a ha => Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 ha) hx2))
               (fun _ _ _ ↦ Nat.zero_le _)
        _ = 1 + (m + 1) := by simp only [geom_sum_two]; ring
        _ > 1 := Nat.lt_add_of_pos_right (Nat.succ_pos m)
    have h2 : ExtendedMersenne ((m + 1) ^ x) y > 1 := by
      calc ExtendedMersenne ((m + 1) ^ x) y
        _ ≥ (Finset.range 2).sum (fun i ↦ ((m + 1) ^ x) ^ i) :=
             Finset.sum_le_sum_of_subset_of_nonneg
               (fun a ha => Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 ha) hy2))
               (fun _ _ _ ↦ Nat.zero_le _)
        _ = 1 + ((m + 1) ^ x) := by simp only [geom_sum_two]; ring
        _ > 1 := Nat.lt_add_of_pos_right (Nat.pow_pos (Nat.succ_pos m))
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp (ExtendedMersenne (m + 1) x) (Dvd.intro _ rfl)) with hA | hA
    · rw [hA] at h1; cases (Nat.lt_irrefl 1 h1)
    · have hB : ExtendedMersenne ((m + 1) ^ x) y = 1 := by
         nth_rw 1 [← mul_one (ExtendedMersenne (m + 1) x)] at hA
         exact Nat.eq_of_mul_eq_mul_left (Nat.lt_trans (Nat.zero_lt_one) h1) hA.symm
      rw [hB] at h2; cases (Nat.lt_irrefl 1 h2)

theorem ExtendedMersenneGcdK (b k₀ k₁ : ℕ) :
  Nat.gcd (ExtendedMersenne b k₀) (ExtendedMersenne b k₁) = ExtendedMersenne b (Nat.gcd k₀ k₁) := by
  cases b with
  | zero =>
    simp only [ExtendedMersenne, zero_geom_sum, Nat.gcd_eq_zero_iff]
    cases k₀ <;> cases k₁ <;> simp
  | succ m =>
    cases m with
    | zero =>
      simp only [ExtendedMersenne, zero_add, one_pow, Finset.sum_const, Finset.card_range,
        smul_eq_mul, mul_one]
    | succ m' =>
      let b' := m' + 2
      have hb : b' - 1 > 0 := Nat.succ_pos m'
      apply Nat.eq_of_mul_eq_mul_right hb
      rw [← Nat.gcd_mul_right, ExtendedMersenneMulPredB, ExtendedMersenneMulPredB, ExtendedMersenneMulPredB]
      exact Nat.pow_sub_one_gcd_pow_sub_one b' k₀ k₁
