import Mathlib

-- well-ordering principle for natural numbers

noncomputable def ExistUniqueMinP {P : ℕ → Prop} (ExistP : ∃ (k : ℕ), P k) : ℕ :=
  Nat.lt_wfRel.wf.min {k | P k} ExistP

theorem PExistUniqueMinP {P : ℕ → Prop} (ExistP : ∃ (k : ℕ), P k) :
  P (ExistUniqueMinP ExistP) := by
  rw [ExistUniqueMinP]
  apply Nat.lt_wfRel.wf.min_mem

theorem ExistUniqueMinPLe {k : ℕ} {P : ℕ → Prop} (Pk : P k) :
  (ExistUniqueMinP (Exists.intro k Pk)) ≤ k:= by
  rw [ExistUniqueMinP]
  exact WellFoundedRelation.wf.min_le Pk (Exists.intro k Pk)

theorem EqExistUniqueMinPIff {P : ℕ → Prop} (ExistP : ∃ (k : ℕ), P k) (k : ℕ) :
  k = ExistUniqueMinP ExistP ↔ (P k ∧ ∀ (k0 : ℕ), (k0 < k → ¬ P k0)) := by
  constructor
  · intro h0
    simp only [h0, PExistUniqueMinP, true_and]
    intro k0 h1
    by_contra h2
    have h3 := ExistUniqueMinPLe h2
    rw [← Nat.not_lt] at h3
    simp only [h1, not_true_eq_false] at h3
  · intro h0
    choose h0 h1 using h0
    by_contra h2
    have h3 := ExistUniqueMinPLe h0
    have h4 : ExistUniqueMinP ExistP < k :=
      Nat.lt_of_le_of_ne h3 fun a ↦ h2 (Eq.symm a)
    have h5 := h1 (ExistUniqueMinP ExistP) h4
    simp only [PExistUniqueMinP, not_true_eq_false] at h5
