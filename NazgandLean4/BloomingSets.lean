import Mathlib
set_option maxHeartbeats 0

axiom «🌸» : Type
axiom «🌺» : «🌸»
axiom «💐» : «🌸» → «🌸»
axiom «💐🌺» : «💐» «🌺» = «🌺»
axiom «🌸∈» : «🌸» → «🌸» → Prop
def «Empty🌸» («🪻0» : «🌸») := ∀ («🪻» : «🌸»), ¬ «🌸∈» «🪻» «🪻0»
axiom «Empty🌸🌺» : «Empty🌸» «🌺»
def «Same🌸s🌸∈» («🪻0» «🪻1» : «🌸») := ∀ («🪻» : «🌸»), («🌸∈» «🪻» «🪻0» ↔ «🌸∈» «🪻» «🪻1»)
axiom «🌸DefinedBy💐AndWhatIs🌸∈» : ∀ («🪻0» «🪻1» : «🌸»),
  («Same🌸s🌸∈» «🪻0» «🪻1» ∧ «💐» «🪻0» = «💐» «🪻1») ↔ «🪻0» = «🪻1»

axiom «PropSub🌸» : («🌸» → Prop) → «🌸» → «🌸»
axiom «🌸∈PropSub🌸» : ∀ (p : («🌸» → Prop)) («🪻» «🪻0» : «🌸»),
  «🌸∈» «🪻0» («PropSub🌸» p «🪻») ↔ (p «🪻0» ∧ «🌸∈» «🪻0» «🪻»)
axiom «💐PropSub🌸» : ∀ (p : («🌸» → Prop)) («🪻» : «🌸»),
  «💐» («PropSub🌸» p «🪻») = «💐» «🪻»

axiom «Max🌸» : «🌸» → «🌸» → «🌸»
axiom «🌸∈Max🌸» : ∀ («🪻0» «🪻1» «🪻2» : «🌸»),
  «🌸∈» «🪻2» («Max🌸» «🪻0» «🪻1») ↔ («🌸∈» «🪻2» «🪻0» ∨ «🌸∈» «🪻2» «🪻1»)
axiom «💐Max🌸» : ∀ («🪻0» «🪻1» : «🌸»), «💐» («Max🌸» «🪻0» «🪻1») = «Max🌸» («💐» «🪻0») («💐» «🪻1»)

--should all be provable with «Same🌸s🌸∈AllIterated💐s↔=»
axiom «SymmetricMax🌸» : ∀ («🪻0» «🪻1» : «🌸»), «Max🌸» «🪻0» «🪻1» = «Max🌸» «🪻1» «🪻0»
axiom «Max🌸OfSelf» : ∀ («🪻» : «🌸»), «Max🌸» «🪻» «🪻» = «🪻»
axiom «Max🌸Of🌺» : ∀ («🪻» : «🌸»), «Max🌸» «🌺» «🪻» = «🪻»
axiom «∃!Max🌸sEq🌺» («🪻0» «🪻1» : «🌸») :
  «Max🌸» «🪻0» «🪻1» = «🌺» ↔ («🪻0» = «🌺» ∧ «🪻1» = «🌺»)

def «Sub🌸» («🪻0» «🪻1» : «🌸») : Prop := («Max🌸» «🪻0» «🪻1») = «🪻1»

axiom «🌸∈→💐Sub🌸💐» : ∀ («🪻0» «🪻1» : «🌸»),
  «🌸∈» «🪻0» «🪻1» → «Sub🌸» («💐» «🪻0») («💐» «🪻1»)

--should all be provable with «Same🌸s🌸∈AllIterated💐s↔=»
axiom «Sub🌸OfMax🌸» : ∀ («🪻0» «🪻1» «🪻2» : «🌸»), «Sub🌸» «🪻0» «🪻1» → «Sub🌸» «🪻0» («Max🌸» «🪻1» «🪻2»)

axiom «🌸OfSmaller💐s» : «🌸» → «🌸»
axiom «🌸∈🌸OfSmaller💐s» : ∀ («🪻0» «🪻1» : «🌸»),
  «🌸∈» «🪻0» («🌸OfSmaller💐s» «🪻1») ↔ («Sub🌸» («💐» «🪻0») «🪻1» ∧ («💐» «🪻0») ≠ «🪻1»)
axiom «💐🌸OfSmaller💐s» : ∀ («🪻» : «🌸»), «💐» («🌸OfSmaller💐s» «🪻») = «🪻»

axiom «Power🌸» : «🌸» → «🌸»
axiom «🌸∈Power🌸» : ∀ («🪻0» «🪻1» : «🌸»),
  «🌸∈» «🪻0» («Power🌸» «🪻1») ↔ «Sub🌸» «🪻0» «🪻1»
axiom «💐Power🌸» : ∀ («🪻» : «🌸»), «💐» («Power🌸» «🪻») = «💐» «🪻»

theorem «Sub🌸OfSelf» («🪻» : «🌸») : «Sub🌸» «🪻» «🪻» := by
  rw [«Sub🌸», «Max🌸OfSelf»]

noncomputable
def «🌸Of1🌸» («🪻» : «🌸») : «🌸» :=
  «PropSub🌸» (λ («🪻2» : «🌸») ↦ «🪻2» = «🪻») («Power🌸» «🪻»)

theorem «🌸∈🌸Of1🌸» («🪻0» «🪻1» : «🌸») :
  «🌸∈» «🪻0» («🌸Of1🌸» «🪻1») ↔ «🪻0» = «🪻1» := by
  rw [«🌸Of1🌸», «🌸∈PropSub🌸», «🌸∈Power🌸»]
  simp only [and_iff_left_iff_imp]
  intro h0
  rw [h0]
  exact «Sub🌸OfSelf» «🪻1»

theorem «💐🌸Of1🌸» («🪻» : «🌸») : «💐» («🌸Of1🌸» «🪻») = «💐» «🪻» := by
  rw [«🌸Of1🌸», «💐PropSub🌸», «💐Power🌸»]

theorem «¬Empty🌸🌸Of1🌸» («🪻» : «🌸») : ¬ «Empty🌸» («🌸Of1🌸» «🪻») := by
  rw [«Empty🌸»]
  simp only [not_forall, not_not]
  use «🪻»
  exact («🌸∈🌸Of1🌸» «🪻» «🪻»).mpr rfl

theorem «Empty🌸Max🌸IffEmpty🌸Empty🌸» («🪻0» «🪻1» : «🌸») :
  «Empty🌸» («Max🌸» «🪻0» «🪻1») ↔ ((«Empty🌸» «🪻0») ∧ («Empty🌸» «🪻1»)) := by
  constructor
  · intro h0
    simp only [«Empty🌸», «🌸∈Max🌸», not_or] at *
    constructor
    · intro «🪻»
      simp only [(h0 «🪻»).left, not_false_eq_true]
    · intro «🪻»
      simp only [(h0 «🪻»).right, not_false_eq_true]
  · intro h0
    obtain ⟨h1, h2⟩ := h0
    rw [«Empty🌸»] at *
    intro «🪻»
    simp only [«🌸∈Max🌸», h1, h2, or_self, not_false_eq_true]

theorem «¬Empty🌸→¬Empty🌸Max🌸» («🪻0» «🪻1» : «🌸») (h : ¬ «Empty🌸» «🪻0») : ¬ «Empty🌸» («Max🌸» «🪻0» «🪻1»)
  := by
  simp only [«Empty🌸Max🌸IffEmpty🌸Empty🌸», h, false_and, not_false_eq_true]

axiom «Max🌸Of🌸∈» : «🌸» → «🌸»
axiom «🌸∈Max🌸Of🌸∈» («🪻0» «🪻1» : «🌸») : «🌸∈» «🪻0» («Max🌸Of🌸∈» «🪻1») ↔
  ∃ («🪻2» : «🌸»), («🌸∈» «🪻2» «🪻1» ∧ «🌸∈» «🪻0» «🪻2»)
axiom «💐Max🌸Of🌸∈» («🪻» : «🌸») : «💐» («Max🌸Of🌸∈» «🪻») = «💐» «🪻»

theorem «Max🌸Of🌸∈🌸Of1🌸» («🪻» : «🌸») :
  «Max🌸Of🌸∈» («🌸Of1🌸» «🪻») = «🪻» := by
  rw [← «🌸DefinedBy💐AndWhatIs🌸∈», «Same🌸s🌸∈», «💐Max🌸Of🌸∈», «💐🌸Of1🌸»]
  simp only [«🌸∈Max🌸Of🌸∈», «🌸∈🌸Of1🌸», exists_eq_left, implies_true,
    and_self]

theorem «Max🌸Of🌸∈Max🌸» («🪻0» «🪻1» : «🌸») :
  «Max🌸Of🌸∈» («Max🌸» «🪻0» «🪻1») =
  «Max🌸» («Max🌸Of🌸∈» «🪻0») («Max🌸Of🌸∈» «🪻1») := by
  rw [← «🌸DefinedBy💐AndWhatIs🌸∈», «Same🌸s🌸∈», «💐Max🌸Of🌸∈», «💐Max🌸»,
    «💐Max🌸», «💐Max🌸Of🌸∈», «💐Max🌸Of🌸∈»]
  simp only [and_true]
  intro «🪻»
  rw [«🌸∈Max🌸Of🌸∈», «🌸∈Max🌸», «🌸∈Max🌸Of🌸∈», «🌸∈Max🌸Of🌸∈»]
  simp only [«🌸∈Max🌸»]
  constructor
  · intro h0
    choose «🪻2» h1 using h0
    obtain ⟨h2, h3⟩ := h1
    cases h2 with
    | inl h0 =>
      left
      use «🪻2»
    | inr h0 =>
      right
      use «🪻2»
  · intro h0
    cases h0 with
    | inl h0 =>
      choose «🪻2» h0 using h0
      use «🪻2»
      simp only [h0, true_or, and_self]
    | inr h0 =>
      choose «🪻2» h0 using h0
      use «🪻2»
      simp only [h0, or_true, and_self]

theorem «MutualSub🌸s=» («🪻0» «🪻1» : «🌸») :
  («Sub🌸» «🪻0» «🪻1» ∧ «Sub🌸» «🪻1» «🪻0») ↔ «🪻0» = «🪻1» := by
  constructor
  · intro ⟨h0, h1⟩
    rw [«Sub🌸»] at h0 h1
    rw [«SymmetricMax🌸»] at h0
    rw [h1] at h0
    exact h0
  · intro h0
    simp only [h0, «Sub🌸OfSelf», and_self]

theorem «TransitiveSub🌸But¬=» («🪻0» «🪻1» «🪻2» : «🌸») (h0 : «Sub🌸» «🪻0» «🪻1») (h1 : «Sub🌸» «🪻1» «🪻2»)
  (h2 : ¬ «🪻1» = «🪻2») : ¬ «🪻0» = «🪻2» := by
  by_contra h3
  rw [h3] at h0
  have h4 := «MutualSub🌸s=» «🪻1» «🪻2»
  simp only [h1, h0, and_self, h2, iff_false, not_true_eq_false] at h4

theorem «TransitiveSub🌸» («🪻0» «🪻1» «🪻2» : «🌸») (h0 : «Sub🌸» «🪻0» «🪻1») (h1 : «Sub🌸» «🪻1» «🪻2») :
  «Sub🌸» «🪻0» «🪻2» := by
  rw [«Sub🌸»] at h1
  rw [← h1]
  exact «Sub🌸OfMax🌸» «🪻0» «🪻1» «🪻2» h0

theorem «Max🌸Of🌸∈🌸OfSmaller💐s» («🪻» : «🌸») :
  «Max🌸Of🌸∈» («🌸OfSmaller💐s» «🪻») = «🌸OfSmaller💐s» «🪻» := by
  rw [← «🌸DefinedBy💐AndWhatIs🌸∈», «Same🌸s🌸∈», «💐Max🌸Of🌸∈»]
  simp only [«🌸∈Max🌸Of🌸∈», and_true]
  intro «🪻0»
  simp_rw [«🌸∈🌸OfSmaller💐s»]
  constructor
  · intro h0
    obtain ⟨«🪻1», h0, h1⟩ := h0
    have h2 := «🌸∈→💐Sub🌸💐» _ _ h1
    have h3 := «TransitiveSub🌸But¬=» _ _ _ h2 (h0.left) (h0.right)
    have h4 := «TransitiveSub🌸» _ _ _ h2 (h0.left)
    simp only [h4, ne_eq, h3, not_false_eq_true, and_self]
  · intro h0
    use «🌸Of1🌸» «🪻0»
    simp only [«💐🌸Of1🌸», h0.left, ne_eq, h0.right, not_false_eq_true, and_self,
      «🌸∈🌸Of1🌸»]

axiom «IteratedPower🌸» : «🌸» → «🌸» → «🌸»
axiom «💐IteratedPower🌸» («🪻0» «🪻1» : «🌸») :
  «💐» («IteratedPower🌸» «🪻0» «🪻1») = «Max🌸» («💐» «🪻0») («💐» «🪻1»)
axiom «IteratedPower🌸Empty🌸» («🪻0» «🪻1» : «🌸») (h : «Empty🌸» «🪻1») :
  «Same🌸s🌸∈» («IteratedPower🌸» «🪻0» «🪻1») «🪻0»
axiom «IteratedPower🌸¬Empty🌸» («🪻0» «🪻1» : «🌸») (h : ¬ «Empty🌸» «🪻1») :
  «IteratedPower🌸» «🪻0» «🪻1» = «IteratedPower🌸» («Power🌸» «🪻0») («Max🌸Of🌸∈» «🪻1»)
axiom «IteratedPower🌸TransfiniteInduction» («🪻» : «🌸») :
  «IteratedPower🌸» «🌺» («🌸OfSmaller💐s» «🪻») = «🌸OfSmaller💐s» «🪻»

-- should be provable
axiom «🌺IteratedPower🌸Sub🌸» («🪻0» «🪻1» «🪻2» : «🌸») (h : «Sub🌸» «🪻1» «🪻2») :
  «Sub🌸» («IteratedPower🌸» «🌺» «🪻1») («IteratedPower🌸» «🪻0» «🪻2»)
axiom «TransfiniteIteratedPower🌸Similar» («🪻0» «🪻1» : «🌸») (h0 : «💐» «🪻0» ≠ «🪻1»)
  (h1 : «Sub🌸» («💐» «🪻0») «🪻1») :
  «IteratedPower🌸» «🪻0» («🌸OfSmaller💐s» «🪻1») = «🌸OfSmaller💐s» «🪻1»

axiom PeanoLessThan1 : «🌸» → «🌸» → Prop
axiom PeanoLessThan1Iff : ∀ («🪻0» «🪻1» : «🌸»), PeanoLessThan1 «🪻0» «🪻1» ↔
  («🌸∈» «🪻0» «🪻1» ∨ ∃ («🪻2» : «🌸»), («🌸∈» «🪻2» «🪻1» ∧ PeanoLessThan1 «🪻0» «🪻2»))

axiom ReplaceLeaves : «🌸» → «🌸» → «🌸»
axiom «ReplaceLeavesEmpty🌸» : ∀ («🪻0» «🪻1» : «🌸»), «Empty🌸» «🪻0» → «Same🌸s🌸∈» (ReplaceLeaves «🪻0» «🪻1») «🪻1»
axiom «💐ReplaceLeaves» : ∀ («🪻0» «🪻1» : «🌸»), «💐» (ReplaceLeaves «🪻0» «🪻1») = «Max🌸» («💐» «🪻0») («💐» «🪻1»)

axiom «🌸∈ReplaceLeaves» : ∀ («🪻0» «🪻1» «🪻2» : «🌸»), (¬ «Empty🌸» «🪻0») →
  («🌸∈» «🪻2» (ReplaceLeaves «🪻0» «🪻1») ↔ (∃ («🪻3» : «🌸»), («🪻2» = ReplaceLeaves «🪻3» «🪻1» ∧ «🌸∈» «🪻3» «🪻0»)))

-- probably provable
axiom «ReplaceLeaves🌺0» («🪻» : «🌸») : (ReplaceLeaves «🪻» «🌺») = «🪻»

def PeanoLessThan2 («🪻0» «🪻1» : «🌸») : Prop :=
  ∃ («🪻2» : «🌸»), («🪻2» ≠ «🌺» ∧ ReplaceLeaves «🪻0» «🪻2» = «🪻1»)
def PeanoLessThan3 («🪻0» «🪻1» : «🌸») : Prop :=
  ∃ («🪻2» : «🌸»), («🪻2» ≠ «🌺» ∧ ReplaceLeaves «🪻2» «🪻0» = «🪻1»)
def «IteratedPower🌸≤» («🪻0» «🪻1» : «🌸») :
  Prop := «Sub🌸» («IteratedPower🌸» «🌺» «🪻0») («IteratedPower🌸» «🌺» «🪻1»)

-- Models random choice and unknowability, but by superdeterminism, the same seed «🌱» results in the same choice
axiom «Choose🌸∈» («🪻» «🌱» : «🌸») (h : ¬ «Empty🌸» «🪻») : «🌸»
axiom «Choose🌸∈🌸∈» («🪻» «🌱» : «🌸») (h : ¬ «Empty🌸» «🪻») : «🌸∈» («Choose🌸∈» «🪻» «🌱» h) «🪻»

noncomputable def «Peano🌸» (k : ℕ) : «🌸» :=
  match k with
  | 0 => «🌺»
  | k0 + 1 => «🌸Of1🌸» («Peano🌸» k0)

--make sure the «💐»=🌺 has only 🌸s generated by a natural number of iterations of «Power🌸»
axiom «💐=🌺IteratedPower🌸≤∃Peano🌸» («🪻0» : «🌸») (h : «💐» «🪻0» = «🌺») :
  ∃ (k : ℕ), «IteratedPower🌸≤» «🪻0» («Peano🌸» k)

axiom «Iterated💐» : «🌸» → «🌸» → «🌸»
axiom «Iterated💐Empty🌸» («🪻0» «🪻1» : «🌸») (h : «Empty🌸» «🪻1») : «Iterated💐» «🪻0» «🪻1» = «🪻0»
axiom «Iterated💐¬Empty🌸» («🪻0» «🪻1» : «🌸») (h : ¬ «Empty🌸» «🪻1») :
  «Iterated💐» «🪻0» «🪻1» = «Iterated💐» («💐» «🪻0») («Max🌸Of🌸∈» «🪻1»)
axiom «Iterated💐Eventual🌺» («🪻» : «🌸») : ∃ («🪻0» : «🌸»), «Iterated💐» «🪻» «🪻0» = «🌺»
axiom «Same🌸s🌸∈AllIterated💐s↔=» : ∀ («🪻0» «🪻1» : «🌸»), ((∀ («🪻ML» : «🌸»),
  «Same🌸s🌸∈» («Iterated💐» «🪻0» «🪻ML») («Iterated💐» «🪻1» «🪻ML»)) ↔ «🪻0» = «🪻1»)
-- axiom «∃🌸OfSameIterated💐Depth» («🪻0» : «🌸») :
--   ∃ («🪻1» : «🌸»), (∀ («🪻2» : «🌸»), («🌸∈» «🪻2» «🪻1» ↔ «Iterated💐» «🪻2» «🪻0» = «🌺»))

theorem «Same🌸s🌸∈Self» («🪻» : «🌸») : «Same🌸s🌸∈» «🪻» «🪻» := by
  simp only [«Same🌸s🌸∈», implies_true]

theorem «Same🌸s🌸∈→Empty🌸↔Empty🌸» («🪻0» «🪻1» : «🌸») (h0 : «Same🌸s🌸∈» «🪻0» «🪻1») :
  «Empty🌸» «🪻0» ↔ «Empty🌸» «🪻1» := by
  constructor
  · intro h1
    rw [«Empty🌸»] at h1
    intro «🪻»
    exact (iff_false_left (h1 «🪻»)).mp (h0 «🪻»)
  · intro h1
    rw [«Empty🌸»] at h1
    intro «🪻»
    rw [h0]
    exact h1 «🪻»

theorem «∃!Empty🌸💐=🌺» («🪻» : «🌸») (h0 : «💐» «🪻» = «🌺») : «Empty🌸» «🪻» ↔ «🪻» = «🌺» := by
  constructor
  · intros h1
    rw [«Empty🌸»] at h1
    rw [← «🌸DefinedBy💐AndWhatIs🌸∈», «💐🌺», «Same🌸s🌸∈», h0]
    simp only [and_true]
    intro «🪻0»
    let h2 := «Empty🌸🌺»
    rw [«Empty🌸»] at h2
    exact (iff_false_right (h2 «🪻0»)).mpr (h1 «🪻0»)
  · intros h3
    rw [h3]
    exact «Empty🌸🌺»

theorem «🌸∈Self→🌸∈Max🌸» («🪻0» «🪻1» «🪻2» : «🌸») : «🌸∈» «🪻2» «🪻0» → «🌸∈» «🪻2» («Max🌸» «🪻0» «🪻1») := by
  intro h0
  rw [«🌸∈Max🌸»]
  left
  exact h0

theorem «🌸∈Sub🌸» («🪻0» «🪻1» «🪻2» : «🌸») (h0 : «Sub🌸» «🪻1» «🪻2»)
  (h1 : «🌸∈» «🪻0» «🪻1») : «🌸∈» «🪻0» «🪻2» := by
  rw [«Sub🌸», ← «🌸DefinedBy💐AndWhatIs🌸∈»] at h0
  obtain ⟨h3, h2⟩ := h0
  rw [«Same🌸s🌸∈»] at h3
  rw [← h3, «🌸∈Max🌸»]
  left
  exact h1

theorem «Sub🌸ImpSub🌸Of💐s» («🪻0» «🪻1» : «🌸») (h : «Sub🌸» «🪻0» «🪻1») : «Sub🌸» («💐» «🪻0») («💐» «🪻1») := by
  rw [«Sub🌸»] at *
  have h0 := congr_arg «💐» h
  rw [«💐Max🌸»] at h0
  exact h0

theorem «🌺Sub🌸All» («🪻» : «🌸») : «Sub🌸» «🌺» «🪻» := by
  rw [«Sub🌸», «Max🌸Of🌺»]

theorem «∃!Sub🌸🌺» («🪻» : «🌸») : «Sub🌸» «🪻» «🌺» ↔ «🪻» = «🌺» := by
  constructor
  · intro h
    rw [«Sub🌸», «SymmetricMax🌸», «Max🌸Of🌺»] at h
    exact h
  · intro h0
    rw [h0]
    exact «🌺Sub🌸All» «🌺»

theorem «🌺≠Power🌸» («🪻0» : «🌸») : «🌺» ≠ («Power🌸» «🪻0») := by
  intro h
  let h0 := congr_arg (λ («🪻» : «🌸») ↦ («🌸∈» «🌺» «🪻»)) h
  simp only [«🌸∈Power🌸», «🌺Sub🌸All»] at h0
  let h1 := «Empty🌸🌺»
  rw [«Empty🌸»] at h1
  let h2 := h1 «🌺»
  rw [h0] at h2
  exact h2 trivial

theorem «Sub🌸Of🌸Of1🌸💐=🌺» («🪻0» «🪻1» : «🌸») (h0 : «💐» «🪻1» = «🌺») :
  «Sub🌸» «🪻0» («🌸Of1🌸» «🪻1») ↔ («🪻0» = «🌺» ∨ «🪻0» = «🌸Of1🌸» «🪻1») := by
  constructor
  · intro h
    have h4 := «Sub🌸ImpSub🌸Of💐s» _ _ h
    rw [«Sub🌸», ← «🌸DefinedBy💐AndWhatIs🌸∈»] at h
    obtain ⟨h1, h2⟩ := h
    rw [«Same🌸s🌸∈»] at h1
    simp_rw [«🌸∈🌸Of1🌸», «🌸∈Max🌸», «🌸∈🌸Of1🌸»] at h1
    simp only [or_iff_right_iff_imp] at h1
    rw [«💐🌸Of1🌸», h0, «∃!Sub🌸🌺»] at h4
    cases Classical.em («Empty🌸» «🪻0») with
    | inl h3 =>
      left
      rw [«∃!Empty🌸💐=🌺» _ h4] at h3
      exact h3
    | inr h6 =>
      right
      rw [← «🌸DefinedBy💐AndWhatIs🌸∈», «💐🌸Of1🌸», h0, h4, «Same🌸s🌸∈»]
      simp only [«🌸∈🌸Of1🌸», and_true]
      intro «🪻»
      constructor
      · exact h1 _
      · intro h9
        rw [h9] at *
        clear «🪻» h9
        rw [«Empty🌸»] at h6
        simp only [not_forall, not_not] at h6
        rcases h6 with ⟨«🪻2», h7⟩
        have h8 := h1 _ h7
        rw [h8] at h7
        exact h7
  · intro h1
    cases h1 with
    | inl h2 =>
      rw [h2]
      exact «🌺Sub🌸All» («🌸Of1🌸» «🪻1»)
    | inr h2 =>
      rw [h2]
      exact «Sub🌸OfSelf» («🌸Of1🌸» «🪻1»)

theorem «¬🌸∈🌺» («🪻» : «🌸») : ¬ «🌸∈» «🪻» «🌺» := by
  have h := «Empty🌸🌺»
  rw [«Empty🌸»] at h
  exact h «🪻»

theorem «🌺Not🌸Of1🌸» («🪻» : «🌸») : ¬ «🌺» = «🌸Of1🌸» «🪻» := by
  rw [← «🌸DefinedBy💐AndWhatIs🌸∈»]
  simp only [not_and]
  have h : ¬ «Same🌸s🌸∈» «🌺» («🌸Of1🌸» «🪻») := by
    rw [«Same🌸s🌸∈»]
    simp only [not_forall]
    use «🪻»
    simp [«¬🌸∈🌺», «🌸∈🌸Of1🌸»]
  simp only [h, IsEmpty.forall_iff]

theorem «Sub🌸Of🌸Of1🌸💐=🌺1» («🪻» «🪻1» : «🌸») (h0 : «💐» «🪻1» = «🌺») :
  («Sub🌸» «🪻» («🌸Of1🌸» «🪻1») ∧ «🪻» ≠ «🌸Of1🌸» «🪻1») ↔ «🪻» = «🌺» := by
  simp only [«Sub🌸Of🌸Of1🌸💐=🌺» _ _ h0, ne_eq]
  constructor
  · intro h
    have h1 := h.left
    have h2 := h.right
    simp only [h2, or_false] at h1
    exact h1
  · intro h
    simp only [h, «🌺Not🌸Of1🌸», true_or, true_and]
    exact fun a => a

theorem «Sub🌸Of🌸Of1🌸💐=🌺2» («🪻» «🪻1» : «🌸») (h0 : «💐» «🪻1» = «🌺») :
  («Sub🌸» «🪻» («🌸Of1🌸» «🪻1») ∧ «🪻» ≠ «🌺») ↔ «🪻» = «🌸Of1🌸» «🪻1» := by
  simp only [«Sub🌸Of🌸Of1🌸💐=🌺» _ _ h0, ne_eq]
  constructor
  · intro h
    have h1 := h.left
    have h2 := h.right
    simp only [h2, false_or] at h1
    exact h1
  · intro h
    simp only [h, or_true, true_and]
    rw [← «🌸DefinedBy💐AndWhatIs🌸∈»]
    simp only [not_and]
    have h1 : ¬ «Same🌸s🌸∈» («🌸Of1🌸» «🪻1») «🌺» := by
      rw [«Same🌸s🌸∈»]
      simp only [not_forall]
      use «🪻1»
      rw [«🌸∈🌸Of1🌸»]
      simp only [true_iff, «¬🌸∈🌺»]
      exact fun a => a
    simp only [h1]
    exact fun a a_1 => a

theorem «🌸Of1🌸Not🌺» («🪻» : «🌸») : «🌸Of1🌸» «🪻» ≠ «🌺»:= by
  let h0 := «🌸∈🌸Of1🌸» «🪻» «🪻»
  by_contra h1
  rw [h1] at h0
  let h2 := «Empty🌸🌺»
  rw [«Empty🌸»] at h2
  let h3 := h2 «🪻»
  simp only [h0, not_true_eq_false] at h3

theorem «=🌸Of1🌸↔=» («🪻0» «🪻1» : «🌸») : «🌸Of1🌸» «🪻0» = «🌸Of1🌸» «🪻1» ↔ «🪻0» = «🪻1» := by
  constructor
  · intro h0
    let h1 := congr_arg «💐» h0
    rw [«💐🌸Of1🌸», «💐🌸Of1🌸»] at h1
    rw [← «🌸DefinedBy💐AndWhatIs🌸∈», «Same🌸s🌸∈»] at h0
    let h2 := h0.left
    simp_rw [«🌸∈🌸Of1🌸»] at h2
    let h3 := h2 «🪻0»
    simp only [true_iff] at h3
    exact h3
  · intro h2
    rw [h2]

theorem «🌸OfSmaller💐s🌺» : «🌸OfSmaller💐s» «🌺» = «🌺» := by
  rw [← «🌸DefinedBy💐AndWhatIs🌸∈», «💐🌸OfSmaller💐s», «💐🌺»]
  let h0 := «Empty🌸🌺»
  rw [«Empty🌸»] at h0
  simp only [and_true]
  intro «🪻»
  simp only [«🌸∈🌸OfSmaller💐s», «∃!Sub🌸🌺», ne_eq, and_not_self, h0]

theorem «IteratedPower🌸Empty🌸↔» («🪻0» «🪻1» : «🌸») :
  «Empty🌸» («IteratedPower🌸» «🪻0» «🪻1») ↔ («Empty🌸» «🪻0» ∧ «Empty🌸» «🪻1») := by
  constructor
  · intro h0
    simp_rw [«Empty🌸»] at *
    constructor
    · intro «🪻»
      sorry
    · intro «🪻»
      have h1 := «🌺IteratedPower🌸Sub🌸»
      sorry
  · intro h0
    have h1 := «IteratedPower🌸Empty🌸» «🪻0» «🪻1» h0.right
    sorry

--shows that iterated power 🌸s are not obvious at higher 💐s
theorem «IteratedPower🌸¬Obvious» («🪻» : «🌸») (h0 : «Empty🌸» «🪻») (h1 : «🪻» ≠ «🌺») :
  ¬ «IteratedPower🌸» «🌺» «🪻» = «🌺» := by
  intro h2
  let h3 := congr_arg «💐» h2
  rw [«💐IteratedPower🌸», «💐🌺», «Max🌸Of🌺»] at h3
  rw [«∃!Empty🌸💐=🌺» «🪻» h3] at h0
  exact h1 h0

theorem «💐Sub🌸Of💐=🌺» («🪻0» «🪻1» : «🌸») (h0 : «💐» «🪻1» = «🌺») (h1 : «Sub🌸» «🪻0» «🪻1») :
  «💐» «🪻0» = «🌺» := by
  rw [«Sub🌸»] at h1
  let h2 := congr_arg «💐» h1
  rw [«💐Max🌸», h0, «SymmetricMax🌸», «Max🌸Of🌺»] at h2
  exact h2

theorem «Same🌸s🌸∈🌸OfSmaller💐s🌸Of1🌸💐=🌺» («🪻0» «🪻1» : «🌸»)
  (h0 : «💐» «🪻0» = «🌺») (h1 : «💐» «🪻1» = «🌺»)
  : «Same🌸s🌸∈» («🌸OfSmaller💐s» («🌸Of1🌸» «🪻0»)) («🌸OfSmaller💐s» («🌸Of1🌸» «🪻1»)) := by
  rw [«Same🌸s🌸∈»]
  intros «🪻»
  have h2 : ∀ («🪻2» «🪻3» : «🌸») (h3 : «💐» «🪻2» = «🌺») (h4 : «💐» «🪻3» = «🌺»),
    «🌸∈» «🪻» («🌸OfSmaller💐s» («🌸Of1🌸» «🪻2»)) →
    «🌸∈» «🪻» («🌸OfSmaller💐s» («🌸Of1🌸» «🪻3»)) := by
    intros «🪻2» «🪻3» h5 h6 h7
    rw [«🌸∈🌸OfSmaller💐s»] at h7
    let h8 := «Sub🌸Of🌸Of1🌸💐=🌺» («💐» «🪻») «🪻2» h5
    rw [h8] at h7
    simp only [ne_eq] at h7
    have h9 : ((«💐» «🪻» = «🌺» ∨ «💐» «🪻» = «🌸Of1🌸» «🪻2») ∧ ¬ «💐» «🪻» = «🌸Of1🌸» «🪻2»)
      → «💐» «🪻» = «🌺» := by tauto
    have h10 := h9 h7
    rw [«🌸∈🌸OfSmaller💐s», h10]
    simp only [«🌺Sub🌸All», ne_eq, true_and]
    let h11 := («🌸Of1🌸Not🌺» «🪻3»).symm
    simp only [h11, not_false_eq_true]
  constructor
  · exact h2 «🪻0» «🪻1» h0 h1
  · exact h2 «🪻1» «🪻0» h1 h0

theorem «Choose🌸∈🌸Of1🌸» («🪻» «🌱» : «🌸») :
  «Choose🌸∈» («🌸Of1🌸» «🪻») «🌱» («¬Empty🌸🌸Of1🌸» «🪻») = «🪻» := by
  let h0 := «Choose🌸∈🌸∈» («🌸Of1🌸» «🪻») «🌱» («¬Empty🌸🌸Of1🌸» «🪻»)
  exact
    («🌸∈🌸Of1🌸»
          («Choose🌸∈» («🌸Of1🌸» «🪻») «🌱» («¬Empty🌸🌸Of1🌸» «🪻»)) «🪻»).mp
      h0

theorem «💐Peano🌸» (k : ℕ) : «💐» («Peano🌸» k) = «🌺» := by
  induction k with
  | zero => rw [«Peano🌸», «💐🌺»]
  | succ k0 ih =>
    rw [«Peano🌸», «💐🌸Of1🌸», ih]

theorem «Peano🌸=🌺↔0» (k0 : ℕ) : «Peano🌸» k0 = «🌺» ↔ k0 = 0 := by
  constructor
  · intro h0
    cases eq_or_ne k0 0 with
    | inl h1 =>
      exact h1
    | inr h1 =>
      rcases Nat.exists_eq_succ_of_ne_zero h1 with ⟨k1, h2⟩
      rw [h2, «Peano🌸»] at h0
      simp only [«🌸Of1🌸Not🌺»] at h0
  · intro h1
    rw [h1, «Peano🌸»]

theorem «Peano🌸Injective» (k₀ k₁ : ℕ) : «Peano🌸» k₀ = «Peano🌸» k₁ ↔ k₀ = k₁ := by
  have «Peano🌸<→≠» (k0 k1 : ℕ) (h : k0 < k1) : «Peano🌸» k0 ≠ «Peano🌸» k1 := by
    have «Peano🌸=↔+=» (k0 k1 k2 : ℕ) : «Peano🌸» k0 = «Peano🌸» k1 ↔ «Peano🌸» (k0 + k2) = «Peano🌸» (k1 + k2) := by
      have «Peano🌸=↔Succ=» (k0 k1 : ℕ) : «Peano🌸» k0 = «Peano🌸» k1 ↔ «Peano🌸» (k0 + 1) = «Peano🌸» (k1 + 1) := by
        constructor
        · intro h0
          rw [«Peano🌸», «Peano🌸», h0]
        · intro h1
          rw [«Peano🌸», «Peano🌸», «=🌸Of1🌸↔=»] at h1
          exact h1
      induction k2 with
      | zero => simp only [add_zero]
      | succ k3 ih =>
        have h0 := «Peano🌸=↔Succ=» (k0 + k3) (k1 + k3)
        rw [h0] at ih
        exact ih
    have h0 : k0 ≤ k1 := by exact Nat.le_of_succ_le h
    let h1 := Nat.exists_eq_add_of_le (Nat.le_of_succ_le h)
    rcases h1 with ⟨k2, h2⟩
    rw [h2]
    simp only [ne_eq]
    rw [h2] at h
    have h4 : 0 < k2 := Nat.lt_add_right_iff_pos.mp h
    have h5 : 0 ≠ k2 := by exact Ne.symm (Nat.ne_zero_of_lt h4)
    have h3 := «Peano🌸=↔+=» 0 k2 k0
    rw [«Peano🌸», eq_comm, «Peano🌸=🌺↔0»] at h3
    simp only [zero_add] at h3
    simp only [ne_eq, eq_comm, h3, Nat.add_comm] at h5
    exact h5
  constructor
  · intro h
    have h0 := Nat.lt_trichotomy k₀ k₁
    cases h0 with
    | inl h1 =>
      simp only [«Peano🌸<→≠» k₀ k₁ h1] at h
    | inr h2 =>
      cases h2 with
      | inl h3 => exact h3
      | inr h4 =>
        simp only [(«Peano🌸<→≠» k₁ k₀ h4).symm] at h
  · intro h
    rw [h]

theorem «ReplaceLeavesEmpty🌸Empty🌸» («🪻0» «🪻1» : «🌸») (h0 : «Empty🌸» «🪻0») (h1 : «Empty🌸» «🪻1») :
  «Empty🌸» (ReplaceLeaves «🪻0» «🪻1») := by
  rw [«Empty🌸»]
  intro «🪻»
  have h2 := «ReplaceLeavesEmpty🌸» «🪻0» «🪻1» h0
  rw [«Same🌸s🌸∈»] at h2
  rw [«Empty🌸»] at h1
  exact (iff_false_right (h1 «🪻»)).mp (h2 «🪻»)

theorem «ReplaceLeaves🌺» («🪻» : «🌸») : (ReplaceLeaves «🌺» «🪻») = «🪻» := by
  rw [← «🌸DefinedBy💐AndWhatIs🌸∈», «💐ReplaceLeaves», «💐🌺», «Max🌸Of🌺»]
  have h0 := «ReplaceLeavesEmpty🌸» «🌺» «🪻» «Empty🌸🌺»
  simp only [h0, and_self]

theorem «NoRussel🌸» («🪻R» : «🌸») (h : ∀ («🪻0» : «🌸»), «🌸∈» «🪻0» «🪻R» ↔ ¬ «🌸∈» «🪻0» «🪻0») : False := by
  have h0 := (h «🪻R»).eq
  exact Lean.Grind.false_of_not_eq_self (id (Eq.symm h0))

theorem «¬Sub🌸→Not🌺» («🪻0» «🪻1» : «🌸») (h : ¬ «Sub🌸» «🪻0» «🪻1») : ¬ «🪻0» = «🌺» := by
  by_contra h0
  rw [h0] at h
  simp only [«🌺Sub🌸All» «🪻1», not_true_eq_false] at h

-- 🌸 containing all 🌸s the of the Russel🌸 restricted to maximum «💐» «🪻L»
-- not obviously inconsistent
theorem «Russel🌸WithMax💐» («🪻R» «🪻L» «🪻L0» «🪻» : «🌸») (h1 : «Sub🌸» («💐» «🪻R») «🪻L0»)
  (h2 : «💐» «🪻L0» = «🌺») (h3 : «🪻L0» = («🌸Of1🌸» «🪻»))
  (h : ∀ («🪻0» : «🌸»), («🌸∈» «🪻0» «🪻R» ↔ (¬ «🌸∈» «🪻0» «🪻0» ∧ «Sub🌸» («💐» «🪻0») «🪻L»))) :
  (¬ «💐» «🪻R» = «🌺») ∧ («💐» («💐» «🪻R») = «🌺») ∧ (¬ «Sub🌸» («💐» «🪻R») «🪻L») ∧
  (¬ «🪻L» = «🪻L0») ∧ («💐» «🪻» = «🌺») ∧ (¬ «Sub🌸» («💐» «🪻R») «🪻L») := by
  simp [h3] at *
  clear h3
  have h0 : ¬ «Sub🌸» («💐» «🪻R») «🪻L» := by
    by_contra h9
    have h10 := h «🪻R»
    simp only [h9, and_true, iff_not_self] at h10
  have h7 : ¬ «🪻L» = («🌸Of1🌸» «🪻») := by
    by_contra h8
    simp [h8, h1] at *
  have h4 := «¬Sub🌸→Not🌺» _ _ h0
  have h6 : «💐» («💐» «🪻R») = «🌺» := «💐Sub🌸Of💐=🌺» («💐» «🪻R») («🌸Of1🌸» «🪻») h2 h1
  have h8 : «💐» «🪻» = «🌺» := by
    rw [«💐🌸Of1🌸»] at h2
    exact h2
  simp [*]

theorem «PeanoLessThan1ForPeano🌸» (k0 k1 : ℕ) : k0 < k1 ↔ PeanoLessThan1 («Peano🌸» k0) («Peano🌸» k1) := by
  constructor
  · intro h0
    rw [PeanoLessThan1Iff]
    sorry
  · intro h0
    sorry

theorem «PeanoLessThan2ForPeano🌸» (k0 k1 : ℕ) : k0 < k1 ↔ PeanoLessThan2 («Peano🌸» k0) («Peano🌸» k1) := by
  constructor
  · intro h0
    sorry
  · intro h0
    sorry

theorem «PeanoLessThan3ForPeano🌸» (k0 k1 : ℕ) : k0 < k1 ↔ PeanoLessThan3 («Peano🌸» k0) («Peano🌸» k1) := by
  constructor
  · intro h0
    sorry
  · intro h0
    sorry

theorem «💐=🌺IteratedPower🌸=SomePeano🌸» («🪻0» : «🌸») (h : «💐» «🪻0» = «🌺») :
  ∃! (k : ℕ), («IteratedPower🌸≤» «🪻0» («Peano🌸» k) ∧
    ∀ (k0 : ℕ), k0 < k → ¬ «IteratedPower🌸≤» «🪻0» («Peano🌸» k0)) := by
  sorry

theorem «Peano🌸🌸∈Succ» (k0 k1 : ℕ) : «🌸∈» («Peano🌸» k0) («Peano🌸» k1) ↔ k1 = k0 + 1:= by
  constructor
  · induction k1 with
    | zero =>
      simp only [right_eq_add, Nat.add_eq_zero, one_ne_zero, and_false, imp_false, «Peano🌸», «¬🌸∈🌺»]
      exact fun a => a
    | succ k2 ih =>
      rw [«Peano🌸», «🌸∈🌸Of1🌸»]
      intro h1
      have h2 : k0 = k2 := («Peano🌸Injective» k0 k2).mp h1
      simp only [h2]
  · intro h
    rw [h]
    induction k0 with
    | zero =>
      rw [«Peano🌸», «Peano🌸», «🌸∈🌸Of1🌸», «Peano🌸»]
    | succ k2 ih =>
      have h0 : («Peano🌸» (k2 + 1 + 1)) = «🌸Of1🌸» («Peano🌸» (k2 + 1)) := rfl
      rw [h0, «🌸∈🌸Of1🌸»]

noncomputable
def «RangePeano🌸» (k : ℕ) : «🌸» := match k with
  | 0 => «🌺»
  | k + 1 => «Max🌸» («RangePeano🌸» k) («Peano🌸» (k + 1))

noncomputable def «🌸Minus» («🪻0» «🪻1» : «🌸») : «🌸» := «PropSub🌸» (λ («🪻2» : «🌸») ↦ ¬ «🌸∈» «🪻2» «🪻1») «🪻0»
theorem «🌸∈🌸Minus» («🪻0» «🪻1» «🪻2» : «🌸») :
  «🌸∈» «🪻2» («🌸Minus» «🪻0» «🪻1») ↔ («🌸∈» «🪻2» «🪻0» ∧ ¬ «🌸∈» «🪻2» «🪻1») := by
  rw [«🌸Minus», «🌸∈PropSub🌸»]
  exact And.comm
theorem «🌸Minus💐» («🪻0» «🪻1» : «🌸») : «💐» («🌸Minus» «🪻0» «🪻1») = «💐» «🪻0» := by
  rw [«🌸Minus», «💐PropSub🌸»]

theorem «🌸MinusSub🌸Self» («🪻0» «🪻1» : «🌸») : «Sub🌸» («🌸Minus» «🪻0» «🪻1») «🪻0» := by
  rw [«Sub🌸», ← «🌸DefinedBy💐AndWhatIs🌸∈»]
  constructor
  · rw [«Same🌸s🌸∈»]
    intro «🪻»
    rw [«🌸∈Max🌸»]
    constructor
    · rw [«🌸∈🌸Minus»]
      intro h
      cases h with
      | inl h => exact h.left
      | inr h => exact h
    · intro h
      right
      exact h
  · rw [«💐Max🌸», «🌸Minus💐», «Max🌸OfSelf»]

theorem «∃!Peano🌸🌸∈RangePeano🌸Succ🌸MinusRangePeano🌸» (k1 k3 : ℕ) :
  «🌸∈» («Peano🌸» k1) («🌸Minus» («RangePeano🌸» (k3 + 1)) («RangePeano🌸» k3)) ↔
  k1 = k3 := by
  constructor
  · rw [«🌸∈🌸Minus»]
    intro h0
    sorry
  · intro h
    rw [h]
    sorry

theorem «RangePeano🌸RangeNat» (k0 k1 : ℕ) : k1 < k0 ↔ «🌸∈» («Peano🌸» k1) («RangePeano🌸» k0) := by
  induction k0 with
  | zero => simp only [not_lt_zero', «RangePeano🌸», «¬🌸∈🌺»]
  | succ k3 ih =>
    constructor
    · intro h0
      rw [«RangePeano🌸», «🌸∈Max🌸», ← ih]
      have h1 : k1 < (k3 + 1) := by exact h0
      have h2 : k1 < k3 ∨ k1 = k3 := by exact Nat.lt_succ_iff_lt_or_eq.mp h1
      cases h2 with
      | inl h2 => simp only [h2, true_or]
      | inr h3 =>
        simp only [h3, lt_self_iff_false, «Peano🌸🌸∈Succ», or_true]
    · intro h0
      cases Classical.em (k1 < k3) with
      | inl h1 => exact Nat.lt_add_right 1 h1
      | inr h1 =>
        simp only [h1, false_iff] at ih
        sorry

-- theorem RangePeano🌸Sub🌸IteratedPower🌸 (k : ℕ) : ∀ («🪻0» «🪻1» : «🌸»),
--   «IteratedPower🌸≤» «🪻0» «🪻1» ↔
--   «Sub🌸» («IteratedPower🌸» «🌺» «🪻0») («IteratedPower🌸» «🌺» («Peano🌸» k)) := sorry

theorem «¬Empty🌸Peano🌸Succ» (k : ℕ) : ¬ «Empty🌸» («Peano🌸» (k + 1)) := by
  rw [«Peano🌸»]
  exact «¬Empty🌸🌸Of1🌸» («Peano🌸» k)

theorem «IteratedPower🌸≤ForPeano🌸» (k0 k1 : ℕ) :
  k0 ≤ k1 ↔ «IteratedPower🌸≤» («Peano🌸» k0) («Peano🌸» k1) :=
  Nat.strong_induction_on k1 fun k2 =>
  have h2 : «IteratedPower🌸» «🌺» «🌺» = «🌺» := by
    sorry
  have h4 : ∀ (k3 : ℕ), ¬ k3 = 0 ↔ ∃ (k2 : ℕ), k3 = k2 + 1 := by
    intro k3
    constructor
    · intro h0
      by_contra h1
      simp only [Nat.exists_eq_add_one, not_lt, nonpos_iff_eq_zero] at h1
      simp [h1] at h0
    · intro h0
      rcases h0 with ⟨k2, h1⟩
      simp only [h1, Nat.add_eq_zero, one_ne_zero, and_false, not_false_eq_true]
  have h3 : ∀ (k : ℕ), «IteratedPower🌸» «🌺» («Peano🌸» k) = «🌺» ↔ k = 0 := by
    intro k
    constructor
    · intro h6
      by_contra h1
      simp only [(h4 k), Nat.exists_eq_add_one] at h1
      sorry
    · intro h0
      rw [h0, «Peano🌸», h2]
  match k2 with
  | 0 => by
    intro h0
    simp only [nonpos_iff_eq_zero, «Peano🌸», «IteratedPower🌸≤»]
    constructor
    · intro h1
      simp only [h1, «Peano🌸», «Sub🌸OfSelf»]
    · intro h1
      simp only [h2, «∃!Sub🌸🌺»] at h1
      sorry
  | k3 + 1 => by
    sorry

theorem «🌸∈Peano🌸Succ» (k : ℕ) («🪻» : «🌸») : «🌸∈» «🪻» («Peano🌸» (k + 1)) ↔ «🪻» = «Peano🌸» k := by
  constructor
  · intro h
    rw [«Peano🌸», «🌸∈🌸Of1🌸»] at h
    exact h
  · intro h
    rw [«Peano🌸», h, «🌸∈🌸Of1🌸»]

theorem «Max🌸Of🌸∈🌸Peano🌸Succ» (k : ℕ) :
  «Max🌸Of🌸∈» («Peano🌸» (k + 1)) = «Peano🌸» k := by
  simp_rw [«Peano🌸», «Max🌸Of🌸∈🌸Of1🌸»]

theorem «IteratedPower🌸IteratedPower🌸Base» («🪻» : «🌸») :
  «IteratedPower🌸» «🌺» («IteratedPower🌸» «🌺» «🪻») = «IteratedPower🌸» «🌺» «🪻» := by
  sorry

theorem «IteratedPower🌸Peano🌸Addition» (k0 k1 : ℕ) :
  («IteratedPower🌸» «🌺» («Peano🌸» (k0 + k1))) =
  («IteratedPower🌸» («IteratedPower🌸» «🌺» («Peano🌸» k0)) («IteratedPower🌸» «🌺» («Peano🌸» k1))) := by
  induction k0 with
  | zero =>
    simp only [zero_add, «Peano🌸», «IteratedPower🌸Empty🌸», «IteratedPower🌸IteratedPower🌸Base»]
    sorry
  | succ k2 ih =>

    sorry

--all «💐»=🌺 🌸s are generated by the «IteratedPower🌸» «🌸∈» the «💐»=🌺
theorem «💐=🌺🌸∈IteratedPower🌸OfSomePeano🌸» («🪻0» : «🌸») : («💐» «🪻0» = «🌺») ↔
  ∃ (k : ℕ), «🌸∈» «🪻0» («IteratedPower🌸» «🌺» («Peano🌸» k)) := by
  constructor
  · have h0 := «💐=🌺IteratedPower🌸≤∃Peano🌸» «🪻0»
    intro h1
    simp only [h1, forall_const] at h0
    rcases h0 with ⟨k, h2⟩
    rw [«IteratedPower🌸≤»] at h2
    use (k + 1)
    rw [«IteratedPower🌸¬Empty🌸» _ _ («¬Empty🌸Peano🌸Succ» _)]
    simp_rw [«Peano🌸»]
    sorry
  · intro h0
    rcases h0 with ⟨k, h1⟩
    have h2 := «🌸∈→💐Sub🌸💐» «🪻0» («IteratedPower🌸» «🌺» («Peano🌸» k)) h1
    have h3 := «💐IteratedPower🌸» «🌺» («Peano🌸» k)
    rw [«💐🌺», «💐Peano🌸», «Max🌸OfSelf»] at h3
    rw [h3] at h2
    exact («∃!Sub🌸🌺» («💐» «🪻0»)).mp h2

theorem «¬Empty🌸SuccPeano🌸» (k : ℕ) : ¬ «Empty🌸» («Peano🌸» (k + 1)) := by
  rw [«Empty🌸»]
  simp only [not_forall, not_not]
  use «Peano🌸» k
  rw [«Peano🌸»]
  exact («🌸∈🌸Of1🌸» («Peano🌸» k) («Peano🌸» k)).mpr rfl

theorem «Max🌸Of🌸∈Peano🌸» (k : ℕ) :
  «Max🌸Of🌸∈» («Peano🌸» (k + 1)) = («Peano🌸» k):= by
  rw [← «🌸DefinedBy💐AndWhatIs🌸∈», «💐Max🌸Of🌸∈», «Same🌸s🌸∈»]
  simp only [«💐Peano🌸», and_true]
  intro «🪻»
  rw [«🌸∈Max🌸Of🌸∈»]
  simp only [«🌸∈Peano🌸Succ»]
  constructor
  · intro h0
    choose «🪻2» h0 using h0
    simp only [h0.left, true_and] at h0
    exact h0
  · intro h0
    use «Peano🌸» k

theorem «IteratedPower🌸NotCommutative» : («IteratedPower🌸» («Peano🌸» 2) «🌺»)
  ≠ («IteratedPower🌸» «🌺» («Peano🌸» 2)) := by
  sorry

noncomputable def AsymmMin («🪻0» «🪻1» : «🌸») := «PropSub🌸» (λ («🪻2» : «🌸») ↦ «🌸∈» «🪻2» «🪻1») «🪻0»

theorem «Sub🌸PropSub🌸» (p : («🌸» → Prop)) («🪻» : «🌸») : «Sub🌸» («PropSub🌸» p «🪻») «🪻» := by
  rw [«Sub🌸»,← «🌸DefinedBy💐AndWhatIs🌸∈», «Same🌸s🌸∈»]
  simp_rw [«🌸∈Max🌸»]
  constructor
  · intro «🪻0»
    simp only [«🌸∈PropSub🌸», or_iff_right_iff_imp, and_imp, imp_self, implies_true]
  · rw [«💐Max🌸», «💐PropSub🌸», «Max🌸OfSelf»]

theorem «🌸∈BothPeano🌸↔=» (k0 k1 : ℕ) («🪻» : «🌸») (h0 : «🌸∈» «🪻» («Peano🌸» k0))
  (h1 : «🌸∈» «🪻» («Peano🌸» k1)) : k0 = k1 := by
  induction k0 with
  | zero =>
    rw [«Peano🌸»] at h0
    simp only [«¬🌸∈🌺»] at h0
  | succ k2 ih =>
    rw [«Peano🌸», «🌸∈🌸Of1🌸»] at h0
    rw [h0, «Peano🌸🌸∈Succ»] at h1
    exact h1.symm

theorem BadMinExample (BadMin : «🌸» → «🌸» → «🌸»)
  (SelfBadMin : ∀ («🪻» : «🌸»), BadMin «🪻» «🪻» = «🪻»)
  («🌸∈BadMin» : ∀ («🪻0» «🪻1» «🪻2» : «🌸»),
  «🌸∈» «🪻2» (BadMin «🪻0» «🪻1») ↔ («🌸∈» «🪻2» «🪻0» ∧ «🌸∈» «🪻2» «🪻1»))
  («💐BadMin» : ∀ («🪻0» «🪻1» : «🌸»),
  «💐» (BadMin «🪻0» «🪻1») = BadMin («💐» «🪻0») («💐» «🪻1»)) : False := by
  let «🪻» := BadMin («🌸OfSmaller💐s» («Peano🌸» 1)) («🌸OfSmaller💐s» («Peano🌸» 2))
  have h0 : «💐» «🪻» = «🌺» := by
    rw [«💐BadMin», «💐🌸OfSmaller💐s», «💐🌸OfSmaller💐s», ← «🌸DefinedBy💐AndWhatIs🌸∈»,
        «Same🌸s🌸∈», «💐🌺»]
    simp only [«🌸∈BadMin», «¬🌸∈🌺», iff_false, not_and, «💐BadMin»,
      «💐Peano🌸», SelfBadMin, and_true]
    intro «🪻3» h
    by_contra h0
    have h1 := «🌸∈BothPeano🌸↔=» 1 2 «🪻3» h h0
    simp only [OfNat.one_ne_ofNat] at h1
  have h1 : ∀ («🪻3» : «🌸»), «🌸∈» «🪻3» «🪻» ↔ «💐» «🪻3» = «🌺» := by
    intro «🪻3»
    constructor
    · intro h1
      have h2 := «🌸∈→💐Sub🌸💐» _ _ h1
      rw [h0, «∃!Sub🌸🌺»] at h2
      exact h2
    · intro h5
      unfold «🪻»
      rw [«🌸∈BadMin», «🌸∈🌸OfSmaller💐s», «🌸∈🌸OfSmaller💐s», h5]
      simp only [«🌺Sub🌸All», ne_eq, true_and]
      have h7 := «Peano🌸=🌺↔0» 1
      have h6 := «Peano🌸=🌺↔0» 2
      simp only [one_ne_zero, iff_false, OfNat.ofNat_ne_zero] at h7 h6
      constructor
      · by_contra h8
        simp only [h8, not_true_eq_false] at h7
      · by_contra h8
        simp only [h8, not_true_eq_false] at h6
  have h2 : «🌸∈» «🪻» «🪻» := by
    rw [h1, h0]
  sorry

-- maybe shorter proof
theorem «ReplaceLeavesIsPeano🌸Add» (k0 k1 : ℕ) : ReplaceLeaves («Peano🌸» k0) («Peano🌸» k1) = «Peano🌸» (k0 + k1) :=
  Nat.strong_induction_on k0 fun k2 =>
    match k2 with
    | 0 => by
      intro h
      rw [«Peano🌸», «ReplaceLeaves🌺»]
      simp only [zero_add]
    | k3 + 1 => by
      intro h
      rw [← «🌸DefinedBy💐AndWhatIs🌸∈», «💐ReplaceLeaves», «💐Peano🌸», «💐Peano🌸», «💐Peano🌸»,
          «Max🌸OfSelf», «Same🌸s🌸∈»]
      simp only [and_true]
      intro «🪻»
      rw [(show k3 + 1 + k1 = k3 + k1 + 1 by ring), «🌸∈Peano🌸Succ»]
      constructor
      · intro h2
        rw [← («🌸∈Peano🌸Succ» (k3 + k1) «🪻»), «🌸∈Peano🌸Succ»]
        rw [«🌸∈ReplaceLeaves» _ _ _ («¬Empty🌸Peano🌸Succ» _)] at h2
        rcases h2 with ⟨«🪻2», h0, h2⟩
        rw [h0]
        clear «🪻» h0
        rw [«🌸∈Peano🌸Succ»] at h2
        rw [h2]
        clear «🪻2» h2
        have h3 := h k3
        simp only [lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt, forall_const] at h3
        exact h3
      · intro h2
        rw [h2]
        clear «🪻» h2
        exact Nat.strong_induction_on k1 fun k4 =>
          match k4 with
          | 0 => by
            intro h0
            rw [«Peano🌸», «ReplaceLeaves🌺0», «Peano🌸🌸∈Succ»]
          | k5 + 1 => by
            intro h0
            simp only [«¬Empty🌸Peano🌸Succ», not_false_eq_true, «🌸∈ReplaceLeaves»]
            use «Peano🌸» k3
            simp only [«Peano🌸🌸∈Succ», and_true]
            exact Nat.strong_induction_on k3 fun k6 =>
            match k6 with
            | 0 => by
              intro h3
              rw [«Peano🌸», «ReplaceLeaves🌺»]
              simp only [zero_add]
            | k7 + 1 => by
              intro h3
              rw [← «🌸DefinedBy💐AndWhatIs🌸∈», «💐Peano🌸», «💐ReplaceLeaves»,
                  «Same🌸s🌸∈», «💐Peano🌸», «💐Peano🌸», «Max🌸OfSelf»]
              simp only [and_true]
              intro «🪻»
              rw [(show (k7 + 1 + (k5 + 1)) = ((k7 + k5 + 1) + 1) by ring), «🌸∈Peano🌸Succ»,
                  «🌸∈ReplaceLeaves» _ _ _ («¬Empty🌸Peano🌸Succ» _)]
              constructor
              · intro h4
                use «Peano🌸» k7
                rw [«🌸∈Peano🌸Succ», h4]
                clear «🪻» h4
                simp only [and_true]
                rw [← «🌸DefinedBy💐AndWhatIs🌸∈», «💐Peano🌸», «💐ReplaceLeaves», «💐Peano🌸»,
                    «💐Peano🌸», «Max🌸OfSelf», «Same🌸s🌸∈»]
                simp only [and_true]
                intro «🪻»
                rw [«🌸∈Peano🌸Succ»]
                constructor
                · intro h5
                  rw [h5]
                  have h6 := h3 k7
                  simp only [lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt, forall_const] at h6
                  rw [← h6, (show (k7 + (k5 + 1)) = ((k7 + k5) + 1) by ring), «🌸∈Peano🌸Succ»]
                · have h5 := h3 k7
                  simp only [lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt, forall_const] at h5
                  rw [← h5, (show (k7 + (k5 + 1)) = ((k7 + k5) + 1) by ring), «🌸∈Peano🌸Succ»]
                  simp only [imp_self]
              · intro h4
                rcases h4 with ⟨«🪻2», h5, h6⟩
                rw [«🌸∈Peano🌸Succ»] at h6
                rw [h6] at h5
                rw [h5]
                clear h5 h6 «🪻» «🪻2»
                rw [← «🌸DefinedBy💐AndWhatIs🌸∈», «💐ReplaceLeaves», «💐Peano🌸», «💐Peano🌸», «💐Peano🌸»,
                    «Max🌸OfSelf», «Same🌸s🌸∈»]
                simp only [«🌸∈Peano🌸Succ», and_true]
                intro «🪻»
                constructor
                · intro h4
                  have h5 := h3 k7
                  simp only [lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt, forall_const] at h5
                  rw [← h5, (show (k7 + (k5 + 1)) = ((k7 + k5) + 1) by ring), «🌸∈Peano🌸Succ»] at h4
                  exact h4
                · intro h4
                  rw [h4]
                  clear «🪻» h4
                  have h5 := h3 k7
                  simp only [lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt, forall_const] at h5
                  rw [← h5, (show (k7 + (k5 + 1)) = ((k7 + k5) + 1) by ring), «🌸∈Peano🌸Succ»]

theorem «SymmetricSame🌸s🌸∈» («🪻0» «🪻1» : «🌸»)
  (h2 : «Same🌸s🌸∈» «🪻0» «🪻1») : «Same🌸s🌸∈» «🪻1» «🪻0» := by
  rw [«Same🌸s🌸∈»] at *
  intro «🪻»
  exact iff_comm.mp (h2 «🪻»)

noncomputable
def «Lift🌸To💐» («🪻0» «🪻L» : «🌸») (_ : «Sub🌸» («💐» «🪻0») «🪻L») : «🌸» := by
  if («💐» «🪻0») = «🪻L»
  then exact «🪻0»
  else exact «PropSub🌸» (λ («🪻» : «🌸») ↦ «🌸∈» «🪻» «🪻0») («🌸OfSmaller💐s» «🪻L»)

theorem «💐Lift🌸To💐» («🪻0» «🪻L» : «🌸») (h0 : «Sub🌸» («💐» «🪻0») «🪻L») :
  «💐» («Lift🌸To💐» «🪻0» «🪻L» h0) = «🪻L» := by
  rw [«Lift🌸To💐»]
  by_cases h1 : («💐» «🪻0») = «🪻L»
  · simp only [h1, ↓reduceDIte]
  · simp only [h1, ↓reduceDIte, «💐PropSub🌸», «💐🌸OfSmaller💐s»]

theorem «🌸∈Lift🌸To💐» («🪻0» «🪻L» : «🌸») (h0 : «Sub🌸» («💐» «🪻0») «🪻L») :
  «Same🌸s🌸∈» («Lift🌸To💐» «🪻0» «🪻L» h0) «🪻0» := by
  rw [«Same🌸s🌸∈»]
  intro «🪻»
  rw [«Lift🌸To💐»]
  by_cases h1 : («💐» «🪻0») = «🪻L»
  · simp only [h1, ↓reduceDIte]
  · simp only [h1, ↓reduceDIte]
    rw [«🌸∈PropSub🌸», «🌸∈🌸OfSmaller💐s»]
    simp only [ne_eq, and_iff_left_iff_imp]
    intro h2
    have h3 := «🌸∈→💐Sub🌸💐» _ _ h2
    have h4 := «TransitiveSub🌸» _ _ _ h3 h0
    simp only [true_and, ne_eq, h4]
    exact «TransitiveSub🌸But¬=» _ _ _ h3 h0 h1

theorem «Empty🌸🌸OfSmaller💐s↔🌺» («🪻» : «🌸») :
  «Empty🌸» («🌸OfSmaller💐s» «🪻») ↔ «🪻» = «🌺» := by
  constructor
  · intro h0
    by_contra h1
    rw [«Empty🌸»] at h0
    have h2 := h0 «🌺»
    rw [«🌸∈🌸OfSmaller💐s», «💐🌺»] at h2
    simp only [«🌺Sub🌸All», ne_eq, true_and, not_not] at h2
    simp only [h2, not_true_eq_false] at h1
  · intro h0
    rw [h0, «🌸OfSmaller💐s🌺»]
    exact «Empty🌸🌺»
