import Mathlib
set_option maxHeartbeats 0

axiom «🌸» : Type
axiom «🌺» : «🌸»
axiom Level : «🌸» → «🌸»
axiom BaseCaseLevel : Level «🌺» = «🌺»
axiom Within : «🌸» → «🌸» → Prop -- the first bloom is in the second bloom
def EmptyBloom («🪻0» : «🌸») := ∀ («🪻» : «🌸»), ¬Within «🪻» «🪻0»
axiom EmptyBloomBaseCase : EmptyBloom «🌺»
def SameBloomsWithin («🪻0» «🪻1» : «🌸») := ∀ («🪻» : «🌸»), (Within «🪻» «🪻0» ↔ Within «🪻» «🪻1»)
axiom BloomDefinedByLevelAndWhatIsWithin : ∀ («🪻0» «🪻1» : «🌸»),
  (SameBloomsWithin «🪻0» «🪻1» ∧ Level «🪻0» = Level «🪻1») ↔ «🪻0» = «🪻1»

axiom PropSubBloom : («🌸» → Prop) → «🌸» → «🌸»
axiom WithinPropSubBloom : ∀ (p : («🌸» → Prop)) («🪻» «🪻0» : «🌸»),
  Within «🪻0» (PropSubBloom p «🪻») ↔ (p «🪻0» ∧ Within «🪻0» «🪻»)
axiom LevelOfPropSubBloom : ∀ (p : («🌸» → Prop)) («🪻» : «🌸»),
  Level (PropSubBloom p «🪻») = Level «🪻»

axiom Maximum : «🌸» → «🌸» → «🌸»
axiom WithinMaximumIffWithinPart : ∀ («🪻0» «🪻1» «🪻2» : «🌸»),
  Within «🪻2» (Maximum «🪻0» «🪻1») ↔ (Within «🪻2» «🪻0» ∨ Within «🪻2» «🪻1»)
axiom LevelOfMaximum : ∀ («🪻0» «🪻1» : «🌸»), Level (Maximum «🪻0» «🪻1») = Maximum (Level «🪻0») (Level «🪻1»)

--should all be provable with EqualIfSameBloomsWithinAllMetaLevels
axiom SymmetricMaximum : ∀ («🪻0» «🪻1» : «🌸»), Maximum «🪻0» «🪻1» = Maximum «🪻1» «🪻0»
axiom MaximumOfSelf : ∀ («🪻» : «🌸»), Maximum «🪻» «🪻» = «🪻»
axiom BaseCaseMaximum : ∀ («🪻» : «🌸»), Maximum «🌺» «🪻» = «🪻»
axiom UniqueMaximumEqBaseCase («🪻0» «🪻1» : «🌸») :
  Maximum «🪻0» «🪻1» = «🌺» ↔ («🪻0» = «🌺» ∧ «🪻1» = «🌺»)

def SubBloom («🪻0» «🪻1» : «🌸») : Prop := (Maximum «🪻0» «🪻1») = «🪻1»

axiom LevelOfWithinSubBloomLevel : ∀ («🪻0» «🪻1» : «🌸»),
  Within «🪻0» «🪻1» → SubBloom (Level «🪻0») (Level «🪻1»)

--should all be provable with EqualIfSameBloomsWithinAllMetaLevels
axiom SubBloomOfMaximum : ∀ («🪻0» «🪻1» «🪻2» : «🌸»), SubBloom «🪻0» «🪻1» → SubBloom «🪻0» (Maximum «🪻1» «🪻2»)

axiom BloomOfSmallerLevels : «🌸» → «🌸»
axiom BloomOfSmallerLevelsWithin : ∀ («🪻0» «🪻1» : «🌸»),
  Within «🪻0» (BloomOfSmallerLevels «🪻1») ↔ (SubBloom (Level «🪻0») «🪻1» ∧ (Level «🪻0») ≠ «🪻1»)
axiom BloomOfSmallerLevelsLevel : ∀ («🪻» : «🌸»), Level (BloomOfSmallerLevels «🪻») = «🪻»

axiom PowerBloom : «🌸» → «🌸»
axiom SubBloomWithinPowerBloom : ∀ («🪻0» «🪻1» : «🌸»),
  SubBloom «🪻0» «🪻1» ↔ Within «🪻0» (PowerBloom «🪻1»)
axiom PowerBloomLevel : ∀ («🪻» : «🌸»), Level (PowerBloom «🪻») = Level «🪻»

theorem SubBloomOfSelf («🪻» : «🌸») : SubBloom «🪻» «🪻» := by
  rw [SubBloom, MaximumOfSelf]

noncomputable
def BloomOfSingleBloom («🪻» : «🌸») : «🌸» :=
  PropSubBloom (λ («🪻2» : «🌸») ↦ «🪻2» = «🪻») (PowerBloom «🪻»)

theorem UniqueWithinBloomOfSingleBloom («🪻0» «🪻1» : «🌸») :
  Within «🪻0» (BloomOfSingleBloom «🪻1») ↔ «🪻0» = «🪻1» := by
  rw [BloomOfSingleBloom, WithinPropSubBloom, ← SubBloomWithinPowerBloom]
  simp only [and_iff_left_iff_imp]
  intro h0
  rw [h0]
  exact SubBloomOfSelf «🪻1»

theorem LevelOfBloomOfSingleBloom («🪻» : «🌸») : Level (BloomOfSingleBloom «🪻») = Level «🪻» := by
  rw [BloomOfSingleBloom, LevelOfPropSubBloom, PowerBloomLevel]

theorem BloomOfSingleBloomNotEmptyBloom («🪻» : «🌸») : ¬EmptyBloom (BloomOfSingleBloom «🪻») := by
  rw [EmptyBloom]
  simp only [not_forall, not_not]
  use «🪻»
  exact (UniqueWithinBloomOfSingleBloom «🪻» «🪻»).mpr rfl

theorem EmptyBloomMaximumIffEmptyBloomEmptyBloom («🪻0» «🪻1» : «🌸») : ((EmptyBloom «🪻0») ∧ (EmptyBloom «🪻1»)) ↔
  EmptyBloom (Maximum «🪻0» «🪻1») := by
  constructor
  · intro h0
    obtain ⟨h1, h2⟩ := h0
    rw [EmptyBloom] at *
    intro «🪻»
    simp only [WithinMaximumIffWithinPart, h1, h2, or_self, not_false_eq_true]
  · intro h0
    simp only [EmptyBloom, WithinMaximumIffWithinPart, not_or] at *
    constructor
    · intro «🪻»
      simp only [(h0 «🪻»).left, not_false_eq_true]
    · intro «🪻»
      simp only [(h0 «🪻»).right, not_false_eq_true]

theorem NotEmptyBloomImpliesNotEmptyBloomMaximum («🪻0» «🪻1» : «🌸») (h : ¬EmptyBloom «🪻0») : ¬EmptyBloom (Maximum «🪻0» «🪻1»)
  := by
  have h0 := EmptyBloomMaximumIffEmptyBloomEmptyBloom «🪻0» «🪻1»
  simp only [h, false_and, false_iff] at h0
  exact h0

axiom MaximumOfWithin («🪻» : «🌸») (h : ¬EmptyBloom «🪻») : «🌸»
axiom MaximumOfWithinBloomOfSingleBloom («🪻» : «🌸») :
  MaximumOfWithin (BloomOfSingleBloom «🪻») (BloomOfSingleBloomNotEmptyBloom «🪻») = «🪻»
axiom MaximumOfWithinLevel («🪻» : «🌸») (h : ¬EmptyBloom «🪻») :
  Level (MaximumOfWithin «🪻» h) = Level «🪻»
axiom MaximumOfWithinMaximum («🪻0» «🪻1» : «🌸») (h0 : ¬EmptyBloom «🪻0») (h1 : ¬EmptyBloom «🪻1») :
  MaximumOfWithin (Maximum «🪻0» «🪻1») (NotEmptyBloomImpliesNotEmptyBloomMaximum «🪻0» «🪻1» h0) =
  Maximum (MaximumOfWithin «🪻0» h0) (MaximumOfWithin «🪻1» h1)

axiom IteratedPowerBloom : «🌸» → «🌸» → «🌸»
axiom IteratedPowerBloomLevel («🪻0» «🪻1» : «🌸») :
  Level (IteratedPowerBloom «🪻0» «🪻1») = Maximum (Level «🪻0») (Level «🪻1»)
axiom IteratedPowerBloomEmptyBloom («🪻0» «🪻1» : «🌸») (h : EmptyBloom «🪻1») :
  SameBloomsWithin (IteratedPowerBloom «🪻0» «🪻1») «🪻0»
axiom IteratedPowerBloomInduction («🪻0» «🪻1» : «🌸») (h : ¬EmptyBloom «🪻1») :
  IteratedPowerBloom «🪻0» «🪻1» = IteratedPowerBloom (PowerBloom «🪻0») (MaximumOfWithin «🪻1» h)
axiom IteratedPowerBloomTransfiniteInduction («🪻» : «🌸») :
  IteratedPowerBloom «🌺» (BloomOfSmallerLevels «🪻») = BloomOfSmallerLevels «🪻»

-- looks provable
axiom IteratedPowerBloomBaseWithin («🪻0» «🪻1» : «🌸») (h : ¬EmptyBloom «🪻1») :
  Within «🌺» (IteratedPowerBloom «🪻0» «🪻1»)
axiom IteratedPowerBloomBaseWithin2 («🪻0» «🪻1» : «🌸») (h : ¬EmptyBloom «🪻1») :
  Within (IteratedPowerBloom «🌺» (MaximumOfWithin «🪻1» h)) (IteratedPowerBloom «🪻0» «🪻1»)

-- should be provable
axiom BaseCaseIteratedPowerBloomSubBloom («🪻0» «🪻1» «🪻2» : «🌸») (h : SubBloom «🪻1» «🪻2») :
  SubBloom (IteratedPowerBloom «🌺» «🪻1») (IteratedPowerBloom «🪻0» «🪻2»)
axiom TransfiniteIteratedPowerBloomSimilar («🪻0» «🪻1» : «🌸») (h0 : Level «🪻0» ≠ «🪻1»)
  (h1 : SubBloom (Level «🪻0») «🪻1») :
  IteratedPowerBloom «🪻0» (BloomOfSmallerLevels «🪻1») = BloomOfSmallerLevels «🪻1»

axiom PeanoLessThan1 : «🌸» → «🌸» → Prop
axiom PeanoLessThan1Iff : ∀ («🪻0» «🪻1» : «🌸»), PeanoLessThan1 «🪻0» «🪻1» ↔
  (Within «🪻0» «🪻1» ∨ ∃ («🪻2» : «🌸»), (Within «🪻2» «🪻1» ∧ PeanoLessThan1 «🪻0» «🪻2»))

axiom ReplaceLeaves : «🌸» → «🌸» → «🌸»
axiom ReplaceLeavesEmptyBloom : ∀ («🪻0» «🪻1» : «🌸»), EmptyBloom «🪻0» → SameBloomsWithin (ReplaceLeaves «🪻0» «🪻1») «🪻1»
axiom ReplaceLeavesLevel : ∀ («🪻0» «🪻1» : «🌸»), Level (ReplaceLeaves «🪻0» «🪻1») = Maximum (Level «🪻0») (Level «🪻1»)

axiom WithinReplaceLeaves : ∀ («🪻0» «🪻1» «🪻2» : «🌸»), (¬EmptyBloom «🪻0») →
  (Within «🪻2» (ReplaceLeaves «🪻0» «🪻1») ↔ (∃ («🪻3» : «🌸»), («🪻2» = ReplaceLeaves «🪻3» «🪻1» ∧ Within «🪻3» «🪻0»)))

-- probably provable
axiom ReplaceLeavesBaseCase2 («🪻» : «🌸») : (ReplaceLeaves «🪻» «🌺») = «🪻»

def PeanoLessThan2 («🪻0» «🪻1» : «🌸») : Prop :=
  ∃ («🪻2» : «🌸»), («🪻2» ≠ «🌺» ∧ ReplaceLeaves «🪻0» «🪻2» = «🪻1»)
def PeanoLessThan3 («🪻0» «🪻1» : «🌸») : Prop :=
  ∃ («🪻2» : «🌸»), («🪻2» ≠ «🌺» ∧ ReplaceLeaves «🪻2» «🪻0» = «🪻1»)
def IteratedPowerBloomLessThanEqual («🪻0» «🪻1» : «🌸») :
  Prop := SubBloom (IteratedPowerBloom «🌺» «🪻0») (IteratedPowerBloom «🌺» «🪻1»)

-- Models random choice and unknowability, but by superdeterminism, the same seed «🌱» results in the same choice
axiom ChooseWithin («🪻» «🌱» : «🌸») (h : ¬EmptyBloom «🪻») : «🌸»
axiom WithinChooseWithin («🪻» «🌱» : «🌸») (h : ¬EmptyBloom «🪻») : Within (ChooseWithin «🪻» «🌱» h) «🪻»

noncomputable def PeanoBloom (k : ℕ) : «🌸» :=
  match k with
  | 0 => «🌺»
  | k0 + 1 => BloomOfSingleBloom (PeanoBloom k0)

--make sure the BaseLevel has only Blooms generated by a natural number of iterations of PowerBloom
axiom BaseLevelIteratedPowerBloomLessThanEqualSomePeanoBloom («🪻0» : «🌸») (h : Level «🪻0» = «🌺») :
  ∃ (k : ℕ), IteratedPowerBloomLessThanEqual «🪻0» (PeanoBloom k)

axiom MetaLevel : «🌸» → «🌸» → «🌸»
axiom MetaLevelBaseCase («🪻0» «🪻1» : «🌸») (h : EmptyBloom «🪻1») : MetaLevel «🪻0» «🪻1» = «🪻0»
axiom MetaLevelNonEmpty («🪻0» «🪻1» : «🌸») (h : ¬EmptyBloom «🪻1») :
  MetaLevel «🪻0» «🪻1» = MetaLevel (Level «🪻0») (MaximumOfWithin «🪻1» h)
axiom MetaLevelEventualBaseCase («🪻» : «🌸») : ∃ («🪻0» : «🌸»), MetaLevel «🪻» «🪻0» = «🌺»
axiom EqualIfSameBloomsWithinAllMetaLevels : ∀ («🪻0» «🪻1» : «🌸»),
  (∀ («🪻2» : «🌸»), Within «🪻2» «🪻0» ↔ Within «🪻2» «🪻1») ↔ «🪻0» = «🪻1»
axiom ExistsBloomOfSameMetaLevelDepth («🪻0» : «🌸») :
  ∃ («🪻1» : «🌸»), (∀ («🪻2» : «🌸»), (Within «🪻2» «🪻1» ↔ MetaLevel «🪻2» «🪻0» = «🌺»))

theorem SameBloomsWithinSelf («🪻» : «🌸») : SameBloomsWithin «🪻» «🪻» := by
  simp only [SameBloomsWithin, implies_true]

theorem EmptyBloomSameBloomsWithin («🪻0» «🪻1» : «🌸») (h0 : SameBloomsWithin «🪻0» «🪻1») :
  EmptyBloom «🪻0» ↔ EmptyBloom «🪻1» := by
  constructor
  · intro h1
    rw [EmptyBloom] at h1
    intro «🪻»
    exact (iff_false_left (h1 «🪻»)).mp (h0 «🪻»)
  · intro h1
    rw [EmptyBloom] at h1
    intro «🪻»
    rw [h0]
    exact h1 «🪻»

theorem UniqueEmptyBloomBaseLevel («🪻» : «🌸») (h0 : Level «🪻» = «🌺») : EmptyBloom «🪻» ↔ «🪻» = «🌺» := by
  constructor
  · intros h1
    rw [EmptyBloom] at h1
    rw [←BloomDefinedByLevelAndWhatIsWithin, BaseCaseLevel, SameBloomsWithin, h0]
    simp only [and_true]
    intro «🪻0»
    let h2 := EmptyBloomBaseCase
    rw [EmptyBloom] at h2
    exact (iff_false_right (h2 «🪻0»)).mpr (h1 «🪻0»)
  · intros h3
    rw [h3]
    exact EmptyBloomBaseCase

theorem WithinSelfImpliesWithinMaximum («🪻0» «🪻1» «🪻2» : «🌸») : Within «🪻2» «🪻0» → Within «🪻2» (Maximum «🪻0» «🪻1») := by
  intro h0
  rw [WithinMaximumIffWithinPart]
  left
  exact h0

theorem WithinSubBloom («🪻0» «🪻1» «🪻2» : «🌸») (h0 : SubBloom «🪻1» «🪻2»)
  (h1 : Within «🪻0» «🪻1») : Within «🪻0» «🪻2» := by
  rw [SubBloom, ← BloomDefinedByLevelAndWhatIsWithin] at h0
  obtain ⟨h3, h2⟩ := h0
  rw [SameBloomsWithin] at h3
  rw [← h3, WithinMaximumIffWithinPart]
  left
  exact h1

theorem SubBloomImpLevelSubBloom («🪻0» «🪻1» : «🌸») (h : SubBloom «🪻0» «🪻1») : SubBloom (Level «🪻0») (Level «🪻1») := by
  rw [SubBloom] at *
  have h0 := congr_arg Level h
  rw [LevelOfMaximum] at h0
  exact h0

theorem TransitiveSubBloom («🪻0» «🪻1» «🪻2» : «🌸») (h0 : SubBloom «🪻0» «🪻1») (h1 : SubBloom «🪻1» «🪻2») :
  SubBloom «🪻0» «🪻2» := by
  rw [SubBloom] at h1
  rw [←h1]
  exact SubBloomOfMaximum «🪻0» «🪻1» «🪻2» h0

theorem BaseCaseSubBloomAll («🪻» : «🌸») : SubBloom «🌺» «🪻» := by
  rw [SubBloom, BaseCaseMaximum]

theorem UniqueSubBloomBaseCase («🪻» : «🌸») : SubBloom «🪻» «🌺» ↔ «🪻» = «🌺» := by
  constructor
  · intro h
    rw [SubBloom, SymmetricMaximum, BaseCaseMaximum] at h
    exact h
  · intro h0
    rw [h0]
    exact BaseCaseSubBloomAll «🌺»

theorem BaseCaseNotPowerBloom («🪻0» : «🌸») : «🌺» ≠ (PowerBloom «🪻0») := by
  intro h
  let h0 := congr_arg (λ(«🪻» : «🌸»)↦(Within «🌺» «🪻»)) h
  simp only [← SubBloomWithinPowerBloom, BaseCaseSubBloomAll] at h0
  let h1 := EmptyBloomBaseCase
  rw [EmptyBloom] at h1
  let h2 := h1 «🌺»
  rw [h0] at h2
  exact h2 trivial

theorem MutualSubBloomsEqual («🪻0» «🪻1» : «🌸») :
  (SubBloom «🪻0» «🪻1» ∧ SubBloom «🪻1» «🪻0») ↔ «🪻0» = «🪻1» := by
  constructor
  · intro ⟨h0, h1⟩
    rw [SubBloom] at h0 h1
    rw [SymmetricMaximum] at h0
    rw [h1] at h0
    exact h0
  · intro h0
    simp only [h0, SubBloomOfSelf, and_self]

theorem SubBloomOfBloomOfSingleBloomBaseLevel («🪻0» «🪻1» : «🌸») (h0 : Level «🪻1» = «🌺») :
  SubBloom «🪻0» (BloomOfSingleBloom «🪻1») ↔ («🪻0» = «🌺» ∨ «🪻0» = BloomOfSingleBloom «🪻1») := by
  constructor
  · intro h
    have h4 := SubBloomImpLevelSubBloom _ _ h
    rw [SubBloom, ← BloomDefinedByLevelAndWhatIsWithin] at h
    obtain ⟨h1, h2⟩ := h
    rw [SameBloomsWithin] at h1
    simp_rw [UniqueWithinBloomOfSingleBloom, WithinMaximumIffWithinPart, UniqueWithinBloomOfSingleBloom] at h1
    simp only [or_iff_right_iff_imp] at h1
    rw [LevelOfBloomOfSingleBloom, h0, UniqueSubBloomBaseCase] at h4
    cases Classical.em (EmptyBloom «🪻0») with
    | inl h3 =>
      left
      rw [UniqueEmptyBloomBaseLevel _ h4] at h3
      exact h3
    | inr h6 =>
      right
      rw [← BloomDefinedByLevelAndWhatIsWithin, LevelOfBloomOfSingleBloom, h0, h4, SameBloomsWithin]
      simp only [UniqueWithinBloomOfSingleBloom, and_true]
      intro «🪻»
      constructor
      · exact h1 _
      · intro h9
        rw [h9] at *
        clear «🪻» h9
        rw [EmptyBloom] at h6
        simp only [not_forall, not_not] at h6
        rcases h6 with ⟨«🪻2», h7⟩
        have h8 := h1 _ h7
        rw [h8] at h7
        exact h7
  · intro h1
    cases h1 with
    | inl h2 =>
      rw [h2]
      exact BaseCaseSubBloomAll (BloomOfSingleBloom «🪻1»)
    | inr h2 =>
      rw [h2]
      exact SubBloomOfSelf (BloomOfSingleBloom «🪻1»)

theorem NotWithinBaseCase («🪻1» : «🌸») : ¬Within «🪻1» «🌺» := by
  have h := EmptyBloomBaseCase
  rw [EmptyBloom] at h
  exact h «🪻1»

theorem BaseCaseNotBloomOfSingleBloom («🪻1» : «🌸») : ¬«🌺» = BloomOfSingleBloom «🪻1» := by
  rw [←BloomDefinedByLevelAndWhatIsWithin]
  simp only [not_and]
  have h : ¬SameBloomsWithin «🌺» (BloomOfSingleBloom «🪻1») := by
    rw [SameBloomsWithin]
    simp only [not_forall]
    use «🪻1»
    simp [NotWithinBaseCase, UniqueWithinBloomOfSingleBloom]
  simp only [h, IsEmpty.forall_iff]

theorem SubBloomOfBloomOfSingleBloomBaseLevel1 («🪻» «🪻1» : «🌸») (h0 : Level «🪻1» = «🌺») :
  (SubBloom «🪻» (BloomOfSingleBloom «🪻1») ∧ «🪻» ≠ BloomOfSingleBloom «🪻1») ↔ «🪻» = «🌺» := by
  rw [SubBloomOfBloomOfSingleBloomBaseLevel _ _ h0]
  constructor
  · intro h
    have h1 := h.left
    have h2 := h.right
    simp only [h2, or_false] at h1
    exact h1
  · intro h
    simp only [h, BaseCaseNotBloomOfSingleBloom, true_or, ne_eq, true_and]
    exact fun a => a

theorem SubBloomOfBloomOfSingleBloomBaseLevel2 («🪻» «🪻1» : «🌸») (h0 : Level «🪻1» = «🌺») :
  (SubBloom «🪻» (BloomOfSingleBloom «🪻1») ∧ «🪻» ≠ «🌺») ↔ «🪻» = BloomOfSingleBloom «🪻1» := by
  rw [SubBloomOfBloomOfSingleBloomBaseLevel _ _ h0]
  constructor
  · intro h
    have h1 := h.left
    have h2 := h.right
    simp only [h2, false_or] at h1
    exact h1
  · intro h
    simp only [h, or_true, ne_eq, true_and]
    rw [←BloomDefinedByLevelAndWhatIsWithin]
    simp only [not_and]
    have h1 : ¬SameBloomsWithin (BloomOfSingleBloom «🪻1») «🌺» := by
      rw [SameBloomsWithin]
      simp only [not_forall]
      use «🪻1»
      rw [UniqueWithinBloomOfSingleBloom]
      simp only [true_iff, NotWithinBaseCase]
      exact fun a => a
    simp only [h1]
    exact fun a a_1 => a

theorem BloomOfSingleBloomNotBaseCase («🪻» : «🌸») : BloomOfSingleBloom «🪻» ≠ «🌺»:= by
  let h0 := UniqueWithinBloomOfSingleBloom «🪻» «🪻»
  by_contra h1
  rw [h1] at h0
  let h2 := EmptyBloomBaseCase
  rw [EmptyBloom] at h2
  let h3 := h2 «🪻»
  simp only [h0, not_true_eq_false] at h3

theorem EqualBloomOfSingleBloom («🪻0» «🪻1» : «🌸») : BloomOfSingleBloom «🪻0» = BloomOfSingleBloom «🪻1» ↔ «🪻0» = «🪻1» := by
  constructor
  · intro h0
    let h1 := congr_arg Level h0
    rw [LevelOfBloomOfSingleBloom, LevelOfBloomOfSingleBloom] at h1
    rw [←BloomDefinedByLevelAndWhatIsWithin, SameBloomsWithin] at h0
    let h2 := h0.left
    simp_rw [UniqueWithinBloomOfSingleBloom] at h2
    let h3 := h2 «🪻0»
    simp only [true_iff] at h3
    exact h3
  · intro h2
    rw [h2]

theorem BaseCaseBloomOfSmallerLevels : BloomOfSmallerLevels «🌺» = «🌺» := by
  rw [←BloomDefinedByLevelAndWhatIsWithin, BloomOfSmallerLevelsLevel, BaseCaseLevel]
  let h0 := EmptyBloomBaseCase
  rw [EmptyBloom] at h0
  simp only [and_true]
  intro «🪻»
  simp only [BloomOfSmallerLevelsWithin, UniqueSubBloomBaseCase, ne_eq, and_not_self, h0]

theorem IteratedPowerBloomEmptyBloomIff («🪻0» «🪻1» : «🌸») :
  EmptyBloom (IteratedPowerBloom «🪻0» «🪻1») ↔ (EmptyBloom «🪻0» ∧ EmptyBloom «🪻1») := by
  constructor
  · intro h0
    simp_rw [EmptyBloom] at *
    constructor
    · intro «🪻»
      sorry
    · intro «🪻»
      have h1 := BaseCaseIteratedPowerBloomSubBloom
      sorry
  · intro h0
    have h1 := IteratedPowerBloomEmptyBloom «🪻0» «🪻1» h0.right
    sorry

--shows that iterated power Blooms are not obvious at higher levels
theorem IteratedPowerBloomCounterexample («🪻» : «🌸») (h0 : EmptyBloom «🪻») (h1 : «🪻» ≠ «🌺») :
  ¬IteratedPowerBloom «🌺» «🪻» = «🌺» := by
  intro h2
  let h3 := congr_arg Level h2
  rw [IteratedPowerBloomLevel, BaseCaseLevel, BaseCaseMaximum] at h3
  rw [UniqueEmptyBloomBaseLevel «🪻» h3] at h0
  exact h1 h0

theorem LevelOfSubBloomOfBaseLevel («🪻0» «🪻1» : «🌸») (h0 : Level «🪻1» = «🌺») (h1 : SubBloom «🪻0» «🪻1») :
  Level «🪻0» = «🌺» := by
  rw [SubBloom] at h1
  let h2 := congr_arg Level h1
  rw [LevelOfMaximum, h0, SymmetricMaximum, BaseCaseMaximum] at h2
  exact h2

theorem SameBloomsWithinBloomOfSmallerLevelsOfSingleBloom («🪻0» «🪻1» : «🌸») (h0 : Level «🪻0» = «🌺») (h1 : Level «🪻1» = «🌺»)
  : SameBloomsWithin (BloomOfSmallerLevels (BloomOfSingleBloom «🪻0»)) (BloomOfSmallerLevels (BloomOfSingleBloom «🪻1»)) := by
  rw [SameBloomsWithin]
  intros «🪻»
  have h2 : ∀ («🪻2» «🪻3» : «🌸») (h3 : Level «🪻2» = «🌺») (h4 : Level «🪻3» = «🌺»),
    Within «🪻» (BloomOfSmallerLevels (BloomOfSingleBloom «🪻2»)) →
    Within «🪻» (BloomOfSmallerLevels (BloomOfSingleBloom «🪻3»)) := by
    intros «🪻2» «🪻3» h5 h6 h7
    rw [BloomOfSmallerLevelsWithin] at h7
    let h8 := SubBloomOfBloomOfSingleBloomBaseLevel (Level «🪻») «🪻2» h5
    rw [h8] at h7
    simp only [ne_eq] at h7
    have h9 : ((Level «🪻» = «🌺» ∨ Level «🪻» = BloomOfSingleBloom «🪻2») ∧ ¬Level «🪻» = BloomOfSingleBloom «🪻2»)
      → Level «🪻» = «🌺» := by tauto
    have h10 := h9 h7
    rw [BloomOfSmallerLevelsWithin, h10]
    simp only [BaseCaseSubBloomAll, ne_eq, true_and]
    let h11 := (BloomOfSingleBloomNotBaseCase «🪻3»).symm
    simp only [h11, not_false_eq_true]
  constructor
  · exact h2 «🪻0» «🪻1» h0 h1
  · exact h2 «🪻1» «🪻0» h1 h0

theorem ChooseWithinBloomOfSingleBloom («🪻» «🌱» : «🌸») :
  ChooseWithin (BloomOfSingleBloom «🪻») «🌱» (BloomOfSingleBloomNotEmptyBloom «🪻») = «🪻» := by
  let h0 := WithinChooseWithin (BloomOfSingleBloom «🪻») «🌱» (BloomOfSingleBloomNotEmptyBloom «🪻»)
  exact
    (UniqueWithinBloomOfSingleBloom
          (ChooseWithin (BloomOfSingleBloom «🪻») «🌱» (BloomOfSingleBloomNotEmptyBloom «🪻»)) «🪻»).mp
      h0

theorem PeanoBloomLevel (k : ℕ) : Level (PeanoBloom k) = «🌺» := by
  induction k with
  | zero => rw [PeanoBloom, BaseCaseLevel]
  | succ k0 ih =>
    rw [PeanoBloom, LevelOfBloomOfSingleBloom, ih]

theorem PeanoBloomEqBaseImp0 (k0 : ℕ) : PeanoBloom k0 = «🌺» ↔ k0 = 0 := by
  constructor
  · intro h0
    cases eq_or_ne k0 0 with
    | inl h1 =>
      exact h1
    | inr h1 =>
      rcases Nat.exists_eq_succ_of_ne_zero h1 with ⟨k1, h2⟩
      rw [h2, PeanoBloom] at h0
      simp only [BloomOfSingleBloomNotBaseCase] at h0
  · intro h1
    rw [h1, PeanoBloom]

theorem PeanoBloomEqIffSucc (k0 k1 : ℕ) : PeanoBloom k0 = PeanoBloom k1 ↔ PeanoBloom (k0 + 1) = PeanoBloom (k1 + 1) := by
  constructor
  · intro h0
    rw [PeanoBloom, PeanoBloom, h0]
  · intro h1
    rw [PeanoBloom, PeanoBloom, EqualBloomOfSingleBloom] at h1
    exact h1

theorem PeanoBloomEqIffAdd (k0 k1 k2 : ℕ) : PeanoBloom k0 = PeanoBloom k1 ↔ PeanoBloom (k0 + k2) = PeanoBloom (k1 + k2) := by
  induction k2 with
  | zero => simp only [add_zero]
  | succ k3 ih =>
    have h0 := PeanoBloomEqIffSucc (k0 + k3) (k1 + k3)
    rw [h0] at ih
    exact ih

theorem PeanoBloomLessNotEq (k0 k1 : ℕ) (h : k0 < k1) : PeanoBloom k0 ≠ PeanoBloom k1 := by
  have h0 : k0 ≤ k1 := by exact Nat.le_of_succ_le h
  let h1 := Nat.exists_eq_add_of_le (Nat.le_of_succ_le h)
  rcases h1 with ⟨k2, h2⟩
  rw [h2]
  simp only [ne_eq]
  rw [h2] at h
  have h4 : 0 < k2 := Nat.lt_add_right_iff_pos.mp h
  have h5 : 0 ≠ k2 := by exact Ne.symm (Nat.ne_zero_of_lt h4)
  have h3 := PeanoBloomEqIffAdd 0 k2 k0
  rw [PeanoBloom, eq_comm, PeanoBloomEqBaseImp0] at h3
  simp only [zero_add] at h3
  simp only [ne_eq, eq_comm, h3, Nat.add_comm] at h5
  exact h5

--Difficult to apply
theorem PeanoBloomInjective : PeanoBloom.Injective := by
  intro k₀ k₁ h
  have h0 := Nat.lt_trichotomy k₀ k₁
  cases h0 with
  | inl h1 =>
    simp only [PeanoBloomLessNotEq k₀ k₁ h1] at h
  | inr h2 =>
    cases h2 with
    | inl h3 => exact h3
    | inr h4 =>
      simp only [(PeanoBloomLessNotEq k₁ k₀ h4).symm] at h

theorem PeanoBloomInjective0 (k₀ k₁ : ℕ) : PeanoBloom k₀ = PeanoBloom k₁ ↔ k₀ = k₁ := by
  constructor
  · intro h
    have h0 := Nat.lt_trichotomy k₀ k₁
    cases h0 with
    | inl h1 =>
      simp only [PeanoBloomLessNotEq k₀ k₁ h1] at h
    | inr h2 =>
      cases h2 with
      | inl h3 => exact h3
      | inr h4 =>
        simp only [(PeanoBloomLessNotEq k₁ k₀ h4).symm] at h
  · intro h
    rw [h]

theorem ReplaceLeavesEmptyBloomEmptyBloom («🪻0» «🪻1» : «🌸») (h0 : EmptyBloom «🪻0») (h1 : EmptyBloom «🪻1») :
  EmptyBloom (ReplaceLeaves «🪻0» «🪻1») := by
  rw [EmptyBloom]
  intro «🪻»
  have h2 := ReplaceLeavesEmptyBloom «🪻0» «🪻1» h0
  rw [SameBloomsWithin] at h2
  rw [EmptyBloom] at h1
  exact (iff_false_right (h1 «🪻»)).mp (h2 «🪻»)

theorem ReplaceLeavesBaseCase («🪻» : «🌸») : (ReplaceLeaves «🌺» «🪻») = «🪻» := by
  rw [←BloomDefinedByLevelAndWhatIsWithin, ReplaceLeavesLevel, BaseCaseLevel, BaseCaseMaximum]
  have h0 := ReplaceLeavesEmptyBloom «🌺» «🪻» EmptyBloomBaseCase
  simp only [h0, and_self]

theorem NoRusselBloom («🪻R» : «🌸») (h : ∀ («🪻0» : «🌸»), Within «🪻0» «🪻R» ↔ ¬Within «🪻0» «🪻0») : False := by
  have h0 := (h «🪻R»).eq
  exact Lean.Grind.false_of_not_eq_self (id (Eq.symm h0))

theorem NotSubBloomImpNotBaseCase («🪻0» «🪻1» : «🌸») (h : ¬SubBloom «🪻0» «🪻1») : ¬«🪻0» = «🌺» := by
  by_contra h0
  rw [h0] at h
  simp only [BaseCaseSubBloomAll «🪻1», not_true_eq_false] at h

theorem SubBloomImpSubBloomOfLevels («🪻0» «🪻1» : «🌸») (h0 : SubBloom «🪻0» «🪻1») :
  SubBloom (Level «🪻0») (Level «🪻1») := by
  rw [SubBloom] at *
  have h1 := congr_arg Level h0
  rw [LevelOfMaximum] at h1
  exact h1

-- Bloom containing all blooms the of the RusselBloom restricted to maximmum level «🪻L»
-- not obviously inconsistent
theorem RusselBloomWithMaxLevel («🪻R» «🪻L» «🪻L0» «🪻» : «🌸») (h1 : SubBloom (Level «🪻R») «🪻L0»)
  (h2 : Level «🪻L0» = «🌺») (h3 : «🪻L0» = (BloomOfSingleBloom «🪻»))
  (h : ∀ («🪻0» : «🌸»), (Within «🪻0» «🪻R» ↔ (¬Within «🪻0» «🪻0» ∧ SubBloom (Level «🪻0») «🪻L»))) :
  (¬Level «🪻R» = «🌺») ∧ (Level (Level «🪻R») = «🌺») ∧ (¬SubBloom (Level «🪻R») «🪻L») ∧
  (¬«🪻L» = «🪻L0») ∧ (Level «🪻» = «🌺») ∧ (¬SubBloom (Level «🪻R») «🪻L») := by
  simp [h3] at *
  clear h3
  have h0 : ¬SubBloom (Level «🪻R») «🪻L» := by
    by_contra h9
    have h10 := h «🪻R»
    simp only [h9, and_true, iff_not_self] at h10
  have h7 : ¬«🪻L» = (BloomOfSingleBloom «🪻») := by
    by_contra h8
    simp [h8, h1] at *
  have h4 := NotSubBloomImpNotBaseCase _ _ h0
  have h6 : Level (Level «🪻R») = «🌺» := LevelOfSubBloomOfBaseLevel (Level «🪻R») (BloomOfSingleBloom «🪻») h2 h1
  have h8 : Level «🪻» = «🌺» := by
    rw [LevelOfBloomOfSingleBloom] at h2
    exact h2
  simp [*]

theorem PeanoLessThan1ForPeanoBloom (k0 k1 : ℕ) : k0 < k1 ↔ PeanoLessThan1 (PeanoBloom k0) (PeanoBloom k1) := by
  constructor
  · intro h0
    rw [PeanoLessThan1Iff]
    sorry
  · intro h0
    sorry

theorem PeanoLessThan2ForPeanoBloom (k0 k1 : ℕ) : k0 < k1 ↔ PeanoLessThan2 (PeanoBloom k0) (PeanoBloom k1) := by
  constructor
  · intro h0
    sorry
  · intro h0
    sorry

theorem PeanoLessThan3ForPeanoBloom (k0 k1 : ℕ) : k0 < k1 ↔ PeanoLessThan3 (PeanoBloom k0) (PeanoBloom k1) := by
  constructor
  · intro h0
    sorry
  · intro h0
    sorry

theorem BaseLevelIteratedPowerBloomEqualSomePeanoBloom («🪻0» : «🌸») (h : Level «🪻0» = «🌺») :
  ∃! (k : ℕ), (IteratedPowerBloomLessThanEqual «🪻0» (PeanoBloom k) ∧
    ∀ (k0 : ℕ), k0 < k → ¬IteratedPowerBloomLessThanEqual «🪻0» (PeanoBloom k0)) := by
  sorry

theorem PeanoBloomWithinSucc (k0 k1 : ℕ) : Within (PeanoBloom k0) (PeanoBloom k1) ↔ k1 = k0 + 1:= by
  constructor
  · induction k1 with
    | zero =>
      simp only [right_eq_add, Nat.add_eq_zero, one_ne_zero, and_false, imp_false, PeanoBloom, NotWithinBaseCase]
      exact fun a => a
    | succ k2 ih =>
      rw [PeanoBloom, UniqueWithinBloomOfSingleBloom]
      intro h1
      have h2 : k0 = k2 := (PeanoBloomInjective0 k0 k2).mp h1
      simp only [h2]
  · intro h
    rw [h]
    induction k0 with
    | zero =>
      rw [PeanoBloom, PeanoBloom, UniqueWithinBloomOfSingleBloom, PeanoBloom]
    | succ k2 ih =>
      have h0 : (PeanoBloom (k2 + 1 + 1)) = BloomOfSingleBloom (PeanoBloom (k2 + 1)) := rfl
      rw [h0, UniqueWithinBloomOfSingleBloom]

noncomputable
def RangePeanoBloom (k : ℕ) : «🌸» := match k with
  | 0 => «🌺»
  | k + 1 => Maximum (RangePeanoBloom k) (PeanoBloom (k + 1))

noncomputable def BloomMinus («🪻0» «🪻1» : «🌸») : «🌸» := PropSubBloom (λ («🪻2» : «🌸») ↦ ¬Within «🪻2» «🪻1») «🪻0»
theorem WithinBloomMinus («🪻0» «🪻1» «🪻2» : «🌸») :
  Within «🪻2» (BloomMinus «🪻0» «🪻1») ↔ (Within «🪻2» «🪻0» ∧ ¬Within «🪻2» «🪻1») := by
  rw [BloomMinus, WithinPropSubBloom]
  exact And.comm
theorem BloomMinusLevel («🪻0» «🪻1» : «🌸») : Level (BloomMinus «🪻0» «🪻1») = Level «🪻0» := by
  rw [BloomMinus, LevelOfPropSubBloom]

theorem BloomMinusSubBloomSelf («🪻0» «🪻1» : «🌸») : SubBloom (BloomMinus «🪻0» «🪻1») «🪻0» := by
  rw [SubBloom, ←BloomDefinedByLevelAndWhatIsWithin]
  constructor
  · rw [SameBloomsWithin]
    intro «🪻»
    rw [WithinMaximumIffWithinPart]
    constructor
    · rw [WithinBloomMinus]
      intro h
      cases h with
      | inl h => exact h.left
      | inr h => exact h
    · intro h
      right
      exact h
  · rw [LevelOfMaximum, BloomMinusLevel, MaximumOfSelf]

theorem UniquePeanoBloomWithinRangePeanoBloomSuccBloomMinusRangePeanoBloom (k1 k3 : ℕ) :
  Within (PeanoBloom k1) (BloomMinus (RangePeanoBloom (k3 + 1)) (RangePeanoBloom k3)) ↔
  k1 = k3 := by
  constructor
  · rw [WithinBloomMinus]
    intro h0
    sorry
  · intro h
    rw [h]
    sorry

theorem RangePeanoBloomRangeNat (k0 k1 : ℕ) : k1 < k0 ↔ Within (PeanoBloom k1) (RangePeanoBloom k0) := by
  induction k0 with
  | zero => simp only [not_lt_zero', RangePeanoBloom, NotWithinBaseCase]
  | succ k3 ih =>
    constructor
    · intro h0
      rw [RangePeanoBloom, WithinMaximumIffWithinPart, ←ih]
      have h1 : k1 < (k3 + 1) := by exact h0
      have h2 : k1 < k3 ∨ k1 = k3 := by exact Nat.lt_succ_iff_lt_or_eq.mp h1
      cases h2 with
      | inl h2 => simp only [h2, true_or]
      | inr h3 =>
        simp only [h3, lt_self_iff_false, PeanoBloomWithinSucc, or_true]
    · intro h0
      cases Classical.em (k1 < k3) with
      | inl h1 => exact Nat.lt_add_right 1 h1
      | inr h1 =>
        simp only [h1, false_iff] at ih
        sorry

-- theorem RangePeanoBloomSubBloomIteratedPowerBloom (k : ℕ) : ∀ («🪻0» «🪻1» : «🌸»),
--   IteratedPowerBloomLessThanEqual «🪻0» «🪻1» ↔
--   SubBloom (IteratedPowerBloom «🌺» «🪻0») (IteratedPowerBloom «🌺» (PeanoBloom k)) := sorry

theorem NotEmptyBloomPeanoBloomSucc (k : ℕ) : ¬EmptyBloom (PeanoBloom (k + 1)) := by
  rw [PeanoBloom]
  exact BloomOfSingleBloomNotEmptyBloom (PeanoBloom k)

theorem IteratedPowerBloomLessThanEqualForPeanoBloom (k0 k1 : ℕ) :
  k0 ≤ k1 ↔ IteratedPowerBloomLessThanEqual (PeanoBloom k0) (PeanoBloom k1) :=
  Nat.strong_induction_on k1 fun k2 =>
  have h2 : IteratedPowerBloom «🌺» «🌺» = «🌺» := by
    sorry
  have h4 : ∀ (k3 : ℕ), ¬k3 = 0 ↔ ∃ (k2 : ℕ), k3 = k2 + 1 := by
    intro k3
    constructor
    · intro h0
      by_contra h1
      simp only [Nat.exists_eq_add_one, not_lt, nonpos_iff_eq_zero] at h1
      simp [h1] at h0
    · intro h0
      rcases h0 with ⟨k2, h1⟩
      simp only [h1, Nat.add_eq_zero, one_ne_zero, and_false, not_false_eq_true]
  have h3 : ∀ (k : ℕ), IteratedPowerBloom «🌺» (PeanoBloom k) = «🌺» ↔ k = 0 := by
    intro k
    constructor
    · intro h6
      by_contra h1
      simp only [(h4 k), Nat.exists_eq_add_one] at h1
      sorry
    · intro h0
      rw [h0, PeanoBloom, h2]
  match k2 with
  | 0 => by
    intro h0
    simp only [nonpos_iff_eq_zero, PeanoBloom, IteratedPowerBloomLessThanEqual]
    constructor
    · intro h1
      simp only [h1, PeanoBloom, SubBloomOfSelf]
    · intro h1
      simp only [h2, UniqueSubBloomBaseCase] at h1
      sorry
  | k3 + 1 => by
    sorry

theorem WithinPeanoBloom (k : ℕ) («🪻» : «🌸») : Within «🪻» (PeanoBloom (k + 1)) ↔ «🪻» = PeanoBloom k := by
  constructor
  · intro h
    rw [PeanoBloom, UniqueWithinBloomOfSingleBloom] at h
    exact h
  · intro h
    rw [PeanoBloom, h, UniqueWithinBloomOfSingleBloom]

theorem MaximumOfWithinBloomPeanoBloomSucc (k : ℕ) :
  MaximumOfWithin (PeanoBloom (k + 1)) (NotEmptyBloomPeanoBloomSucc k) = PeanoBloom k := by
  simp_rw [PeanoBloom, MaximumOfWithinBloomOfSingleBloom]

theorem IteratedPowerBloomIteratedPowerBloomBase («🪻» : «🌸») :
  IteratedPowerBloom «🌺» (IteratedPowerBloom «🌺» «🪻») = IteratedPowerBloom «🌺» «🪻» := by
  sorry

theorem IteratedPowerBloomPeanoBloomAddition (k0 k1 : ℕ) :
  (IteratedPowerBloom «🌺» (PeanoBloom (k0 + k1))) =
  (IteratedPowerBloom (IteratedPowerBloom «🌺» (PeanoBloom k0)) (IteratedPowerBloom «🌺» (PeanoBloom k1))) := by
  induction k0 with
  | zero =>
    simp only [zero_add, PeanoBloom, IteratedPowerBloomEmptyBloom, IteratedPowerBloomIteratedPowerBloomBase]
    sorry
  | succ k2 ih =>

    sorry

--all BaseLevel Blooms are generated by the IteratedPowerBloom within the BaseLevel
theorem BaseLevelWithinIteratedPowerBloomOfSomePeanoBloom («🪻0» : «🌸») : (Level «🪻0» = «🌺») ↔
  ∃ (k : ℕ), Within «🪻0» (IteratedPowerBloom «🌺» (PeanoBloom k)) := by
  constructor
  · have h0 := BaseLevelIteratedPowerBloomLessThanEqualSomePeanoBloom «🪻0»
    intro h1
    simp only [h1, forall_const] at h0
    rcases h0 with ⟨k, h2⟩
    rw [IteratedPowerBloomLessThanEqual] at h2
    use (k + 1)
    rw [IteratedPowerBloomInduction _ _ (NotEmptyBloomPeanoBloomSucc _)]
    simp_rw [PeanoBloom]
    sorry
  · intro h0
    rcases h0 with ⟨k, h1⟩
    have h2 := LevelOfWithinSubBloomLevel «🪻0» (IteratedPowerBloom «🌺» (PeanoBloom k)) h1
    have h3 := IteratedPowerBloomLevel «🌺» (PeanoBloom k)
    rw [BaseCaseLevel, PeanoBloomLevel, MaximumOfSelf] at h3
    rw [h3] at h2
    exact (UniqueSubBloomBaseCase (Level «🪻0»)).mp h2

theorem NotEmptyBloomSuccPeanoBloom (k : ℕ) : ¬EmptyBloom (PeanoBloom (k + 1)) := by
  rw [EmptyBloom]
  simp only [not_forall, not_not]
  use PeanoBloom k
  rw [PeanoBloom]
  exact (UniqueWithinBloomOfSingleBloom (PeanoBloom k) (PeanoBloom k)).mpr rfl

theorem MaximumOfWithinPeanoBloom (k : ℕ) :
  MaximumOfWithin (PeanoBloom (k + 1)) (NotEmptyBloomSuccPeanoBloom k) = (PeanoBloom k):= by
  induction k with
  | zero =>
    rw [PeanoBloom]
    simp only [zero_add]
    have h0 : PeanoBloom 1 = BloomOfSingleBloom (PeanoBloom 0) := by exact rfl
    simp_rw [h0, MaximumOfWithinBloomOfSingleBloom]
    rw [PeanoBloom]
  | succ k ih =>
    have h0 : PeanoBloom (k + 1 + 1) = BloomOfSingleBloom (PeanoBloom (k + 1)) := by exact rfl
    simp_rw [h0, MaximumOfWithinBloomOfSingleBloom]

theorem IteratedPowerBloomNotCommutative : (IteratedPowerBloom (PeanoBloom 2) «🌺»)
  ≠ (IteratedPowerBloom «🌺» (PeanoBloom 2)) := by
  sorry

noncomputable def AsymmMinimum («🪻0» «🪻1» : «🌸») := PropSubBloom (λ («🪻2» : «🌸») ↦ Within «🪻2» «🪻1») «🪻0»

theorem PropSubBloomSubBloom (p : («🌸» → Prop)) («🪻» : «🌸») : SubBloom (PropSubBloom p «🪻») «🪻» := by
  rw [SubBloom,←BloomDefinedByLevelAndWhatIsWithin, SameBloomsWithin]
  simp_rw [WithinMaximumIffWithinPart]
  constructor
  · intro «🪻0»
    simp only [WithinPropSubBloom, or_iff_right_iff_imp, and_imp, imp_self, implies_true]
  · rw [LevelOfMaximum, LevelOfPropSubBloom, MaximumOfSelf]

theorem WithinBothPeanoBloomIffEqual (k0 k1 : ℕ) («🪻» : «🌸») (h0 : Within «🪻» (PeanoBloom k0))
  (h1 : Within «🪻» (PeanoBloom k1)) : k0 = k1 := by
  induction k0 with
  | zero =>
    rw [PeanoBloom] at h0
    simp only [NotWithinBaseCase] at h0
  | succ k2 ih =>
    rw [PeanoBloom, UniqueWithinBloomOfSingleBloom] at h0
    rw [h0, PeanoBloomWithinSucc] at h1
    exact h1.symm

theorem BadMinimumExample (BadMinimum : «🌸» → «🌸» → «🌸»)
  (SelfBadMinimum : ∀ («🪻» : «🌸»), BadMinimum «🪻» «🪻» = «🪻»)
  (WithinBadMinimum : ∀ («🪻0» «🪻1» «🪻2» : «🌸»),
  Within «🪻2» (BadMinimum «🪻0» «🪻1») ↔ (Within «🪻2» «🪻0» ∧ Within «🪻2» «🪻1»))
  (LevelOfBadMinimum : ∀ («🪻0» «🪻1» : «🌸»),
  Level (BadMinimum «🪻0» «🪻1») = BadMinimum (Level «🪻0») (Level «🪻1»)) : False := by
  let «🪻» := BadMinimum (BloomOfSmallerLevels (PeanoBloom 1)) (BloomOfSmallerLevels (PeanoBloom 2))
  have h4 : «🪻» = BadMinimum (BloomOfSmallerLevels (PeanoBloom 1)) (BloomOfSmallerLevels (PeanoBloom 2)) := rfl
  have h0 : Level «🪻» = «🌺» := by
    rw [LevelOfBadMinimum, BloomOfSmallerLevelsLevel, BloomOfSmallerLevelsLevel, ← BloomDefinedByLevelAndWhatIsWithin,
        SameBloomsWithin, BaseCaseLevel]
    simp only [WithinBadMinimum, NotWithinBaseCase, iff_false, not_and, LevelOfBadMinimum,
      PeanoBloomLevel, SelfBadMinimum, and_true]
    intro «🪻3» h
    by_contra h0
    have h1 := WithinBothPeanoBloomIffEqual 1 2 «🪻3» h h0
    simp only [OfNat.one_ne_ofNat] at h1
  have h1 : ∀ («🪻3» : «🌸»), Within «🪻3» «🪻» ↔ Level «🪻3» = «🌺» := by
    intro «🪻3»
    constructor
    · intro h1
      have h2 := LevelOfWithinSubBloomLevel _ _ h1
      rw [h0, UniqueSubBloomBaseCase] at h2
      exact h2
    · intro h5
      rw [h4, WithinBadMinimum, BloomOfSmallerLevelsWithin, BloomOfSmallerLevelsWithin, h5]
      simp only [BaseCaseSubBloomAll, ne_eq, true_and]
      have h7 := PeanoBloomEqBaseImp0 1
      have h6 := PeanoBloomEqBaseImp0 2
      simp only [one_ne_zero, iff_false, OfNat.ofNat_ne_zero] at h7 h6
      constructor
      · by_contra h8
        simp only [h8, not_true_eq_false] at h7
      · by_contra h8
        simp only [h8, not_true_eq_false] at h6
  have h2 : Within «🪻» «🪻» := by
    rw [h1, h0]
  sorry

-- maybe shorter proof
theorem ReplaceLeavesIsPeanoBloomAdd (k0 k1 : ℕ) : ReplaceLeaves (PeanoBloom k0) (PeanoBloom k1) = PeanoBloom (k0 + k1) :=
  Nat.strong_induction_on k0 fun k2 =>
    match k2 with
    | 0 => by
      intro h
      rw [PeanoBloom, ReplaceLeavesBaseCase]
      simp only [zero_add]
    | k3 + 1 => by
      intro h
      rw [← BloomDefinedByLevelAndWhatIsWithin, ReplaceLeavesLevel, PeanoBloomLevel, PeanoBloomLevel, PeanoBloomLevel,
          MaximumOfSelf, SameBloomsWithin]
      simp only [and_true]
      intro «🪻»
      rw [(show k3 + 1 + k1 = k3 + k1 + 1 by ring), WithinPeanoBloom]
      have h1 : ∀ (k8 : ℕ), ¬EmptyBloom (PeanoBloom (k8 + 1)) := by
        intro k8
        simp only [PeanoBloom]
        exact BloomOfSingleBloomNotEmptyBloom _
      constructor
      · intro h2
        rw [←(WithinPeanoBloom (k3 + k1) «🪻»), WithinPeanoBloom]
        rw [WithinReplaceLeaves _ _ _ (h1 _)] at h2
        rcases h2 with ⟨«🪻2», h0, h2⟩
        rw [h0]
        clear «🪻» h0
        rw [WithinPeanoBloom] at h2
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
            rw [PeanoBloom, ReplaceLeavesBaseCase2, PeanoBloomWithinSucc]
          | k5 + 1 => by
            intro h0
            simp only [h1, not_false_eq_true, WithinReplaceLeaves]
            use PeanoBloom k3
            simp only [PeanoBloomWithinSucc, and_true]
            cases Classical.em (k1 = k5 + 1) with
            | inl h2 =>
              rw [h2] at h
              simp only [lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt, h]
            | inr h2 =>
              exact Nat.strong_induction_on k3 fun k6 =>
              match k6 with
              | 0 => by
                intro h3
                rw [PeanoBloom, ReplaceLeavesBaseCase]
                simp only [zero_add]
              | k7 + 1 => by
                intro h3
                rw [← BloomDefinedByLevelAndWhatIsWithin, PeanoBloomLevel, ReplaceLeavesLevel,
                    SameBloomsWithin, PeanoBloomLevel, PeanoBloomLevel, MaximumOfSelf]
                simp only [and_true]
                intro «🪻»
                rw [(show (k7 + 1 + (k5 + 1)) = ((k7 + k5 + 1) + 1) by ring), WithinPeanoBloom,
                    WithinReplaceLeaves _ _ _ (h1 _)]
                constructor
                · intro h4
                  use PeanoBloom k7
                  rw [WithinPeanoBloom, h4]
                  clear «🪻» h4
                  simp only [and_true]
                  rw [← BloomDefinedByLevelAndWhatIsWithin, PeanoBloomLevel, ReplaceLeavesLevel, PeanoBloomLevel,
                      PeanoBloomLevel, MaximumOfSelf, SameBloomsWithin]
                  simp only [and_true]
                  intro «🪻»
                  rw [WithinPeanoBloom]
                  constructor
                  · intro h5
                    rw [h5]
                    have h6 := h3 k7
                    simp only [lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt, forall_const] at h6
                    rw [←h6, (show (k7 + (k5 + 1)) = ((k7 + k5) + 1) by ring), WithinPeanoBloom]
                  · have h5 := h3 k7
                    simp only [lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt, forall_const] at h5
                    rw [←h5, (show (k7 + (k5 + 1)) = ((k7 + k5) + 1) by ring), WithinPeanoBloom]
                    simp only [imp_self]
                · intro h4
                  rcases h4 with ⟨«🪻2», h5, h6⟩
                  rw [WithinPeanoBloom] at h6
                  rw [h6] at h5
                  rw [h5]
                  clear h5 h6 «🪻» «🪻2»
                  rw [← BloomDefinedByLevelAndWhatIsWithin, ReplaceLeavesLevel, PeanoBloomLevel, PeanoBloomLevel, PeanoBloomLevel,
                      MaximumOfSelf, SameBloomsWithin]
                  simp only [WithinPeanoBloom, and_true]
                  intro «🪻»
                  constructor
                  · intro h4
                    have h5 := h3 k7
                    simp only [lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt, forall_const] at h5
                    rw [← h5, (show (k7 + (k5 + 1)) = ((k7 + k5) + 1) by ring), WithinPeanoBloom] at h4
                    exact h4
                  · intro h4
                    rw [h4]
                    clear «🪻» h4
                    have h5 := h3 k7
                    simp only [lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt, forall_const] at h5
                    rw [← h5, (show (k7 + (k5 + 1)) = ((k7 + k5) + 1) by ring), WithinPeanoBloom]

theorem SymmetricSameBloomsWithin («🪻0» «🪻1» : «🌸»)
  (h2 : SameBloomsWithin «🪻0» «🪻1») : SameBloomsWithin «🪻1» «🪻0» := by
  rw [SameBloomsWithin] at *
  intro «🪻»
  exact iff_comm.mp (h2 «🪻»)

theorem TransitiveSubBloomButNotEqual («🪻0» «🪻1» «🪻2» : «🌸») (h0 : SubBloom «🪻0» «🪻1») (h1 : SubBloom «🪻1» «🪻2»)
  (h2 : ¬«🪻1» = «🪻2») : ¬«🪻0» = «🪻2» := by
  by_contra h3
  rw [h3] at h0
  have h4 := MutualSubBloomsEqual «🪻1» «🪻2»
  simp only [h1, h0, and_self, h2, iff_false, not_true_eq_false] at h4

theorem ExistsUniqueLiftBloomToLevel («🪻0» «🪻L» : «🌸») (h0 : SubBloom (Level «🪻0») «🪻L») :
  ∃! («🪻» : «🌸»), (SameBloomsWithin «🪻0» «🪻» ∧ Level «🪻» = «🪻L») := by
  cases Classical.em ((Level «🪻0») = «🪻L») with
  | inl h1 =>
    use «🪻0»
    simp only [and_imp]
    constructor
    · simp only [SameBloomsWithinSelf, h1, and_self]
    · intro «🪻» h2 h3
      rw [← BloomDefinedByLevelAndWhatIsWithin]
      simp only [h2, SymmetricSameBloomsWithin, h3, h1, and_self]
  | inr h1 =>
    use PropSubBloom (λ («🪻» : «🌸») ↦ Within «🪻» «🪻0») (BloomOfSmallerLevels «🪻L»)
    simp only [and_imp]
    constructor
    · constructor
      · rw [SameBloomsWithin]
        intro «🪻»
        rw [WithinPropSubBloom, BloomOfSmallerLevelsWithin]
        simp only [ne_eq, iff_self_and]
        intro h2
        have h3 := LevelOfWithinSubBloomLevel _ _ h2
        have h4 := TransitiveSubBloom _ _ _ h3 h0
        simp only [true_and, ne_eq, h4]
        exact TransitiveSubBloomButNotEqual _ _ _ h3 h0 h1
      · rw [LevelOfPropSubBloom, BloomOfSmallerLevelsLevel]
    · intro «🪻» h2 h3
      rw [← BloomDefinedByLevelAndWhatIsWithin]
      constructor
      · rw [SameBloomsWithin]
        intro «🪻1»
        rw[WithinPropSubBloom, BloomOfSmallerLevelsWithin]
        rw [SameBloomsWithin] at h2
        simp only [ne_eq, iff_self_and, h2]
        intro h4
        constructor
        · rw [(h2 _).symm] at h4
          have h5 := LevelOfWithinSubBloomLevel _ _ h4
          exact TransitiveSubBloom _ _ _ h5 h0
        · rw [← (h2 _)] at h4
          have h5 := LevelOfWithinSubBloomLevel _ _ h4
          exact TransitiveSubBloomButNotEqual _ _ _ h5 h0 h1
      · rw [LevelOfPropSubBloom, BloomOfSmallerLevelsLevel]
        exact h3
