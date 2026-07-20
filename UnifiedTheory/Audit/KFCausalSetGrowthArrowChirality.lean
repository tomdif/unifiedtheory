/-
  Audit/KFCausalSetGrowthArrowChirality.lean

  THE MAXIMAL-BIRTH ARROW AS A CHIRALITY SOURCE

  Static causal orders and the vacuum spectator action are reflection fixed,
  so they cannot select a member of the two-element chirality orbit.  A
  sequential-growth edge contains strictly more structure: it distinguishes a
  newborn maximal event.  At that event the inclusive future contains only
  the event itself, whereas the inclusive past also contains its precursor.

  This file tests whether that process-level asymmetry supplies the missing
  clock orientation.  The answer is conditional but sharper than the static
  no-go: every non-gregarious maximal birth has a strictly positive,
  order-dual-odd geometric source and, under the standard phase response,
  selects the `-i`, `Xi=+1` projective branch.  A gregarious birth has source
  zero, so the all-antichain trajectory remains an exact exceptional sector
  rather than being hidden.  A conjugate response is equally reflection
  covariant, isolating one residual Z2 coupling sign.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalSetFutureFrequencyHandedness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetGrowthArrowChirality

noncomputable section

open scoped BigOperators ComplexConjugate
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetTransitionEdges
open UnifiedTheory.Audit.KFCausalSetGeometricVolumeAction
open UnifiedTheory.Audit.KFCausalSetGeometricOrientationDynamics
open UnifiedTheory.Audit.KFCausalSetRelationalChiralitySelection
open UnifiedTheory.Audit.KFCausalSetBellCausality
open UnifiedTheory.Audit.KFCausalSetChiralGrowth
open UnifiedTheory.Audit.KFCausalSetChiralityGenerationNoGo
open UnifiedTheory.Audit.KFCausalSetFutureFrequencyHandedness

/-! ## 1. Exact geometry of the newborn maximal event -/

/-- Rational precursor population, written in the same incidence-counting
language as the geometric volume profile. -/
def precursorPopulationQ {n : ℕ} {parent : CardinalCausalOrder n}
    (past : CausalPastSet parent) : ℚ :=
  ∑ i : Fin n, if past.mem i = true then 1 else 0

/-- A newborn maximal event has no old event in its causal future. -/
theorem precursorExtension_newborn_futureVolumeQ {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent) :
    causalFutureVolumeQ (precursorOneElementExtension parent past)
        (Fin.last n) = 1 := by
  unfold causalFutureVolumeQ precursorOneElementExtension
  rw [Fin.sum_univ_castSucc]
  simp [precursorExtensionRel]

/-- Its inclusive past consists of itself plus exactly the precursor. -/
theorem precursorExtension_newborn_pastVolumeQ {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent) :
    causalPastVolumeQ (precursorOneElementExtension parent past)
        (Fin.last n) = 1 + precursorPopulationQ past := by
  unfold causalPastVolumeQ precursorPopulationQ
  rw [Fin.sum_univ_castSucc]
  simp [precursorOneElementExtension, precursorExtensionRel]
  ring

/-- Process-level orientation source carried by a maximal birth. -/
def maximalBirthOrientationSourceQ {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent) : ℚ :=
  causalOrientationDensityQ (precursorOneElementExtension parent past)
    (Fin.last n)

/-- Exact source formula.  Only the precursor population supplies the
past/future asymmetry; the denominator is the total child incidence volume. -/
theorem maximalBirthOrientationSourceQ_formula {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent) :
    maximalBirthOrientationSourceQ parent past =
      precursorPopulationQ past /
        (2 * totalCausalPastVolumeQ
          (precursorOneElementExtension parent past)) := by
  unfold maximalBirthOrientationSourceQ causalOrientationDensityQ
    normalizedCausalPastVolumeDensityQ
    normalizedCausalFutureVolumeDensityQ
  rw [precursorExtension_newborn_pastVolumeQ,
    precursorExtension_newborn_futureVolumeQ]
  ring

/-! ## 2. Positivity and the exact exceptional sector -/

theorem precursorPopulationQ_nonneg {n : ℕ}
    {parent : CardinalCausalOrder n} (past : CausalPastSet parent) :
    0 ≤ precursorPopulationQ past := by
  unfold precursorPopulationQ
  positivity

/-- Any causally linked birth has strictly positive precursor population. -/
theorem precursorPopulationQ_pos_of_mem {n : ℕ}
    {parent : CardinalCausalOrder n} (past : CausalPastSet parent)
    {ancestor : Fin n} (hAncestor : past.mem ancestor = true) :
    0 < precursorPopulationQ past := by
  unfold precursorPopulationQ
  have hTerm : (0 : ℚ) <
      (if past.mem ancestor = true then 1 else 0) := by simp [hAncestor]
  have hOthers : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ (if past.mem i = true then (1 : ℚ) else 0) := by
    intro i _hi
    split <;> norm_num
  exact hTerm.trans_le
    (Finset.single_le_sum hOthers (Finset.mem_univ ancestor))

theorem precursorPopulationQ_eq_zero_iff_empty {n : ℕ}
    {parent : CardinalCausalOrder n} (past : CausalPastSet parent) :
    precursorPopulationQ past = 0 ↔
      past = emptyCausalPastSet parent := by
  constructor
  · intro hZero
    apply CausalPastSet.ext
    funext i
    change past.mem i = false
    cases hMem : past.mem i with
    | false => rfl
    | true =>
        have hPositive := precursorPopulationQ_pos_of_mem past hMem
        rw [hZero] at hPositive
        norm_num at hPositive
  · rintro rfl
    simp [precursorPopulationQ, emptyCausalPastSet]

theorem maximalBirthOrientationSourceQ_nonneg {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent) :
    0 ≤ maximalBirthOrientationSourceQ parent past := by
  rw [maximalBirthOrientationSourceQ_formula]
  exact div_nonneg (precursorPopulationQ_nonneg past)
    (mul_nonneg (by norm_num)
      (le_of_lt (totalCausalPastVolumeQ_pos
        (precursorOneElementExtension parent past) (Fin.last n))))

theorem maximalBirthOrientationSourceQ_pos_of_mem {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent)
    {ancestor : Fin n} (hAncestor : past.mem ancestor = true) :
    0 < maximalBirthOrientationSourceQ parent past := by
  rw [maximalBirthOrientationSourceQ_formula]
  exact div_pos (precursorPopulationQ_pos_of_mem past hAncestor)
    (mul_pos (by norm_num)
      (totalCausalPastVolumeQ_pos
        (precursorOneElementExtension parent past) (Fin.last n)))

@[simp]
theorem precursorPopulationQ_empty {n : ℕ}
    (parent : CardinalCausalOrder n) :
    precursorPopulationQ (emptyCausalPastSet parent) = 0 := by
  simp [precursorPopulationQ, emptyCausalPastSet]

@[simp]
theorem maximalBirthOrientationSourceQ_empty {n : ℕ}
    (parent : CardinalCausalOrder n) :
    maximalBirthOrientationSourceQ parent (emptyCausalPastSet parent) = 0 := by
  rw [maximalBirthOrientationSourceQ_formula,
    precursorPopulationQ_empty]
  simp

/-- The growth-arrow source vanishes exactly on a gregarious birth. -/
theorem maximalBirthOrientationSourceQ_eq_zero_iff_empty {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent) :
    maximalBirthOrientationSourceQ parent past = 0 ↔
      past = emptyCausalPastSet parent := by
  rw [maximalBirthOrientationSourceQ_formula]
  have hDenominator :
      (2 * totalCausalPastVolumeQ
        (precursorOneElementExtension parent past) : ℚ) ≠ 0 := by
    exact ne_of_gt (mul_pos (by norm_num)
      (totalCausalPastVolumeQ_pos
        (precursorOneElementExtension parent past) (Fin.last n)))
  rw [div_eq_zero_iff]
  simp [hDenominator, precursorPopulationQ_eq_zero_iff_empty]

theorem maximalBirthOrientationSourceQ_pos_iff_nonempty {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent) :
    0 < maximalBirthOrientationSourceQ parent past ↔
      past ≠ emptyCausalPastSet parent := by
  constructor
  · intro hPositive hEmpty
    subst past
    rw [maximalBirthOrientationSourceQ_empty] at hPositive
    norm_num at hPositive
  · intro hNonempty
    exact lt_of_le_of_ne (maximalBirthOrientationSourceQ_nonneg parent past)
      (fun hZero => hNonempty
        ((maximalBirthOrientationSourceQ_eq_zero_iff_empty parent past).mp
          hZero.symm))

/-! ## 3. Order reflection turns maximal growth into the opposite source -/

/-- Source seen after reversing every causal arrow in the child.  The
distinguished newborn is then minimal rather than maximal. -/
def reflectedMaximalBirthOrientationSourceQ {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent) : ℚ :=
  causalOrientationDensityQ
    (cardinalCausalOrderDual
      (precursorOneElementExtension parent past)) (Fin.last n)

theorem reflectedMaximalBirthOrientationSourceQ_eq_neg {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent) :
    reflectedMaximalBirthOrientationSourceQ parent past =
      -maximalBirthOrientationSourceQ parent past := by
  exact causalOrientationDensityQ_dual_odd
    (precursorOneElementExtension parent past) (Fin.last n)

theorem reflectedMaximalBirthOrientationSourceQ_neg_of_mem {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent)
    {ancestor : Fin n} (hAncestor : past.mem ancestor = true) :
    reflectedMaximalBirthOrientationSourceQ parent past < 0 := by
  rw [reflectedMaximalBirthOrientationSourceQ_eq_neg]
  exact neg_lt_zero.mpr
    (maximalBirthOrientationSourceQ_pos_of_mem parent past hAncestor)

/-! ## 4. The growth-arrow phase and projective sign -/

/-- The selected quarter-turn phase obtained directly from the oriented birth
source. -/
def maximalBirthSelectedPhase {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent) : ℂ :=
  relationalChiralityPhase
    (maximalBirthOrientationSourceQ parent past)

theorem maximalBirthSelectedPhase_eq_negI_of_mem {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent)
    {ancestor : Fin n} (hAncestor : past.mem ancestor = true) :
    maximalBirthSelectedPhase parent past = -Complex.I := by
  unfold maximalBirthSelectedPhase
  apply relationalChiralityPhase_of_pos
  exact_mod_cast maximalBirthOrientationSourceQ_pos_of_mem
    parent past hAncestor

/-- The reflected minimal-birth source selects the conjugate quarter turn. -/
theorem reflectedMaximalBirthSelectedPhase_eq_posI_of_mem {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent)
    {ancestor : Fin n} (hAncestor : past.mem ancestor = true) :
    relationalChiralityPhase
        (reflectedMaximalBirthOrientationSourceQ parent past) =
      Complex.I := by
  apply relationalChiralityPhase_of_neg
  exact_mod_cast reflectedMaximalBirthOrientationSourceQ_neg_of_mem
    parent past hAncestor

/-! ## 5. A residual response-sign theorem -/

/-- Reflection covariance required of a microscopic phase response away from
the achiral point. -/
def IsReflectionCovariantPhaseResponse (response : ℝ → ℂ) : Prop :=
  ∀ source : ℝ, source ≠ 0 →
    response (-source) = star (response source)

theorem relationalChiralityPhase_reflectionCovariant :
    IsReflectionCovariantPhaseResponse relationalChiralityPhase :=
  relationalChiralityPhase_reflection

/-- Conjugate response law.  It obeys the same reflection covariance while
reversing which quarter turn is attached to a positive source. -/
def conjugateRelationalChiralityPhase (source : ℝ) : ℂ :=
  star (relationalChiralityPhase source)

theorem conjugateRelationalChiralityPhase_reflectionCovariant :
    IsReflectionCovariantPhaseResponse
      conjugateRelationalChiralityPhase := by
  intro source hNonzero
  unfold conjugateRelationalChiralityPhase
  rw [relationalChiralityPhase_reflection source hNonzero]

theorem conjugateRelationalChiralityPhase_of_pos
    {source : ℝ} (hPositive : 0 < source) :
    conjugateRelationalChiralityPhase source = Complex.I := by
  unfold conjugateRelationalChiralityPhase
  rw [relationalChiralityPhase_of_pos hPositive]
  simp

/-- **Residual coupling-sign degeneracy.**  The maximal-birth arrow generates
a nonzero reflection-odd source, but reflection covariance alone admits two
opposite phase responses to it.  The remaining microscopic datum is therefore
the sign of the source-to-clock coupling, not a boundary value of `Xi`. -/
theorem maximalBirthArrow_response_sign_not_fixed_by_reflection {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent)
    {ancestor : Fin n} (hAncestor : past.mem ancestor = true) :
    IsReflectionCovariantPhaseResponse relationalChiralityPhase
      ∧ IsReflectionCovariantPhaseResponse
          conjugateRelationalChiralityPhase
      ∧ relationalChiralityPhase
          (maximalBirthOrientationSourceQ parent past) = -Complex.I
      ∧ conjugateRelationalChiralityPhase
          (maximalBirthOrientationSourceQ parent past) = Complex.I
      ∧ relationalChiralityPhase
          (maximalBirthOrientationSourceQ parent past) ≠
        conjugateRelationalChiralityPhase
          (maximalBirthOrientationSourceQ parent past) := by
  have hPositiveQ :=
    maximalBirthOrientationSourceQ_pos_of_mem parent past hAncestor
  have hPositiveR :
      (0 : ℝ) < maximalBirthOrientationSourceQ parent past := by
    exact_mod_cast hPositiveQ
  refine ⟨relationalChiralityPhase_reflectionCovariant,
    conjugateRelationalChiralityPhase_reflectionCovariant,
    relationalChiralityPhase_of_pos hPositiveR,
    conjugateRelationalChiralityPhase_of_pos hPositiveR, ?_⟩
  rw [relationalChiralityPhase_of_pos hPositiveR,
    conjugateRelationalChiralityPhase_of_pos hPositiveR]
  intro hEqual
  have hImaginary := congrArg Complex.im hEqual
  norm_num at hImaginary

/-- Partial selector that exposes the gregarious zero rather than assigning it
an arbitrary chirality. -/
def maximalBirthSelectedPhase? {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent) :
    Option ℂ :=
  if maximalBirthOrientationSourceQ parent past = 0 then none
  else some (maximalBirthSelectedPhase parent past)

@[simp]
theorem maximalBirthSelectedPhase?_empty {n : ℕ}
    (parent : CardinalCausalOrder n) :
    maximalBirthSelectedPhase? parent (emptyCausalPastSet parent) = none := by
  simp [maximalBirthSelectedPhase?, maximalBirthOrientationSourceQ_empty]

theorem maximalBirthSelectedPhase?_eq_some_negI_of_mem {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent)
    {ancestor : Fin n} (hAncestor : past.mem ancestor = true) :
    maximalBirthSelectedPhase? parent past = some (-Complex.I) := by
  have hNonzero : maximalBirthOrientationSourceQ parent past ≠ 0 :=
    ne_of_gt (maximalBirthOrientationSourceQ_pos_of_mem
      parent past hAncestor)
  simp [maximalBirthSelectedPhase?, hNonzero,
    maximalBirthSelectedPhase_eq_negI_of_mem parent past hAncestor]

/-- Chirality slot selected by the oriented maximal-birth source. -/
def maximalBirthSelectedSector {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent) : Fin 2 :=
  relationalChiralitySector
    (maximalBirthOrientationSourceQ parent past)

theorem maximalBirthSelectedSector_eq_one_of_mem {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent)
    {ancestor : Fin n} (hAncestor : past.mem ancestor = true) :
    maximalBirthSelectedSector parent past = 1 := by
  unfold maximalBirthSelectedSector relationalChiralitySector
  simp [show (0 : ℝ) < maximalBirthOrientationSourceQ parent past by
    exact_mod_cast maximalBirthOrientationSourceQ_pos_of_mem
      parent past hAncestor]

/-- The standard response to a linked maximal-birth source satisfies the exact
finite clock/birth coefficient contract. -/
theorem maximalBirthArrow_satisfies_clockBirth_of_mem {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent)
    {ancestor : Fin n} (hAncestor : past.mem ancestor = true) :
    SatisfiesClockBirthIdentification
      (causalPositiveOrientationEvolution (Real.pi / 2))
      (chiralMultiplicativeSignatureWeight
        (maximalBirthSelectedSector parent past)) := by
  rw [maximalBirthSelectedSector_eq_one_of_mem parent past hAncestor]
  exact positiveClockBirthIdentification

/-- Complete normalized growth law seeded by one oriented maximal birth. -/
def maximalBirthSelectedGrowthLaw {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent) :
    RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch :=
  chiralCausalSetGrowthLaw (maximalBirthSelectedSector parent past)

theorem maximalBirthSelectedGrowthLaw_eq_positive_of_mem {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent)
    {ancestor : Fin n} (hAncestor : past.mem ancestor = true) :
    maximalBirthSelectedGrowthLaw parent past =
      causalPositiveOrientationGrowthLaw := by
  unfold maximalBirthSelectedGrowthLaw causalPositiveOrientationGrowthLaw
  rw [maximalBirthSelectedSector_eq_one_of_mem parent past hAncestor]

/-- Once any non-gregarious maximal birth supplies the sign, the existing
projective theorem transports `Xi=+1` through every later refinement. -/
theorem maximalBirthArrow_selects_and_transports_left_sign {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent)
    {ancestor : Fin n} (hAncestor : past.mem ancestor = true)
    (steps : ℕ) :
    maximalBirthSelectedPhase? parent past = some (-Complex.I)
      ∧ inducedCylinderChiralitySign
          (maximalBirthSelectedGrowthLaw parent past)
          (chiralRankTwoCoarseGraining.refineBy steps) = 1 := by
  constructor
  · exact maximalBirthSelectedPhase?_eq_some_negI_of_mem
      parent past hAncestor
  · rw [maximalBirthSelectedGrowthLaw_eq_positive_of_mem
      parent past hAncestor]
    exact causalPositiveOrientationGrowthLaw_sign_transport steps

/-! ## 6. Canonical first linked birth -/

/-- The first causally connected alternative: a one-event parent followed by
a full-precursor maximal birth. -/
def firstLinkedParent : CardinalCausalOrder 1 :=
  cardinalCausalAntichain 1

def firstLinkedPast : CausalPastSet firstLinkedParent :=
  fullCausalPastSet firstLinkedParent

theorem firstLinkedPast_mem : firstLinkedPast.mem 0 = true := by
  rfl

/-- The first full-precursor extension is exactly the two-event chain in the
repository's canonical labeling. -/
theorem firstLinkedChild_eq_chainTwo :
    precursorOneElementExtension firstLinkedParent firstLinkedPast =
      cardinalCausalChainTwo := by
  apply CardinalCausalOrder.ext
  decide

/-- Exact magnitude of the first growth-arrow source.  It is the geometric
chain-two interior value, not a pure endpoint. -/
theorem firstLinkedBirth_source_exact :
    maximalBirthOrientationSourceQ firstLinkedParent firstLinkedPast =
      (1 : ℚ) / 6 := by
  rw [maximalBirthOrientationSourceQ_formula]
  have hPopulation : precursorPopulationQ firstLinkedPast = 1 := by
    norm_num [firstLinkedPast, precursorPopulationQ, fullCausalPastSet]
  rw [hPopulation, firstLinkedChild_eq_chainTwo,
    chainTwo_totalCausalPastVolumeQ]
  norm_num

/-- The process-generated source is already nonzero at the first linked
alternative. -/
theorem firstLinkedBirth_source_pos :
    0 < maximalBirthOrientationSourceQ firstLinkedParent firstLinkedPast :=
  maximalBirthOrientationSourceQ_pos_of_mem
    firstLinkedParent firstLinkedPast firstLinkedPast_mem

/-- Capstone for what sequential growth now does and does not determine.  The
future-maximal birth generates a positive source, the selected response seeds
and transports `Xi=+1`, and the reflected child gives the opposite source.
However, the two covariant response laws above prove that choosing the sign of
the phase response remains one microscopic coupling choice. -/
theorem firstLinkedBirth_growth_arrow_frontier :
    0 < maximalBirthOrientationSourceQ firstLinkedParent firstLinkedPast
      ∧ reflectedMaximalBirthOrientationSourceQ
          firstLinkedParent firstLinkedPast < 0
      ∧ maximalBirthSelectedPhase?
          firstLinkedParent firstLinkedPast = some (-Complex.I)
      ∧ SatisfiesClockBirthIdentification
          (causalPositiveOrientationEvolution (Real.pi / 2))
          (chiralMultiplicativeSignatureWeight
            (maximalBirthSelectedSector
              firstLinkedParent firstLinkedPast))
      ∧ (∀ steps : ℕ,
          inducedCylinderChiralitySign
              (maximalBirthSelectedGrowthLaw
                firstLinkedParent firstLinkedPast)
              (chiralRankTwoCoarseGraining.refineBy steps) = 1)
      ∧ IsReflectionCovariantPhaseResponse relationalChiralityPhase
      ∧ IsReflectionCovariantPhaseResponse
          conjugateRelationalChiralityPhase := by
  refine ⟨firstLinkedBirth_source_pos,
    reflectedMaximalBirthOrientationSourceQ_neg_of_mem
      firstLinkedParent firstLinkedPast firstLinkedPast_mem,
    maximalBirthSelectedPhase?_eq_some_negI_of_mem
      firstLinkedParent firstLinkedPast firstLinkedPast_mem,
    maximalBirthArrow_satisfies_clockBirth_of_mem
      firstLinkedParent firstLinkedPast firstLinkedPast_mem, ?_,
    relationalChiralityPhase_reflectionCovariant,
    conjugateRelationalChiralityPhase_reflectionCovariant⟩
  intro steps
  exact (maximalBirthArrow_selects_and_transports_left_sign
    firstLinkedParent firstLinkedPast firstLinkedPast_mem steps).2

#print axioms precursorExtension_newborn_futureVolumeQ
#print axioms precursorExtension_newborn_pastVolumeQ
#print axioms maximalBirthOrientationSourceQ_formula
#print axioms maximalBirthOrientationSourceQ_eq_zero_iff_empty
#print axioms maximalBirthOrientationSourceQ_pos_iff_nonempty
#print axioms maximalBirthOrientationSourceQ_pos_of_mem
#print axioms reflectedMaximalBirthOrientationSourceQ_eq_neg
#print axioms reflectedMaximalBirthSelectedPhase_eq_posI_of_mem
#print axioms maximalBirthArrow_response_sign_not_fixed_by_reflection
#print axioms maximalBirthSelectedPhase_eq_negI_of_mem
#print axioms maximalBirthArrow_satisfies_clockBirth_of_mem
#print axioms maximalBirthArrow_selects_and_transports_left_sign
#print axioms firstLinkedChild_eq_chainTwo
#print axioms firstLinkedBirth_source_exact
#print axioms firstLinkedBirth_growth_arrow_frontier

end

end UnifiedTheory.Audit.KFCausalSetGrowthArrowChirality
