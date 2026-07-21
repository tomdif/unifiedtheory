/-
  Audit/KFCausalSetMicroscopicResponseLaw.lean

  RIGIDITY OF THE MICROSCOPIC SOURCE-TO-PHASE RESPONSE

  This file closes the finite response-classification problem at an explicit
  theorem boundary.  In the smallest local real ansatz, an energy depending
  affinely on an order-odd birth source and an orientation coordinate is
  forced by achiral neutrality and combined reflection covariance to be the
  single bilinear interaction

                         E_g(Xi,y) = g Xi y.

  A nonzero effective drive has a unique auxiliary minimum on the full
  strongly-positive interval |y| <= 1/2.  Its two possible signs select the
  two pure quarter-turn endpoints.  This is not geometric attainment: the
  causal-volume coordinate obeys the stronger uniform bound |y_geom| < 1/4
  at every finite rank, so it remains strictly above the boundary energy and
  cannot approach either endpoint.  Independently, elementary Born
  normalization, relation-
  complement symmetry, the ancestor gauge, and independent composition
  classify every signature law as exactly one of the two chiral characters.
  Complex conjugation identifies those two complete cylinder theories.

  The theorem does not derive the affine-local ansatz or elementary relation-
  complement symmetry from continuum dynamics.  It proves that, once those
  finite microscopic locality/symmetry conditions are imposed, no further
  response function or observable Z2 parameter remains.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalSetConjugationCompleteness
import UnifiedTheory.Audit.KFCausalSetMicroscopicSpectatorAction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetMicroscopicResponseLaw

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open UnifiedTheory.Audit.KFOrientationGrowthDecoherence
open UnifiedTheory.Audit.KFOrientationHigherRankDecoherence
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetTransitionEdges
open UnifiedTheory.Audit.KFCausalSetBellCausality
open UnifiedTheory.Audit.KFCausalSetChiralGrowth
open UnifiedTheory.Audit.KFCausalSetChiralDynamics
open UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw
open UnifiedTheory.Audit.KFCausalSetMultiplicityCorrectedRunning
open UnifiedTheory.Audit.KFCausalSetMicroscopicSpectatorAction
open UnifiedTheory.Audit.KFCausalSetChiralityGenerationNoGo
open UnifiedTheory.Audit.KFCausalSetFutureFrequencyHandedness
open UnifiedTheory.Audit.KFCausalSetGrowthArrowChirality
open UnifiedTheory.Audit.KFCausalSetConjugationCompleteness
open UnifiedTheory.Audit.KFCausalSetGeometricOrientationDynamics
open UnifiedTheory.Audit.KFCausalSetGeometricOrientationAsymptotics

/-! ## 1. The unique local reflection-even source interaction -/

/-- The most general real function affine in both a pseudoscalar source and
an orientation coordinate. -/
def affineBilinearOrientationEnergy
    (constant sourceBias orientationBias coupling source orientation : ℝ) : ℝ :=
  constant + sourceBias * source + orientationBias * orientation +
    coupling * source * orientation

/-- Simultaneous reversal of source and orientation is the finite reflection
law appropriate to a pseudoscalar coupling. -/
def IsCombinedReflectionInvariant
    (energy : ℝ → ℝ → ℝ) : Prop :=
  ∀ source orientation,
    energy (-source) (-orientation) = energy source orientation

/-- With no order-odd source, the energy must not prefer an orientation. -/
def IsAchiralNeutral (energy : ℝ → ℝ → ℝ) : Prop :=
  ∀ orientation, energy 0 orientation = 0

/-- Reflection invariance removes both terms that are odd in only one of the
two variables. -/
theorem affineBilinear_reflectionInvariant_iff
    (constant sourceBias orientationBias coupling : ℝ) :
    IsCombinedReflectionInvariant
        (affineBilinearOrientationEnergy constant sourceBias
          orientationBias coupling) ↔
      sourceBias = 0 ∧ orientationBias = 0 := by
  constructor
  · intro hReflection
    have hSource := hReflection 1 0
    have hOrientation := hReflection 0 1
    constructor
    · norm_num [affineBilinearOrientationEnergy] at hSource
      linarith
    · norm_num [affineBilinearOrientationEnergy] at hOrientation
      linarith
  · rintro ⟨rfl, rfl⟩ source orientation
    simp [affineBilinearOrientationEnergy]

/-- Achiral neutrality removes the constant and orientation-only terms. -/
theorem affineBilinear_achiralNeutral_iff
    (constant sourceBias orientationBias coupling : ℝ) :
    IsAchiralNeutral
        (affineBilinearOrientationEnergy constant sourceBias
          orientationBias coupling) ↔
      constant = 0 ∧ orientationBias = 0 := by
  constructor
  · intro hNeutral
    have hZero := hNeutral 0
    have hOne := hNeutral 1
    constructor
    · simpa [affineBilinearOrientationEnergy] using hZero
    · norm_num [affineBilinearOrientationEnergy] at hZero hOne
      linarith
  · rintro ⟨rfl, rfl⟩ orientation
    simp [affineBilinearOrientationEnergy]

/-- The surviving interaction after the two structural laws. -/
def bilinearOrientationEnergy
    (coupling source orientation : ℝ) : ℝ :=
  coupling * source * orientation

theorem bilinearOrientationEnergy_reflection
    (coupling source orientation : ℝ) :
    bilinearOrientationEnergy coupling (-source) (-orientation) =
      bilinearOrientationEnergy coupling source orientation := by
  simp [bilinearOrientationEnergy]

theorem bilinearOrientationEnergy_achiral
    (coupling orientation : ℝ) :
    bilinearOrientationEnergy coupling 0 orientation = 0 := by
  simp [bilinearOrientationEnergy]

/-- **Local interaction rigidity.**  An affine-bilinear response satisfying
combined reflection invariance and no-source neutrality contains exactly one
real coefficient and is identically `g Xi y`. -/
theorem affineBilinear_localInteraction_unique
    (constant sourceBias orientationBias coupling : ℝ)
    (hReflection : IsCombinedReflectionInvariant
      (affineBilinearOrientationEnergy constant sourceBias
        orientationBias coupling))
    (hNeutral : IsAchiralNeutral
      (affineBilinearOrientationEnergy constant sourceBias
        orientationBias coupling)) :
    constant = 0 ∧ sourceBias = 0 ∧ orientationBias = 0 ∧
      (∀ source orientation,
        affineBilinearOrientationEnergy constant sourceBias
            orientationBias coupling source orientation =
          bilinearOrientationEnergy coupling source orientation) := by
  obtain ⟨hSourceBias, hOrientationBias⟩ :=
    (affineBilinear_reflectionInvariant_iff
      constant sourceBias orientationBias coupling).mp hReflection
  obtain ⟨hConstant, _⟩ :=
    (affineBilinear_achiralNeutral_iff
      constant sourceBias orientationBias coupling).mp hNeutral
  refine ⟨hConstant, hSourceBias, hOrientationBias, ?_⟩
  intro source orientation
  simp [affineBilinearOrientationEnergy, bilinearOrientationEnergy,
    hConstant, hSourceBias, hOrientationBias]

/-! ## 2. Nonzero drive uniquely selects a pure auxiliary endpoint -/

/-- A selected orientation is the unique minimum of an energy on the abstract
full strong-positivity interval.  This definition does not assert that the
selected value lies in the image of the finite causal-volume geometry. -/
def IsUniqueAdmissibleMinimum
    (energy : ℝ → ℝ) (selected : ℝ) : Prop :=
  IsAdmissibleOrientationParameter selected ∧
    ∀ orientation, IsAdmissibleOrientationParameter orientation →
      energy selected ≤ energy orientation ∧
        (energy orientation = energy selected ↔ orientation = selected)

/-- A positive effective coupling uniquely selects `y=-1/2`. -/
theorem bilinear_positiveDrive_uniqueMinimum
    {coupling source : ℝ} (hDrive : 0 < coupling * source) :
    IsUniqueAdmissibleMinimum
      (bilinearOrientationEnergy coupling source) (-1 / 2) := by
  constructor
  · norm_num [IsAdmissibleOrientationParameter]
  · intro orientation hAdmissible
    have hLower : -(1 / 2 : ℝ) ≤ orientation :=
      (abs_le.mp hAdmissible).1
    unfold bilinearOrientationEnergy
    constructor
    · nlinarith
    · constructor
      · intro hEqual
        nlinarith
      · rintro rfl
        rfl

/-- A negative effective coupling uniquely selects `y=+1/2`. -/
theorem bilinear_negativeDrive_uniqueMinimum
    {coupling source : ℝ} (hDrive : coupling * source < 0) :
    IsUniqueAdmissibleMinimum
      (bilinearOrientationEnergy coupling source) (1 / 2) := by
  constructor
  · norm_num [IsAdmissibleOrientationParameter]
  · intro orientation hAdmissible
    have hUpper : orientation ≤ (1 / 2 : ℝ) :=
      (abs_le.mp hAdmissible).2
    unfold bilinearOrientationEnergy
    constructor
    · nlinarith
    · constructor
      · intro hEqual
        nlinarith
      · rintro rfl
        rfl

/-- At zero effective drive there is no phase response.  This makes the
gregarious/all-antichain exception explicit. -/
def bilinearSelectedPhase? (coupling source : ℝ) : Option ℂ :=
  if 0 < coupling * source then some (-Complex.I)
  else if coupling * source < 0 then some Complex.I
  else none

theorem bilinearSelectedPhase?_zeroSource (coupling : ℝ) :
    bilinearSelectedPhase? coupling 0 = none := by
  simp [bilinearSelectedPhase?]

theorem bilinearSelectedPhase?_reflection
    {coupling source : ℝ} (hCoupling : coupling ≠ 0)
    (hSource : source ≠ 0) :
    bilinearSelectedPhase? coupling (-source) =
      (bilinearSelectedPhase? coupling source).map star := by
  have hDrive : coupling * source ≠ 0 := mul_ne_zero hCoupling hSource
  rcases lt_or_gt_of_ne hDrive with hNegative | hPositive
  · have hReflected : 0 < coupling * -source := by nlinarith
    simp [bilinearSelectedPhase?, hNegative,
      not_lt_of_ge (le_of_lt hNegative)]
  · have hReflected : coupling * -source < 0 := by nlinarith
    simp [bilinearSelectedPhase?, hPositive,
      not_lt_of_ge (le_of_lt hPositive)]

/-! ## 3. Classification of every balanced compositional edge law -/

/-- The exact finite microscopic assumptions used in the signature-law
classification. -/
structure IsBalancedCompositionalSignatureLaw
    (weight : ℕ → ℕ → ℂ) : Prop where
  multiplicative : IsMultiplicativeSignatureWeight weight
  ancestorGauge : weight 1 0 = 1
  elementaryPartition : 1 + weight 0 1 ≠ 0
  elementaryBornNormalized :
    elementaryEmptyBornWeight (weight 0 1) +
      elementaryFullBornWeight (weight 0 1) = 1
  relationComplementSymmetric :
    ElementaryRelationComplementSymmetric (weight 0 1)

/-- The two chiral signature characters are distinguishable before taking the
global conjugation quotient. -/
theorem chiralMultiplicativeSignatureWeight_injective :
    Function.Injective chiralMultiplicativeSignatureWeight := by
  intro first second hEqual
  fin_cases first <;> fin_cases second
  · rfl
  · have hPhase := congrFun (congrFun hEqual 0) 1
    have hImaginary := congrArg Complex.im hPhase
    norm_num [chiralMultiplicativeSignatureWeight,
      multiplicativeSignatureWeight, chiralMaximalEventPhase] at hImaginary
  · have hPhase := congrFun (congrFun hEqual 0) 1
    have hImaginary := congrArg Complex.im hPhase
    norm_num [chiralMultiplicativeSignatureWeight,
      multiplicativeSignatureWeight, chiralMaximalEventPhase] at hImaginary
  · rfl

/-- **Balanced character classification.**  There are exactly two complete
independently compositional signature laws, not a larger response family. -/
theorem balancedCompositionalSignatureLaw_classification
    (weight : ℕ → ℕ → ℂ)
    (hLaw : IsBalancedCompositionalSignatureLaw weight) :
    ∃! chirality : Fin 2,
      weight = chiralMultiplicativeSignatureWeight chirality := by
  have hPhase : weight 0 1 = Complex.I ∨
      weight 0 1 = -Complex.I :=
    elementary_symmetry_derives_chiral_phase
      (weight 0 1) hLaw.elementaryPartition
      hLaw.elementaryBornNormalized hLaw.relationComplementSymmetric
  rcases hPhase with hPositive | hNegative
  · have hWeight :
        weight = chiralMultiplicativeSignatureWeight 0 := by
      apply chiralMultiplicativeSignatureWeight_unique 0 weight
        hLaw.multiplicative hLaw.ancestorGauge
      simpa [chiralMaximalEventPhase] using hPositive
    refine ⟨0, hWeight, ?_⟩
    intro chirality hOther
    apply chiralMultiplicativeSignatureWeight_injective
    exact hOther.symm.trans hWeight
  · have hWeight :
        weight = chiralMultiplicativeSignatureWeight 1 := by
      apply chiralMultiplicativeSignatureWeight_unique 1 weight
        hLaw.multiplicative hLaw.ancestorGauge
      simpa [chiralMaximalEventPhase] using hNegative
    refine ⟨1, hWeight, ?_⟩
    intro chirality hOther
    apply chiralMultiplicativeSignatureWeight_injective
    exact hOther.symm.trans hWeight

/-- Every pair of admissible laws is either identical or related pointwise by
complex conjugation. -/
theorem balancedCompositionalSignatureLaws_equal_or_conjugate
    (first second : ℕ → ℕ → ℂ)
    (hFirst : IsBalancedCompositionalSignatureLaw first)
    (hSecond : IsBalancedCompositionalSignatureLaw second) :
    first = second ∨
      ∀ omega maximal, second omega maximal = star (first omega maximal) := by
  obtain ⟨firstChirality, hFirstWeight, _⟩ :=
    balancedCompositionalSignatureLaw_classification first hFirst
  obtain ⟨secondChirality, hSecondWeight, _⟩ :=
    balancedCompositionalSignatureLaw_classification second hSecond
  subst first
  subst second
  fin_cases firstChirality <;> fin_cases secondChirality
  · exact Or.inl rfl
  · right
    intro omega maximal
    simpa [reflectedMicroscopicChirality] using
      (chiralMultiplicativeSignatureWeight_reflection
        (0 : Fin 2) omega maximal).symm
  · right
    intro omega maximal
    simpa [reflectedMicroscopicChirality] using
      (chiralMultiplicativeSignatureWeight_reflection
        (1 : Fin 2) omega maximal).symm
  · exact Or.inl rfl

/-! ## 4. Balanced purity, sign matching, and its variational encoding -/

/-- The chirality whose orientation endpoint minimizes a given nonzero
effective drive. -/
def driveSelectedChirality (coupling source : ℝ) : Fin 2 :=
  if 0 < coupling * source then 1 else 0

theorem chiralBoundaryOrientationParameter_injective :
    Function.Injective chiralBoundaryOrientationParameter := by
  intro first second hEqual
  fin_cases first <;> fin_cases second
  · rfl
  · norm_num [chiralBoundaryOrientationParameter,
      chiralMaximalEventPhase] at hEqual
  · norm_num [chiralBoundaryOrientationParameter,
      chiralMaximalEventPhase] at hEqual
  · rfl

/-- Each of the two chiral characters satisfies the exact elementary balance
and composition contract used in the classification. -/
theorem chiralMultiplicativeSignatureWeight_isBalancedCompositional
    (chirality : Fin 2) :
    IsBalancedCompositionalSignatureLaw
      (chiralMultiplicativeSignatureWeight chirality) := by
  constructor
  · exact chiralMultiplicativeSignatureWeight_isMultiplicative chirality
  · simp [chiralMultiplicativeSignatureWeight,
      multiplicativeSignatureWeight]
  · fin_cases chirality
    · intro hZero
      have hImaginary := congrArg Complex.im hZero
      norm_num [chiralMultiplicativeSignatureWeight,
        multiplicativeSignatureWeight, chiralMaximalEventPhase] at hImaginary
    · intro hZero
      have hImaginary := congrArg Complex.im hZero
      norm_num [chiralMultiplicativeSignatureWeight,
        multiplicativeSignatureWeight, chiralMaximalEventPhase] at hImaginary
  · fin_cases chirality <;>
      norm_num [elementaryEmptyBornWeight, elementaryFullBornWeight,
        chiralMultiplicativeSignatureWeight,
        multiplicativeSignatureWeight, chiralMaximalEventPhase,
        Complex.normSq_apply]
  · fin_cases chirality <;>
      norm_num [ElementaryRelationComplementSymmetric,
        elementaryEmptyBornWeight, elementaryFullBornWeight,
        chiralMultiplicativeSignatureWeight,
        multiplicativeSignatureWeight, chiralMaximalEventPhase,
        Complex.normSq_apply]

/-- The selected chiral endpoint is exactly the unique auxiliary variational
minimum whenever the effective drive is nonzero. -/
theorem driveSelectedChirality_uniqueMinimum
    {coupling source : ℝ} (hDrive : coupling * source ≠ 0) :
    IsUniqueAdmissibleMinimum
      (bilinearOrientationEnergy coupling source)
      (chiralBoundaryOrientationParameter
        (driveSelectedChirality coupling source)) := by
  rcases lt_or_gt_of_ne hDrive with hNegative | hPositive
  · have hNotPositive : ¬0 < coupling * source :=
      not_lt_of_ge (le_of_lt hNegative)
    simpa [driveSelectedChirality, hNotPositive,
      chiralBoundaryOrientationParameter, chiralMaximalEventPhase] using
      (bilinear_negativeDrive_uniqueMinimum hNegative)
  · simpa [driveSelectedChirality, hPositive,
      chiralBoundaryOrientationParameter, chiralMaximalEventPhase] using
      (bilinear_positiveDrive_uniqueMinimum hPositive)

/-- The piecewise sign response returns the elementary coefficient of the
drive-selected chiral character.  This is the explicit response rule; it is
not a consequence of geometric endpoint attainment. -/
theorem bilinearSelectedPhase?_eq_driveSelectedCharacter
    {coupling source : ℝ} (hDrive : coupling * source ≠ 0) :
    bilinearSelectedPhase? coupling source =
      some (chiralMaximalEventPhase
        (driveSelectedChirality coupling source)) := by
  rcases lt_or_gt_of_ne hDrive with hNegative | hPositive
  · have hNotPositive : ¬0 < coupling * source :=
      not_lt_of_ge (le_of_lt hNegative)
    simp [bilinearSelectedPhase?, driveSelectedChirality, hNegative,
      hNotPositive, chiralMaximalEventPhase]
  · simp [bilinearSelectedPhase?, driveSelectedChirality, hPositive,
      chiralMaximalEventPhase]

/-- A balanced character is sign-matched when its elementary phase is exactly
the output of the source-response rule. -/
def IsSignMatchedBalancedSignatureLaw
    (coupling source : ℝ) (weight : ℕ → ℕ → ℂ) : Prop :=
  IsBalancedCompositionalSignatureLaw weight ∧
    bilinearSelectedPhase? coupling source = some (weight 0 1)

/-- Balanced birth microphysics restricts the law to the pure conjugate pair;
the explicit sign response then chooses exactly one member.  No clock/birth
identification is a hypothesis of this finite theorem. -/
theorem signResponse_uniqueBalancedSignatureLaw
    {coupling source : ℝ} (hDrive : coupling * source ≠ 0) :
    ∃! weight : ℕ → ℕ → ℂ,
      IsSignMatchedBalancedSignatureLaw coupling source weight := by
  let selected := driveSelectedChirality coupling source
  refine ⟨chiralMultiplicativeSignatureWeight selected, ?_, ?_⟩
  · constructor
    · exact chiralMultiplicativeSignatureWeight_isBalancedCompositional selected
    · rw [bilinearSelectedPhase?_eq_driveSelectedCharacter hDrive]
      simp [selected, chiralMultiplicativeSignatureWeight,
        multiplicativeSignatureWeight]
  · intro weight hWeight
    obtain ⟨chirality, hCharacter, _⟩ :=
      balancedCompositionalSignatureLaw_classification weight hWeight.1
    have hMatch := hWeight.2
    rw [bilinearSelectedPhase?_eq_driveSelectedCharacter hDrive,
      hCharacter] at hMatch
    have hPhase : chiralMaximalEventPhase selected =
        chiralMaximalEventPhase chirality := by
      simpa [selected, chiralMultiplicativeSignatureWeight,
        multiplicativeSignatureWeight] using Option.some.inj hMatch
    have hChirality : selected = chirality := by
      apply chiralBoundaryOrientationParameter_injective
      simp [chiralBoundaryOrientationParameter, hPhase]
    simpa [hChirality] using hCharacter

/-- A balanced compositional law is variationally compatible when its pure
auxiliary endpoint is the unique minimum of the local source energy. -/
def IsVariationallySelectedBalancedSignatureLaw
    (coupling source : ℝ) (weight : ℕ → ℕ → ℂ) : Prop :=
  IsBalancedCompositionalSignatureLaw weight ∧
    ∃ chirality : Fin 2,
      weight = chiralMultiplicativeSignatureWeight chirality ∧
        IsUniqueAdmissibleMinimum
          (bilinearOrientationEnergy coupling source)
          (chiralBoundaryOrientationParameter chirality)

/-- **Variational response uniqueness.**  For every nonzero effective drive,
there is exactly one balanced compositional signature law whose endpoint is
the local energy minimum.  This theorem is the explicit bridge between the
energy classification and the edge-character classification. -/
theorem variationalResponse_uniqueBalancedSignatureLaw
    {coupling source : ℝ} (hDrive : coupling * source ≠ 0) :
    ∃! weight : ℕ → ℕ → ℂ,
      IsVariationallySelectedBalancedSignatureLaw coupling source weight := by
  let selected := driveSelectedChirality coupling source
  refine ⟨chiralMultiplicativeSignatureWeight selected, ?_, ?_⟩
  · exact ⟨chiralMultiplicativeSignatureWeight_isBalancedCompositional selected,
      selected, rfl, driveSelectedChirality_uniqueMinimum hDrive⟩
  · intro weight hWeight
    obtain ⟨_hBalanced, chirality, hCharacter, hMinimum⟩ := hWeight
    have hSelectedMinimum := driveSelectedChirality_uniqueMinimum hDrive
    have hForward := hMinimum.2
      (chiralBoundaryOrientationParameter selected) hSelectedMinimum.1
    have hBackward := hSelectedMinimum.2
      (chiralBoundaryOrientationParameter chirality) hMinimum.1
    have hEnergy :
        bilinearOrientationEnergy coupling source
            (chiralBoundaryOrientationParameter chirality) =
          bilinearOrientationEnergy coupling source
            (chiralBoundaryOrientationParameter selected) :=
      le_antisymm hForward.1 hBackward.1
    have hParameter : chiralBoundaryOrientationParameter chirality =
        chiralBoundaryOrientationParameter selected :=
      hSelectedMinimum.2
        (chiralBoundaryOrientationParameter chirality) hMinimum.1 |>.2.mp hEnergy
    have hChirality : chirality = selected :=
      chiralBoundaryOrientationParameter_injective hParameter
    rw [hCharacter, hChirality]

/-- **Mechanism audit.**  On nonzero drive, the variational predicate and the
direct sign-matching predicate select exactly the same balanced character.
Consequently the inaccessible boundary minimum covariantly encodes the sign
rule but supplies no additional finite dynamical selection mechanism. -/
theorem variationalSelection_iff_signMatching
    {coupling source : ℝ} (hDrive : coupling * source ≠ 0)
    (weight : ℕ → ℕ → ℂ) :
    IsVariationallySelectedBalancedSignatureLaw coupling source weight ↔
      IsSignMatchedBalancedSignatureLaw coupling source weight := by
  let selectedWeight := chiralMultiplicativeSignatureWeight
    (driveSelectedChirality coupling source)
  have hVariationalSelected :
      IsVariationallySelectedBalancedSignatureLaw
        coupling source selectedWeight := by
    exact ⟨chiralMultiplicativeSignatureWeight_isBalancedCompositional _,
      driveSelectedChirality coupling source, rfl,
      driveSelectedChirality_uniqueMinimum hDrive⟩
  have hSignSelected :
      IsSignMatchedBalancedSignatureLaw coupling source selectedWeight := by
    exact ⟨chiralMultiplicativeSignatureWeight_isBalancedCompositional _, by
      rw [bilinearSelectedPhase?_eq_driveSelectedCharacter hDrive]
      simp [selectedWeight, chiralMultiplicativeSignatureWeight,
        multiplicativeSignatureWeight]⟩
  obtain ⟨variationalWitness, _hVariationalWitness, hVariationalUnique⟩ :=
    variationalResponse_uniqueBalancedSignatureLaw hDrive
  obtain ⟨signWitness, _hSignWitness, hSignUnique⟩ :=
    signResponse_uniqueBalancedSignatureLaw hDrive
  constructor
  · intro hWeight
    have hToWitness := hVariationalUnique weight hWeight
    have hSelectedToWitness :=
      hVariationalUnique selectedWeight hVariationalSelected
    rw [hToWitness.trans hSelectedToWitness.symm]
    exact hSignSelected
  · intro hWeight
    have hToWitness := hSignUnique weight hWeight
    have hSelectedToWitness := hSignUnique selectedWeight hSignSelected
    rw [hToWitness.trans hSelectedToWitness.symm]
    exact hVariationalSelected

/-! ## 5. Attainment audit: finite geometry never reaches the minimizer -/

/-- The finite geometric orientation coordinate is uniformly distinct from
either pure chiral boundary value.  This is stronger than finite-rank strict
interiority: the geometric image lies in `(-1/4,1/4)`, while the character
endpoints have absolute value `1/2`. -/
theorem finiteGeometricOrientation_ne_chiralBoundary {n : ℕ}
    (parent : CardinalCausalOrder n) (event : Fin n)
    (chirality : Fin 2) :
    ((causalOrientationDensityQ parent event : ℚ) : ℝ) ≠
      chiralBoundaryOrientationParameter chirality := by
  intro hEqual
  have hGeometric := causalOrientationDensityR_abs_lt_quarter parent event
  have hBoundary := chiralBoundaryOrientationParameter_endpoint chirality
  rw [hEqual] at hGeometric
  nlinarith

/-- For nonzero drive, every finite geometric coordinate has strictly greater
energy than the auxiliary pure endpoint.  Thus the variational theorem is a
boundary-character selection theorem, not an attainment theorem for the
causal-volume coordinate. -/
theorem finiteGeometricOrientation_strictlyAbove_variationalIdeal {n : ℕ}
    (parent : CardinalCausalOrder n) (event : Fin n)
    {coupling source : ℝ} (hDrive : coupling * source ≠ 0) :
    bilinearOrientationEnergy coupling source
        (chiralBoundaryOrientationParameter
          (driveSelectedChirality coupling source)) <
      bilinearOrientationEnergy coupling source
        ((causalOrientationDensityQ parent event : ℚ) : ℝ) := by
  let geometric : ℝ :=
    ((causalOrientationDensityQ parent event : ℚ) : ℝ)
  let selected : ℝ :=
    chiralBoundaryOrientationParameter
      (driveSelectedChirality coupling source)
  have hGeometricQuarter : |geometric| < (1 : ℝ) / 4 := by
    simpa [geometric] using
      (causalOrientationDensityR_abs_lt_quarter parent event)
  have hGeometricAdmissible : IsAdmissibleOrientationParameter geometric := by
    exact le_trans (le_of_lt hGeometricQuarter) (by norm_num)
  have hMinimum : IsUniqueAdmissibleMinimum
      (bilinearOrientationEnergy coupling source) selected := by
    simpa [selected] using driveSelectedChirality_uniqueMinimum hDrive
  have hComparison := hMinimum.2 geometric hGeometricAdmissible
  have hNotEqual : geometric ≠ selected := by
    simpa [geometric, selected] using
      finiteGeometricOrientation_ne_chiralBoundary parent event
        (driveSelectedChirality coupling source)
  have hEnergyNotEqual :
      bilinearOrientationEnergy coupling source geometric ≠
        bilinearOrientationEnergy coupling source selected := by
    intro hEnergy
    exact hNotEqual (hComparison.2.mp hEnergy)
  exact lt_of_le_of_ne hComparison.1 hEnergyNotEqual.symm

/-- Direct resolution of the apparent birth-source tension.  The source is
definitionally the newborn's geometric odd residual, but that same finite
coordinate never attains the pure response minimum.  The phase character is
therefore a quantum sign response to an interior geometric source. -/
theorem maximalBirthGeometry_strictlyAbove_variationalIdeal {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent)
    {coupling : ℝ}
    (hDrive : coupling *
      (((maximalBirthOrientationSourceQ parent past : ℚ) : ℝ)) ≠ 0) :
    bilinearOrientationEnergy coupling
        (((maximalBirthOrientationSourceQ parent past : ℚ) : ℝ))
        (chiralBoundaryOrientationParameter
          (driveSelectedChirality coupling
            (((maximalBirthOrientationSourceQ parent past : ℚ) : ℝ)))) <
      bilinearOrientationEnergy coupling
        (((maximalBirthOrientationSourceQ parent past : ℚ) : ℝ))
        (((causalOrientationDensityQ
          (precursorOneElementExtension parent past) (Fin.last n) : ℚ) : ℝ)) := by
  exact finiteGeometricOrientation_strictlyAbove_variationalIdeal
    (precursorOneElementExtension parent past) (Fin.last n) hDrive

/-- **Resolved architecture.**  The birth source and geometric odd residual
are one and the same finite-rank datum, at every rank; nevertheless that datum
is disjoint from both pure character endpoints.  Thus source unification does
not imply order-parameter attainment. -/
theorem maximalBirthSource_isGeometric_and_ne_quantumBoundary {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent) :
    maximalBirthOrientationSourceQ parent past =
        causalOrientationDensityQ
          (precursorOneElementExtension parent past) (Fin.last n)
      ∧ ∀ chirality : Fin 2,
        (((maximalBirthOrientationSourceQ parent past : ℚ) : ℝ)) ≠
          chiralBoundaryOrientationParameter chirality := by
  refine ⟨maximalBirthSource_eq_geometricOrientationResidual parent past, ?_⟩
  intro chirality
  rw [maximalBirthSource_eq_geometricOrientationResidual]
  exact finiteGeometricOrientation_ne_chiralBoundary
    (precursorOneElementExtension parent past) (Fin.last n) chirality

/-! ## 6. The geometric birth source is mapped by the classified sign law -/

/-- Coupling sign associated with a representative of the conjugation pair.
Slot `1` is the standard future-growth convention. -/
def chiralResponseCoupling (chirality : Fin 2) : ℝ :=
  if chirality = 0 then -1 else 1

/-- Every linked maximal birth responds with the elementary coefficient of
its classified signature character.  The varying geometric magnitude drops
out, but the source must be nonzero. -/
theorem chiralResponseCoupling_matches_linkedBirth
    (chirality : Fin 2) {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent)
    {ancestor : Fin n} (hAncestor : past.mem ancestor = true) :
    bilinearSelectedPhase? (chiralResponseCoupling chirality)
        (((maximalBirthOrientationSourceQ parent past : ℚ) : ℝ)) =
      some (chiralMaximalEventPhase chirality) := by
  have hPositive :
      (0 : ℝ) < ((maximalBirthOrientationSourceQ parent past : ℚ) : ℝ) := by
    exact_mod_cast maximalBirthOrientationSourceQ_pos_of_mem
      parent past hAncestor
  fin_cases chirality
  · have hNotNegative :
        ¬(((maximalBirthOrientationSourceQ parent past : ℚ) : ℝ) < 0) :=
      not_lt_of_ge (le_of_lt hPositive)
    simp [chiralResponseCoupling, bilinearSelectedPhase?, hPositive,
      hNotNegative, chiralMaximalEventPhase]
  · simp [chiralResponseCoupling, bilinearSelectedPhase?, hPositive,
      chiralMaximalEventPhase]

/-- On the standard representative, the unique auxiliary variational endpoint,
the quarter-turn phase, and the projectively transported cylinder sign are one
theorem.  The attainment audit above keeps this distinct from the finite
geometric coordinate. -/
theorem linkedMaximalBirth_standardResponse_complete {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent)
    {ancestor : Fin n} (hAncestor : past.mem ancestor = true) :
    IsUniqueAdmissibleMinimum
        (bilinearOrientationEnergy 1
          (((maximalBirthOrientationSourceQ parent past : ℚ) : ℝ)))
        (-1 / 2)
      ∧ bilinearSelectedPhase? 1
          (((maximalBirthOrientationSourceQ parent past : ℚ) : ℝ)) =
        maximalBirthSelectedPhase? parent past
      ∧ (∀ steps : ℕ,
          inducedCylinderChiralitySign causalPositiveOrientationGrowthLaw
            (chiralRankTwoCoarseGraining.refineBy steps) = 1) := by
  have hPositive :
      (0 : ℝ) < ((maximalBirthOrientationSourceQ parent past : ℚ) : ℝ) := by
    exact_mod_cast maximalBirthOrientationSourceQ_pos_of_mem
      parent past hAncestor
  refine ⟨bilinear_positiveDrive_uniqueMinimum (by simpa using hPositive), ?_,
    causalPositiveOrientationGrowthLaw_sign_transport⟩
  rw [maximalBirthSelectedPhase?_eq_some_negI_of_mem
    parent past hAncestor]
  simp [bilinearSelectedPhase?, hPositive]

/-- The order-reversed birth selects the conjugate endpoint and transports the
opposite printed sign. -/
theorem linkedMinimalBirth_reflectedResponse_complete {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent)
    {ancestor : Fin n} (hAncestor : past.mem ancestor = true) :
    IsUniqueAdmissibleMinimum
        (bilinearOrientationEnergy 1
          (((reflectedMaximalBirthOrientationSourceQ parent past : ℚ) : ℝ)))
        (1 / 2)
      ∧ bilinearSelectedPhase? 1
          (((reflectedMaximalBirthOrientationSourceQ parent past : ℚ) : ℝ)) =
        some Complex.I
      ∧ (∀ steps : ℕ,
          inducedCylinderChiralitySign causalReflectedOrientationGrowthLaw
            (chiralRankTwoCoarseGraining.refineBy steps) = -1) := by
  have hNegativeQ :=
    reflectedMaximalBirthOrientationSourceQ_neg_of_mem
      parent past hAncestor
  have hNegative :
      (((reflectedMaximalBirthOrientationSourceQ parent past : ℚ) : ℝ)) < 0 := by
    exact_mod_cast hNegativeQ
  refine ⟨bilinear_negativeDrive_uniqueMinimum (by simpa using hNegative), ?_,
    causalReflectedOrientationGrowthLaw_sign_transport⟩
  simp [bilinearSelectedPhase?, hNegative,
    not_lt_of_ge (le_of_lt hNegative)]

/-! ## 7. Conjugation completeness of the newest harmonic action law -/

/-- The real ancestor-pair interaction does not disturb the conjugation
doublet: at every signature, conjugating only reverses chirality. -/
theorem interactingChiralSignatureWeight_star
    (lambda : ℝ) (chirality : Fin 2) (omega maximal : ℕ) :
    star (interactingChiralSignatureWeight lambda chirality omega maximal) =
      interactingChiralSignatureWeight lambda
        (reflectedMicroscopicChirality chirality) omega maximal := by
  fin_cases chirality <;>
    simp [interactingChiralSignatureWeight,
      chiralGaussianPower_eq_phase_pow, chiralMaximalEventPhase,
      reflectedMicroscopicChirality]

theorem interactingChiralCausalEdgeAmplitude_star
    (lambda : ℝ) (chirality : Fin 2) {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent) :
    star ((interactingChiralCausalEdgeAmplitude lambda chirality).amplitude
        parent past) =
      (interactingChiralCausalEdgeAmplitude lambda
        (reflectedMicroscopicChirality chirality)).amplitude parent past := by
  exact interactingChiralSignatureWeight_star lambda chirality
    past.ancestorCount past.maximalCount

theorem interacting_causalEdgeAmplitudePartition_star
    (lambda : ℝ) (chirality : Fin 2) {n : ℕ}
    (parent : CardinalCausalOrder n) :
    star (causalEdgeAmplitudePartition
        (interactingChiralCausalEdgeAmplitude lambda chirality) parent) =
      causalEdgeAmplitudePartition
        (interactingChiralCausalEdgeAmplitude lambda
          (reflectedMicroscopicChirality chirality)) parent := by
  classical
  unfold causalEdgeAmplitudePartition
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro past _
  exact interactingChiralCausalEdgeAmplitude_star
    lambda chirality parent past

theorem interacting_labeledAggregatedCausalEdgeAmplitude_star
    (lambda : ℝ) (chirality : Fin 2) {n : ℕ}
    (parent : CardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1)) :
    star (labeledAggregatedCausalEdgeAmplitude
        (interactingChiralCausalEdgeAmplitude lambda chirality)
        parent child) =
      labeledAggregatedCausalEdgeAmplitude
        (interactingChiralCausalEdgeAmplitude lambda
          (reflectedMicroscopicChirality chirality)) parent child := by
  classical
  unfold labeledAggregatedCausalEdgeAmplitude
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro past _
  exact interactingChiralCausalEdgeAmplitude_star
    lambda chirality parent past.val

theorem interacting_unlabeledAggregatedCausalEdgeAmplitude_star
    (lambda : ℝ) (chirality : Fin 2) {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1)) :
    star (unlabeledAggregatedCausalEdgeAmplitude
        (interactingChiralCausalEdgeAmplitude lambda chirality)
        parent child) =
      unlabeledAggregatedCausalEdgeAmplitude
        (interactingChiralCausalEdgeAmplitude lambda
          (reflectedMicroscopicChirality chirality)) parent child := by
  refine Quotient.inductionOn parent ?_
  intro parentRepresentative
  exact interacting_labeledAggregatedCausalEdgeAmplitude_star
    lambda chirality parentRepresentative child

theorem interacting_unlabeledCausalEdgeAmplitudePartition_star
    (lambda : ℝ) (chirality : Fin 2) {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n) :
    star (unlabeledCausalEdgeAmplitudePartition
        (interactingChiralCausalEdgeAmplitude lambda chirality) parent) =
      unlabeledCausalEdgeAmplitudePartition
        (interactingChiralCausalEdgeAmplitude lambda
          (reflectedMicroscopicChirality chirality)) parent := by
  refine Quotient.inductionOn parent ?_
  intro parentRepresentative
  exact interacting_causalEdgeAmplitudePartition_star
    lambda chirality parentRepresentative

/-- Conjugation exchanges the normalized transitions of the microscopic
spectator-action law at every rank. -/
theorem microscopicSpectatorTransition_star
    (action : VacuumSpectatorCausalAction) (chirality : Fin 2) {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1)) :
    star (microscopicSpectatorTransition action chirality parent child) =
      microscopicSpectatorTransition action
        (reflectedMicroscopicChirality chirality) parent child := by
  unfold microscopicSpectatorTransition
  simp only [div_eq_mul_inv, star_mul', star_inv₀]
  rw [interacting_unlabeledAggregatedCausalEdgeAmplitude_star,
    interacting_unlabeledCausalEdgeAmplitudePartition_star]

theorem microscopicSpectatorGrowthLaw_transition_star
    (action : VacuumSpectatorCausalAction) (chirality : Fin 2) {n : ℕ}
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n) :
    star ((microscopicSpectatorCausalSetGrowthLaw action chirality).transition
        n pathPrefix child) =
      (microscopicSpectatorCausalSetGrowthLaw action
        (reflectedMicroscopicChirality chirality)).transition
          n pathPrefix child := by
  exact microscopicSpectatorTransition_star action chirality
    (currentUnlabeledCausalOrder n pathPrefix) child

theorem microscopicSpectator_finiteRankedPathAmplitude_star
    (action : VacuumSpectatorCausalAction) (chirality : Fin 2) :
    ∀ (n : ℕ) (path : RankedGrowthPath CausalSetGrowthBranch n),
      star (finiteRankedPathAmplitude
          (microscopicSpectatorCausalSetGrowthLaw action chirality) n path) =
        finiteRankedPathAmplitude
          (microscopicSpectatorCausalSetGrowthLaw action
            (reflectedMicroscopicChirality chirality)) n path
  | 0, path => by simp
  | n + 1, path => by
      rcases path with ⟨pathPrefix, branch⟩
      rw [finiteRankedPathAmplitude_snoc,
        finiteRankedPathAmplitude_snoc, star_mul']
      rw [microscopicSpectator_finiteRankedPathAmplitude_star
          action chirality n pathPrefix,
        microscopicSpectatorGrowthLaw_transition_star]

theorem microscopicSpectator_finiteRankedDepthDecoherence_star
    (action : VacuumSpectatorCausalAction) (chirality : Fin 2)
    (n : ℕ) (first second : RankedGrowthPath CausalSetGrowthBranch n) :
    star (finiteRankedDepthDecoherence
        (microscopicSpectatorCausalSetGrowthLaw action chirality)
        n first second) =
      finiteRankedDepthDecoherence
        (microscopicSpectatorCausalSetGrowthLaw action
          (reflectedMicroscopicChirality chirality)) n first second := by
  unfold finiteRankedDepthDecoherence amplitudeDecoherence
  rw [star_mul']
  simp only [star_star]
  rw [microscopicSpectator_finiteRankedPathAmplitude_star,
    microscopicSpectator_finiteRankedPathAmplitude_star]
  simp [reflectedMicroscopicChirality_involutive]

theorem microscopicSpectator_finiteGrowthEventDecoherence_star
    (action : VacuumSpectatorCausalAction) (chirality : Fin 2)
    (n : ℕ)
    (first second : Finset (RankedGrowthPath CausalSetGrowthBranch n)) :
    star (growthEventDecoherence
        (finiteRankedDepthDecoherence
          (microscopicSpectatorCausalSetGrowthLaw action chirality) n)
        first second) =
      growthEventDecoherence
        (finiteRankedDepthDecoherence
          (microscopicSpectatorCausalSetGrowthLaw action
            (reflectedMicroscopicChirality chirality)) n) first second := by
  classical
  unfold growthEventDecoherence
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro history _
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro other _
  exact microscopicSpectator_finiteRankedDepthDecoherence_star
    action chirality n history other

theorem microscopicSpectator_finiteGrowthQuantumMeasure_eq
    (action : VacuumSpectatorCausalAction) (chirality : Fin 2)
    (n : ℕ) (event : Finset (RankedGrowthPath CausalSetGrowthBranch n)) :
    growthQuantumMeasure
        (finiteRankedDepthDecoherence
          (microscopicSpectatorCausalSetGrowthLaw action chirality) n) event =
      growthQuantumMeasure
        (finiteRankedDepthDecoherence
          (microscopicSpectatorCausalSetGrowthLaw action
            (reflectedMicroscopicChirality chirality)) n) event := by
  unfold growthQuantumMeasure
  rw [← microscopicSpectator_finiteGrowthEventDecoherence_star]
  simp

theorem microscopicSpectator_conjugation_commutes_with_refinement
    (action : VacuumSpectatorCausalAction) (chirality : Fin 2)
    (n : ℕ)
    (first second : Finset (RankedGrowthPath CausalSetGrowthBranch n))
    (steps : ℕ) :
    star (growthEventDecoherence
        (finiteRankedDepthDecoherence
          (microscopicSpectatorCausalSetGrowthLaw action chirality)
          (n + steps))
        (refineRankedGrowthEventBy first steps)
        (refineRankedGrowthEventBy second steps)) =
      growthEventDecoherence
        (finiteRankedDepthDecoherence
          (microscopicSpectatorCausalSetGrowthLaw action
            (reflectedMicroscopicChirality chirality)) n) first second := by
  rw [microscopicSpectator_finiteGrowthEventDecoherence_star]
  exact finiteRankedDepthDecoherence_projective_by
    (microscopicSpectatorCausalSetGrowthLaw action
      (reflectedMicroscopicChirality chirality)) n first second steps

theorem microscopicSpectator_rankedCylinderPresentationAmplitude_star
    (action : VacuumSpectatorCausalAction) (chirality : Fin 2)
    (cylinder : RankedCylinderPresentation CausalSetGrowthBranch) :
    star (rankedCylinderPresentationAmplitude
        (microscopicSpectatorCausalSetGrowthLaw action chirality) cylinder) =
      rankedCylinderPresentationAmplitude
        (microscopicSpectatorCausalSetGrowthLaw action
          (reflectedMicroscopicChirality chirality)) cylinder := by
  classical
  unfold rankedCylinderPresentationAmplitude
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro path _
  exact microscopicSpectator_finiteRankedPathAmplitude_star
    action chirality cylinder.depth path

theorem microscopicSpectator_infiniteRankedCylinderAmplitude_star
    (action : VacuumSpectatorCausalAction) (chirality : Fin 2)
    (event : InfiniteRankedCylinderEvent CausalSetGrowthBranch) :
    star (infiniteRankedCylinderAmplitude
        (microscopicSpectatorCausalSetGrowthLaw action chirality) event) =
      infiniteRankedCylinderAmplitude
        (microscopicSpectatorCausalSetGrowthLaw action
          (reflectedMicroscopicChirality chirality)) event := by
  refine Quotient.inductionOn event ?_
  intro cylinder
  exact microscopicSpectator_rankedCylinderPresentationAmplitude_star
    action chirality cylinder

theorem microscopicSpectator_infiniteRankedCylinderDecoherence_star
    (action : VacuumSpectatorCausalAction) (chirality : Fin 2)
    (first second : InfiniteRankedCylinderEvent CausalSetGrowthBranch) :
    star (infiniteRankedCylinderDecoherence
        (microscopicSpectatorCausalSetGrowthLaw action chirality)
        first second) =
      infiniteRankedCylinderDecoherence
        (microscopicSpectatorCausalSetGrowthLaw action
          (reflectedMicroscopicChirality chirality)) first second := by
  unfold infiniteRankedCylinderDecoherence amplitudeDecoherence
  rw [star_mul']
  simp only [star_star]
  rw [microscopicSpectator_infiniteRankedCylinderAmplitude_star,
    microscopicSpectator_infiniteRankedCylinderAmplitude_star]
  simp [reflectedMicroscopicChirality_involutive]

theorem microscopicSpectator_infiniteRankedCylinderQuantumMeasure_eq
    (action : VacuumSpectatorCausalAction) (chirality : Fin 2)
    (event : InfiniteRankedCylinderEvent CausalSetGrowthBranch) :
    infiniteRankedCylinderQuantumMeasure
        (microscopicSpectatorCausalSetGrowthLaw action chirality) event =
      infiniteRankedCylinderQuantumMeasure
        (microscopicSpectatorCausalSetGrowthLaw action
          (reflectedMicroscopicChirality chirality)) event := by
  unfold infiniteRankedCylinderQuantumMeasure
  rw [← microscopicSpectator_infiniteRankedCylinderDecoherence_star]
  simp

/-- Complete conjugation contract specialized to the zero-free harmonic law
generated by the microscopic spectator action. -/
structure IsCompleteMicroscopicActionConjugationEquivalence
    (action : VacuumSpectatorCausalAction) (chirality : Fin 2) : Prop where
  transition : ∀ {n : ℕ}
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n),
    star ((microscopicSpectatorCausalSetGrowthLaw action chirality).transition
        n pathPrefix child) =
      (microscopicSpectatorCausalSetGrowthLaw action
        (reflectedMicroscopicChirality chirality)).transition
          n pathPrefix child
  finitePath : ∀ (n : ℕ)
    (path : RankedGrowthPath CausalSetGrowthBranch n),
    star (finiteRankedPathAmplitude
        (microscopicSpectatorCausalSetGrowthLaw action chirality) n path) =
      finiteRankedPathAmplitude
        (microscopicSpectatorCausalSetGrowthLaw action
          (reflectedMicroscopicChirality chirality)) n path
  finiteEvent : ∀ (n : ℕ)
    (first second : Finset (RankedGrowthPath CausalSetGrowthBranch n)),
    star (growthEventDecoherence
        (finiteRankedDepthDecoherence
          (microscopicSpectatorCausalSetGrowthLaw action chirality) n)
        first second) =
      growthEventDecoherence
        (finiteRankedDepthDecoherence
          (microscopicSpectatorCausalSetGrowthLaw action
            (reflectedMicroscopicChirality chirality)) n) first second
  finiteMeasure : ∀ (n : ℕ)
    (event : Finset (RankedGrowthPath CausalSetGrowthBranch n)),
    growthQuantumMeasure
        (finiteRankedDepthDecoherence
          (microscopicSpectatorCausalSetGrowthLaw action chirality) n) event =
      growthQuantumMeasure
        (finiteRankedDepthDecoherence
          (microscopicSpectatorCausalSetGrowthLaw action
            (reflectedMicroscopicChirality chirality)) n) event
  refinement : ∀ (n : ℕ)
    (first second : Finset (RankedGrowthPath CausalSetGrowthBranch n))
    (steps : ℕ),
    star (growthEventDecoherence
        (finiteRankedDepthDecoherence
          (microscopicSpectatorCausalSetGrowthLaw action chirality)
          (n + steps))
        (refineRankedGrowthEventBy first steps)
        (refineRankedGrowthEventBy second steps)) =
      growthEventDecoherence
        (finiteRankedDepthDecoherence
          (microscopicSpectatorCausalSetGrowthLaw action
            (reflectedMicroscopicChirality chirality)) n) first second
  infiniteCylinder : ∀
    (first second : InfiniteRankedCylinderEvent CausalSetGrowthBranch),
    star (infiniteRankedCylinderDecoherence
        (microscopicSpectatorCausalSetGrowthLaw action chirality)
        first second) =
      infiniteRankedCylinderDecoherence
        (microscopicSpectatorCausalSetGrowthLaw action
          (reflectedMicroscopicChirality chirality)) first second
  infiniteMeasure : ∀
    (event : InfiniteRankedCylinderEvent CausalSetGrowthBranch),
    infiniteRankedCylinderQuantumMeasure
        (microscopicSpectatorCausalSetGrowthLaw action chirality) event =
      infiniteRankedCylinderQuantumMeasure
        (microscopicSpectatorCausalSetGrowthLaw action
          (reflectedMicroscopicChirality chirality)) event

theorem completeMicroscopicActionConjugationEquivalence
    (action : VacuumSpectatorCausalAction) (chirality : Fin 2) :
    IsCompleteMicroscopicActionConjugationEquivalence action chirality where
  transition := microscopicSpectatorGrowthLaw_transition_star action chirality
  finitePath :=
    microscopicSpectator_finiteRankedPathAmplitude_star action chirality
  finiteEvent :=
    microscopicSpectator_finiteGrowthEventDecoherence_star action chirality
  finiteMeasure :=
    microscopicSpectator_finiteGrowthQuantumMeasure_eq action chirality
  refinement :=
    microscopicSpectator_conjugation_commutes_with_refinement action chirality
  infiniteCylinder :=
    microscopicSpectator_infiniteRankedCylinderDecoherence_star action chirality
  infiniteMeasure :=
    microscopicSpectator_infiniteRankedCylinderQuantumMeasure_eq action chirality

/-- The variational response of every linked birth is literally the
elementary phase retained by the newest zero-free microscopic action law. -/
theorem microscopicAction_elementaryPhase_matches_linkedBirth
    (action : VacuumSpectatorCausalAction) (chirality : Fin 2) {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent)
    {ancestor : Fin n} (hAncestor : past.mem ancestor = true) :
    interactingChiralSignatureWeight
        (microscopicSpectatorPairCoupling action 1) chirality 1 1 =
        chiralMaximalEventPhase chirality
      ∧ bilinearSelectedPhase? (chiralResponseCoupling chirality)
          (((maximalBirthOrientationSourceQ parent past : ℚ) : ℝ)) =
        some (chiralMaximalEventPhase chirality) := by
  exact ⟨(interactingChiralSignatureWeight_elementary
      (microscopicSpectatorPairCoupling action 1) chirality).2,
    chiralResponseCoupling_matches_linkedBirth
      chirality parent past hAncestor⟩

/-! ## 8. Finite response completeness -/

/-- **Microscopic response completeness.**  Within the affine-bilinear
lowest-order ansatz, the local energy has one coefficient; the balanced
compositional edge law has exactly one of two representatives; the explicit
sign rule maps every linked birth to its representative's pure phase; and the
complete cylinder quotient has only one conjugation-gauge sector.  Direct
sign matching and variational selection are extensionally identical for every
nonzero drive.  The pure endpoint is only an auxiliary boundary optimum:
every finite geometric coordinate has strictly higher energy and is uniformly
separated from it.  The variational functional therefore supplies neither a
relaxation flow nor an additional finite selection mechanism.

The open physics is now outside this theorem's hypotheses: deriving affine
locality and elementary relation-complement symmetry from deeper dynamics,
and proving a continuum Lorentzian/CP correspondence. -/
theorem finiteMicroscopicResponseLaw_complete
    (constant sourceBias orientationBias coupling : ℝ)
    (hReflection : IsCombinedReflectionInvariant
      (affineBilinearOrientationEnergy constant sourceBias
        orientationBias coupling))
    (hNeutral : IsAchiralNeutral
      (affineBilinearOrientationEnergy constant sourceBias
        orientationBias coupling))
    (weight : ℕ → ℕ → ℂ)
    (hWeight : IsBalancedCompositionalSignatureLaw weight) :
    (constant = 0 ∧ sourceBias = 0 ∧ orientationBias = 0 ∧
      ∀ source orientation,
        affineBilinearOrientationEnergy constant sourceBias
            orientationBias coupling source orientation =
          bilinearOrientationEnergy coupling source orientation)
      ∧ (∃! chirality : Fin 2,
        weight = chiralMultiplicativeSignatureWeight chirality)
      ∧ (∀ {effectiveCoupling source : ℝ},
        effectiveCoupling * source ≠ 0 →
          ∃! selectedWeight : ℕ → ℕ → ℂ,
            IsVariationallySelectedBalancedSignatureLaw
              effectiveCoupling source selectedWeight)
      ∧ (∀ {effectiveCoupling source : ℝ},
        effectiveCoupling * source ≠ 0 →
          ∀ candidate : ℕ → ℕ → ℂ,
            IsVariationallySelectedBalancedSignatureLaw
                effectiveCoupling source candidate ↔
              IsSignMatchedBalancedSignatureLaw
                effectiveCoupling source candidate)
      ∧ (∀ {n : ℕ} (parent : CardinalCausalOrder n) (event : Fin n)
          {effectiveCoupling source : ℝ},
        effectiveCoupling * source ≠ 0 →
          bilinearOrientationEnergy effectiveCoupling source
              (chiralBoundaryOrientationParameter
                (driveSelectedChirality effectiveCoupling source)) <
            bilinearOrientationEnergy effectiveCoupling source
              ((causalOrientationDensityQ parent event : ℚ) : ℝ))
      ∧ (∀ (chirality : Fin 2) {n : ℕ}
          (parent : CardinalCausalOrder n) (past : CausalPastSet parent)
          {ancestor : Fin n}, past.mem ancestor = true →
        bilinearSelectedPhase? (chiralResponseCoupling chirality)
            (((maximalBirthOrientationSourceQ parent past : ℚ) : ℝ)) =
          some (chiralMaximalEventPhase chirality))
      ∧ IsCompleteChiralConjugationEquivalence 1
      ∧ (∀ action : VacuumSpectatorCausalAction,
        IsCompleteMicroscopicActionConjugationEquivalence action 1)
      ∧ (∀ first second : ChiralCylinderGaugeSector, first = second) := by
  exact ⟨affineBilinear_localInteraction_unique
      constant sourceBias orientationBias coupling hReflection hNeutral,
    balancedCompositionalSignatureLaw_classification weight hWeight,
    fun hDrive => variationalResponse_uniqueBalancedSignatureLaw hDrive,
    fun hDrive candidate => variationalSelection_iff_signMatching
      hDrive candidate,
    fun {n} parent event {effectiveCoupling source} hDrive =>
      finiteGeometricOrientation_strictlyAbove_variationalIdeal
        (n := n) parent event
        (coupling := effectiveCoupling) (source := source) hDrive,
    fun chirality _ parent past _ hAncestor =>
      chiralResponseCoupling_matches_linkedBirth
        chirality parent past hAncestor,
    completeChiralConjugationEquivalence 1,
    fun action => completeMicroscopicActionConjugationEquivalence action 1,
    chiralCylinderGaugeSector_unique⟩

#print axioms affineBilinear_localInteraction_unique
#print axioms bilinear_positiveDrive_uniqueMinimum
#print axioms bilinearSelectedPhase?_reflection
#print axioms balancedCompositionalSignatureLaw_classification
#print axioms balancedCompositionalSignatureLaws_equal_or_conjugate
#print axioms bilinearSelectedPhase?_eq_driveSelectedCharacter
#print axioms signResponse_uniqueBalancedSignatureLaw
#print axioms variationalResponse_uniqueBalancedSignatureLaw
#print axioms variationalSelection_iff_signMatching
#print axioms finiteGeometricOrientation_ne_chiralBoundary
#print axioms finiteGeometricOrientation_strictlyAbove_variationalIdeal
#print axioms maximalBirthGeometry_strictlyAbove_variationalIdeal
#print axioms maximalBirthSource_isGeometric_and_ne_quantumBoundary
#print axioms chiralResponseCoupling_matches_linkedBirth
#print axioms linkedMaximalBirth_standardResponse_complete
#print axioms linkedMinimalBirth_reflectedResponse_complete
#print axioms completeMicroscopicActionConjugationEquivalence
#print axioms microscopicAction_elementaryPhase_matches_linkedBirth
#print axioms finiteMicroscopicResponseLaw_complete

end

end UnifiedTheory.Audit.KFCausalSetMicroscopicResponseLaw
