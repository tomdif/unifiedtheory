/-
  Audit/KFCausalDoubleConservationLaw.lean

  THE CAUSAL DOUBLE-CONSERVATION LAW

  This module turns the repository's bi-normalization intersection from a
  sufficient construction into an exact local rigidity theorem.

  For scalar successor amplitudes `a_e`, demand that one unresolved birth
  preserve every incoming complex amplitude and its Born mass:

      sum_e z a_e = z,
      sum_e |z a_e|^2 = |z|^2               for every z.

  These operational conservation laws are equivalent, respectively, to

      sum_e a_e = 1,
      sum_e |a_e|^2 = 1.

  For carrier operators `K_e`, the exact analogue is

      sum_e K_e X = X,
      sum_e (K_e X)^dagger (K_e X) = X^dagger X   for every X.

  These are equivalent to coherent exhaustivity and Kraus completeness:

      sum_e K_e = I,
      sum_e K_e^dagger K_e = I.

  Thus bi-normalization is necessary and sufficient for simultaneous local
  conservation of coherent quantum data and Born records.  No tensor-product
  factor, partial trace, or state-independent record algebra is assumed.

  The theorem is a rigidity result conditional on the two universal local
  conservation demands.  It does not derive those demands from causal order,
  and it does not select the microscopic operators.  The existing harmonic
  causal law and its holonomy lift are proved to inhabit the rigid class.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalBornNormalizationTransfer
import UnifiedTheory.Audit.KFCausalHolonomyBirthCouplingLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalDoubleConservationLaw

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
open UnifiedTheory.Audit.KFOrientationGrowthDecoherence
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalBornShellGeneralLaw
open UnifiedTheory.Audit.KFCausalBornNormalizationTransfer
open UnifiedTheory.Audit.KFCausalHolonomyBirthCouplingLaw
open UnifiedTheory.Audit.KFOrientationCPChannelTower

universe u

/-! ## 1. Scalar local rigidity -/

/-- Every incoming scalar amplitude is preserved after summing over the
unresolved successor alternatives. -/
def PreservesEveryCoherentScalar {Outcome : Type u} [Fintype Outcome]
    (amplitude : Outcome → ℂ) : Prop :=
  ∀ incoming : ℂ, ∑ outcome, incoming * amplitude outcome = incoming

/-- Every incoming scalar Born mass is preserved after summing the resolved
successor masses. -/
def PreservesEveryBornScalar {Outcome : Type u} [Fintype Outcome]
    (amplitude : Outcome → ℂ) : Prop :=
  ∀ incoming : ℂ,
    ∑ outcome, Complex.normSq (incoming * amplitude outcome) =
      Complex.normSq incoming

/-- Universal coherent conservation is exactly coherent normalization. -/
theorem preservesEveryCoherentScalar_iff_sum_eq_one
    {Outcome : Type u} [Fintype Outcome] (amplitude : Outcome → ℂ) :
    PreservesEveryCoherentScalar amplitude ↔
      ∑ outcome, amplitude outcome = 1 := by
  constructor
  · intro h
    simpa [PreservesEveryCoherentScalar] using h 1
  · intro h incoming
    rw [← Finset.mul_sum, h, mul_one]

/-- Universal Born-mass conservation is exactly Born normalization. -/
theorem preservesEveryBornScalar_iff_born_sum_eq_one
    {Outcome : Type u} [Fintype Outcome] (amplitude : Outcome → ℂ) :
    PreservesEveryBornScalar amplitude ↔
      ∑ outcome, Complex.normSq (amplitude outcome) = 1 := by
  constructor
  · intro h
    simpa [PreservesEveryBornScalar] using h 1
  · intro h incoming
    simp only [Complex.normSq_mul]
    rw [← Finset.mul_sum, h, mul_one]

/-- **Scalar double-conservation rigidity.**  Simultaneous preservation of
every coherent parent amplitude and every Born mass is equivalent to the two
local normalization equations. -/
theorem scalarDoubleConservation_iff_biNormalized
    {Outcome : Type u} [Fintype Outcome] (amplitude : Outcome → ℂ) :
    (PreservesEveryCoherentScalar amplitude ∧
      PreservesEveryBornScalar amplitude) ↔
    ((∑ outcome, amplitude outcome = 1) ∧
      (∑ outcome, Complex.normSq (amplitude outcome) = 1)) := by
  rw [preservesEveryCoherentScalar_iff_sum_eq_one,
    preservesEveryBornScalar_iff_born_sum_eq_one]

/-! ## 2. All-rank scalar growth -/

/-- For a Born-normalized growth law, adding universal coherent conservation
is equivalent to universal double conservation at every parent. -/
theorem bornGrowth_coherent_iff_doubleConservation
    {Branch : ℕ → Type u} [∀ n, Fintype (Branch n)]
    (law : RankedBornNormalizedComplexGrowthLaw Branch) :
    (∀ (n : ℕ) (pathPrefix : RankedGrowthPath Branch n),
      ∑ branch, law.transition n pathPrefix branch = 1) ↔
    (∀ (n : ℕ) (pathPrefix : RankedGrowthPath Branch n),
      PreservesEveryCoherentScalar (law.transition n pathPrefix) ∧
      PreservesEveryBornScalar (law.transition n pathPrefix)) := by
  constructor
  · intro hCoherent n pathPrefix
    apply (scalarDoubleConservation_iff_biNormalized _).2
    exact ⟨hCoherent n pathPrefix, law.bornNormalized n pathPrefix⟩
  · intro hConserved n pathPrefix
    exact (scalarDoubleConservation_iff_biNormalized _).1
      (hConserved n pathPrefix) |>.1

/-- The canonical harmonic Born-shell law obeys the operational double
conservation law at every causal rank and every path prefix. -/
theorem canonicalHarmonic_preserves_both_at_every_parent
    (chirality : Fin 2) :
    ∀ (n : ℕ) (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n),
      PreservesEveryCoherentScalar
          ((canonicalHarmonicBornNormalizedGrowthLaw chirality).transition
            n pathPrefix) ∧
      PreservesEveryBornScalar
          ((canonicalHarmonicBornNormalizedGrowthLaw chirality).transition
            n pathPrefix) := by
  exact (bornGrowth_coherent_iff_doubleConservation
      (canonicalHarmonicBornNormalizedGrowthLaw chirality)).1
    (canonicalHarmonicCriticalBornShell_all_rank chirality).1

/-! ## 3. Operator local rigidity -/

/-- Summing over an unresolved operator-valued birth preserves every incoming
carrier amplitude.  Using arbitrary square matrices as incoming amplitudes
avoids choosing a basis vector or a tensor-product environment. -/
def PreservesEveryCoherentCarrier {dimension outcomes : ℕ}
    (operator : Fin outcomes → SquareMatrix dimension) : Prop :=
  ∀ incoming : SquareMatrix dimension,
    ∑ outcome, operator outcome * incoming = incoming

/-- Resolving the birth alternatives preserves the complete quadratic carrier
form of every incoming amplitude. -/
def PreservesEveryBornCarrier {dimension outcomes : ℕ}
    (operator : Fin outcomes → SquareMatrix dimension) : Prop :=
  ∀ incoming : SquareMatrix dimension,
    ∑ outcome,
        (operator outcome * incoming)ᴴ * (operator outcome * incoming) =
      incomingᴴ * incoming

/-- Universal coherent carrier conservation is exactly operator
exhaustivity. -/
theorem preservesEveryCoherentCarrier_iff_sum_eq_one
    {dimension outcomes : ℕ}
    (operator : Fin outcomes → SquareMatrix dimension) :
    PreservesEveryCoherentCarrier operator ↔
      ∑ outcome, operator outcome = (1 : SquareMatrix dimension) := by
  constructor
  · intro h
    simpa [PreservesEveryCoherentCarrier] using
      h (1 : SquareMatrix dimension)
  · intro h incoming
    rw [← Matrix.sum_mul, h, Matrix.one_mul]

/-- Universal quadratic carrier conservation is exactly Kraus completeness. -/
theorem preservesEveryBornCarrier_iff_complete
    {dimension outcomes : ℕ}
    (operator : Fin outcomes → SquareMatrix dimension) :
    PreservesEveryBornCarrier operator ↔
      (∑ outcome, (operator outcome)ᴴ * operator outcome) =
        (1 : SquareMatrix dimension) := by
  constructor
  · intro h
    simpa [PreservesEveryBornCarrier] using
      h (1 : SquareMatrix dimension)
  · intro h incoming
    simp_rw [Matrix.conjTranspose_mul]
    have hTerm (outcome : Fin outcomes) :
        (incomingᴴ * (operator outcome)ᴴ) *
              (operator outcome * incoming) =
          incomingᴴ * ((operator outcome)ᴴ * operator outcome) *
            incoming := by
      simp only [Matrix.mul_assoc]
    simp_rw [hTerm]
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, h, Matrix.mul_one]

/-- **Operator double-conservation rigidity.**  The two operational local
conservation demands force, and are forced by, coherent exhaustivity and
Kraus completeness. -/
theorem carrierDoubleConservation_iff_projectiveBorn
    {dimension outcomes : ℕ}
    (operator : Fin outcomes → SquareMatrix dimension) :
    (PreservesEveryCoherentCarrier operator ∧
      PreservesEveryBornCarrier operator) ↔
    ((∑ outcome, operator outcome) = (1 : SquareMatrix dimension) ∧
      (∑ outcome, (operator outcome)ᴴ * operator outcome) =
        (1 : SquareMatrix dimension)) := by
  rw [preservesEveryCoherentCarrier_iff_sum_eq_one,
    preservesEveryBornCarrier_iff_complete]

/-- The operational conservation laws canonically produce the repository's
bi-normalized operator-growth structure. -/
def projectiveBornOperatorLawOfDoubleConservation
    {dimension outcomes : ℕ}
    (operator : Fin outcomes → SquareMatrix dimension)
    (hConserved : PreservesEveryCoherentCarrier operator ∧
      PreservesEveryBornCarrier operator) :
    ProjectiveBornOperatorLaw dimension outcomes where
  operator := operator
  bornComplete :=
    (carrierDoubleConservation_iff_projectiveBorn operator).1 hConserved |>.2
  coherentlyExhaustive :=
    (carrierDoubleConservation_iff_projectiveBorn operator).1 hConserved |>.1

/-- Conversely, every projective Born operator law preserves both forms of
data for every incoming carrier amplitude. -/
theorem projectiveBornOperatorLaw_preservesEveryParent
    {dimension outcomes : ℕ}
    (law : ProjectiveBornOperatorLaw dimension outcomes) :
    PreservesEveryCoherentCarrier law.operator ∧
      PreservesEveryBornCarrier law.operator := by
  apply (carrierDoubleConservation_iff_projectiveBorn law.operator).2
  exact ⟨law.coherentlyExhaustive, law.bornComplete⟩

/-! ## 4. Existing causal realizations satisfy the rigid law -/

/-- The first nontrivial pair of unlabeled causal births satisfies both
operational conservation laws on the native three-sheet carrier. -/
theorem rankOneCausalBirth_preserves_both
    (chirality : Fin 2) :
    PreservesEveryCoherentCarrier
        (rankOneCausalProjectiveBornLaw chirality).operator ∧
      PreservesEveryBornCarrier
        (rankOneCausalProjectiveBornLaw chirality).operator :=
  projectiveBornOperatorLaw_preservesEveryParent
    (rankOneCausalProjectiveBornLaw chirality)

/-- The corrected six-outcome harmonic causal/holonomy process, already
proved CPTP and projective, is an operator double-conservation law. -/
def harmonicCausalProjectiveBornLaw (chirality : Fin 2) :
    ProjectiveBornOperatorLaw 3 6 where
  operator := harmonicBornShellHolonomyKrausOperator chirality
  bornComplete := harmonicBornShellHolonomyKrausOperator_complete chirality
  coherentlyExhaustive :=
    harmonicBornShellHolonomyKrausOperator_sum_eq_one chirality

theorem harmonicCausalOperator_preserves_both
    (chirality : Fin 2) :
    PreservesEveryCoherentCarrier
        (harmonicCausalProjectiveBornLaw chirality).operator ∧
      PreservesEveryBornCarrier
        (harmonicCausalProjectiveBornLaw chirality).operator :=
  projectiveBornOperatorLaw_preservesEveryParent
    (harmonicCausalProjectiveBornLaw chirality)

/-! ## 5. Capstone and axiom audit -/

/-- The candidate microscopic law has an exact logical status: local double
conservation is equivalent to bi-normalization, and both the all-rank scalar
harmonic law and the concrete operator-valued causal realizations satisfy it.
The remaining physics is selection of the local operators from deeper causal
dynamics and derivation of a record algebra or observable discriminator. -/
theorem causalDoubleConservationLaw_capstone :
    (∀ {Outcome : Type u} [Fintype Outcome]
        (amplitude : Outcome → ℂ),
      (PreservesEveryCoherentScalar amplitude ∧
          PreservesEveryBornScalar amplitude) ↔
        ((∑ outcome, amplitude outcome = 1) ∧
          (∑ outcome, Complex.normSq (amplitude outcome) = 1))) ∧
    (∀ (dimension outcomes : ℕ)
        (operator : Fin outcomes → SquareMatrix dimension),
      (PreservesEveryCoherentCarrier operator ∧
          PreservesEveryBornCarrier operator) ↔
        ((∑ outcome, operator outcome) = (1 : SquareMatrix dimension) ∧
          (∑ outcome, (operator outcome)ᴴ * operator outcome) =
            (1 : SquareMatrix dimension))) := by
  constructor
  · intro Outcome _ amplitude
    exact scalarDoubleConservation_iff_biNormalized amplitude
  · intro dimension outcomes operator
    exact carrierDoubleConservation_iff_projectiveBorn operator

#print axioms preservesEveryCoherentScalar_iff_sum_eq_one
#print axioms preservesEveryBornScalar_iff_born_sum_eq_one
#print axioms scalarDoubleConservation_iff_biNormalized
#print axioms bornGrowth_coherent_iff_doubleConservation
#print axioms canonicalHarmonic_preserves_both_at_every_parent
#print axioms preservesEveryCoherentCarrier_iff_sum_eq_one
#print axioms preservesEveryBornCarrier_iff_complete
#print axioms carrierDoubleConservation_iff_projectiveBorn
#print axioms rankOneCausalBirth_preserves_both
#print axioms harmonicCausalOperator_preserves_both
#print axioms causalDoubleConservationLaw_capstone

end

end UnifiedTheory.Audit.KFCausalDoubleConservationLaw
