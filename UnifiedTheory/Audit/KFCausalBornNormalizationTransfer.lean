/-
  Audit/KFCausalBornNormalizationTransfer.lean

  NORMALIZATION TRANSFER AUDIT FOR CAUSAL SEQUENTIAL GROWTH

  The older wave family normalizes the coherent transition sum

      sum_child a(child) = 1,

  whereas a classical/Born transition law normalizes

      sum_child |a(child)|^2 = 1.

  These are independent constraints.  This file proves the exact consequences
  that transfer before any model-specific causal or action assumptions enter:

  * Born normalization makes path Born weights a projectively consistent
    classical cylinder probability and hence gives zero normalization churn;
  * coherent normalization, not Born normalization, is what makes the scalar
    rank-one amplitude decoherence functional projective under independent
    ket/bra refinement;
  * neither normalization implies the other, while their intersection is
    nonempty and contains the familiar quadrature pair;
  * simultaneous normalization is exactly the scalar form of the repository's
    operator interference-cancellation law.

  Therefore a Born-only completion is a second dynamics, not a harmless
  reparameterization of the coherent wave equations.  The all-rank harmonic
  Born-shell law already inhabits the intersection, but its additional
  least-disturbance/radial selection law is real microscopic input.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalBornShellGeneralLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBornNormalizationTransfer

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open UnifiedTheory.Audit.KFOrientationGrowthDecoherence
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalBornShellGeneralLaw

universe u

/-! ## 1. The Born-normalized theory -/

/-- A state-dependent finite branching law normalized in squared modulus.
Unlike `RankedNormalizedComplexGrowthLaw`, this structure does not assume that
the complex transition amplitudes themselves sum to one. -/
structure RankedBornNormalizedComplexGrowthLaw
    (Branch : ℕ → Type u) [∀ n, Fintype (Branch n)] where
  transition : ∀ n : ℕ, RankedGrowthPath Branch n → Branch n → ℂ
  bornNormalized : ∀ (n : ℕ) (pathPrefix : RankedGrowthPath Branch n),
    ∑ branch, Complex.normSq (transition n pathPrefix branch) = 1

/-- Product amplitude along a path for a Born-normalized law. -/
def finiteBornPathAmplitude {Branch : ℕ → Type u}
    [∀ n, Fintype (Branch n)]
    (law : RankedBornNormalizedComplexGrowthLaw Branch) :
    ∀ n : ℕ, RankedGrowthPath Branch n → ℂ
  | 0, _ => 1
  | n + 1, path =>
      finiteBornPathAmplitude law n path.1 *
        law.transition n path.1 path.2

/-- Classical path weight induced by the local Born rule. -/
def finiteBornPathWeight {Branch : ℕ → Type u}
    [∀ n, Fintype (Branch n)]
    (law : RankedBornNormalizedComplexGrowthLaw Branch)
    (n : ℕ) (path : RankedGrowthPath Branch n) : ℝ :=
  Complex.normSq (finiteBornPathAmplitude law n path)

@[simp]
theorem finiteBornPathWeight_zero {Branch : ℕ → Type u}
    [∀ n, Fintype (Branch n)]
    (law : RankedBornNormalizedComplexGrowthLaw Branch)
    (path : RankedGrowthPath Branch 0) :
    finiteBornPathWeight law 0 path = 1 := by
  simp [finiteBornPathWeight, finiteBornPathAmplitude]

/-- Local Born normalization is exactly marginal conservation for each path. -/
theorem finiteBornPathWeight_sum_children {Branch : ℕ → Type u}
    [∀ n, Fintype (Branch n)]
    (law : RankedBornNormalizedComplexGrowthLaw Branch) (n : ℕ)
    (pathPrefix : RankedGrowthPath Branch n) :
    ∑ branch,
        finiteBornPathWeight law (n + 1) (pathPrefix, branch) =
      finiteBornPathWeight law n pathPrefix := by
  classical
  simp only [finiteBornPathWeight, finiteBornPathAmplitude,
    Complex.normSq_mul]
  rw [← Finset.mul_sum, law.bornNormalized, mul_one]

/-- Born probability of a finite path event. -/
def finiteBornEventProbability {Branch : ℕ → Type u}
    [∀ n, Fintype (Branch n)]
    (law : RankedBornNormalizedComplexGrowthLaw Branch) (n : ℕ)
    (event : Finset (RankedGrowthPath Branch n)) : ℝ :=
  ∑ path ∈ event, finiteBornPathWeight law n path

/-- Every finite event has exactly the same Born probability after one full
refinement.  This is the finite-cylinder martingale law missing from the
coherent-only completion experiment. -/
theorem finiteBornEventProbability_refine {Branch : ℕ → Type u}
    [∀ n, Fintype (Branch n)]
    (law : RankedBornNormalizedComplexGrowthLaw Branch) (n : ℕ)
    (event : Finset (RankedGrowthPath Branch n)) :
    finiteBornEventProbability law (n + 1)
        (refineRankedGrowthEvent event) =
      finiteBornEventProbability law n event := by
  classical
  unfold finiteBornEventProbability refineRankedGrowthEvent
  change ∑ path ∈ event ×ˢ (Finset.univ : Finset (Branch n)),
      Complex.normSq
        (finiteBornPathAmplitude law n path.1 *
          law.transition n path.1 path.2) =
    ∑ pathPrefix ∈ event,
      finiteBornPathWeight law n pathPrefix
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro pathPrefix _
  simp only [Complex.normSq_mul]
  change ∑ branch,
      Complex.normSq (finiteBornPathAmplitude law n pathPrefix) *
        Complex.normSq (law.transition n pathPrefix branch) =
    finiteBornPathWeight law n pathPrefix
  rw [← Finset.mul_sum, law.bornNormalized, mul_one]
  rfl

/-- Total diagonal probability is one at every finite depth. -/
theorem finiteBornPathWeight_sum_univ {Branch : ℕ → Type u}
    [∀ n, Fintype (Branch n)]
    (law : RankedBornNormalizedComplexGrowthLaw Branch) : ∀ n : ℕ,
    ∑ path : RankedGrowthPath Branch n,
      finiteBornPathWeight law n path = 1
  | 0 => by
      have hCard : Fintype.card (RankedGrowthPath Branch 0) = 1 := by
        change Fintype.card PUnit = 1
        simp
      simp [finiteBornPathWeight, finiteBornPathAmplitude, hCard]
  | n + 1 => by
      classical
      rw [← refineRankedGrowthEvent_univ (Branch := Branch) n]
      change finiteBornEventProbability law (n + 1)
          (refineRankedGrowthEvent
            (Finset.univ : Finset (RankedGrowthPath Branch n))) = 1
      rw [finiteBornEventProbability_refine]
      exact finiteBornPathWeight_sum_univ law n

theorem finiteBornEventProbability_nonneg {Branch : ℕ → Type u}
    [∀ n, Fintype (Branch n)]
    (law : RankedBornNormalizedComplexGrowthLaw Branch) (n : ℕ)
    (event : Finset (RankedGrowthPath Branch n)) :
    0 ≤ finiteBornEventProbability law n event := by
  unfold finiteBornEventProbability finiteBornPathWeight
  exact Finset.sum_nonneg fun path _ => Complex.normSq_nonneg _

/-- Normalization-flow churn vanishes pointwise, before summing any norm or
absolute difference over prefixes. -/
theorem bornNormalizationFlowDefect_eq_zero
    {Branch : ℕ → Type u} [∀ n, Fintype (Branch n)]
    (law : RankedBornNormalizedComplexGrowthLaw Branch) (n : ℕ)
    (pathPrefix : RankedGrowthPath Branch n) :
    (∑ branch,
        finiteBornPathWeight law (n + 1) (pathPrefix, branch)) -
      finiteBornPathWeight law n pathPrefix = 0 := by
  rw [finiteBornPathWeight_sum_children]
  ring

/-! ## 2. The two normalizations are independent -/

/-- A Born-normalized binary transition whose coherent sum is `7/5`. -/
def bornOnlyBinaryAmplitude (branch : Fin 2) : ℂ :=
  if branch = 0 then (3 / 5 : ℝ) else (4 / 5 : ℝ)

theorem bornOnlyBinaryAmplitude_bornNormalized :
    ∑ branch, Complex.normSq (bornOnlyBinaryAmplitude branch) = 1 := by
  rw [Fin.sum_univ_two]
  norm_num [bornOnlyBinaryAmplitude, Complex.normSq]

theorem bornOnlyBinaryAmplitude_coherentSum :
    ∑ branch, bornOnlyBinaryAmplitude branch = 7 / 5 := by
  rw [Fin.sum_univ_two]
  norm_num [bornOnlyBinaryAmplitude]

theorem bornNormalization_does_not_imply_coherentNormalization :
    (∑ branch, Complex.normSq (bornOnlyBinaryAmplitude branch) = 1) ∧
      (∑ branch, bornOnlyBinaryAmplitude branch) ≠ 1 := by
  refine ⟨bornOnlyBinaryAmplitude_bornNormalized, ?_⟩
  rw [bornOnlyBinaryAmplitude_coherentSum]
  norm_num

/-- A coherently normalized binary transition with Born mass `1/2`. -/
def coherentOnlyBinaryAmplitude (_branch : Fin 2) : ℂ := 1 / 2

theorem coherentOnlyBinaryAmplitude_coherentNormalized :
    ∑ branch, coherentOnlyBinaryAmplitude branch = 1 := by
  rw [Fin.sum_univ_two]
  norm_num [coherentOnlyBinaryAmplitude]

theorem coherentOnlyBinaryAmplitude_bornMass :
    ∑ branch, Complex.normSq (coherentOnlyBinaryAmplitude branch) = 1 / 2 := by
  rw [Fin.sum_univ_two]
  norm_num [coherentOnlyBinaryAmplitude, Complex.normSq]

theorem coherentNormalization_does_not_imply_bornNormalization :
    (∑ branch, coherentOnlyBinaryAmplitude branch = 1) ∧
      (∑ branch, Complex.normSq (coherentOnlyBinaryAmplitude branch)) ≠ 1 := by
  refine ⟨coherentOnlyBinaryAmplitude_coherentNormalized, ?_⟩
  rw [coherentOnlyBinaryAmplitude_bornMass]
  norm_num

/-- The quadrature pair lies in the nonempty intersection of the constraints. -/
def biNormalizedQuadratureAmplitude (branch : Fin 2) : ℂ :=
  if branch = 0 then (1 + Complex.I) / 2 else (1 - Complex.I) / 2

theorem biNormalizedQuadratureAmplitude_coherentNormalized :
    ∑ branch, biNormalizedQuadratureAmplitude branch = 1 := by
  rw [Fin.sum_univ_two]
  simp [biNormalizedQuadratureAmplitude]
  ring

theorem biNormalizedQuadratureAmplitude_bornNormalized :
    ∑ branch, Complex.normSq (biNormalizedQuadratureAmplitude branch) = 1 := by
  rw [Fin.sum_univ_two]
  norm_num [biNormalizedQuadratureAmplitude, Complex.normSq]

/-- Total scalar interference is coherent mass minus diagonal Born mass. -/
def finiteTotalScalarInterference {Branch : Type u} [Fintype Branch]
    (amplitude : Branch → ℂ) : ℝ :=
  Complex.normSq (∑ branch, amplitude branch) -
    ∑ branch, Complex.normSq (amplitude branch)

/-- Simultaneous coherent and Born normalization cancels the total real
off-diagonal interference while permitting individual interference terms. -/
theorem biNormalization_totalScalarInterference_eq_zero
    {Branch : Type u} [Fintype Branch] (amplitude : Branch → ℂ)
    (hCoherent : ∑ branch, amplitude branch = 1)
    (hBorn : ∑ branch, Complex.normSq (amplitude branch) = 1) :
    finiteTotalScalarInterference amplitude = 0 := by
  simp [finiteTotalScalarInterference, hCoherent, hBorn]

/-! ## 3. What coherent projectivity still requires -/

/-- A Born-normalized law enters the old rank-one projective history theory
only after coherent normalization is supplied as an additional law. -/
def RankedBornNormalizedComplexGrowthLaw.toCoherentGrowthLaw
    {Branch : ℕ → Type u} [∀ n, Fintype (Branch n)]
    (law : RankedBornNormalizedComplexGrowthLaw Branch)
    (hCoherent : ∀ (n : ℕ) (pathPrefix : RankedGrowthPath Branch n),
      ∑ branch, law.transition n pathPrefix branch = 1) :
    RankedNormalizedComplexGrowthLaw Branch where
  transition := law.transition
  normalized := hCoherent

/-- The intersection theory has both exact diagonal martingales and the old
independent-ket/bra projective decoherence functional. -/
theorem biNormalizedGrowthLaw_two_consistencies
    {Branch : ℕ → Type u} [∀ n, Fintype (Branch n)]
    (law : RankedBornNormalizedComplexGrowthLaw Branch)
    (hCoherent : ∀ (n : ℕ) (pathPrefix : RankedGrowthPath Branch n),
      ∑ branch, law.transition n pathPrefix branch = 1) :
    (∀ (n : ℕ) (event : Finset (RankedGrowthPath Branch n)),
      finiteBornEventProbability law (n + 1)
          (refineRankedGrowthEvent event) =
        finiteBornEventProbability law n event) ∧
    (∀ (n : ℕ) (event₁ event₂ :
        Finset (RankedGrowthPath Branch n)),
      growthEventDecoherence
          (finiteRankedDepthDecoherence
            (law.toCoherentGrowthLaw hCoherent) (n + 1))
          (refineRankedGrowthEvent event₁)
          (refineRankedGrowthEvent event₂) =
        growthEventDecoherence
          (finiteRankedDepthDecoherence
            (law.toCoherentGrowthLaw hCoherent) n)
          event₁ event₂) := by
  constructor
  · exact finiteBornEventProbability_refine law
  · intro n event₁ event₂
    exact finiteRankedDepthDecoherence_projective
      (law.toCoherentGrowthLaw hCoherent) n event₁ event₂

/-! ## 4. An exact martingale interpolation with retained interference -/

/-- Convex interpolation between the coherent quantum measure and its Born
diagonal.  This is a measure-level definition; no claim that a microscopic
CPTP instrument generates the interpolation is made here. -/
def partiallyDephasedCylinderMeasure
    {Branch : ℕ → Type u} [∀ n, Fintype (Branch n)]
    (law : RankedBornNormalizedComplexGrowthLaw Branch)
    (hCoherent : ∀ (n : ℕ) (pathPrefix : RankedGrowthPath Branch n),
      ∑ branch, law.transition n pathPrefix branch = 1)
    (dephasing : ℝ) (n : ℕ)
    (event : Finset (RankedGrowthPath Branch n)) : ℝ :=
  (1 - dephasing) *
      growthQuantumMeasure
        (finiteRankedDepthDecoherence
          (law.toCoherentGrowthLaw hCoherent) n) event +
    dephasing * finiteBornEventProbability law n event

/-- Unlike the earlier coherent-only dephasing experiment, the bi-normalized
interpolation is an exact cylinder martingale at every dephasing strength. -/
theorem partiallyDephasedCylinderMeasure_refine
    {Branch : ℕ → Type u} [∀ n, Fintype (Branch n)]
    (law : RankedBornNormalizedComplexGrowthLaw Branch)
    (hCoherent : ∀ (n : ℕ) (pathPrefix : RankedGrowthPath Branch n),
      ∑ branch, law.transition n pathPrefix branch = 1)
    (dephasing : ℝ) (n : ℕ)
    (event : Finset (RankedGrowthPath Branch n)) :
    partiallyDephasedCylinderMeasure law hCoherent dephasing (n + 1)
        (refineRankedGrowthEvent event) =
      partiallyDephasedCylinderMeasure law hCoherent dephasing n event := by
  have hQuantum := congrArg Complex.re
    (finiteRankedDepthDecoherence_projective
      (law.toCoherentGrowthLaw hCoherent) n event event)
  have hQuantumMeasure :
      growthQuantumMeasure
          (finiteRankedDepthDecoherence
            (law.toCoherentGrowthLaw hCoherent) (n + 1))
          (refineRankedGrowthEvent event) =
        growthQuantumMeasure
          (finiteRankedDepthDecoherence
            (law.toCoherentGrowthLaw hCoherent) n) event := by
    exact hQuantum
  unfold partiallyDephasedCylinderMeasure
  rw [hQuantumMeasure, finiteBornEventProbability_refine]

theorem partiallyDephasedCylinderMeasure_nonneg
    {Branch : ℕ → Type u} [∀ n, Fintype (Branch n)]
    (law : RankedBornNormalizedComplexGrowthLaw Branch)
    (hCoherent : ∀ (n : ℕ) (pathPrefix : RankedGrowthPath Branch n),
      ∑ branch, law.transition n pathPrefix branch = 1)
    (dephasing : ℝ) (hZero : 0 ≤ dephasing) (hOne : dephasing ≤ 1)
    (n : ℕ) (event : Finset (RankedGrowthPath Branch n)) :
    0 ≤ partiallyDephasedCylinderMeasure law hCoherent dephasing n event := by
  unfold partiallyDephasedCylinderMeasure
  apply add_nonneg
  · exact mul_nonneg (sub_nonneg.mpr hOne)
      (amplitude_growthQuantumMeasure_nonneg _ event)
  · exact mul_nonneg hZero (finiteBornEventProbability_nonneg law n event)

theorem partiallyDephasedCylinderMeasure_normalized
    {Branch : ℕ → Type u} [∀ n, Fintype (Branch n)]
    (law : RankedBornNormalizedComplexGrowthLaw Branch)
    (hCoherent : ∀ (n : ℕ) (pathPrefix : RankedGrowthPath Branch n),
      ∑ branch, law.transition n pathPrefix branch = 1)
    (dephasing : ℝ) (n : ℕ) :
    partiallyDephasedCylinderMeasure law hCoherent dephasing n Finset.univ = 1 := by
  let coherentLaw := law.toCoherentGrowthLaw hCoherent
  have hTotal := normalized_total_event
    (finiteRankedDepthDecoherence coherentLaw n)
    (finiteRankedDepthDecoherence_normalized coherentLaw n)
  have hQuantum :
      growthQuantumMeasure (finiteRankedDepthDecoherence coherentLaw n)
        Finset.univ = 1 := by
    unfold growthQuantumMeasure
    rw [hTotal]
    norm_num
  have hBorn : finiteBornEventProbability law n Finset.univ = 1 := by
    simpa [finiteBornEventProbability] using finiteBornPathWeight_sum_univ law n
  unfold partiallyDephasedCylinderMeasure
  change (1 - dephasing) *
      growthQuantumMeasure (finiteRankedDepthDecoherence coherentLaw n)
        Finset.univ +
      dephasing * finiteBornEventProbability law n Finset.univ = 1
  rw [hQuantum, hBorn]
  ring

/-- The amount left beyond the Born diagonal is exactly multiplied by
`1-dephasing`; hence every `dephasing ≠ 1` retains any nonzero interference
already present in the coherent cylinder measure. -/
theorem partiallyDephasedCylinderMeasure_interferenceResidual
    {Branch : ℕ → Type u} [∀ n, Fintype (Branch n)]
    (law : RankedBornNormalizedComplexGrowthLaw Branch)
    (hCoherent : ∀ (n : ℕ) (pathPrefix : RankedGrowthPath Branch n),
      ∑ branch, law.transition n pathPrefix branch = 1)
    (dephasing : ℝ) (n : ℕ)
    (event : Finset (RankedGrowthPath Branch n)) :
    partiallyDephasedCylinderMeasure law hCoherent dephasing n event -
        finiteBornEventProbability law n event =
      (1 - dephasing) *
        (growthQuantumMeasure
            (finiteRankedDepthDecoherence
              (law.toCoherentGrowthLaw hCoherent) n) event -
          finiteBornEventProbability law n event) := by
  unfold partiallyDephasedCylinderMeasure
  ring

/-! ## 5. The repository's harmonic intersection law -/

theorem ofReal_finiteComplexBornMass {Branch : Type u} [Fintype Branch]
    (amplitude : Branch → ℂ) :
    ((∑ branch, Complex.normSq (amplitude branch) : ℝ) : ℂ) =
      finiteComplexBornMass amplitude := by
  classical
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro branch _
  exact Complex.normSq_eq_conj_mul_self

/-- The already-formalized canonical harmonic Born-shell transition is an
actual all-rank inhabitant of the Born-normalized theory. -/
def canonicalHarmonicBornNormalizedGrowthLaw (chirality : Fin 2) :
    RankedBornNormalizedComplexGrowthLaw CausalSetGrowthBranch where
  transition :=
    (canonicalHarmonicCriticalBornShellGrowthLaw chirality).transition
  bornNormalized := by
    intro n pathPrefix
    apply Complex.ofReal_injective
    calc
      ((∑ child,
          Complex.normSq
            ((canonicalHarmonicCriticalBornShellGrowthLaw chirality).transition
              n pathPrefix child) : ℝ) : ℂ) =
          finiteComplexBornMass
            ((canonicalHarmonicCriticalBornShellGrowthLaw chirality).transition
              n pathPrefix) :=
        ofReal_finiteComplexBornMass _
      _ = 1 :=
        (canonicalHarmonicCriticalBornShell_all_rank chirality).2.1 n pathPrefix
      _ = ((1 : ℝ) : ℂ) := by norm_num

/-- The harmonic law already proves that interference-compatible scalar
cylinder projectivity and a diagonal Born martingale can coexist.  What it
does not prove is tail-event convergence or a physical record instrument. -/
theorem canonicalHarmonicBornLaw_two_consistencies (chirality : Fin 2) :
    (∀ (n : ℕ) (event :
        Finset (RankedGrowthPath CausalSetGrowthBranch n)),
      finiteBornEventProbability
          (canonicalHarmonicBornNormalizedGrowthLaw chirality) (n + 1)
          (refineRankedGrowthEvent event) =
        finiteBornEventProbability
          (canonicalHarmonicBornNormalizedGrowthLaw chirality) n event) ∧
    (∀ (n : ℕ) (event₁ event₂ :
        Finset (RankedGrowthPath CausalSetGrowthBranch n)),
      growthEventDecoherence
          (finiteRankedDepthDecoherence
            (canonicalHarmonicCriticalBornShellGrowthLaw chirality) (n + 1))
          (refineRankedGrowthEvent event₁)
          (refineRankedGrowthEvent event₂) =
        growthEventDecoherence
          (finiteRankedDepthDecoherence
            (canonicalHarmonicCriticalBornShellGrowthLaw chirality) n)
          event₁ event₂) := by
  exact biNormalizedGrowthLaw_two_consistencies
    (canonicalHarmonicBornNormalizedGrowthLaw chirality)
    (canonicalHarmonicCriticalBornShell_all_rank chirality).1

/-- The concrete harmonic law therefore supports an exact normalized
finite-cylinder martingale at every dephasing strength, including partially
coherent members. -/
theorem canonicalHarmonicPartiallyDephasedMeasure_projective
    (chirality : Fin 2) (dephasing : ℝ) (n : ℕ)
    (event : Finset (RankedGrowthPath CausalSetGrowthBranch n)) :
    partiallyDephasedCylinderMeasure
        (canonicalHarmonicBornNormalizedGrowthLaw chirality)
        (canonicalHarmonicCriticalBornShell_all_rank chirality).1
        dephasing (n + 1) (refineRankedGrowthEvent event) =
      partiallyDephasedCylinderMeasure
        (canonicalHarmonicBornNormalizedGrowthLaw chirality)
        (canonicalHarmonicCriticalBornShell_all_rank chirality).1
        dephasing n event := by
  exact partiallyDephasedCylinderMeasure_refine _ _ _ _ _

/-! ## 6. Axiom audit -/

#print axioms finiteBornPathWeight_sum_children
#print axioms finiteBornEventProbability_refine
#print axioms finiteBornPathWeight_sum_univ
#print axioms bornNormalizationFlowDefect_eq_zero
#print axioms bornNormalization_does_not_imply_coherentNormalization
#print axioms coherentNormalization_does_not_imply_bornNormalization
#print axioms biNormalizedQuadratureAmplitude_bornNormalized
#print axioms biNormalization_totalScalarInterference_eq_zero
#print axioms biNormalizedGrowthLaw_two_consistencies
#print axioms partiallyDephasedCylinderMeasure_refine
#print axioms partiallyDephasedCylinderMeasure_normalized
#print axioms partiallyDephasedCylinderMeasure_interferenceResidual
#print axioms canonicalHarmonicBornLaw_two_consistencies
#print axioms canonicalHarmonicPartiallyDephasedMeasure_projective

end

end UnifiedTheory.Audit.KFCausalBornNormalizationTransfer
