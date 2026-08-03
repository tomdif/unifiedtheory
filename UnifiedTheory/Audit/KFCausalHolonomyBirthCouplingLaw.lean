/-
  Audit/KFCausalHolonomyBirthCouplingLaw.lean

  COUPLING THE CAUSAL HOLONOMY INSTRUMENT TO UNLABELED BIRTHS

  The scalar sequential-growth law and the internal S3 instrument each obey
  coherent projectivity.  Their independent product coupling obeys the same
  law automatically, but it is Born complete only when the scalar birth
  amplitudes have unit total squared norm.

  This module proves three exact consequences.

  * At the first nontrivial causal-set parent, the existing chiral birth law
    is precisely the scalar specialization of the holonomy split.  Its
    quarter-turn phase makes the product coupling both coherently exhaustive
    and Born complete.

  * At the next harmonic three-bin parent, the normalized scalar amplitudes
    have total squared norm 3681/2113.  Therefore the naive independent
    product coupling is not trace preserving.  Higher-rank causal geometry
    and the internal carrier cannot be coupled by a blind tensor product;
    birth-dependent carrier operators or an explicit normalization channel
    are required.

  * The unique nonnegative radial correction preserving the invariant total
    and the existing zero-sum direction has scale sqrt(2113/4465).  It gives
    an explicit six-outcome CPTP, strongly positive operator-history process
    obeying both forms of cylinder projectivity.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalHolonomyBornProjectiveGrowth
import UnifiedTheory.Audit.KFCausalSetChiralityGenerationNoGo
import UnifiedTheory.Audit.KFCausalSetSourceQuantumEnsemble

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalHolonomyBirthCouplingLaw

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
open UnifiedTheory.LayerB.Kraus
open UnifiedTheory.Audit.KFCausalHolonomyBornProjectiveGrowth
open UnifiedTheory.Audit.KFOrientationCPChannelTower
open UnifiedTheory.Audit.KFOrientationGrowthDecoherence
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetTransitionEdges
open UnifiedTheory.Audit.KFCausalSetBellCausality
open UnifiedTheory.Audit.KFCausalSetChiralGrowth
open UnifiedTheory.Audit.KFCausalSetMultiplicityCorrectedRunning
open UnifiedTheory.Audit.KFCausalSetChiralityGenerationNoGo
open UnifiedTheory.Audit.KFCausalSetSourceQuantumEnsemble

/-! ## 1. The existing causal birth law is the scalar holonomy split -/

/-- The phase used by the matrix split is the negative of the raw timid-birth
phase.  With chirality zero this is exactly the concrete `-i` law. -/
def rankOneHolonomySplitPhase (chirality : Fin 2) : ℂ :=
  -chiralMaximalEventPhase chirality

/-- Scalar specialization of the first symmetric holonomy branch, obtained
by evaluating the three-cycle on the trivial character. -/
def scalarPhaseSplitFirst (phase : ℂ) : ℂ :=
  (1 + phase) / 2

/-- Scalar specialization of the complementary holonomy branch. -/
def scalarPhaseSplitSecond (phase : ℂ) : ℂ :=
  (1 - phase) / 2

/-- The actual harmonic gregarious transition at the unique one-event parent
is the scalar specialization of the first holonomy operator. -/
theorem harmonic_rankOne_gregarious_is_scalar_holonomy_split
    (chirality : Fin 2)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch 1) :
    (harmonicCriticalCausalSetGrowthLaw chirality).transition
        1 pathPrefix rankOneGregariousChild =
      scalarPhaseSplitFirst (rankOneHolonomySplitPhase chirality) := by
  rw [harmonicCritical_rankOne_transition_eq_chiral,
    chiral_rankOne_gregarious_transition,
    chiral_normalized_gregarious_amplitude]
  simp [scalarPhaseSplitFirst, rankOneHolonomySplitPhase]
  ring

/-- The actual harmonic timid transition is the scalar specialization of the
second holonomy operator. -/
theorem harmonic_rankOne_timid_is_scalar_holonomy_split
    (chirality : Fin 2)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch 1) :
    (harmonicCriticalCausalSetGrowthLaw chirality).transition
        1 pathPrefix rankOneTimidChild =
      scalarPhaseSplitSecond (rankOneHolonomySplitPhase chirality) := by
  rw [harmonicCritical_rankOne_transition_eq_chiral,
    chiral_rankOne_timid_transition,
    chiral_normalized_timid_amplitude]
  simp [scalarPhaseSplitSecond, rankOneHolonomySplitPhase]

/-- The lifted gregarious birth operator on the native three-sheet carrier. -/
def rankOneGregariousHolonomyOperator (chirality : Fin 2) : SquareMatrix 3 :=
  phaseSplitFirstKraus (rankOneHolonomySplitPhase chirality)

/-- The lifted timid birth operator on the native three-sheet carrier. -/
def rankOneTimidHolonomyOperator (chirality : Fin 2) : SquareMatrix 3 :=
  phaseSplitSecondKraus (rankOneHolonomySplitPhase chirality)

/-- The representation lift preserves coherent causal exhaustivity. -/
theorem rankOneHolonomyOperators_sum_eq_one (chirality : Fin 2) :
    rankOneGregariousHolonomyOperator chirality +
        rankOneTimidHolonomyOperator chirality =
      (1 : SquareMatrix 3) := by
  exact phaseSplit_sum_eq_one (rankOneHolonomySplitPhase chirality)

/-- The causal quarter turn makes the representation lift Born complete. -/
theorem rankOneHolonomyOperators_born_complete (chirality : Fin 2) :
    (rankOneGregariousHolonomyOperator chirality)ᴴ *
          rankOneGregariousHolonomyOperator chirality +
        (rankOneTimidHolonomyOperator chirality)ᴴ *
          rankOneTimidHolonomyOperator chirality =
      (1 : SquareMatrix 3) := by
  rw [rankOneGregariousHolonomyOperator,
    rankOneTimidHolonomyOperator, phaseSplit_complete_iff_unitNorm]
  fin_cases chirality <;>
    norm_num [rankOneHolonomySplitPhase, chiralMaximalEventPhase,
      Complex.I_mul_I]

/-- The two actual causal children therefore define a CPTP instrument without
adding a new phase or a fitted normalization. -/
def rankOneCausalBirthHolonomyInstrument (chirality : Fin 2) :
    KrausRepresentation 3 3 2 where
  K := fun outcome => if outcome = 0 then
    rankOneGregariousHolonomyOperator chirality
  else
    rankOneTimidHolonomyOperator chirality
  complete := by
    rw [Fin.sum_univ_two]
    simpa using rankOneHolonomyOperators_born_complete chirality

theorem rankOneCausalBirthHolonomyInstrument_isCPTP (chirality : Fin 2) :
    IsCPTP (rankOneCausalBirthHolonomyInstrument chirality).toLinearMap :=
  kraus_isCPTP _

/-! ## 2. Compatibility law for an independent scalar/internal coupling -/

/-- Blind tensor-product coupling of a scalar causal birth amplitude to an
independent internal holonomy record. -/
def independentBirthHolonomyOperator {n : ℕ}
    (amplitude : Fin n → ℂ) (branch : Fin n × Fin 2) : SquareMatrix 3 :=
  amplitude branch.1 • causalHolonomyKrausOperator branch.2

theorem independentBirthHolonomyOperator_record_sum {n : ℕ}
    (amplitude : Fin n → ℂ) (birth : Fin n) :
    (∑ record : Fin 2,
      independentBirthHolonomyOperator amplitude (birth, record)) =
      amplitude birth • (1 : SquareMatrix 3) := by
  unfold independentBirthHolonomyOperator
  simp only
  rw [← Finset.smul_sum, causalHolonomyKrausOperator_sum_eq_one]

/-- Coherent projectivity of the product coupling asks only for the scalar
amplitudes to sum to one, exactly as in sequential growth. -/
theorem independentBirthHolonomyOperator_coherent_sum {n : ℕ}
    (amplitude : Fin n → ℂ) :
    (∑ branch : Fin n × Fin 2,
      independentBirthHolonomyOperator amplitude branch) =
      (∑ birth, amplitude birth) • (1 : SquareMatrix 3) := by
  rw [Fintype.sum_prod_type]
  simp_rw [independentBirthHolonomyOperator_record_sum]
  rw [Finset.sum_smul]

set_option maxHeartbeats 4000000 in
/-- For one scalar birth amplitude, summing over the internal record produces
its squared norm times identity. -/
theorem independentBirthHolonomyOperator_record_born_sum
    (amplitude : ℂ) :
    (∑ record : Fin 2,
      (amplitude • causalHolonomyKrausOperator record)ᴴ *
        (amplitude • causalHolonomyKrausOperator record)) =
      (star amplitude * amplitude) • (1 : SquareMatrix 3) := by
  rw [Fin.sum_univ_two]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [causalHolonomyKrausOperator, identityRecordKraus,
      threeCycleRecordKraus, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_three]
  all_goals ring_nf
  all_goals norm_num [Complex.I_mul_I, map_ofNat]
  all_goals ring

/-- **Scalar/internal compatibility law.**  The Born normalization of the
independent product coupling is the scalar total squared norm. -/
theorem independentBirthHolonomyOperator_born_sum {n : ℕ}
    (amplitude : Fin n → ℂ) :
    (∑ branch : Fin n × Fin 2,
      (independentBirthHolonomyOperator amplitude branch)ᴴ *
        independentBirthHolonomyOperator amplitude branch) =
      (∑ birth, star (amplitude birth) * amplitude birth) •
        (1 : SquareMatrix 3) := by
  rw [Fintype.sum_prod_type]
  simp_rw [independentBirthHolonomyOperator,
    independentBirthHolonomyOperator_record_born_sum]
  rw [Finset.sum_smul]

/-- Positive real scalar weights cannot be simultaneously nontrivial,
coherently normalized, and Born normalized in a two-branch product coupling.
They collapse to a deterministic endpoint. -/
theorem nonnegative_real_twoBranch_coherent_born_forces_deterministic
    (first second : ℝ) (hFirst : 0 ≤ first) (hSecond : 0 ≤ second)
    (hCoherent : first + second = 1)
    (hBorn : first ^ 2 + second ^ 2 = 1) :
    (first = 0 ∧ second = 1) ∨ (first = 1 ∧ second = 0) := by
  have hProduct : first * second = 0 := by nlinarith [sq_nonneg (first + second)]
  rcases mul_eq_zero.mp hProduct with hZero | hZero
  · left
    exact ⟨hZero, by linarith⟩
  · right
    exact ⟨by linarith, hZero⟩

/-- In particular, the nontrivial uniform classical split is coherently
normalized but misses Born completeness by an exact factor of two. -/
theorem uniform_twoBranch_product_coupling_not_born_complete :
    (((1 / 2 : ℂ) • (1 : SquareMatrix 3)) ≠
      (1 : SquareMatrix 3)) := by
  intro h
  have h00 := congr_fun (congr_fun h (0 : Fin 3)) (0 : Fin 3)
  norm_num at h00

/-! ## 3. Exact higher-rank obstruction from the harmonic causal law -/

/-- The actual normalized harmonic amplitudes of the first three-bin parent,
viewed as the scalar side of the independent coupling. -/
def harmonicAntichainTwoBirthAmplitude (chirality : Fin 2) : Fin 3 → ℂ :=
  harmonicAntichainTwoNormalizedSourceBinAmplitude chirality

/-- Coherent sequential-growth normalization survives the product coupling. -/
theorem harmonicAntichainTwo_product_coherently_exhaustive
    (chirality : Fin 2) :
    (∑ branch : Fin 3 × Fin 2,
      independentBirthHolonomyOperator
        (harmonicAntichainTwoBirthAmplitude chirality) branch) =
      (1 : SquareMatrix 3) := by
  rw [independentBirthHolonomyOperator_coherent_sum,
    harmonicAntichainTwoBirthAmplitude,
    harmonicAntichainTwoNormalizedSourceBinAmplitude_sum]
  simp

/-- The scalar squared norm at the first three-bin harmonic parent is not one
but `3681/2113`. -/
theorem harmonicAntichainTwo_scalarBornMass_exact (chirality : Fin 2) :
    (∑ birth,
      star (harmonicAntichainTwoBirthAmplitude chirality birth) *
        harmonicAntichainTwoBirthAmplitude chirality birth) =
      ((3681 / 2113 : ℝ) : ℂ) := by
  have hNorm (z : ℂ) :
      star z * z = (Complex.normSq z : ℂ) := by
    apply Complex.ext <;>
      simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  unfold harmonicAntichainTwoBirthAmplitude
  simp_rw [hNorm]
  rw [← Complex.ofReal_sum]
  change ((∑ birth,
      harmonicAntichainTwoSourceBinQuantumMeasure chirality birth : ℝ) : ℂ) = _
  rw [harmonicAntichainTwoSourceBinQuantumMeasure_sum]

/-- **Higher-rank tensor-product no-go.**  The naive product of the actual
harmonic birth amplitudes with the independently normalized holonomy
instrument is coherently projective but not Born complete. -/
theorem harmonicAntichainTwo_independent_product_not_born_complete
    (chirality : Fin 2) :
    (∑ branch : Fin 3 × Fin 2,
      (independentBirthHolonomyOperator
        (harmonicAntichainTwoBirthAmplitude chirality) branch)ᴴ *
      independentBirthHolonomyOperator
        (harmonicAntichainTwoBirthAmplitude chirality) branch) ≠
      (1 : SquareMatrix 3) := by
  rw [independentBirthHolonomyOperator_born_sum,
    harmonicAntichainTwo_scalarBornMass_exact]
  intro h
  have h00 := congr_fun (congr_fun h (0 : Fin 3)) (0 : Fin 3)
  norm_num at h00

/-! ## 4. The forced replacement: bi-normalized operator growth -/

/-- A finite operator-valued growth law satisfying both notions of
consistency used in this repository.  `bornComplete` is trace preservation;
`coherentlyExhaustive` is independent ket/bra cylinder projectivity. -/
structure ProjectiveBornOperatorLaw (dimension outcomes : ℕ) where
  operator : Fin outcomes → SquareMatrix dimension
  bornComplete :
    (∑ outcome,
      (operator outcome)ᴴ * operator outcome) =
        (1 : SquareMatrix dimension)
  coherentlyExhaustive :
    (∑ outcome, operator outcome) =
      (1 : SquareMatrix dimension)

/-- Every bi-normalized operator law is a genuine Kraus instrument. -/
def ProjectiveBornOperatorLaw.toKraus {dimension outcomes : ℕ}
    (law : ProjectiveBornOperatorLaw dimension outcomes) :
    KrausRepresentation dimension dimension outcomes where
  K := law.operator
  complete := law.bornComplete

/-- Total operator interference: coherent norm minus the incoherent Born
sum.  Expanding the first term makes this the sum of all off-diagonal
operator products. -/
def totalOperatorInterference {dimension outcomes : ℕ}
    (operator : Fin outcomes → SquareMatrix dimension) :
    SquareMatrix dimension :=
  ((∑ outcome, operator outcome)ᴴ *
      (∑ outcome, operator outcome)) -
    ∑ outcome, (operator outcome)ᴴ * operator outcome

/-- **Operator interference conservation law.**  Simultaneous Born and
coherent normalization forces the total off-diagonal operator interference
to cancel exactly. -/
theorem ProjectiveBornOperatorLaw.totalInterference_eq_zero
    {dimension outcomes : ℕ}
    (law : ProjectiveBornOperatorLaw dimension outcomes) :
    totalOperatorInterference law.operator = 0 := by
  simp [totalOperatorInterference, law.coherentlyExhaustive,
    law.bornComplete]

/-- The two actual rank-one causal births supply the first nontrivial
bi-normalized operator law. -/
def rankOneCausalProjectiveBornLaw (chirality : Fin 2) :
    ProjectiveBornOperatorLaw 3 2 where
  operator := fun outcome => if outcome = 0 then
    rankOneGregariousHolonomyOperator chirality
  else
    rankOneTimidHolonomyOperator chirality
  bornComplete := by
    rw [Fin.sum_univ_two]
    simpa using rankOneHolonomyOperators_born_complete chirality
  coherentlyExhaustive := by
    rw [Fin.sum_univ_two]
    simpa using rankOneHolonomyOperators_sum_eq_one chirality

theorem rankOneCausal_totalOperatorInterference_zero (chirality : Fin 2) :
    totalOperatorInterference
      (rankOneCausalProjectiveBornLaw chirality).operator = 0 :=
  (rankOneCausalProjectiveBornLaw chirality).totalInterference_eq_zero

/-- A single global complex rescaling of the naive harmonic product. -/
def globallyRescaledHarmonicProductOperator
    (chirality : Fin 2) (scale : ℂ) (branch : Fin 3 × Fin 2) :
    SquareMatrix 3 :=
  scale • independentBirthHolonomyOperator
    (harmonicAntichainTwoBirthAmplitude chirality) branch

/-- Coherent normalization fixes the attempted global repair factor to one. -/
theorem globallyRescaledHarmonicProduct_coherent_forces_scale_one
    (chirality : Fin 2) (scale : ℂ)
    (hCoherent :
      (∑ branch : Fin 3 × Fin 2,
        globallyRescaledHarmonicProductOperator chirality scale branch) =
        (1 : SquareMatrix 3)) :
    scale = 1 := by
  have hSum :
      (∑ branch : Fin 3 × Fin 2,
        globallyRescaledHarmonicProductOperator chirality scale branch) =
        scale • (1 : SquareMatrix 3) := by
    unfold globallyRescaledHarmonicProductOperator
    rw [← Finset.smul_sum,
      harmonicAntichainTwo_product_coherently_exhaustive]
  rw [hSum] at hCoherent
  have h00 := congr_fun (congr_fun hCoherent (0 : Fin 3)) (0 : Fin 3)
  simpa using h00

/-- **No scalar repair theorem.**  No complex global normalization can make
the naive higher-rank product coupling both coherently projective and Born
complete.  The required correction must depend on the birth or act
nontrivially on the carrier. -/
theorem harmonicAntichainTwo_no_global_scalar_product_repair
    (chirality : Fin 2) :
    ¬∃ scale : ℂ,
      (∑ branch : Fin 3 × Fin 2,
        globallyRescaledHarmonicProductOperator chirality scale branch) =
          (1 : SquareMatrix 3)
      ∧ (∑ branch : Fin 3 × Fin 2,
        (globallyRescaledHarmonicProductOperator
          chirality scale branch)ᴴ *
        globallyRescaledHarmonicProductOperator
          chirality scale branch) =
          (1 : SquareMatrix 3) := by
  rintro ⟨scale, hCoherent, hBorn⟩
  have hScale :=
    globallyRescaledHarmonicProduct_coherent_forces_scale_one
      chirality scale hCoherent
  subst scale
  apply harmonicAntichainTwo_independent_product_not_born_complete chirality
  simpa [globallyRescaledHarmonicProductOperator] using hBorn

/-! ## 5. Canonical zero-sum Born-shell correction -/

/-- Remove the invariant scalar component of a coherently normalized
three-branch amplitude. -/
def centeredThreeAmplitude (amplitude : Fin 3 → ℂ) (branch : Fin 3) : ℂ :=
  amplitude branch - 1 / 3

/-- Preserve the invariant component and radially rescale only the standard
zero-sum `S3` component. -/
def threeAmplitudeBornShellCorrection
    (scale : ℂ) (amplitude : Fin 3 → ℂ) (branch : Fin 3) : ℂ :=
  1 / 3 + scale * centeredThreeAmplitude amplitude branch

theorem centeredThreeAmplitude_sum_zero
    (amplitude : Fin 3 → ℂ)
    (hCoherent : ∑ branch, amplitude branch = 1) :
    ∑ branch, centeredThreeAmplitude amplitude branch = 0 := by
  rw [Fin.sum_univ_three] at hCoherent ⊢
  simp only [centeredThreeAmplitude]
  linear_combination hCoherent

/-- The correction leaves the coherent total exactly unchanged for every
radial scale. -/
theorem threeAmplitudeBornShellCorrection_sum_one
    (scale : ℂ) (amplitude : Fin 3 → ℂ)
    (hCoherent : ∑ branch, amplitude branch = 1) :
    ∑ branch, threeAmplitudeBornShellCorrection scale amplitude branch = 1 := by
  rw [Fin.sum_univ_three]
  have hCentered := centeredThreeAmplitude_sum_zero amplitude hCoherent
  rw [Fin.sum_univ_three] at hCentered
  simp only [threeAmplitudeBornShellCorrection]
  linear_combination scale * hCentered

/-- Orthogonal Pythagoras for the trivial plus zero-sum decomposition. -/
theorem centeredThreeAmplitude_bornMass
    (amplitude : Fin 3 → ℂ) (mass : ℂ)
    (hCoherent : ∑ branch, amplitude branch = 1)
    (hMass : ∑ branch, star (amplitude branch) * amplitude branch = mass) :
    ∑ branch,
        star (centeredThreeAmplitude amplitude branch) *
          centeredThreeAmplitude amplitude branch =
      mass - 1 / 3 := by
  rw [Fin.sum_univ_three] at hCoherent hMass ⊢
  have hStar :
      star (amplitude 0) + star (amplitude 1) + star (amplitude 2) = 1 := by
    simpa only [star_add, star_one] using congrArg star hCoherent
  calc
    star (centeredThreeAmplitude amplitude 0) *
          centeredThreeAmplitude amplitude 0 +
        star (centeredThreeAmplitude amplitude 1) *
          centeredThreeAmplitude amplitude 1 +
        star (centeredThreeAmplitude amplitude 2) *
          centeredThreeAmplitude amplitude 2 =
        (star (amplitude 0) * amplitude 0 +
          star (amplitude 1) * amplitude 1 +
          star (amplitude 2) * amplitude 2) -
        (1 / 3) *
          (star (amplitude 0) + star (amplitude 1) + star (amplitude 2)) -
        (1 / 3) * (amplitude 0 + amplitude 1 + amplitude 2) + 1 / 3 := by
      simp only [centeredThreeAmplitude, star_sub, star_div₀, star_one,
        star_ofNat]
      ring
    _ = mass - 1 / 3 := by rw [hMass, hStar, hCoherent]; ring

/-- **Born-shell theorem.**  If the radial scale sends the zero-sum norm to
`2/3`, the corrected amplitude simultaneously has coherent sum one and Born
mass one. -/
theorem threeAmplitudeBornShellCorrection_bornMass_one
    (scale : ℂ) (amplitude : Fin 3 → ℂ) (mass : ℂ)
    (hCoherent : ∑ branch, amplitude branch = 1)
    (hMass : ∑ branch, star (amplitude branch) * amplitude branch = mass)
    (hScale : star scale * scale * (mass - 1 / 3) = 2 / 3) :
    ∑ branch,
        star (threeAmplitudeBornShellCorrection scale amplitude branch) *
          threeAmplitudeBornShellCorrection scale amplitude branch = 1 := by
  have hCentered := centeredThreeAmplitude_sum_zero amplitude hCoherent
  have hCenteredMass :=
    centeredThreeAmplitude_bornMass amplitude mass hCoherent hMass
  rw [Fin.sum_univ_three] at hCentered hCenteredMass ⊢
  have hStarCentered :
      star (centeredThreeAmplitude amplitude 0) +
          star (centeredThreeAmplitude amplitude 1) +
          star (centeredThreeAmplitude amplitude 2) = 0 := by
    simpa only [star_add, star_zero] using congrArg star hCentered
  calc
    star (threeAmplitudeBornShellCorrection scale amplitude 0) *
          threeAmplitudeBornShellCorrection scale amplitude 0 +
        star (threeAmplitudeBornShellCorrection scale amplitude 1) *
          threeAmplitudeBornShellCorrection scale amplitude 1 +
        star (threeAmplitudeBornShellCorrection scale amplitude 2) *
          threeAmplitudeBornShellCorrection scale amplitude 2 =
        1 / 3 +
          (scale / 3) *
            (centeredThreeAmplitude amplitude 0 +
              centeredThreeAmplitude amplitude 1 +
              centeredThreeAmplitude amplitude 2) +
          (star scale / 3) *
            (star (centeredThreeAmplitude amplitude 0) +
              star (centeredThreeAmplitude amplitude 1) +
              star (centeredThreeAmplitude amplitude 2)) +
          (star scale * scale) *
            (star (centeredThreeAmplitude amplitude 0) *
                centeredThreeAmplitude amplitude 0 +
              star (centeredThreeAmplitude amplitude 1) *
                centeredThreeAmplitude amplitude 1 +
              star (centeredThreeAmplitude amplitude 2) *
                centeredThreeAmplitude amplitude 2) := by
      simp only [threeAmplitudeBornShellCorrection, star_add,
        StarMul.star_mul, star_div₀, star_one, star_ofNat]
      ring
    _ = 1 := by
      rw [hCentered, hStarCentered, hCenteredMass]
      rw [hScale]
      ring

/-- Exact radial scale selected by the first harmonic three-bin Born excess. -/
def harmonicAntichainTwoBornShellScale : ℂ :=
  (Real.sqrt ((2113 : ℝ) / 4465) : ℝ)

theorem harmonicAntichainTwoBornShellScale_normSq :
    star harmonicAntichainTwoBornShellScale *
        harmonicAntichainTwoBornShellScale =
      ((2113 / 4465 : ℝ) : ℂ) := by
  have hNonnegative : (0 : ℝ) ≤ 2113 / 4465 := by norm_num
  unfold harmonicAntichainTwoBornShellScale
  rw [show star (((Real.sqrt ((2113 : ℝ) / 4465) : ℝ) : ℂ)) =
      (((Real.sqrt ((2113 : ℝ) / 4465) : ℝ) : ℂ)) by simp]
  rw [← Complex.ofReal_mul]
  exact_mod_cast (show
    Real.sqrt ((2113 : ℝ) / 4465) *
        Real.sqrt ((2113 : ℝ) / 4465) = 2113 / 4465 by
      simpa [pow_two] using Real.sq_sqrt hNonnegative)

/-- The displayed scale is the unique nonnegative radial factor that repairs
the exact harmonic three-bin Born mass while preserving its zero-sum ray. -/
theorem harmonicAntichainTwoBornShellScale_unique
    (scale : ℝ) (hNonnegative : 0 ≤ scale)
    (hRepair :
      scale ^ 2 * ((3681 / 2113 : ℝ) - 1 / 3) = 2 / 3) :
    scale = Real.sqrt ((2113 : ℝ) / 4465) := by
  have hScaleSq : scale ^ 2 = (2113 : ℝ) / 4465 := by
    norm_num at hRepair ⊢
    nlinarith
  have hRadicand : (0 : ℝ) ≤ 2113 / 4465 := by norm_num
  have hSqrtSq := Real.sq_sqrt hRadicand
  have hSqrtNonnegative := Real.sqrt_nonneg ((2113 : ℝ) / 4465)
  nlinarith

/-- Harmonic causal amplitudes corrected only in their intrinsic zero-sum
sheet component. -/
def harmonicAntichainTwoBornShellAmplitude
    (chirality : Fin 2) : Fin 3 → ℂ :=
  threeAmplitudeBornShellCorrection
    harmonicAntichainTwoBornShellScale
    (harmonicAntichainTwoBirthAmplitude chirality)

theorem harmonicAntichainTwoBornShellAmplitude_sum_one
    (chirality : Fin 2) :
    ∑ branch, harmonicAntichainTwoBornShellAmplitude chirality branch = 1 := by
  exact threeAmplitudeBornShellCorrection_sum_one _ _
    (harmonicAntichainTwoNormalizedSourceBinAmplitude_sum chirality)

theorem harmonicAntichainTwoBornShellAmplitude_bornMass_one
    (chirality : Fin 2) :
    ∑ branch,
        star (harmonicAntichainTwoBornShellAmplitude chirality branch) *
          harmonicAntichainTwoBornShellAmplitude chirality branch = 1 := by
  apply threeAmplitudeBornShellCorrection_bornMass_one
      harmonicAntichainTwoBornShellScale
      (harmonicAntichainTwoBirthAmplitude chirality)
      (((3681 / 2113 : ℝ) : ℂ))
    (harmonicAntichainTwoNormalizedSourceBinAmplitude_sum chirality)
    (harmonicAntichainTwo_scalarBornMass_exact chirality)
  rw [harmonicAntichainTwoBornShellScale_normSq]
  norm_num

/-- The corrected scalar law can now be coupled independently to the
holonomy instrument while preserving coherent projectivity. -/
theorem harmonicAntichainTwoBornShell_product_coherently_exhaustive
    (chirality : Fin 2) :
    (∑ branch : Fin 3 × Fin 2,
      independentBirthHolonomyOperator
        (harmonicAntichainTwoBornShellAmplitude chirality) branch) =
      (1 : SquareMatrix 3) := by
  rw [independentBirthHolonomyOperator_coherent_sum,
    harmonicAntichainTwoBornShellAmplitude_sum_one]
  simp

/-- The same corrected product is exactly Born complete. -/
theorem harmonicAntichainTwoBornShell_product_born_complete
    (chirality : Fin 2) :
    (∑ branch : Fin 3 × Fin 2,
      (independentBirthHolonomyOperator
        (harmonicAntichainTwoBornShellAmplitude chirality) branch)ᴴ *
      independentBirthHolonomyOperator
        (harmonicAntichainTwoBornShellAmplitude chirality) branch) =
      (1 : SquareMatrix 3) := by
  rw [independentBirthHolonomyOperator_born_sum,
    harmonicAntichainTwoBornShellAmplitude_bornMass_one]
  simp

/-! ## 6. All-depth promotion of the corrected harmonic coupling -/

/-- Reindex the three causal bins and two internal records as six finite
Kraus outcomes. -/
def harmonicBornShellHolonomyKrausOperator
    (chirality : Fin 2) (outcome : Fin 6) : SquareMatrix 3 :=
  independentBirthHolonomyOperator
    (harmonicAntichainTwoBornShellAmplitude chirality)
    (finProdFinEquiv.symm outcome)

theorem harmonicBornShellHolonomyKrausOperator_sum_eq_one
    (chirality : Fin 2) :
    (∑ outcome : Fin 6,
      harmonicBornShellHolonomyKrausOperator chirality outcome) =
      (1 : SquareMatrix 3) := by
  have hReindex :
      (∑ outcome : Fin 6,
        harmonicBornShellHolonomyKrausOperator chirality outcome) =
        ∑ branch : Fin 3 × Fin 2,
          independentBirthHolonomyOperator
            (harmonicAntichainTwoBornShellAmplitude chirality) branch :=
    by
      simpa [harmonicBornShellHolonomyKrausOperator] using
        (Equiv.sum_comp finProdFinEquiv.symm
          (fun branch : Fin 3 × Fin 2 =>
            independentBirthHolonomyOperator
              (harmonicAntichainTwoBornShellAmplitude chirality) branch))
  rw [hReindex,
    harmonicAntichainTwoBornShell_product_coherently_exhaustive]

theorem harmonicBornShellHolonomyKrausOperator_complete
    (chirality : Fin 2) :
    (∑ outcome : Fin 6,
      (harmonicBornShellHolonomyKrausOperator chirality outcome)ᴴ *
        harmonicBornShellHolonomyKrausOperator chirality outcome) =
      (1 : SquareMatrix 3) := by
  have hReindex :
      (∑ outcome : Fin 6,
        (harmonicBornShellHolonomyKrausOperator chirality outcome)ᴴ *
          harmonicBornShellHolonomyKrausOperator chirality outcome) =
        ∑ branch : Fin 3 × Fin 2,
          (independentBirthHolonomyOperator
            (harmonicAntichainTwoBornShellAmplitude chirality) branch)ᴴ *
          independentBirthHolonomyOperator
            (harmonicAntichainTwoBornShellAmplitude chirality) branch :=
    by
      simpa [harmonicBornShellHolonomyKrausOperator] using
        (Equiv.sum_comp finProdFinEquiv.symm
          (fun branch : Fin 3 × Fin 2 =>
            (independentBirthHolonomyOperator
              (harmonicAntichainTwoBornShellAmplitude chirality) branch)ᴴ *
            independentBirthHolonomyOperator
              (harmonicAntichainTwoBornShellAmplitude chirality) branch))
  rw [hReindex, harmonicAntichainTwoBornShell_product_born_complete]

/-- The corrected causal-bin/internal-record process is a genuine quantum
instrument. -/
def harmonicBornShellHolonomyInstrument (chirality : Fin 2) :
    KrausRepresentation 3 3 6 where
  K := harmonicBornShellHolonomyKrausOperator chirality
  complete := harmonicBornShellHolonomyKrausOperator_complete chirality

theorem harmonicBornShellHolonomyInstrument_isCPTP (chirality : Fin 2) :
    IsCPTP (harmonicBornShellHolonomyInstrument chirality).toLinearMap :=
  kraus_isCPTP _

/-- All-depth operator-history kernel of the corrected harmonic coupling. -/
def harmonicBornShellHolonomyKernel (chirality : Fin 2) :
    GrowthDecoherenceFunctional (List (Fin 6)) :=
  recordOperatorKernel (harmonicBornShellHolonomyInstrument chirality)
    zeroSumSheetDensityRoot

theorem harmonicBornShellHolonomyKernel_stronglyPositive
    (chirality : Fin 2) :
    IsStronglyPositiveGrowthFunctional
      (harmonicBornShellHolonomyKernel chirality) :=
  recordOperatorKernel_stronglyPositive _ _

theorem harmonicBornShellHolonomyKernel_projective
    (chirality : Fin 2) (first second : List (Fin 6)) :
    (∑ outcome : Fin 6,
      harmonicBornShellHolonomyKernel chirality
          (outcome :: first) (outcome :: second)) =
      harmonicBornShellHolonomyKernel chirality first second :=
  recordOperatorKernel_sum_cons _ _ _ _

theorem harmonicBornShellHolonomyKernel_exhaustively_projective
    (chirality : Fin 2) (first second : List (Fin 6)) :
    (∑ left : Fin 6, ∑ right : Fin 6,
      harmonicBornShellHolonomyKernel chirality
          (left :: first) (right :: second)) =
      harmonicBornShellHolonomyKernel chirality first second :=
  recordOperatorKernel_double_sum_cons_of_sum_eq_one _ _
    (harmonicBornShellHolonomyKrausOperator_sum_eq_one chirality) _ _

theorem harmonicBornShellHolonomyKernel_root_normalized
    (chirality : Fin 2) :
    harmonicBornShellHolonomyKernel chirality [] [] = 1 := by
  change recordOperatorKernel
      (harmonicBornShellHolonomyInstrument chirality)
      zeroSumSheetDensityRoot [] [] = 1
  have hRoot := causalHolonomyBornKernel_root_normalized
  change recordOperatorKernel causalHolonomyInstrument
      zeroSumSheetDensityRoot [] [] = 1 at hRoot
  simpa [recordOperatorKernel, recordOperatorAmplitude,
    recordPathOperator] using hRoot

/-- The corrected six-outcome dynamics has every finite consistency property
required of the proposed microscopic law. -/
theorem harmonicBornShellHolonomy_projective_growth_complete
    (chirality : Fin 2) :
    IsCPTP (harmonicBornShellHolonomyInstrument chirality).toLinearMap
      ∧ IsStronglyPositiveGrowthFunctional
          (harmonicBornShellHolonomyKernel chirality)
      ∧ harmonicBornShellHolonomyKernel chirality [] [] = 1
      ∧ (∀ first second : List (Fin 6),
          (∑ outcome : Fin 6,
            harmonicBornShellHolonomyKernel chirality
              (outcome :: first) (outcome :: second)) =
            harmonicBornShellHolonomyKernel chirality first second)
      ∧ (∀ first second : List (Fin 6),
          (∑ left : Fin 6, ∑ right : Fin 6,
            harmonicBornShellHolonomyKernel chirality
              (left :: first) (right :: second)) =
            harmonicBornShellHolonomyKernel chirality first second) := by
  exact ⟨harmonicBornShellHolonomyInstrument_isCPTP _,
    harmonicBornShellHolonomyKernel_stronglyPositive _,
    harmonicBornShellHolonomyKernel_root_normalized _,
    harmonicBornShellHolonomyKernel_projective _,
    harmonicBornShellHolonomyKernel_exhaustively_projective _⟩

/-- Capstone: the first causal branch admits the canonical holonomy lift; the
first genuinely three-way harmonic parent rules out blind product coupling
and every global scalar repair; the unique radial correction of its zero-sum
component then produces a normalized, strongly positive, projective
six-outcome operator process. -/
theorem causalHolonomyBirthCoupling_capstone (chirality : Fin 2)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch 1) :
    (harmonicCriticalCausalSetGrowthLaw chirality).transition
        1 pathPrefix rankOneGregariousChild =
          scalarPhaseSplitFirst (rankOneHolonomySplitPhase chirality)
      ∧ (harmonicCriticalCausalSetGrowthLaw chirality).transition
        1 pathPrefix rankOneTimidChild =
          scalarPhaseSplitSecond (rankOneHolonomySplitPhase chirality)
      ∧ (rankOneGregariousHolonomyOperator chirality)ᴴ *
            rankOneGregariousHolonomyOperator chirality +
          (rankOneTimidHolonomyOperator chirality)ᴴ *
            rankOneTimidHolonomyOperator chirality =
          (1 : SquareMatrix 3)
      ∧ (∑ branch : Fin 3 × Fin 2,
          independentBirthHolonomyOperator
            (harmonicAntichainTwoBirthAmplitude chirality) branch) =
          (1 : SquareMatrix 3)
      ∧ (∑ branch : Fin 3 × Fin 2,
          (independentBirthHolonomyOperator
            (harmonicAntichainTwoBirthAmplitude chirality) branch)ᴴ *
          independentBirthHolonomyOperator
            (harmonicAntichainTwoBirthAmplitude chirality) branch) ≠
          (1 : SquareMatrix 3)
      ∧ (¬∃ scale : ℂ,
          (∑ branch : Fin 3 × Fin 2,
            globallyRescaledHarmonicProductOperator
              chirality scale branch) = (1 : SquareMatrix 3)
          ∧ (∑ branch : Fin 3 × Fin 2,
            (globallyRescaledHarmonicProductOperator
              chirality scale branch)ᴴ *
            globallyRescaledHarmonicProductOperator
              chirality scale branch) = (1 : SquareMatrix 3))
      ∧ (IsCPTP
            (harmonicBornShellHolonomyInstrument chirality).toLinearMap
        ∧ IsStronglyPositiveGrowthFunctional
            (harmonicBornShellHolonomyKernel chirality)
        ∧ harmonicBornShellHolonomyKernel chirality [] [] = 1
        ∧ (∀ first second : List (Fin 6),
            (∑ outcome : Fin 6,
              harmonicBornShellHolonomyKernel chirality
                (outcome :: first) (outcome :: second)) =
              harmonicBornShellHolonomyKernel chirality first second)
        ∧ (∀ first second : List (Fin 6),
            (∑ left : Fin 6, ∑ right : Fin 6,
              harmonicBornShellHolonomyKernel chirality
                (left :: first) (right :: second)) =
              harmonicBornShellHolonomyKernel chirality first second)) := by
  exact ⟨harmonic_rankOne_gregarious_is_scalar_holonomy_split _ _,
    harmonic_rankOne_timid_is_scalar_holonomy_split _ _,
    rankOneHolonomyOperators_born_complete _,
    harmonicAntichainTwo_product_coherently_exhaustive _,
    harmonicAntichainTwo_independent_product_not_born_complete _,
    harmonicAntichainTwo_no_global_scalar_product_repair _,
    harmonicBornShellHolonomy_projective_growth_complete _⟩

#print axioms harmonic_rankOne_gregarious_is_scalar_holonomy_split
#print axioms rankOneHolonomyOperators_born_complete
#print axioms independentBirthHolonomyOperator_born_sum
#print axioms nonnegative_real_twoBranch_coherent_born_forces_deterministic
#print axioms harmonicAntichainTwo_scalarBornMass_exact
#print axioms harmonicAntichainTwo_independent_product_not_born_complete
#print axioms ProjectiveBornOperatorLaw.totalInterference_eq_zero
#print axioms rankOneCausal_totalOperatorInterference_zero
#print axioms harmonicAntichainTwo_no_global_scalar_product_repair
#print axioms threeAmplitudeBornShellCorrection_bornMass_one
#print axioms harmonicAntichainTwoBornShellScale_unique
#print axioms harmonicAntichainTwoBornShellAmplitude_bornMass_one
#print axioms harmonicBornShellHolonomy_projective_growth_complete
#print axioms causalHolonomyBirthCoupling_capstone

end

end UnifiedTheory.Audit.KFCausalHolonomyBirthCouplingLaw
