/-
  Audit/KFCausalSetFutureFrequencyHandedness.lean

  CLOCK/BIRTH HANDEDNESS AND THE REFLECTION TRIPWIRE

  The preceding chirality-generation no-go is exact: a reflection-fixed
  vacuum cannot choose between the two phases `+i` and `-i`.  This file tests
  a proposed clock mechanism and then runs it through that obstruction.  The
  result is a reflection doublet, not an escape from the no-go.

  Sections 1--4 isolate a branch-relative microscopic bridge law: one elementary,
  future-directed growth step is represented by the standard
  positive-frequency unitary phase

      U(E, tau) = exp(-i E tau),       E > 0, tau > 0,

  in units with hbar = 1.  At the elementary quarter turn `E tau = pi/2`, this
  convention gives `U = -i`; its complex conjugate is `+i`.

  The repository had already proved the independent causal dictionary

      phase -i  <->  y = -1/2  <->  Xi = -2y = +1
                <->  P_weak(Xi) = P_L.

  Sections 5--9 stress-test that phase inside the finite causal route sector.
  For fixed oriented curvature operator `H`, positivity and zero-ground
  normalization uniquely give `H_plus = 1+H = 2P_plus`; its nondegenerate
  unitary flow first orthogonalizes at `pi/2` and sends the first route to
  `-i` times the second.  But reflection replaces `H` by `-H` and gives the
  equally positive, zero-ground Hamiltonian `H_minus = 1-H = 2P_minus`.
  Its first orthogonal transition occurs at the same time with coefficient
  `+i`.  Both coefficients extend to normalized, strongly positive,
  projectively consistent unlabeled growth laws and transport opposite
  nonzero cylinder signs through every finite refinement.

  Thus positive frequency, positivity, ground-zero normalization, and clock
  minimality do not select an absolute sign.  The exact remaining input is an
  *oriented clock/birth alignment*: which reflected holonomy sector is ground,
  together with identifying a maximal birth with the first orthogonal route
  transition.  The future accretion arrow may motivate that alignment, but the
  present all-rank growth axioms do not derive it.  This is precisely what the
  prior reflection no-go requires.  No continuum Lorentzian Dirac field is
  reconstructed here.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalSetWeakHandednessBridge
import UnifiedTheory.Audit.KFCausalSetGeometricOrientationAsymptotics
import UnifiedTheory.Audit.KFOrientationPathQuantum
import UnifiedTheory.LayerB.MargolusLevitinTight

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetFutureFrequencyHandedness

noncomputable section

open scoped ComplexConjugate ComplexOrder
open Matrix
open UnifiedTheory.Audit.KFCausalSetBellCausality
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetOrientationRestriction
open UnifiedTheory.Audit.KFCausalSetChiralGrowth
open UnifiedTheory.Audit.KFCausalSetChiralityGenerationNoGo
open UnifiedTheory.Audit.KFCausalSetGeometricOrientationDynamics
open UnifiedTheory.Audit.KFCausalSetGeometricOrientationAsymptotics
open UnifiedTheory.Audit.KFCausalSetMicroscopicSpectatorAction
open UnifiedTheory.Audit.KFOrientationGrowthDecoherence
open UnifiedTheory.Audit.KFOrientationHistoryRigidity
open UnifiedTheory.Audit.KFOrientationHigherRankDecoherence
open UnifiedTheory.Audit.KFCausalSetWeakHandednessBridge
open UnifiedTheory.Audit.KFOrientationCPChannelTower
open UnifiedTheory.Audit.KFOrientationPathQuantum
open UnifiedTheory.Audit.KFOrientationSpinOne
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.MargolusLevitinTight

/-! ## 1. The future positive-frequency phase -/

/-- Standard future-directed positive-frequency phase in units `hbar = 1`. -/
def futurePositiveFrequencyPhase (energy properTime : ℝ) : ℂ :=
  Complex.exp ((-(energy * properTime) : ℝ) * Complex.I)

/-- A positive-energy future quarter turn has phase exactly `-i`. -/
theorem futurePositiveFrequencyPhase_quarter_turn
    (energy properTime : ℝ)
    (_hEnergy : 0 < energy) (_hTime : 0 < properTime)
    (hQuarter : energy * properTime = Real.pi / 2) :
    futurePositiveFrequencyPhase energy properTime = -Complex.I := by
  unfold futurePositiveFrequencyPhase
  rw [hQuarter]
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re]
    simp [Real.cos_neg, Real.cos_pi_div_two]
  · rw [Complex.exp_ofReal_mul_I_im]
    simp [Real.sin_neg, Real.sin_pi_div_two]

/-- Reversing the growth-time orientation complex-conjugates the unitary
phase.  Thus the reflected elementary character is the reverse-frequency
solution once the future arrow has been fixed. -/
theorem futurePositiveFrequencyPhase_reverse_time
    (energy properTime : ℝ) :
    futurePositiveFrequencyPhase energy (-properTime) =
      star (futurePositiveFrequencyPhase energy properTime) := by
  unfold futurePositiveFrequencyPhase
  change Complex.exp ((-(energy * -properTime) : ℝ) * Complex.I) =
    conj
      (Complex.exp ((-(energy * properTime) : ℝ) * Complex.I))
  rw [← Complex.exp_conj]
  congr 1
  apply Complex.ext <;> simp

/-- At a positive-energy quarter turn the reverse-time phase is `+i`. -/
theorem reverseTimePhase_quarter_turn
    (energy properTime : ℝ)
    (hEnergy : 0 < energy) (hTime : 0 < properTime)
    (hQuarter : energy * properTime = Real.pi / 2) :
    futurePositiveFrequencyPhase energy (-properTime) = Complex.I := by
  rw [futurePositiveFrequencyPhase_reverse_time,
    futurePositiveFrequencyPhase_quarter_turn energy properTime
      hEnergy hTime hQuarter]
  simp

/-! ## 2. Unique microscopic chirality selected by that phase -/

/-- The future positive-frequency quarter turn matches exactly one of the two
Bell-causal chiral characters: microscopic chirality slot `1`, whose phase is
`-i`. -/
theorem futurePositiveFrequency_unique_microscopic_chirality
    (energy properTime : ℝ)
    (hEnergy : 0 < energy) (hTime : 0 < properTime)
    (hQuarter : energy * properTime = Real.pi / 2) :
    ∃! chirality : Fin 2,
      chiralMaximalEventPhase chirality =
        futurePositiveFrequencyPhase energy properTime := by
  have hPhase := futurePositiveFrequencyPhase_quarter_turn
    energy properTime hEnergy hTime hQuarter
  refine ⟨1, ?_, ?_⟩
  · rw [hPhase]
    norm_num [chiralMaximalEventPhase]
  · intro chirality hMatch
    fin_cases chirality
    · rw [hPhase] at hMatch
      have hImaginary := congrArg Complex.im hMatch
      norm_num [chiralMaximalEventPhase] at hImaginary
    · rfl

/-- Any microscopic character matching a future positive-frequency quarter
turn is necessarily chirality slot `1`. -/
theorem futurePositiveFrequency_phase_match_eq_one
    (energy properTime : ℝ)
    (hEnergy : 0 < energy) (hTime : 0 < properTime)
    (hQuarter : energy * properTime = Real.pi / 2)
    {chirality : Fin 2}
    (hMatch : chiralMaximalEventPhase chirality =
      futurePositiveFrequencyPhase energy properTime) :
    chirality = 1 := by
  fin_cases chirality
  · have hPhase := futurePositiveFrequencyPhase_quarter_turn
      energy properTime hEnergy hTime hQuarter
    rw [hPhase] at hMatch
    have hImaginary := congrArg Complex.im hMatch
    norm_num [chiralMaximalEventPhase] at hImaginary
  · rfl

/-- The selected microscopic character has the pure orientation endpoint
`y = -1/2`. -/
theorem futurePositiveFrequency_orientation_endpoint :
    chiralBoundaryOrientationParameter (1 : Fin 2) = -1 / 2 := by
  norm_num [chiralBoundaryOrientationParameter, chiralMaximalEventPhase]

/-- Consequently its cylinder chirality coordinate is `Xi = -2y = +1`. -/
theorem futurePositiveFrequency_cylinder_sign :
    -2 * chiralBoundaryOrientationParameter (1 : Fin 2) = 1 := by
  rw [futurePositiveFrequency_orientation_endpoint]
  ring

/-- The reverse-time quarter turn matches the reflected microscopic character,
slot `0`, whose cylinder sign is `-1`. -/
theorem reverseTimePhase_selects_reflected_character
    (energy properTime : ℝ)
    (hEnergy : 0 < energy) (hTime : 0 < properTime)
    (hQuarter : energy * properTime = Real.pi / 2) :
    chiralMaximalEventPhase (0 : Fin 2) =
        futurePositiveFrequencyPhase energy (-properTime)
      ∧ -2 * chiralBoundaryOrientationParameter (0 : Fin 2) = -1 := by
  constructor
  · rw [reverseTimePhase_quarter_turn energy properTime
      hEnergy hTime hQuarter]
    norm_num [chiralMaximalEventPhase]
  · norm_num [chiralBoundaryOrientationParameter,
      chiralMaximalEventPhase]

/-! ## 3. Promotion on the chosen positive-oriented branch -/

/-- The unique future-positive-frequency endpoint gives exactly the standard
left Weyl projector. -/
theorem futurePositiveFrequency_selects_leftWeylProjector
    (psi : DiracWeakSpinor) :
    causalWeylProjector
        (-2 * chiralBoundaryOrientationParameter (1 : Fin 2)) psi =
      leftWeylProjector psi := by
  rw [futurePositiveFrequency_cylinder_sign]
  exact causalWeylProjector_one psi

/-- The associated charged-current vertex is exactly the standard left weak
vertex. -/
theorem futurePositiveFrequency_selects_leftWeakVertex
    (generator : WeakDoublet →ₗ[ℂ] WeakDoublet) :
    causalWeakVertex
        (-2 * chiralBoundaryOrientationParameter (1 : Fin 2)) generator =
      leftWeakVertex generator := by
  rw [futurePositiveFrequency_cylinder_sign]
  funext psi
  exact causalWeakVertex_one generator psi

/-- Every phase-matched microscopic character, without hard-coding its index,
has cylinder sign `+1` and the standard left-handed charged current. -/
theorem futurePositiveFrequency_matched_character_is_left
    (energy properTime : ℝ)
    (hEnergy : 0 < energy) (hTime : 0 < properTime)
    (hQuarter : energy * properTime = Real.pi / 2)
    {chirality : Fin 2}
    (hMatch : chiralMaximalEventPhase chirality =
      futurePositiveFrequencyPhase energy properTime) :
    (-2 * chiralBoundaryOrientationParameter chirality = 1)
      ∧ IsNontrivialPurelyLeftHanded
          (causalWeakVertex
            (-2 * chiralBoundaryOrientationParameter chirality)
            weakRaising) := by
  have hSelected := futurePositiveFrequency_phase_match_eq_one
    energy properTime hEnergy hTime hQuarter hMatch
  subst chirality
  refine ⟨futurePositiveFrequency_cylinder_sign, ?_⟩
  rw [futurePositiveFrequency_selects_leftWeakVertex]
  exact standard_charged_current_is_nontrivial_purely_left

/-- **Branch-relative handedness theorem.**

Once an oriented clock is required to carry the displayed positive-frequency
phase, a positive-energy elementary quarter turn uniquely matches one
microscopic chiral character.  That character has `Xi = +1` and produces a
nontrivial purely left-handed charged weak current.  Section 7 proves that the
reflected oriented clock satisfies the same reflection-even requirements and
selects the opposite character. -/
theorem future_positive_frequency_derives_left_handed_weak_interaction
    (energy properTime : ℝ)
    (hEnergy : 0 < energy) (hTime : 0 < properTime)
    (hQuarter : energy * properTime = Real.pi / 2) :
    ∃! chirality : Fin 2,
      chiralMaximalEventPhase chirality =
          futurePositiveFrequencyPhase energy properTime
        ∧ (-2 * chiralBoundaryOrientationParameter chirality = 1)
        ∧ IsNontrivialPurelyLeftHanded
            (causalWeakVertex
              (-2 * chiralBoundaryOrientationParameter chirality)
              weakRaising) := by
  refine ⟨1, ?_, ?_⟩
  · have hPhase := futurePositiveFrequencyPhase_quarter_turn
      energy properTime hEnergy hTime hQuarter
    rw [hPhase]
    refine ⟨by norm_num [chiralMaximalEventPhase],
      futurePositiveFrequency_cylinder_sign, ?_⟩
    rw [futurePositiveFrequency_selects_leftWeakVertex]
    exact standard_charged_current_is_nontrivial_purely_left
  · intro chirality hSelected
    exact futurePositiveFrequency_phase_match_eq_one
      energy properTime hEnergy hTime hQuarter hSelected.1

/-! ## 4. Honest boundary: why positive energy alone is not enough -/

/-- Spectrum positivity by itself is reflection even: it cannot distinguish
the two chiral slots.  The selecting content is the dynamical phase bridge,
not the inequality `0 < energy` in isolation. -/
theorem positiveEnergy_is_chirality_blind (energy : ℝ) :
    (0 < energy ∧ (0 : Fin 2) = 0) ↔
      (0 < energy ∧ (1 : Fin 2) = 1) := by
  simp

/-! ## 5. The causal path sector supplies the positive Hamiltonian

The preceding sections stated the positive-frequency bridge abstractly.  The
finite two-route causal sector already contains enough structure to construct
it.  The native curvature Hamiltonian has eigenvalues `-1,+1`; shifting its
ground energy to zero gives the positive Hamiltonian `H_plus = 1 + H`, with
spectrum `0,2`.  Ground-energy shifts leave projective dynamics unchanged but
fix the phase relevant to the Margolus--Levitin energy-above-ground bound. -/

/-- The one-parameter family of identity shifts of the native orientation
Hamiltonian. -/
def causalOrientationHamiltonianShift (offset : ℝ) : SquareMatrix 2 :=
  (offset : ℂ) • 1 + quotientCurvatureHamiltonian

/-- The negative holonomy sector has shifted energy `offset-1`. -/
theorem causalOrientationHamiltonianShift_negativeKet (offset : ℝ) :
    causalOrientationHamiltonianShift offset * negativeHolonomyKet =
      ((offset - 1 : ℝ) : ℂ) • negativeHolonomyKet := by
  unfold causalOrientationHamiltonianShift
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul,
    quotientCurvature_negativeKet]
  module

/-- Ground-zero normalization removes the apparent arbitrary identity shift:
the native negative holonomy eigenstate has energy zero for exactly one real
offset, namely `offset=1`. -/
theorem causalOrientationHamiltonianShift_zeroGround_unique
    (offset : ℝ)
    (hGround :
      causalOrientationHamiltonianShift offset * negativeHolonomyKet = 0) :
    offset = 1 := by
  rw [causalOrientationHamiltonianShift_negativeKet] at hGround
  have hComponent := congrArg (fun ket : PathKet => ket 0 0) hGround
  norm_num [negativeHolonomyKet] at hComponent
  have hSqrt : ((spinOneSqrtTwo : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast spinOneSqrtTwo_ne_zero
  field_simp [hSqrt] at hComponent
  rcases hComponent with hOffset | hSqrtZero
  · have hOffsetReal : offset - 1 = 0 := by exact_mod_cast hOffset
    linarith
  · exact (spinOneSqrtTwo_ne_zero hSqrtZero).elim

/-- Ground-shifted causal orientation Hamiltonian. -/
def causalPositiveOrientationHamiltonian : SquareMatrix 2 :=
  1 + quotientCurvatureHamiltonian

theorem causalPositiveOrientationHamiltonian_eq_uniqueGroundShift :
    causalPositiveOrientationHamiltonian =
      causalOrientationHamiltonianShift 1 := by
  unfold causalPositiveOrientationHamiltonian
    causalOrientationHamiltonianShift
  norm_num

theorem causalPositiveOrientationHamiltonian_eq_projector :
    causalPositiveOrientationHamiltonian =
      (2 : ℝ) • positiveOrientationProjector := by
  unfold causalPositiveOrientationHamiltonian positiveOrientationProjector
  module

/-- The shifted causal Hamiltonian is Hermitian. -/
theorem causalPositiveOrientationHamiltonian_isHermitian :
    causalPositiveOrientationHamiltonian.IsHermitian := by
  unfold causalPositiveOrientationHamiltonian
  exact Matrix.isHermitian_one.add
    quotientCurvatureHamiltonian_isHermitian

/-- The shifted causal Hamiltonian is positive semidefinite. -/
theorem causalPositiveOrientationHamiltonian_posSemidef :
    causalPositiveOrientationHamiltonian.PosSemidef := by
  rw [causalPositiveOrientationHamiltonian_eq_projector]
  have hTwo : (0 : ℝ) ≤ 2 := by norm_num
  exact positiveOrientationProjector_isPathDensity.2.1.smul hTwo

/-- Complete identity-shift stress test.  For the fixed oriented operator `H`,
`offset*I+H` is positive semidefinite exactly when `offset >= 1`; hence the
zero-ground choice is also the unique minimal positive shift.  This theorem is
deliberately scoped to fixed `H`: reflection replaces `H` by `-H`, a distinct
ambiguity handled below. -/
theorem causalOrientationHamiltonianShift_posSemidef_iff (offset : ℝ) :
    (causalOrientationHamiltonianShift offset).PosSemidef ↔ 1 ≤ offset := by
  constructor
  · intro hPos
    let witness : Fin 2 → ℂ := ![(1 : ℂ), -Complex.I]
    have hQuadratic := hPos.dotProduct_mulVec_nonneg witness
    have hValue :
        star witness ⬝ᵥ
            (causalOrientationHamiltonianShift offset *ᵥ witness) =
          ((2 * (offset - 1) : ℝ) : ℂ) := by
      unfold witness causalOrientationHamiltonianShift
      rw [quotientCurvatureHamiltonian_exact]
      simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two,
        Pi.star_apply]
      norm_num [Fin.ext_iff, Complex.I_sq]
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [hValue] at hQuadratic
    have hReal : 0 ≤ 2 * (offset - 1) :=
      (Complex.nonneg_iff.mp hQuadratic).1
    linarith
  · intro hOffset
    have hScalar :
        (((offset - 1 : ℝ) : ℂ) • (1 : SquareMatrix 2)).PosSemidef := by
      have hNonnegative : (0 : ℂ) ≤ ((offset - 1 : ℝ) : ℂ) := by
        rw [Complex.nonneg_iff]
        exact ⟨by simpa using sub_nonneg.mpr hOffset, by simp⟩
      exact Matrix.PosSemidef.one.smul hNonnegative
    have hDecomposition :
        causalOrientationHamiltonianShift offset =
          ((offset - 1 : ℝ) : ℂ) • (1 : SquareMatrix 2) +
            causalPositiveOrientationHamiltonian := by
      unfold causalOrientationHamiltonianShift
        causalPositiveOrientationHamiltonian
      module
    rw [hDecomposition]
    exact hScalar.add causalPositiveOrientationHamiltonian_posSemidef

/-- The positive holonomy sector has energy `2`. -/
theorem causalPositiveOrientationHamiltonian_positiveKet :
    causalPositiveOrientationHamiltonian * positiveHolonomyKet =
      (2 : ℂ) • positiveHolonomyKet := by
  unfold causalPositiveOrientationHamiltonian
  rw [Matrix.add_mul, Matrix.one_mul, quotientCurvature_positiveKet]
  module

/-- The negative holonomy sector is the zero-energy ground sector. -/
theorem causalPositiveOrientationHamiltonian_negativeKet :
    causalPositiveOrientationHamiltonian * negativeHolonomyKet = 0 := by
  unfold causalPositiveOrientationHamiltonian
  rw [Matrix.add_mul, Matrix.one_mul, quotientCurvature_negativeKet]
  module

/-- The fixed branch has a genuine nondegenerate two-level spectrum: the
normalized orthogonal holonomy basis carries distinct energies `2` and `0`.
Thus no spectral degeneracy is hidden in the quarter-time argument. -/
theorem causalPositiveOrientationHamiltonian_nondegenerate_spectralPair :
    ketInner positiveHolonomyKet positiveHolonomyKet = 1
      ∧ ketInner negativeHolonomyKet negativeHolonomyKet = 1
      ∧ ketInner positiveHolonomyKet negativeHolonomyKet = 0
      ∧ causalPositiveOrientationHamiltonian * positiveHolonomyKet =
          (2 : ℂ) • positiveHolonomyKet
      ∧ causalPositiveOrientationHamiltonian * negativeHolonomyKet = 0
      ∧ (2 : ℂ) ≠ 0 := by
  exact ⟨positiveHolonomyKet_normalized,
    negativeHolonomyKet_normalized,
    holonomyKets_orthogonal,
    causalPositiveOrientationHamiltonian_positiveKet,
    causalPositiveOrientationHamiltonian_negativeKet, by norm_num⟩

/-- The first causal route is the equal superposition of the ground and
excited holonomy eigenstates. -/
theorem path13Ket_equal_holonomy_superposition :
    path13Ket =
      ((1 / spinOneSqrtTwo : ℝ) : ℂ) • positiveHolonomyKet +
        ((1 / spinOneSqrtTwo : ℝ) : ℂ) • negativeHolonomyKet := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [path13Ket, positiveHolonomyKet, negativeHolonomyKet,
      Fin.ext_iff]
  · field_simp [spinOneSqrtTwo_ne_zero]
    norm_num [← pow_two, spinOneSqrtTwo_sq_complex]

/-- Energy expectation of a path ket. -/
def pathEnergyExpectation (hamiltonian : SquareMatrix 2)
    (psi : PathKet) : ℝ :=
  (ketInner psi (hamiltonian * psi)).re

/-- The initial causal route has mean energy exactly `1` above the ground. -/
theorem path13_causalPositive_meanEnergy :
    pathEnergyExpectation causalPositiveOrientationHamiltonian path13Ket = 1 := by
  have hAction :
      causalPositiveOrientationHamiltonian * path13Ket =
        !![(1 : ℂ); Complex.I] := by
    unfold causalPositiveOrientationHamiltonian
    rw [quotientCurvatureHamiltonian_exact]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [path13Ket, Matrix.mul_apply, Fin.sum_univ_succ,
        Fin.ext_iff]
  unfold pathEnergyExpectation
  rw [hAction]
  norm_num [ketInner, path13Ket, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_succ, Fin.ext_iff]

/-! ## 6. Exact spectral evolution and the minimal orthogonal birth -/

/-- Spectral unitary evolution of the positive causal Hamiltonian.  The
excited projector carries energy `2`; the ground projector carries energy
`0`. -/
def causalPositiveOrientationEvolution (time : ℝ) : SquareMatrix 2 :=
  Complex.exp (((-2 * time : ℝ) : ℂ) * Complex.I) •
      positiveOrientationProjector +
    negativeOrientationProjector

/-- The excited holonomy ket acquires precisely the energy-`2` phase. -/
theorem causalPositiveOrientationEvolution_positiveKet (time : ℝ) :
    causalPositiveOrientationEvolution time * positiveHolonomyKet =
      Complex.exp (((-2 * time : ℝ) : ℂ) * Complex.I) •
        positiveHolonomyKet := by
  have hPositive :
      positiveOrientationProjector * positiveHolonomyKet =
        positiveHolonomyKet := by
    unfold positiveOrientationProjector
    rw [Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul,
      quotientCurvature_positiveKet]
    module
  have hNegative :
      negativeOrientationProjector * positiveHolonomyKet = 0 := by
    unfold negativeOrientationProjector
    rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul,
      quotientCurvature_positiveKet]
    module
  unfold causalPositiveOrientationEvolution
  rw [Matrix.add_mul, Matrix.smul_mul, hPositive, hNegative]
  module

/-- The negative holonomy ket is the stationary zero-energy ground state. -/
theorem causalPositiveOrientationEvolution_negativeKet (time : ℝ) :
    causalPositiveOrientationEvolution time * negativeHolonomyKet =
      negativeHolonomyKet := by
  have hPositive :
      positiveOrientationProjector * negativeHolonomyKet = 0 := by
    unfold positiveOrientationProjector
    rw [Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul,
      quotientCurvature_negativeKet]
    module
  have hNegative :
      negativeOrientationProjector * negativeHolonomyKet =
        negativeHolonomyKet := by
    unfold negativeOrientationProjector
    rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul,
      quotientCurvature_negativeKet]
    module
  unfold causalPositiveOrientationEvolution
  rw [Matrix.add_mul, Matrix.smul_mul, hPositive, hNegative]
  module

theorem orientationProjectors_orthogonal_reverse :
    negativeOrientationProjector * positiveOrientationProjector = 0 := by
  unfold positiveOrientationProjector negativeOrientationProjector
  simp only [Matrix.smul_mul, Matrix.mul_smul,
    Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    quotientCurvatureHamiltonian_sq]
  module

/-- The excited phase has unit modulus, expressed algebraically in the form
needed by the projector proof of unitarity. -/
theorem causalPositive_excitedPhase_star_mul (time : ℝ) :
    star (Complex.exp (((-2 * time : ℝ) : ℂ) * Complex.I)) *
        Complex.exp (((-2 * time : ℝ) : ℂ) * Complex.I) = 1 := by
  rw [Complex.star_def, Complex.conj_mul']
  rw [Complex.norm_exp_ofReal_mul_I]
  norm_num

theorem causalPositiveOrientationEvolution_conjTranspose (time : ℝ) :
    (causalPositiveOrientationEvolution time)ᴴ =
      star (Complex.exp (((-2 * time : ℝ) : ℂ) * Complex.I)) •
          positiveOrientationProjector +
        negativeOrientationProjector := by
  unfold causalPositiveOrientationEvolution
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul]
  simp [(positiveOrientationProjector_isPathDensity.1).eq,
    (negativeOrientationProjector_isPathDensity.1).eq]

/-- The spectral flow generated by the positive causal Hamiltonian is unitary
at every real time. -/
theorem causalPositiveOrientationEvolution_unitary (time : ℝ) :
    (causalPositiveOrientationEvolution time)ᴴ *
        causalPositiveOrientationEvolution time = 1 := by
  rw [causalPositiveOrientationEvolution_conjTranspose]
  unfold causalPositiveOrientationEvolution
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul]
  rw [positiveOrientationProjector_idempotent,
    orientationProjectors_orthogonal,
    orientationProjectors_orthogonal_reverse,
    negativeOrientationProjector_idempotent]
  simp only [smul_zero, add_zero, zero_add, smul_smul]
  rw [mul_comm
    (Complex.exp (((-2 * time : ℝ) : ℂ) * Complex.I))
    (star (Complex.exp (((-2 * time : ℝ) : ℂ) * Complex.I)))]
  rw [causalPositive_excitedPhase_star_mul]
  simp only [one_smul]
  exact orientationProjectors_sum

theorem causalPositiveOrientationEvolution_zero :
    causalPositiveOrientationEvolution 0 = 1 := by
  unfold causalPositiveOrientationEvolution
  norm_num [orientationProjectors_sum]

/-- At time `pi/2`, the excited energy-2 phase is exactly `-1`. -/
theorem causalPositive_excitedPhase_quarter :
    Complex.exp (((-2 * (Real.pi / 2) : ℝ) : ℂ) * Complex.I) = -1 := by
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re]
    rw [show -2 * (Real.pi / 2) = -Real.pi by ring]
    simp [Real.cos_neg, Real.cos_pi]
  · rw [Complex.exp_ofReal_mul_I_im]
    rw [show -2 * (Real.pi / 2) = -Real.pi by ring]
    simp [Real.sin_neg, Real.sin_pi]

/-- At the negative quarter time the energy-2 eigenphase is still `-1`.
Consequently reversing the parameter of this same concrete half-period
evolution does not produce the conjugate route coefficient. -/
theorem causalPositive_excitedPhase_negativeQuarter :
    Complex.exp (((-2 * (-(Real.pi / 2)) : ℝ) : ℂ) * Complex.I) = -1 := by
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re]
    rw [show -2 * (-(Real.pi / 2)) = Real.pi by ring]
    simp [Real.cos_pi]
  · rw [Complex.exp_ofReal_mul_I_im]
    rw [show -2 * (-(Real.pi / 2)) = Real.pi by ring]
    simp [Real.sin_pi]

/-- The positive Hamiltonian's quarter-time unitary is `-H_orientation`. -/
theorem causalPositiveOrientationEvolution_quarter :
    causalPositiveOrientationEvolution (Real.pi / 2) =
      -quotientCurvatureHamiltonian := by
  unfold causalPositiveOrientationEvolution
  rw [causalPositive_excitedPhase_quarter]
  unfold positiveOrientationProjector negativeOrientationProjector
  module

/-- The same `H_plus` evolution at negative quarter time equals its positive
quarter-time value.  The `+i` route transition therefore comes from the
reflected ground/excited assignment `H_minus`, not merely from replacing
`time` by `-time` while holding `H_plus` fixed. -/
theorem causalPositiveOrientationEvolution_negativeQuarter :
    causalPositiveOrientationEvolution (-(Real.pi / 2)) =
      -quotientCurvatureHamiltonian := by
  unfold causalPositiveOrientationEvolution
  rw [causalPositive_excitedPhase_negativeQuarter]
  unfold positiveOrientationProjector negativeOrientationProjector
  module

theorem causalPositiveOrientationEvolution_negativeQuarter_path13 :
    causalPositiveOrientationEvolution (-(Real.pi / 2)) * path13Ket =
      (-Complex.I) • path22Ket := by
  rw [causalPositiveOrientationEvolution_negativeQuarter,
    quotientCurvatureHamiltonian_exact]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [path13Ket, path22Ket, Matrix.mul_apply,
      Fin.sum_univ_succ, Fin.ext_iff, Complex.I_sq]

/-- **Dynamical phase selection.**  The positive causal Hamiltonian sends the
first route to the orthogonal second route with coefficient exactly `-i`. -/
theorem causalPositiveOrientationEvolution_quarter_path13 :
    causalPositiveOrientationEvolution (Real.pi / 2) * path13Ket =
      (-Complex.I) • path22Ket := by
  rw [causalPositiveOrientationEvolution_quarter,
    quotientCurvatureHamiltonian_exact]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [path13Ket, path22Ket, Matrix.mul_apply,
      Fin.sum_univ_succ, Fin.ext_iff, Complex.I_sq]

/-- The endpoint reached by the positive causal evolution is orthogonal to the
initial route. -/
theorem causalPositiveOrientationEvolution_quarter_orthogonal :
    ketInner path13Ket
      (causalPositiveOrientationEvolution (Real.pi / 2) * path13Ket) = 0 := by
  rw [causalPositiveOrientationEvolution_quarter_path13]
  norm_num [ketInner, path13Ket, path22Ket, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_succ, Fin.ext_iff]

/-- The causal route's energy distribution in the holonomy basis: equal
weight on energies `0` and `2`. -/
noncomputable def causalOrientationEnergySpectrum : EnergySpectrum 2 :=
  saturatingSpectrum 2 (by norm_num)

/-- The abstract `{0,2}` survival amplitude is exactly the overlap of the
initial causal route with its matrix evolution, so the speed-limit statement
applies to the same dynamics that generates the chiral coefficient. -/
theorem causalOrientationEnergySpectrum_survival_eq_pathOverlap (time : ℝ) :
    causalOrientationEnergySpectrum.survivalAmplitude time =
      ketInner path13Ket
        (causalPositiveOrientationEvolution time * path13Ket) := by
  let phase : ℂ :=
    Complex.exp (((-2 * time : ℝ) : ℂ) * Complex.I)
  have hSpectrum :
      causalOrientationEnergySpectrum.survivalAmplitude time =
        (1 + phase) / 2 := by
    unfold causalOrientationEnergySpectrum saturatingSpectrum
      EnergySpectrum.survivalAmplitude
    rw [Fin.sum_univ_two]
    simp only [Fin.isValue, if_true,
      show ((1 : Fin 2) = 0) = False from by decide, if_false]
    have hPhase :
        Complex.exp
            (-Complex.I * (((2 : ℝ) : ℂ)) * (time : ℂ)) = phase := by
      unfold phase
      congr 1
      push_cast
      ring
    rw [hPhase]
    norm_num
    ring
  have hPath :
      ketInner path13Ket
          (causalPositiveOrientationEvolution time * path13Ket) =
        (1 + phase) / 2 := by
    have hFirstComponent :
        (causalPositiveOrientationEvolution time * path13Ket) 0 0 =
          (1 + phase) / 2 := by
      unfold causalPositiveOrientationEvolution positiveOrientationProjector
        negativeOrientationProjector
      rw [quotientCurvatureHamiltonian_exact]
      norm_num [path13Ket, Matrix.mul_apply, Fin.sum_univ_succ,
        Fin.ext_iff]
      have hMatrixPhase :
          Complex.exp (-(2 * (time : ℂ) * Complex.I)) = phase := by
        unfold phase
        congr 1
        push_cast
        ring
      rw [hMatrixPhase]
      ring
    unfold ketInner
    rw [Matrix.mul_apply]
    simp only [Fin.sum_univ_two]
    norm_num [path13Ket, Matrix.conjTranspose_apply, Fin.ext_iff]
    exact hFirstComponent
  rw [hSpectrum, hPath]

/-- Both designated causal routes have the same survival amplitude under the
fixed Hamiltonian.  Therefore changing the initial route cannot produce an
earlier orthogonalization hidden from the `path13` calculation. -/
theorem causalPositiveOrientationEvolution_pathSurvival_equal (time : ℝ) :
    ketInner path22Ket
        (causalPositiveOrientationEvolution time * path22Ket) =
      ketInner path13Ket
        (causalPositiveOrientationEvolution time * path13Ket) := by
  have hComponents :
      causalPositiveOrientationEvolution time 1 1 =
        causalPositiveOrientationEvolution time 0 0 := by
    unfold causalPositiveOrientationEvolution
      positiveOrientationProjector negativeOrientationProjector
    rw [quotientCurvatureHamiltonian_exact]
    norm_num [Matrix.one_apply, Fin.ext_iff]
  unfold ketInner
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  norm_num [path13Ket, path22Ket, Matrix.conjTranspose_apply, Fin.ext_iff]
  exact hComponents

theorem causalOrientationEnergySpectrum_meanEnergy :
    causalOrientationEnergySpectrum.energyExpectation = 1 := by
  unfold causalOrientationEnergySpectrum
  simpa using saturatingSpectrum_energyExpectation 2 (by norm_num)

theorem causalOrientationEnergySpectrum_quarter_survival_zero :
    (causalOrientationEnergySpectrum.survivalAmplitude
        (Real.pi / 2)).re = 0
      ∧ (causalOrientationEnergySpectrum.survivalAmplitude
        (Real.pi / 2)).im = 0 := by
  unfold causalOrientationEnergySpectrum
  simpa using saturating_survival_zero 2 (by norm_num)

/-- The causal birth exactly saturates the positive-energy quantum speed
limit: `T * meanEnergy = pi/2`. -/
theorem causalOrientationBirth_saturates_margolusLevitin :
    (Real.pi / 2) * causalOrientationEnergySpectrum.energyExpectation =
      Real.pi / 2 := by
  rw [causalOrientationEnergySpectrum_meanEnergy]
  ring

/-- No orthogonal evolution of the same causal energy spectrum can occur
earlier than `pi/2`. -/
theorem causalOrientationBirth_quarter_is_minimal
    (time : ℝ) (hTime : 0 ≤ time)
    (hOrthogonalRe :
      (causalOrientationEnergySpectrum.survivalAmplitude time).re = 0)
    (_hOrthogonalIm :
      (causalOrientationEnergySpectrum.survivalAmplitude time).im = 0) :
    Real.pi / 2 ≤ time := by
  have hCos : Real.cos (2 * time) = -1 := by
    rw [EnergySpectrum.survivalAmplitude_re] at hOrthogonalRe
    unfold causalOrientationEnergySpectrum saturatingSpectrum at hOrthogonalRe
    rw [Fin.sum_univ_two] at hOrthogonalRe
    norm_num at hOrthogonalRe
    linarith
  rcases Real.cos_eq_neg_one_iff.mp hCos with ⟨turns, hTurns⟩
  have hTurnsNonnegative : (0 : ℤ) ≤ turns := by
    by_contra hNegative
    have hAtMostNegOne : turns ≤ -1 := by omega
    have hCast : (turns : ℝ) ≤ -1 := by exact_mod_cast hAtMostNegOne
    have hTwoTime : 0 ≤ 2 * time := by linarith
    rw [← hTurns] at hTwoTime
    nlinarith [Real.pi_pos]
  have hTurnsCast : (0 : ℝ) ≤ turns := by exact_mod_cast hTurnsNonnegative
  have hPiLe : Real.pi ≤ 2 * time := by
    rw [← hTurns]
    nlinarith [Real.pi_pos]
  linarith

/-- Matrix-level form of minimality: the unitary path evolution cannot make
the initial route orthogonal to itself before `pi/2`. -/
theorem causalPositiveOrientationEvolution_firstOrthogonal
    (time : ℝ) (hTime : 0 ≤ time)
    (hOrthogonal :
      ketInner path13Ket
        (causalPositiveOrientationEvolution time * path13Ket) = 0) :
    Real.pi / 2 ≤ time := by
  have hSurvival :
      causalOrientationEnergySpectrum.survivalAmplitude time = 0 := by
    rw [causalOrientationEnergySpectrum_survival_eq_pathOverlap,
      hOrthogonal]
  exact causalOrientationBirth_quarter_is_minimal time hTime
    (congrArg Complex.re hSurvival) (congrArg Complex.im hSurvival)

theorem causalPositiveOrientationEvolution_path22_firstOrthogonal
    (time : ℝ) (hTime : 0 ≤ time)
    (hOrthogonal :
      ketInner path22Ket
        (causalPositiveOrientationEvolution time * path22Ket) = 0) :
    Real.pi / 2 ≤ time := by
  apply causalPositiveOrientationEvolution_firstOrthogonal time hTime
  rw [← causalPositiveOrientationEvolution_pathSurvival_equal]
  exact hOrthogonal

/-! ## 7. Reflection tripwire: ground-zero and minimality leave a pair

The fixed-orientation results above remove two genuine sources of slack: the
identity shift is uniquely minimal and the first orthogonal time is exactly
`pi/2`.  They do not choose an absolute orientation.  Reflection replaces
`H` by `-H`, exchanges the two spectral projectors, and produces an equally
positive ground-zero Hamiltonian whose quarter transition has the conjugate
coefficient.  This is the precise point at which the earlier vacuum
reflection no-go continues to apply. -/

/-- Reflection partner of the positive-oriented Hamiltonian. -/
def causalReflectedOrientationHamiltonian : SquareMatrix 2 :=
  1 - quotientCurvatureHamiltonian

theorem causalReflectedOrientationHamiltonian_eq_projector :
    causalReflectedOrientationHamiltonian =
      (2 : ℝ) • negativeOrientationProjector := by
  unfold causalReflectedOrientationHamiltonian negativeOrientationProjector
  module

theorem causalReflectedOrientationHamiltonian_posSemidef :
    causalReflectedOrientationHamiltonian.PosSemidef := by
  rw [causalReflectedOrientationHamiltonian_eq_projector]
  have hTwo : (0 : ℝ) ≤ 2 := by norm_num
  exact negativeOrientationProjector_isPathDensity.2.1.smul hTwo

/-- In the reflected branch the positive holonomy ket is the zero-energy
ground state. -/
theorem causalReflectedOrientationHamiltonian_positiveKet :
    causalReflectedOrientationHamiltonian * positiveHolonomyKet = 0 := by
  unfold causalReflectedOrientationHamiltonian
  rw [Matrix.sub_mul, Matrix.one_mul, quotientCurvature_positiveKet]
  module

/-- The reflected negative holonomy sector has energy `2`. -/
theorem causalReflectedOrientationHamiltonian_negativeKet :
    causalReflectedOrientationHamiltonian * negativeHolonomyKet =
      (2 : ℂ) • negativeHolonomyKet := by
  unfold causalReflectedOrientationHamiltonian
  rw [Matrix.sub_mul, Matrix.one_mul, quotientCurvature_negativeKet]
  module

theorem causalPositive_reflectedHamiltonians_ne :
    causalPositiveOrientationHamiltonian ≠
      causalReflectedOrientationHamiltonian := by
  intro hEqual
  have hEntry := congrFun (congrFun hEqual 0) 1
  norm_num [causalPositiveOrientationHamiltonian,
    causalReflectedOrientationHamiltonian,
    quotientCurvatureHamiltonian_exact] at hEntry
  have hImaginary := congrArg Complex.im hEntry
  norm_num at hImaginary

/-- Positive-frequency spectral evolution of the reflected ground/excited
assignment. -/
def causalReflectedOrientationEvolution (time : ℝ) : SquareMatrix 2 :=
  Complex.exp (((-2 * time : ℝ) : ℂ) * Complex.I) •
      negativeOrientationProjector +
    positiveOrientationProjector

theorem causalReflectedOrientationEvolution_conjTranspose (time : ℝ) :
    (causalReflectedOrientationEvolution time)ᴴ =
      star (Complex.exp (((-2 * time : ℝ) : ℂ) * Complex.I)) •
          negativeOrientationProjector +
        positiveOrientationProjector := by
  unfold causalReflectedOrientationEvolution
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul]
  simp [(positiveOrientationProjector_isPathDensity.1).eq,
    (negativeOrientationProjector_isPathDensity.1).eq]

theorem causalReflectedOrientationEvolution_unitary (time : ℝ) :
    (causalReflectedOrientationEvolution time)ᴴ *
        causalReflectedOrientationEvolution time = 1 := by
  rw [causalReflectedOrientationEvolution_conjTranspose]
  unfold causalReflectedOrientationEvolution
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul]
  rw [negativeOrientationProjector_idempotent,
    orientationProjectors_orthogonal_reverse,
    orientationProjectors_orthogonal,
    positiveOrientationProjector_idempotent]
  simp only [smul_zero, add_zero, zero_add, smul_smul]
  rw [mul_comm
    (Complex.exp (((-2 * time : ℝ) : ℂ) * Complex.I))
    (star (Complex.exp (((-2 * time : ℝ) : ℂ) * Complex.I)))]
  rw [causalPositive_excitedPhase_star_mul]
  simp only [one_smul]
  rw [add_comm]
  exact orientationProjectors_sum

theorem causalReflectedOrientationEvolution_quarter :
    causalReflectedOrientationEvolution (Real.pi / 2) =
      quotientCurvatureHamiltonian := by
  unfold causalReflectedOrientationEvolution
  rw [causalPositive_excitedPhase_quarter]
  unfold positiveOrientationProjector negativeOrientationProjector
  module

/-- The reflected but still positive-frequency clock produces the conjugate
transition coefficient `+i`. -/
theorem causalReflectedOrientationEvolution_quarter_path13 :
    causalReflectedOrientationEvolution (Real.pi / 2) * path13Ket =
      Complex.I • path22Ket := by
  rw [causalReflectedOrientationEvolution_quarter,
    quotientCurvatureHamiltonian_exact]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [path13Ket, path22Ket, Matrix.mul_apply,
      Fin.sum_univ_succ, Fin.ext_iff, Complex.I_sq]

/-- Coefficient of the elementary transition from the first causal route to
the second. -/
def elementaryClockBirthCoefficient (evolution : SquareMatrix 2) : ℂ :=
  ketInner path22Ket (evolution * path13Ket)

theorem positiveClockBirthCoefficient_eq_negI :
    elementaryClockBirthCoefficient
        (causalPositiveOrientationEvolution (Real.pi / 2)) =
      -Complex.I := by
  unfold elementaryClockBirthCoefficient
  rw [causalPositiveOrientationEvolution_quarter_path13]
  norm_num [ketInner, path22Ket, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_succ, Fin.ext_iff]

theorem reflectedClockBirthCoefficient_eq_posI :
    elementaryClockBirthCoefficient
        (causalReflectedOrientationEvolution (Real.pi / 2)) =
      Complex.I := by
  unfold elementaryClockBirthCoefficient
  rw [causalReflectedOrientationEvolution_quarter_path13]
  norm_num [ketInner, path22Ket, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_succ, Fin.ext_iff]

/-- The third named microscopic principle in its exact theorem-level shape:
the maximal-event signature character is identified with the first
orthogonal causal-route transition coefficient.  The definition does not
choose a sign; the oriented evolution supplied to it does. -/
def SatisfiesClockBirthIdentification
    (evolution : SquareMatrix 2) (weight : ℕ → ℕ → ℂ) : Prop :=
  weight 0 1 = elementaryClockBirthCoefficient evolution

theorem positiveClockBirthIdentification :
    SatisfiesClockBirthIdentification
      (causalPositiveOrientationEvolution (Real.pi / 2))
      (chiralMultiplicativeSignatureWeight 1) := by
  unfold SatisfiesClockBirthIdentification
  rw [positiveClockBirthCoefficient_eq_negI]
  norm_num [chiralMultiplicativeSignatureWeight,
    multiplicativeSignatureWeight, chiralMaximalEventPhase]

theorem reflectedClockBirthIdentification :
    SatisfiesClockBirthIdentification
      (causalReflectedOrientationEvolution (Real.pi / 2))
      (chiralMultiplicativeSignatureWeight 0) := by
  unfold SatisfiesClockBirthIdentification
  rw [reflectedClockBirthCoefficient_eq_posI]
  norm_num [chiralMultiplicativeSignatureWeight,
    multiplicativeSignatureWeight, chiralMaximalEventPhase]

/-- The reflected route has the same survival amplitude, so it has exactly the
same first orthogonal time despite producing the opposite transition phase. -/
theorem causalReflectedOrientationEnergySpectrum_survival_eq_pathOverlap
    (time : ℝ) :
    causalOrientationEnergySpectrum.survivalAmplitude time =
      ketInner path13Ket
        (causalReflectedOrientationEvolution time * path13Ket) := by
  let phase : ℂ :=
    Complex.exp (((-2 * time : ℝ) : ℂ) * Complex.I)
  have hSpectrum :
      causalOrientationEnergySpectrum.survivalAmplitude time =
        (1 + phase) / 2 := by
    unfold causalOrientationEnergySpectrum saturatingSpectrum
      EnergySpectrum.survivalAmplitude
    rw [Fin.sum_univ_two]
    simp only [Fin.isValue, if_true,
      show ((1 : Fin 2) = 0) = False from by decide, if_false]
    have hPhase :
        Complex.exp
            (-Complex.I * (((2 : ℝ) : ℂ)) * (time : ℂ)) = phase := by
      unfold phase
      congr 1
      push_cast
      ring
    rw [hPhase]
    norm_num
    ring
  have hPath :
      ketInner path13Ket
          (causalReflectedOrientationEvolution time * path13Ket) =
        (1 + phase) / 2 := by
    have hFirstComponent :
        (causalReflectedOrientationEvolution time * path13Ket) 0 0 =
          (1 + phase) / 2 := by
      unfold causalReflectedOrientationEvolution
        positiveOrientationProjector negativeOrientationProjector
      rw [quotientCurvatureHamiltonian_exact]
      norm_num [path13Ket, Matrix.mul_apply, Fin.sum_univ_succ,
        Fin.ext_iff]
      have hMatrixPhase :
          Complex.exp (-(2 * (time : ℂ) * Complex.I)) = phase := by
        unfold phase
        congr 1
        push_cast
        ring
      rw [hMatrixPhase]
      ring
    unfold ketInner
    rw [Matrix.mul_apply]
    simp only [Fin.sum_univ_two]
    norm_num [path13Ket, Matrix.conjTranspose_apply, Fin.ext_iff]
    exact hFirstComponent
  rw [hSpectrum, hPath]

theorem causalReflectedOrientationEvolution_firstOrthogonal
    (time : ℝ) (hTime : 0 ≤ time)
    (hOrthogonal :
      ketInner path13Ket
        (causalReflectedOrientationEvolution time * path13Ket) = 0) :
    Real.pi / 2 ≤ time := by
  have hSurvival :
      causalOrientationEnergySpectrum.survivalAmplitude time = 0 := by
    rw [causalReflectedOrientationEnergySpectrum_survival_eq_pathOverlap,
      hOrthogonal]
  exact causalOrientationBirth_quarter_is_minimal time hTime
    (congrArg Complex.re hSurvival) (congrArg Complex.im hSurvival)

/-- **Reflection tripwire.**  All reflection-even consistency requirements
leave two distinct, equally admissible clock Hamiltonians.  Their first
orthogonal births occur at the same time and carry conjugate phases.  Therefore
the `-i`/left endpoint is branch-relative; it is not selected by positivity,
ground-zero normalization, unitarity, or minimality alone. -/
theorem causal_clock_birth_reflection_tripwire :
    causalPositiveOrientationHamiltonian.PosSemidef
      ∧ causalReflectedOrientationHamiltonian.PosSemidef
      ∧ causalPositiveOrientationHamiltonian ≠
          causalReflectedOrientationHamiltonian
      ∧ causalPositiveOrientationEvolution (Real.pi / 2) * path13Ket =
          (-Complex.I) • path22Ket
      ∧ causalReflectedOrientationEvolution (Real.pi / 2) * path13Ket =
          Complex.I • path22Ket
      ∧ (∀ select : VacuumSpectatorCausalAction → Fin 2,
          ¬(∀ action,
            select (vacuumSpectatorActionReflection action) =
              reflectedMicroscopicChirality (select action))) := by
  exact ⟨causalPositiveOrientationHamiltonian_posSemidef,
    causalReflectedOrientationHamiltonian_posSemidef,
    causalPositive_reflectedHamiltonians_ne,
    causalPositiveOrientationEvolution_quarter_path13,
    causalReflectedOrientationEvolution_quarter_path13,
    no_reflection_covariant_vacuum_chirality_selector⟩

/-! ## 8. Branch-relative finite sign promotion -/

/-- On the positive-oriented branch, the transition coefficient matches
exactly one Bell-causal microscopic chirality, the left-selecting slot. -/
theorem causalPositiveBirth_unique_chiral_phase :
    ∃! chirality : Fin 2,
      chiralMaximalEventPhase chirality = -Complex.I := by
  refine ⟨1, ?_, ?_⟩
  · norm_num [chiralMaximalEventPhase]
  · intro chirality hPhase
    fin_cases chirality
    · have hImaginary := congrArg Complex.im hPhase
      norm_num [chiralMaximalEventPhase] at hImaginary
    · rfl

/-! ## 9. Promotion to the projective sequential-growth tower -/

/-- The normalized unlabeled sequential-growth law obtained by extending the
positive-branch elementary coefficient through the unique multiplicative
chiral signature character. -/
def causalPositiveOrientationGrowthLaw :
    RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch :=
  chiralCausalSetGrowthLaw 1

/-- The microscopic maximal-event character of the selected growth law is the
same `-i` generated by the positive causal Hamiltonian. -/
theorem causalPositiveOrientationGrowthLaw_maximalPhase :
    chiralMultiplicativeSignatureWeight 1 0 1 = -Complex.I := by
  norm_num [chiralMultiplicativeSignatureWeight,
    multiplicativeSignatureWeight, chiralMaximalEventPhase]

/-- Independent composition and the ancestor gauge extend the generated
elementary phase to one and only one complete signature weight. -/
theorem causalPositiveOrientationGrowthLaw_signature_unique
    (weight : ℕ → ℕ → ℂ)
    (hMultiplicative : IsMultiplicativeSignatureWeight weight)
    (hAncestor : weight 1 0 = 1)
    (hGeneratedPhase : weight 0 1 = -Complex.I) :
    weight = chiralMultiplicativeSignatureWeight 1 := by
  apply chiralMultiplicativeSignatureWeight_unique 1 weight
    hMultiplicative hAncestor
  simpa [chiralMaximalEventPhase] using hGeneratedPhase

/-- Every finite restriction of the Hamiltonian-selected growth law is
normalized and strongly positive. -/
theorem causalPositiveOrientationGrowthLaw_finite_quantum_consistency
    (depth : ℕ) :
    IsNormalizedGrowthFunctional
        (finiteRankedDepthDecoherence
          causalPositiveOrientationGrowthLaw depth)
      ∧ IsStronglyPositiveGrowthFunctional
        (growthEventDecoherence
          (finiteRankedDepthDecoherence
            causalPositiveOrientationGrowthLaw depth)) := by
  exact ⟨finiteRankedDepthDecoherence_normalized
      causalPositiveOrientationGrowthLaw depth,
    finiteRankedDepthDecoherence_stronglyPositive
      causalPositiveOrientationGrowthLaw depth⟩

/-- Its decoherence functional is exactly projectively consistent under every
one-step refinement. -/
theorem causalPositiveOrientationGrowthLaw_projective
    (depth : ℕ)
    (first second : Finset
      (RankedGrowthPath CausalSetGrowthBranch depth)) :
    growthEventDecoherence
        (finiteRankedDepthDecoherence
          causalPositiveOrientationGrowthLaw (depth + 1))
        (refineRankedGrowthEvent first) (refineRankedGrowthEvent second) =
      growthEventDecoherence
        (finiteRankedDepthDecoherence
          causalPositiveOrientationGrowthLaw depth) first second := by
  exact finiteRankedDepthDecoherence_projective
    causalPositiveOrientationGrowthLaw depth first second

/-- At the first nontrivial route partition, the selected sequential-growth
law produces the pure endpoint `y=-1/2` rather than receiving it as separate
boundary data. -/
theorem causalPositiveOrientationGrowthLaw_kernel :
    inducedOrientationKernel causalPositiveOrientationGrowthLaw
        chiralRankTwoCoarseGraining =
      balancedHistoryKernel (-1 / 2) := by
  unfold causalPositiveOrientationGrowthLaw
  rw [chiral_inducedOrientationKernel_exact,
    futurePositiveFrequency_orientation_endpoint]

/-- **Generated-sign transport.**  The nonzero cylinder sign produced at the
first branching depth is `Xi=+1` and is transported unchanged through every
finite projective refinement. -/
theorem causalPositiveOrientationGrowthLaw_sign_transport (steps : ℕ) :
    inducedCylinderChiralitySign causalPositiveOrientationGrowthLaw
        (chiralRankTwoCoarseGraining.refineBy steps) = 1 := by
  rw [inducedCylinderChiralitySign_refineBy]
  unfold inducedCylinderChiralitySign causalPositiveOrientationGrowthLaw
  rw [chiral_inducedOrientationParameter_exact,
    futurePositiveFrequency_orientation_endpoint]
  ring

/-- Reflection partner of the branch-selected growth law. -/
def causalReflectedOrientationGrowthLaw :
    RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch :=
  chiralCausalSetGrowthLaw 0

theorem causalReflectedOrientationGrowthLaw_maximalPhase :
    chiralMultiplicativeSignatureWeight 0 0 1 = Complex.I := by
  norm_num [chiralMultiplicativeSignatureWeight,
    multiplicativeSignatureWeight, chiralMaximalEventPhase]

theorem causalReflectedOrientationGrowthLaw_kernel :
    inducedOrientationKernel causalReflectedOrientationGrowthLaw
        chiralRankTwoCoarseGraining =
      balancedHistoryKernel (1 / 2) := by
  unfold causalReflectedOrientationGrowthLaw
  rw [chiral_inducedOrientationKernel_exact]
  norm_num [chiralBoundaryOrientationParameter, chiralMaximalEventPhase]

theorem causalReflectedOrientationGrowthLaw_sign_transport (steps : ℕ) :
    inducedCylinderChiralitySign causalReflectedOrientationGrowthLaw
        (chiralRankTwoCoarseGraining.refineBy steps) = -1 := by
  rw [inducedCylinderChiralitySign_refineBy]
  unfold inducedCylinderChiralitySign causalReflectedOrientationGrowthLaw
  rw [chiral_inducedOrientationParameter_exact]
  norm_num [chiralBoundaryOrientationParameter, chiralMaximalEventPhase]

/-- The full projective construction remains a reflection doublet.  The same
positive-frequency rule, zero-ground normalization, first-orthogonal clock,
composition law, normalization, and refinement transport produce opposite
nonzero cylinder signs on the two reflected branches. -/
theorem projective_clock_birth_reflection_doublet :
    SatisfiesClockBirthIdentification
        (causalPositiveOrientationEvolution (Real.pi / 2))
        (chiralMultiplicativeSignatureWeight 1)
      ∧ SatisfiesClockBirthIdentification
        (causalReflectedOrientationEvolution (Real.pi / 2))
        (chiralMultiplicativeSignatureWeight 0)
      ∧ (∀ steps : ℕ,
          inducedCylinderChiralitySign causalPositiveOrientationGrowthLaw
            (chiralRankTwoCoarseGraining.refineBy steps) = 1)
      ∧ (∀ steps : ℕ,
          inducedCylinderChiralitySign causalReflectedOrientationGrowthLaw
            (chiralRankTwoCoarseGraining.refineBy steps) = -1) := by
  exact ⟨positiveClockBirthIdentification,
    reflectedClockBirthIdentification,
    causalPositiveOrientationGrowthLaw_sign_transport,
    causalReflectedOrientationGrowthLaw_sign_transport⟩

/-- **The geometric and birth channels do not merge at large rank.**  Every
finite geometric orientation datum has a uniform strict quarter-gap from both
pure birth endpoints.  Since the bound is independent of rank, no sequence of
such data can converge to either endpoint. -/
theorem geometric_clockBirth_channels_uniformly_disjoint {n : ℕ}
    (parent : CardinalCausalOrder n) (event : Fin n) :
    (1 : ℚ) / 4 <
        |(1 : ℚ) / 2 - causalOrientationDensityQ parent event|
      ∧ (1 : ℚ) / 4 <
        |-(1 : ℚ) / 2 - causalOrientationDensityQ parent event| :=
  geometricOrientation_uniform_gap_from_pure_endpoints parent event

/-- **Finite positive-branch derivation.**  After choosing the `H_plus`
orientation branch, its first orthogonal birth is the exact
Margolus--Levitin-saturating transition `path13 -> -i path22`.  The coefficient
selects `Xi=+1` and the standard nontrivial left-handed weak vertex.  The
reflection tripwire above proves that this is conditional on the branch
alignment, not an absolute vacuum selection. -/
theorem finite_causal_positive_energy_derives_left_handed_weak_interaction :
    causalPositiveOrientationHamiltonian.PosSemidef
      ∧ ketInner path13Ket path22Ket = 0
      ∧ causalPositiveOrientationEvolution (Real.pi / 2) * path13Ket =
          (-Complex.I) • path22Ket
      ∧ (Real.pi / 2) *
          causalOrientationEnergySpectrum.energyExpectation = Real.pi / 2
      ∧ (∃! chirality : Fin 2,
          chiralMaximalEventPhase chirality = -Complex.I)
      ∧ IsNontrivialPurelyLeftHanded
          (causalWeakVertex
            (-2 * chiralBoundaryOrientationParameter (1 : Fin 2))
            weakRaising) := by
  refine ⟨causalPositiveOrientationHamiltonian_posSemidef,
    pathKets_orthogonal,
    causalPositiveOrientationEvolution_quarter_path13,
    causalOrientationBirth_saturates_margolusLevitin,
    causalPositiveBirth_unique_chiral_phase, ?_⟩
  rw [futurePositiveFrequency_selects_leftWeakVertex]
  exact standard_charged_current_is_nontrivial_purely_left

/-- **Positive-branch projective capstone.**  The chosen orientation
Hamiltonian gives `-i`; composition extends it uniquely to a normalized
unlabeled growth law; all finite decoherence functionals are normalized,
strongly positive, and projectively consistent; the induced nonzero `Xi=+1`
sign survives every refinement and selects the standard left-handed charged
current.  `projective_clock_birth_reflection_doublet` is the accompanying
absolute-claim boundary. -/
theorem causal_positive_energy_sequential_growth_derives_left_handedness :
    causalPositiveOrientationHamiltonian.PosSemidef
      ∧ (∀ time : ℝ,
        (causalPositiveOrientationEvolution time)ᴴ *
            causalPositiveOrientationEvolution time = 1)
      ∧ causalPositiveOrientationEvolution (Real.pi / 2) * path13Ket =
          (-Complex.I) • path22Ket
      ∧ chiralMultiplicativeSignatureWeight 1 0 1 = -Complex.I
      ∧ (∀ depth : ℕ,
          IsNormalizedGrowthFunctional
              (finiteRankedDepthDecoherence
                causalPositiveOrientationGrowthLaw depth)
            ∧ IsStronglyPositiveGrowthFunctional
              (growthEventDecoherence
                (finiteRankedDepthDecoherence
                  causalPositiveOrientationGrowthLaw depth)))
      ∧ (∀ (depth : ℕ)
          (first second : Finset
            (RankedGrowthPath CausalSetGrowthBranch depth)),
          growthEventDecoherence
              (finiteRankedDepthDecoherence
                causalPositiveOrientationGrowthLaw (depth + 1))
              (refineRankedGrowthEvent first)
              (refineRankedGrowthEvent second) =
            growthEventDecoherence
              (finiteRankedDepthDecoherence
                causalPositiveOrientationGrowthLaw depth) first second)
      ∧ (∀ steps : ℕ,
          inducedCylinderChiralitySign causalPositiveOrientationGrowthLaw
            (chiralRankTwoCoarseGraining.refineBy steps) = 1)
      ∧ IsNontrivialPurelyLeftHanded
          (causalWeakVertex
            (-2 * chiralBoundaryOrientationParameter (1 : Fin 2))
            weakRaising) := by
  refine ⟨causalPositiveOrientationHamiltonian_posSemidef,
    causalPositiveOrientationEvolution_unitary,
    causalPositiveOrientationEvolution_quarter_path13,
    causalPositiveOrientationGrowthLaw_maximalPhase,
    causalPositiveOrientationGrowthLaw_finite_quantum_consistency,
    causalPositiveOrientationGrowthLaw_projective,
    causalPositiveOrientationGrowthLaw_sign_transport, ?_⟩
  rw [futurePositiveFrequency_selects_leftWeakVertex]
  exact standard_charged_current_is_nontrivial_purely_left

#print axioms futurePositiveFrequencyPhase_quarter_turn
#print axioms futurePositiveFrequencyPhase_reverse_time
#print axioms futurePositiveFrequency_unique_microscopic_chirality
#print axioms future_positive_frequency_derives_left_handed_weak_interaction
#print axioms causalOrientationHamiltonianShift_zeroGround_unique
#print axioms causalOrientationHamiltonianShift_posSemidef_iff
#print axioms causalPositiveOrientationHamiltonian_posSemidef
#print axioms causalPositiveOrientationHamiltonian_nondegenerate_spectralPair
#print axioms causalPositiveOrientationEvolution_unitary
#print axioms causalPositiveOrientationEvolution_quarter_path13
#print axioms causalPositiveOrientationEvolution_negativeQuarter_path13
#print axioms causalOrientationBirth_quarter_is_minimal
#print axioms causalPositiveOrientationEvolution_firstOrthogonal
#print axioms causalReflectedOrientationEvolution_unitary
#print axioms causalReflectedOrientationEvolution_quarter_path13
#print axioms causal_clock_birth_reflection_tripwire
#print axioms finite_causal_positive_energy_derives_left_handed_weak_interaction
#print axioms causalPositiveOrientationGrowthLaw_signature_unique
#print axioms causalPositiveOrientationGrowthLaw_projective
#print axioms causalPositiveOrientationGrowthLaw_sign_transport
#print axioms projective_clock_birth_reflection_doublet
#print axioms geometric_clockBirth_channels_uniformly_disjoint
#print axioms causal_positive_energy_sequential_growth_derives_left_handedness

end

end UnifiedTheory.Audit.KFCausalSetFutureFrequencyHandedness
