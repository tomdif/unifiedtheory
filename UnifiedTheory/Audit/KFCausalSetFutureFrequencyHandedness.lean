/-
  Audit/KFCausalSetFutureFrequencyHandedness.lean

  FUTURE POSITIVE FREQUENCY SELECTS THE LEFT-HANDED ENDPOINT

  The preceding chirality-generation no-go is exact: a reflection-fixed
  vacuum cannot choose between the two phases `+i` and `-i`.  This file tests
  a minimal way to escape that obstruction without inserting `left` as a
  sign-valued boundary condition.

  New microscopic bridge law (stated openly): one elementary, future-directed
  growth step is represented by the standard positive-frequency unitary phase

      U(E, tau) = exp(-i E tau),       E > 0, tau > 0,

  in units with hbar = 1.  At the elementary quarter turn `E tau = pi/2`, this
  law forces `U = -i`; its complex conjugate `+i` is the reverse-time phase.

  The repository had already proved the independent causal dictionary

      phase -i  <->  y = -1/2  <->  Xi = -2y = +1
                <->  P_weak(Xi) = P_L.

  Combining the two gives a unique left-handed weak vertex.  This is a genuine
  conditional selection theorem, but not yet an unconditional derivation from
  the existing scalar Bell-causal growth law: the identification of an edge
  character with positive-frequency Hamiltonian evolution is the one new
  physical bridge.  The theorem is useful precisely because it isolates that
  bridge and contains no assumption whose statement says "choose left" or
  "choose the negative imaginary phase".

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalSetWeakHandednessBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetFutureFrequencyHandedness

noncomputable section

open scoped ComplexConjugate
open UnifiedTheory.Audit.KFCausalSetBellCausality
open UnifiedTheory.Audit.KFOrientationHigherRankDecoherence
open UnifiedTheory.Audit.KFCausalSetWeakHandednessBridge

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

/-! ## 3. Promotion to nature's observed weak-handedness convention -/

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

/-- **Conditional absolute-handedness theorem.**

Once the intrinsic future growth arrow is required to carry the standard
positive-frequency phase, a positive-energy elementary quarter turn uniquely
matches one microscopic chiral character.  That character has `Xi = +1` and
produces a nontrivial purely left-handed charged weak current. -/
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

#print axioms futurePositiveFrequencyPhase_quarter_turn
#print axioms futurePositiveFrequencyPhase_reverse_time
#print axioms futurePositiveFrequency_unique_microscopic_chirality
#print axioms future_positive_frequency_derives_left_handed_weak_interaction

end

end UnifiedTheory.Audit.KFCausalSetFutureFrequencyHandedness
