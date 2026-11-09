/- Synthesis of the Standard Model fiber Yukawa hierarchy (`democraticMatrix`,
`perturbedYukawa`, one massive + two massless generations, CKM diagonal
dominance, Jarlskog suppression, Wolfenstein hierarchy) with 3-generation
multi-packet source neutrality and arbitrary-degree `M` polynomial response
lower bounds. -/
import UnifiedTheory.Audit.KFCausalSMThreeGenerationFiberMultiPacketInstantiation
import UnifiedTheory.LayerB.YukawaFromFiber

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalSMYukawaHierarchyMultiPacketSynthesis
noncomputable section
open UnifiedTheory.LayerB.GenerationsFromFiber (generationCount three_generations)
open UnifiedTheory.LayerB.YukawaFromFiber
  (democraticMatrix democratic_trace democratic_idempotent_relation
   democratic_eigenvector_massive democratic_eigenvector_massless
   democratic_one_massive_two_massless perturbedYukawa perturbed_at_zero
   democratic_limit_two_massless geometric_hierarchy jarlskog_suppressed
   mass_ratio_exceeds_one ckm_diagonal_dominance
   wolfenstein_lambda wolfenstein_in_range wolfenstein_jarlskog wolfenstein_mass_ratio)
open UnifiedTheory.Audit.KFCausalCommonComplexDegreeMPolynomialResponseLowerBound
  (factoredPolyProfile degreeMPolyProfile cauchySchwarzWeightRatio
   seconds_factored_neutral_zero inputLift_factored_neutral_zero
   momentumLift_factored_neutral_zero
   momentum_degreeM_neutral_eq_constant output_degreeM_neutral_eq_constant
   momentumOutput_degreeM_neutral_eq_constant
   hamiltonianOutput_degreeM_neutral_eq_constant
   inputLift_degreeM_neutral_eq_constant momentumLift_degreeM_neutral_eq_constant
   clockKineticEnergy_degreeM_neutral_eq_constant
   clockKineticResponse_degreeM_neutral_eq_constant
   potentialEnergy_degreeM_neutral_eq_constant
   potentialResponse_degreeM_neutral_eq_constant
   fullEnergy_degreeM_neutral_eq_constant fullResponse_degreeM_neutral_eq_constant)
open UnifiedTheory.Audit.KFCausalSMThreeGenerationFiberMultiPacketInstantiation
  (smThreeGenWeights smThreeGenAmplitudes
   smThreeGen_weighted_sum_eq
   smThreeGen_state_factored_neutral_zero
   smThreeGen_momentum_factored_neutral_zero
   smThreeGen_output_factored_neutral_zero
   smThreeGen_momentumOutput_factored_neutral_zero
   smThreeGen_hamiltonianOutput_factored_neutral_zero
   smThreeGen_fullEnergy_factored_neutral_zero
   smThreeGen_fullResponse_factored_neutral_zero
   smThreeGen_state_degreeM_eq_constant
   smThreeGen_fullEnergy_degreeM_eq
   smThreeGen_degreeM_fullEnergy_lower_unit
   smThreeGen_clockKinetic_lower_degreeM
   smThreeGen_full_bound_degreeM)
open KFCausalReciprocalNeutralSuperposition (state momentum output momentumOutput)
open KFCausalReciprocalNeutralHamiltonian (inputLift momentumLift fullEnergy fullResponse)
open KFCausalReciprocalNeutralKineticResponse (clockKineticEnergy clockKineticResponse)
open KFCausalWeightedReciprocalNeutralPotentialTransport (potentialEnergy potentialResponse)
open KFCausalReciprocalNeutralStrongHamiltonian (seconds hamiltonianOutput)

/-! ### 1. Bridge Between Democratic / Massless Yukawa Modes and Multi-Packet Neutrality -/

def realGenModeToComplex (w : Fin 3 → ℝ) (i : Fin 3) : ℂ :=
  (w i : ℂ)

def democraticGenMode : Fin 3 → ℝ :=
  fun _ => 1

def masslessMode₁ : Fin 3 → ℝ :=
  fun i => if i = 0 then 1 else if i = 1 then -1 else 0

def masslessMode₂ : Fin 3 → ℝ :=
  fun i => if i = 0 then 1 else if i = 2 then -1 else 0

theorem realGenModeToComplex_democratic :
    realGenModeToComplex democraticGenMode = smThreeGenWeights := by
  funext _
  simp [realGenModeToComplex, democraticGenMode, smThreeGenWeights]

theorem democratic_mulVec_democraticGenMode (y₀ : ℝ) :
    (democraticMatrix y₀).mulVec democraticGenMode = (3 * y₀) • democraticGenMode :=
  democratic_eigenvector_massive y₀

theorem realGenModeToComplex_sum_eq (w : Fin 3 → ℝ) :
    realGenModeToComplex w 0 + realGenModeToComplex w 1 + realGenModeToComplex w 2 =
      ((w 0 + w 1 + w 2 : ℝ) : ℂ) := by
  simp [realGenModeToComplex]

theorem realGenModeToComplex_sum_zero_of_ortho (w : Fin 3 → ℝ)
    (h_ortho : w 0 + w 1 + w 2 = 0) :
    realGenModeToComplex w 0 + realGenModeToComplex w 1 + realGenModeToComplex w 2 = 0 := by
  rw [realGenModeToComplex_sum_eq, h_ortho, Complex.ofReal_zero]

theorem realGenModeToComplex_weighted_sum_zero_of_ortho (w : Fin 3 → ℝ)
    (h_ortho : w 0 + w 1 + w 2 = 0) :
    ∑ i : Fin 3, smThreeGenWeights i * realGenModeToComplex w i = 0 :=
  (smThreeGen_weighted_sum_eq (realGenModeToComplex w)).trans
    (realGenModeToComplex_sum_zero_of_ortho w h_ortho)

theorem masslessMode₁_ortho :
    masslessMode₁ 0 + masslessMode₁ 1 + masslessMode₁ 2 = 0 := by
  simp [masslessMode₁]

theorem masslessMode₂_ortho :
    masslessMode₂ 0 + masslessMode₂ 1 + masslessMode₂ 2 = 0 := by
  simp [masslessMode₂]

theorem massless_mode_yukawa_and_neutral_bridge (y₀ : ℝ) (w : Fin 3 → ℝ)
    (h_ortho : w 0 + w 1 + w 2 = 0) :
    (democraticMatrix y₀).mulVec w = 0 ∧
      (perturbedYukawa y₀ 0).mulVec w = 0 ∧
      ∑ i : Fin 3, smThreeGenWeights i * realGenModeToComplex w i = 0 :=
  ⟨democratic_eigenvector_massless y₀ w h_ortho,
   democratic_limit_two_massless y₀ w h_ortho,
   realGenModeToComplex_weighted_sum_zero_of_ortho w h_ortho⟩

/-! ### 2. Exact Multi-Packet Vacuum Decoupling of Massless Generation Modes -/

variable (ε h a₀ w₀ p₀ : ℝ) (b₀ : ℂ) (w : Fin 3 → ℝ) (Q : Polynomial ℂ)
  (hε : 0 < ε) (ha₀ : 0 < a₀) (hh : h ≠ 0) (hw₀ : 1 ≤ w₀)
  (hb : |h| ≤ 2 * Real.pi * ε / 3)

theorem massless_mode_state_zero (h_ortho : w 0 + w 1 + w 2 = 0) :
    state 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (factoredPolyProfile (realGenModeToComplex w) Q)
        hε (fun _ => ha₀) hh (fun _ => hw₀) = 0 :=
  smThreeGen_state_factored_neutral_zero ε h a₀ w₀ p₀ b₀ (realGenModeToComplex w) Q
    hε ha₀ hh hw₀ (realGenModeToComplex_sum_zero_of_ortho w h_ortho)

theorem massless_mode_momentum_zero (h_ortho : w 0 + w 1 + w 2 = 0) :
    momentum 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (factoredPolyProfile (realGenModeToComplex w) Q)
        hε (fun _ => ha₀) hh (fun _ => hw₀) = 0 :=
  smThreeGen_momentum_factored_neutral_zero ε h a₀ w₀ p₀ b₀ (realGenModeToComplex w) Q
    hε ha₀ hh hw₀ (realGenModeToComplex_sum_zero_of_ortho w h_ortho)

theorem massless_mode_output_zero (h_ortho : w 0 + w 1 + w 2 = 0) (j : Fin 8) :
    output 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (factoredPolyProfile (realGenModeToComplex w) Q)
        hε (fun _ => ha₀) hh (fun _ => hw₀) hb j = 0 :=
  smThreeGen_output_factored_neutral_zero ε h a₀ w₀ p₀ b₀ (realGenModeToComplex w) Q
    hε ha₀ hh hw₀ hb (realGenModeToComplex_sum_zero_of_ortho w h_ortho) j

theorem massless_mode_momentumOutput_zero (h_ortho : w 0 + w 1 + w 2 = 0) (j : Fin 8) :
    momentumOutput 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (factoredPolyProfile (realGenModeToComplex w) Q)
        hε (fun _ => ha₀) hh (fun _ => hw₀) hb j = 0 :=
  smThreeGen_momentumOutput_factored_neutral_zero ε h a₀ w₀ p₀ b₀ (realGenModeToComplex w) Q
    hε ha₀ hh hw₀ hb (realGenModeToComplex_sum_zero_of_ortho w h_ortho) j

theorem massless_mode_seconds_zero (h_ortho : w 0 + w 1 + w 2 = 0)
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (j : Fin 8) :
    seconds 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (factoredPolyProfile (realGenModeToComplex w) Q)
        hε (fun _ => ha₀) hh (fun _ => hw₀) hb_narrow j = 0 :=
  seconds_factored_neutral_zero 3 ε h a₀ w₀ p₀ b₀ smThreeGenWeights
    (realGenModeToComplex w) Q hε ha₀ hh hw₀
    (realGenModeToComplex_weighted_sum_zero_of_ortho w h_ortho) hb_narrow j

theorem massless_mode_hamiltonianOutput_zero (h_ortho : w 0 + w 1 + w 2 = 0)
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    hamiltonianOutput 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (factoredPolyProfile (realGenModeToComplex w) Q)
        hε (fun _ => ha₀) hh (fun _ => hw₀) hb_narrow mass2 quartic vacuum t = 0 :=
  smThreeGen_hamiltonianOutput_factored_neutral_zero ε h a₀ w₀ p₀ b₀ (realGenModeToComplex w) Q
    hε ha₀ hh hw₀ (realGenModeToComplex_sum_zero_of_ortho w h_ortho) hb_narrow mass2 quartic vacuum t

theorem massless_mode_inputLift_zero (h_ortho : w 0 + w 1 + w 2 = 0)
    (mass2 quartic vacuum t : ℝ) :
    inputLift 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (factoredPolyProfile (realGenModeToComplex w) Q)
        hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t = 0 :=
  inputLift_factored_neutral_zero 3 ε h a₀ w₀ p₀ b₀ smThreeGenWeights
    (realGenModeToComplex w) Q hε ha₀ hh hw₀ hb
    (realGenModeToComplex_weighted_sum_zero_of_ortho w h_ortho) mass2 quartic vacuum t

theorem massless_mode_momentumLift_zero (h_ortho : w 0 + w 1 + w 2 = 0)
    (mass2 quartic vacuum t : ℝ) :
    momentumLift 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (factoredPolyProfile (realGenModeToComplex w) Q)
        hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t = 0 :=
  momentumLift_factored_neutral_zero 3 ε h a₀ w₀ p₀ b₀ smThreeGenWeights
    (realGenModeToComplex w) Q hε ha₀ hh hw₀ hb
    (realGenModeToComplex_weighted_sum_zero_of_ortho w h_ortho) mass2 quartic vacuum t

theorem massless_mode_fullEnergy_zero (h_ortho : w 0 + w 1 + w 2 = 0)
    (mass2 quartic vacuum t : ℝ) :
    fullEnergy 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (factoredPolyProfile (realGenModeToComplex w) Q)
        hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t = 0 :=
  smThreeGen_fullEnergy_factored_neutral_zero ε h a₀ w₀ p₀ b₀ (realGenModeToComplex w) Q
    hε ha₀ hh hw₀ hb (realGenModeToComplex_sum_zero_of_ortho w h_ortho) mass2 quartic vacuum t

theorem massless_mode_fullResponse_zero (h_ortho : w 0 + w 1 + w 2 = 0)
    (mass2 quartic vacuum t : ℝ) :
    fullResponse 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (factoredPolyProfile (realGenModeToComplex w) Q)
        hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t = 0 :=
  smThreeGen_fullResponse_factored_neutral_zero ε h a₀ w₀ p₀ b₀ (realGenModeToComplex w) Q
    hε ha₀ hh hw₀ hb (realGenModeToComplex_sum_zero_of_ortho w h_ortho) mass2 quartic vacuum t

/-! ### 3. Democratic + Massless Degree-`M` Multi-Packet Decomposition & Master Synthesis -/

def yukawaDegreeMPolyProfile (M : ℕ) (z : ℂ) (w : Fin M → Fin 3 → ℝ) :
    Fin 3 → Polynomial ℂ :=
  degreeMPolyProfile M (smThreeGenAmplitudes z) (fun r => realGenModeToComplex (w r))

theorem yukawaDegreeM_massless_modes_zero (y₀ : ℝ) (M : ℕ) (w : Fin M → Fin 3 → ℝ)
    (hw : ∀ r : Fin M, w r 0 + w r 1 + w r 2 = 0) (r : Fin M) :
    (democraticMatrix y₀).mulVec (w r) = 0 ∧ (perturbedYukawa y₀ 0).mulVec (w r) = 0 :=
  ⟨democratic_eigenvector_massless y₀ (w r) (hw r),
   democratic_limit_two_massless y₀ (w r) (hw r)⟩

theorem yukawaDegreeM_state_eq_democratic (M : ℕ) (z : ℂ) (w : Fin M → Fin 3 → ℝ)
    (hw : ∀ r : Fin M, w r 0 + w r 1 + w r 2 = 0) :
    state 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (yukawaDegreeMPolyProfile M z w) hε (fun _ => ha₀) hh (fun _ => hw₀) =
      state 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (fun i => Polynomial.C (smThreeGenAmplitudes z i)) hε (fun _ => ha₀) hh (fun _ => hw₀) :=
  smThreeGen_state_degreeM_eq_constant ε h a₀ w₀ p₀ b₀ hε ha₀ hh hw₀ M z
    (fun r => realGenModeToComplex (w r))
    (fun r => realGenModeToComplex_sum_zero_of_ortho (w r) (hw r))

theorem yukawaDegreeM_momentum_eq_democratic (M : ℕ) (z : ℂ) (w : Fin M → Fin 3 → ℝ)
    (hw : ∀ r : Fin M, w r 0 + w r 1 + w r 2 = 0) :
    momentum 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (yukawaDegreeMPolyProfile M z w) hε (fun _ => ha₀) hh (fun _ => hw₀) =
      momentum 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (fun i => Polynomial.C (smThreeGenAmplitudes z i)) hε (fun _ => ha₀) hh (fun _ => hw₀) :=
  momentum_degreeM_neutral_eq_constant 3 ε h a₀ w₀ p₀ b₀ smThreeGenWeights
    (smThreeGenAmplitudes z) hε ha₀ hh hw₀ M (fun r => realGenModeToComplex (w r))
    (fun r => realGenModeToComplex_weighted_sum_zero_of_ortho (w r) (hw r))

theorem yukawaDegreeM_output_eq_democratic (M : ℕ) (z : ℂ) (w : Fin M → Fin 3 → ℝ)
    (hw : ∀ r : Fin M, w r 0 + w r 1 + w r 2 = 0) (j : Fin 8) :
    output 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (yukawaDegreeMPolyProfile M z w) hε (fun _ => ha₀) hh (fun _ => hw₀) hb j =
      output 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (fun i => Polynomial.C (smThreeGenAmplitudes z i)) hε (fun _ => ha₀) hh (fun _ => hw₀) hb j :=
  output_degreeM_neutral_eq_constant 3 ε h a₀ w₀ p₀ b₀ smThreeGenWeights
    (smThreeGenAmplitudes z) hε ha₀ hh hw₀ hb M (fun r => realGenModeToComplex (w r))
    (fun r => realGenModeToComplex_weighted_sum_zero_of_ortho (w r) (hw r)) j

theorem yukawaDegreeM_momentumOutput_eq_democratic (M : ℕ) (z : ℂ) (w : Fin M → Fin 3 → ℝ)
    (hw : ∀ r : Fin M, w r 0 + w r 1 + w r 2 = 0) (j : Fin 8) :
    momentumOutput 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (yukawaDegreeMPolyProfile M z w) hε (fun _ => ha₀) hh (fun _ => hw₀) hb j =
      momentumOutput 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (fun i => Polynomial.C (smThreeGenAmplitudes z i)) hε (fun _ => ha₀) hh (fun _ => hw₀) hb j :=
  momentumOutput_degreeM_neutral_eq_constant 3 ε h a₀ w₀ p₀ b₀ smThreeGenWeights
    (smThreeGenAmplitudes z) hε ha₀ hh hw₀ hb M (fun r => realGenModeToComplex (w r))
    (fun r => realGenModeToComplex_weighted_sum_zero_of_ortho (w r) (hw r)) j

theorem yukawaDegreeM_hamiltonianOutput_eq_democratic (M : ℕ) (z : ℂ) (w : Fin M → Fin 3 → ℝ)
    (hw : ∀ r : Fin M, w r 0 + w r 1 + w r 2 = 0)
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    hamiltonianOutput 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (yukawaDegreeMPolyProfile M z w) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb_narrow mass2 quartic vacuum t =
      hamiltonianOutput 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (fun i => Polynomial.C (smThreeGenAmplitudes z i)) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb_narrow mass2 quartic vacuum t :=
  hamiltonianOutput_degreeM_neutral_eq_constant 3 ε h a₀ w₀ p₀ b₀ smThreeGenWeights
    (smThreeGenAmplitudes z) hε ha₀ hh hw₀ M (fun r => realGenModeToComplex (w r))
    (fun r => realGenModeToComplex_weighted_sum_zero_of_ortho (w r) (hw r))
    hb_narrow mass2 quartic vacuum t

theorem yukawaDegreeM_inputLift_eq_democratic (M : ℕ) (z : ℂ) (w : Fin M → Fin 3 → ℝ)
    (hw : ∀ r : Fin M, w r 0 + w r 1 + w r 2 = 0)
    (mass2 quartic vacuum t : ℝ) :
    inputLift 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (yukawaDegreeMPolyProfile M z w) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t =
      inputLift 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (fun i => Polynomial.C (smThreeGenAmplitudes z i)) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t :=
  inputLift_degreeM_neutral_eq_constant 3 ε h a₀ w₀ p₀ b₀ smThreeGenWeights
    (smThreeGenAmplitudes z) hε ha₀ hh hw₀ hb M (fun r => realGenModeToComplex (w r))
    (fun r => realGenModeToComplex_weighted_sum_zero_of_ortho (w r) (hw r))
    mass2 quartic vacuum t

theorem yukawaDegreeM_momentumLift_eq_democratic (M : ℕ) (z : ℂ) (w : Fin M → Fin 3 → ℝ)
    (hw : ∀ r : Fin M, w r 0 + w r 1 + w r 2 = 0)
    (mass2 quartic vacuum t : ℝ) :
    momentumLift 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (yukawaDegreeMPolyProfile M z w) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t =
      momentumLift 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (fun i => Polynomial.C (smThreeGenAmplitudes z i)) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t :=
  momentumLift_degreeM_neutral_eq_constant 3 ε h a₀ w₀ p₀ b₀ smThreeGenWeights
    (smThreeGenAmplitudes z) hε ha₀ hh hw₀ hb M (fun r => realGenModeToComplex (w r))
    (fun r => realGenModeToComplex_weighted_sum_zero_of_ortho (w r) (hw r))
    mass2 quartic vacuum t

theorem yukawaDegreeM_clockKineticEnergy_eq_democratic (M : ℕ) (z : ℂ) (w : Fin M → Fin 3 → ℝ)
    (hw : ∀ r : Fin M, w r 0 + w r 1 + w r 2 = 0) (t : ℝ) :
    clockKineticEnergy 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (yukawaDegreeMPolyProfile M z w) hε (fun _ => ha₀) hh (fun _ => hw₀) hb t =
      clockKineticEnergy 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (fun i => Polynomial.C (smThreeGenAmplitudes z i)) hε (fun _ => ha₀) hh (fun _ => hw₀) hb t :=
  clockKineticEnergy_degreeM_neutral_eq_constant 3 ε h a₀ w₀ p₀ b₀ smThreeGenWeights
    (smThreeGenAmplitudes z) hε ha₀ hh hw₀ hb M (fun r => realGenModeToComplex (w r))
    (fun r => realGenModeToComplex_weighted_sum_zero_of_ortho (w r) (hw r)) t

theorem yukawaDegreeM_clockKineticResponse_eq_democratic (M : ℕ) (z : ℂ) (w : Fin M → Fin 3 → ℝ)
    (hw : ∀ r : Fin M, w r 0 + w r 1 + w r 2 = 0) (t : ℝ) :
    clockKineticResponse 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (yukawaDegreeMPolyProfile M z w) hε (fun _ => ha₀) hh (fun _ => hw₀) hb t =
      clockKineticResponse 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (fun i => Polynomial.C (smThreeGenAmplitudes z i)) hε (fun _ => ha₀) hh (fun _ => hw₀) hb t :=
  clockKineticResponse_degreeM_neutral_eq_constant 3 ε h a₀ w₀ p₀ b₀ smThreeGenWeights
    (smThreeGenAmplitudes z) hε ha₀ hh hw₀ hb M (fun r => realGenModeToComplex (w r))
    (fun r => realGenModeToComplex_weighted_sum_zero_of_ortho (w r) (hw r)) t

theorem yukawaDegreeM_potentialEnergy_eq_democratic (M : ℕ) (z : ℂ) (w : Fin M → Fin 3 → ℝ)
    (hw : ∀ r : Fin M, w r 0 + w r 1 + w r 2 = 0) (mass2 quartic vacuum : ℝ) :
    potentialEnergy mass2 quartic vacuum 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
        smThreeGenWeights (fun _ => b₀) (yukawaDegreeMPolyProfile M z w)
        hε (fun _ => ha₀) hh (fun _ => hw₀) hb =
      potentialEnergy mass2 quartic vacuum 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
        smThreeGenWeights (fun _ => b₀) (fun i => Polynomial.C (smThreeGenAmplitudes z i))
        hε (fun _ => ha₀) hh (fun _ => hw₀) hb :=
  potentialEnergy_degreeM_neutral_eq_constant 3 ε h a₀ w₀ p₀ b₀ smThreeGenWeights
    (smThreeGenAmplitudes z) hε ha₀ hh hw₀ hb M (fun r => realGenModeToComplex (w r))
    (fun r => realGenModeToComplex_weighted_sum_zero_of_ortho (w r) (hw r))
    mass2 quartic vacuum

theorem yukawaDegreeM_potentialResponse_eq_democratic (M : ℕ) (z : ℂ) (w : Fin M → Fin 3 → ℝ)
    (hw : ∀ r : Fin M, w r 0 + w r 1 + w r 2 = 0) (mass2 quartic vacuum : ℝ) :
    potentialResponse mass2 quartic vacuum 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
        smThreeGenWeights (fun _ => b₀) (yukawaDegreeMPolyProfile M z w)
        hε (fun _ => ha₀) hh (fun _ => hw₀) hb =
      potentialResponse mass2 quartic vacuum 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
        smThreeGenWeights (fun _ => b₀) (fun i => Polynomial.C (smThreeGenAmplitudes z i))
        hε (fun _ => ha₀) hh (fun _ => hw₀) hb :=
  potentialResponse_degreeM_neutral_eq_constant 3 ε h a₀ w₀ p₀ b₀ smThreeGenWeights
    (smThreeGenAmplitudes z) hε ha₀ hh hw₀ hb M (fun r => realGenModeToComplex (w r))
    (fun r => realGenModeToComplex_weighted_sum_zero_of_ortho (w r) (hw r))
    mass2 quartic vacuum

theorem yukawaDegreeM_fullEnergy_eq_democratic (M : ℕ) (z : ℂ) (w : Fin M → Fin 3 → ℝ)
    (hw : ∀ r : Fin M, w r 0 + w r 1 + w r 2 = 0) (mass2 quartic vacuum t : ℝ) :
    fullEnergy 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (yukawaDegreeMPolyProfile M z w) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t =
      9 * ‖z‖ ^ 2 *
        fullEnergy 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
          (fun _ => 1) hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t :=
  smThreeGen_fullEnergy_degreeM_eq ε h a₀ w₀ p₀ b₀ hε ha₀ hh hw₀ hb M z
    (fun r => realGenModeToComplex (w r))
    (fun r => realGenModeToComplex_sum_zero_of_ortho (w r) (hw r))
    mass2 quartic vacuum t

theorem yukawaDegreeM_fullResponse_eq_democratic (M : ℕ) (z : ℂ) (w : Fin M → Fin 3 → ℝ)
    (hw : ∀ r : Fin M, w r 0 + w r 1 + w r 2 = 0) (mass2 quartic vacuum t : ℝ) :
    fullResponse 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (yukawaDegreeMPolyProfile M z w) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t =
      fullResponse 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (fun i => Polynomial.C (smThreeGenAmplitudes z i)) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t :=
  fullResponse_degreeM_neutral_eq_constant 3 ε h a₀ w₀ p₀ b₀ smThreeGenWeights
    (smThreeGenAmplitudes z) hε ha₀ hh hw₀ hb M (fun r => realGenModeToComplex (w r))
    (fun r => realGenModeToComplex_weighted_sum_zero_of_ortho (w r) (hw r))
    mass2 quartic vacuum t

theorem yukawaDegreeM_fullEnergy_lower_unit (M : ℕ) (z : ℂ) (w : Fin M → Fin 3 → ℝ)
    (hw : ∀ r : Fin M, w r 0 + w r 1 + w r 2 = 0) (mass2 quartic vacuum t : ℝ) :
    3 * ‖z‖ ^ 2 *
        fullEnergy 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
          (fun _ => 1) hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t ≤
      fullEnergy 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (yukawaDegreeMPolyProfile M z w) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t :=
  smThreeGen_degreeM_fullEnergy_lower_unit ε h a₀ w₀ p₀ b₀ hε ha₀ hh hw₀ hb M z
    (fun r => realGenModeToComplex (w r))
    (fun r => realGenModeToComplex_sum_zero_of_ortho (w r) (hw r))
    mass2 quartic vacuum t

theorem yukawaDegreeM_clockKinetic_lower (M : ℕ) (z : ℂ) (w : Fin M → Fin 3 → ℝ)
    (hw : ∀ r : Fin M, w r 0 + w r 1 + w r 2 = 0) (t : ℝ) :
    -(1 / (4 * ε)) *
        clockKineticEnergy 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
          smThreeGenWeights (fun _ => b₀) (yukawaDegreeMPolyProfile M z w)
          hε (fun _ => ha₀) hh (fun _ => hw₀) hb t ≤
      clockKineticResponse 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
        smThreeGenWeights (fun _ => b₀) (yukawaDegreeMPolyProfile M z w)
        hε (fun _ => ha₀) hh (fun _ => hw₀) hb t :=
  smThreeGen_clockKinetic_lower_degreeM ε h a₀ w₀ p₀ b₀ hε ha₀ hh hw₀ hb M z
    (fun r => realGenModeToComplex (w r))
    (fun r => realGenModeToComplex_sum_zero_of_ortho (w r) (hw r)) t

theorem yukawaDegreeM_full_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (mass2 quartic vacuum : ℝ),
      0 ≤ mass2 → 0 ≤ quartic → 0 ≤ vacuum →
      ∀ (M : ℕ) (ε h a₀ w₀ p₀ : ℝ) (b₀ z : ℂ)
      (w : Fin M → Fin 3 → ℝ)
      (hε : 0 < ε) (ha₀ : 0 < a₀) (hh : h ≠ 0) (hw₀ : 1 ≤ w₀)
      (hb : |h| ≤ 2 * Real.pi * ε / 3)
      (_hw : ∀ r : Fin M, w r 0 + w r 1 + w r 2 = 0) (t : ℝ),
      -(K / ε) * fullEnergy 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
        smThreeGenWeights (fun _ => b₀) (yukawaDegreeMPolyProfile M z w)
        hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t ≤
      fullResponse 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
        smThreeGenWeights (fun _ => b₀) (yukawaDegreeMPolyProfile M z w)
        hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t := by
  let hfull := smThreeGen_full_bound_degreeM
  let K := Classical.choose hfull
  have hK := Classical.choose_spec hfull
  refine ⟨K, hK.1, ?_⟩
  intro mass2 quartic vacuum hmass hquartic hvacuum M ε h a₀ w₀ p₀ b₀ z w
    hε ha₀ hh hw₀ hb hw t
  exact hK.2 mass2 quartic vacuum hmass hquartic hvacuum M ε h a₀ w₀ p₀ b₀ z
    (fun r => realGenModeToComplex (w r)) hε ha₀ hh hw₀ hb
    (fun r => realGenModeToComplex_sum_zero_of_ortho (w r) (hw r)) t

theorem wolfenstein_hierarchy_and_ckm_summary :
    (0 < wolfenstein_lambda ∧ wolfenstein_lambda < 1) ∧
      (wolfenstein_lambda > wolfenstein_lambda ^ 2 ∧
        wolfenstein_lambda ^ 2 > wolfenstein_lambda ^ 3 ∧
        wolfenstein_lambda ^ 3 > wolfenstein_lambda ^ 4) ∧
      (wolfenstein_lambda ^ 6 < wolfenstein_lambda) ∧
      (1 / wolfenstein_lambda > 1) ∧
      (1 - wolfenstein_lambda ^ 2 / 2 > 1 / 2) ∧
      (wolfenstein_lambda ^ 6 < 2e-4 ∧ wolfenstein_lambda ^ 6 > 1e-5) ∧
      (1 / wolfenstein_lambda ^ 2 > 20 ∧ 1 / wolfenstein_lambda ^ 2 < 21) :=
  ⟨wolfenstein_in_range,
   geometric_hierarchy wolfenstein_lambda wolfenstein_in_range.1 wolfenstein_in_range.2,
   jarlskog_suppressed wolfenstein_lambda wolfenstein_in_range.1 wolfenstein_in_range.2,
   mass_ratio_exceeds_one wolfenstein_lambda wolfenstein_in_range.1 wolfenstein_in_range.2,
   ckm_diagonal_dominance wolfenstein_lambda wolfenstein_in_range.1 wolfenstein_in_range.2,
   wolfenstein_jarlskog,
   wolfenstein_mass_ratio⟩

theorem smYukawa_multiPacket_master_synthesis :
    (generationCount 3 = 3) ∧
      (∀ y₀ : ℝ, ∑ i : Fin 3, democraticMatrix y₀ i i = 3 * y₀) ∧
      (∀ y₀ : ℝ, democraticMatrix y₀ * democraticMatrix y₀ =
        (3 * y₀) • democraticMatrix y₀) ∧
      (∀ y₀ : ℝ, perturbedYukawa y₀ 0 = democraticMatrix y₀) ∧
      (∀ (y₀ : ℝ) (w : Fin 3 → ℝ), w 0 + w 1 + w 2 = 0 →
        (democraticMatrix y₀).mulVec w = 0 ∧
        (perturbedYukawa y₀ 0).mulVec w = 0 ∧
        ∑ i : Fin 3, smThreeGenWeights i * realGenModeToComplex w i = 0) ∧
      (∀ δ : ℝ, 0 < δ → δ < 1 →
        (δ > δ ^ 2 ∧ δ ^ 2 > δ ^ 3 ∧ δ ^ 3 > δ ^ 4) ∧
        δ ^ 6 < δ ∧ 1 / δ > 1 ∧ 1 - δ ^ 2 / 2 > 1 / 2) ∧
      (0 < wolfenstein_lambda ∧ wolfenstein_lambda < 1) ∧
      (∀ (M : ℕ) (ε h a₀ w₀ p₀ : ℝ) (b₀ z : ℂ) (w : Fin M → Fin 3 → ℝ)
        (hε : 0 < ε) (ha₀ : 0 < a₀) (hh : h ≠ 0) (hw₀ : 1 ≤ w₀)
        (hb : |h| ≤ 2 * Real.pi * ε / 3),
        (∀ r : Fin M, w r 0 + w r 1 + w r 2 = 0) →
        ∀ (mass2 quartic vacuum t : ℝ),
        3 * ‖z‖ ^ 2 *
          fullEnergy 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
            (fun _ => 1) hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t ≤
        fullEnergy 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
          (yukawaDegreeMPolyProfile M z w) hε (fun _ => ha₀) hh (fun _ => hw₀)
          hb mass2 quartic vacuum t) :=
  ⟨three_generations,
   democratic_trace,
   democratic_idempotent_relation,
   perturbed_at_zero,
   massless_mode_yukawa_and_neutral_bridge,
   fun δ h0 h1 =>
     ⟨geometric_hierarchy δ h0 h1,
      jarlskog_suppressed δ h0 h1,
      mass_ratio_exceeds_one δ h0 h1,
      ckm_diagonal_dominance δ h0 h1⟩,
   wolfenstein_in_range,
   fun M ε h a₀ w₀ p₀ b₀ z w hε ha₀ hh hw₀ hb hw mass2 quartic vacuum t =>
     yukawaDegreeM_fullEnergy_lower_unit ε h a₀ w₀ p₀ b₀ hε ha₀ hh hw₀ hb
       M z w hw mass2 quartic vacuum t⟩

#print axioms realGenModeToComplex_democratic
#print axioms democratic_mulVec_democraticGenMode
#print axioms realGenModeToComplex_sum_eq
#print axioms realGenModeToComplex_sum_zero_of_ortho
#print axioms realGenModeToComplex_weighted_sum_zero_of_ortho
#print axioms masslessMode₁_ortho
#print axioms masslessMode₂_ortho
#print axioms massless_mode_yukawa_and_neutral_bridge
#print axioms massless_mode_state_zero
#print axioms massless_mode_momentum_zero
#print axioms massless_mode_output_zero
#print axioms massless_mode_momentumOutput_zero
#print axioms massless_mode_seconds_zero
#print axioms massless_mode_hamiltonianOutput_zero
#print axioms massless_mode_inputLift_zero
#print axioms massless_mode_momentumLift_zero
#print axioms massless_mode_fullEnergy_zero
#print axioms massless_mode_fullResponse_zero
#print axioms yukawaDegreeM_massless_modes_zero
#print axioms yukawaDegreeM_state_eq_democratic
#print axioms yukawaDegreeM_momentum_eq_democratic
#print axioms yukawaDegreeM_output_eq_democratic
#print axioms yukawaDegreeM_momentumOutput_eq_democratic
#print axioms yukawaDegreeM_hamiltonianOutput_eq_democratic
#print axioms yukawaDegreeM_inputLift_eq_democratic
#print axioms yukawaDegreeM_momentumLift_eq_democratic
#print axioms yukawaDegreeM_clockKineticEnergy_eq_democratic
#print axioms yukawaDegreeM_clockKineticResponse_eq_democratic
#print axioms yukawaDegreeM_potentialEnergy_eq_democratic
#print axioms yukawaDegreeM_potentialResponse_eq_democratic
#print axioms yukawaDegreeM_fullEnergy_eq_democratic
#print axioms yukawaDegreeM_fullResponse_eq_democratic
#print axioms yukawaDegreeM_fullEnergy_lower_unit
#print axioms yukawaDegreeM_clockKinetic_lower
#print axioms yukawaDegreeM_full_bound
#print axioms wolfenstein_hierarchy_and_ckm_summary
#print axioms smYukawa_multiPacket_master_synthesis
end
end UnifiedTheory.Audit.KFCausalSMYukawaHierarchyMultiPacketSynthesis
