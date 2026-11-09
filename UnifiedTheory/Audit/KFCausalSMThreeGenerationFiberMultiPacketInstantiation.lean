/- Instantiation of the multi-packet quantum clock-floor family at `n = 3`
fermion generations (`Fin 3`, `generationCount 3 = 3`), connecting the gauge
fiber `O(1)` section count on `CP²`, spatial dimension and CKM CP-violation
constraints, and the 3-generation equal-weight Cauchy-Schwarz enhancement
factor `9 / 3 = 3 = (generationCount 3 : ℝ)` for arbitrary-degree `M` neutral
polynomial profiles. -/
import UnifiedTheory.Audit.KFCausalCommonComplexDegreeMPolynomialResponseLowerBound
import UnifiedTheory.LayerB.GenerationsFromFiber
import UnifiedTheory.LayerB.ThreeGenerations

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalSMThreeGenerationFiberMultiPacketInstantiation
noncomputable section
open UnifiedTheory.LayerB.GenerationsFromFiber
  (swap_gauge charge charge_not_gauge_invariant vector_space_dim
   generationCount generations_eq_colors three_generations bettiCP betti_CP2)
open UnifiedTheory.LayerB.ThreeGenerations
  (eigenvalue_count three_eigenvalues spatial_dim spatial_dim_3
   nAngles nPhases ckm_params_3 cp_violation_requires_d_ge_3
   d3_minimal_for_cp generation_dimension_chain
   sym_2x2_discriminant_nonneg sym_2x2_char_discriminant
   sym_2x2_has_real_eigenvalues spectral_dimension_chain)
open UnifiedTheory.Audit.KFCausalCommonComplexDegreeMPolynomialResponseLowerBound
  (factoredPolyProfile degreeMPolyProfile cauchySchwarzWeightRatio
   state_factored_eq_sum_smul momentum_factored_eq_sum_smul
   output_factored_eq_sum_smul momentumOutput_factored_eq_sum_smul
   seconds_factored_eq_sum_smul
   state_factored_neutral_zero momentum_factored_neutral_zero
   output_factored_neutral_zero momentumOutput_factored_neutral_zero
   hamiltonianOutput_factored_neutral_zero
   fullEnergy_factored_neutral_zero fullResponse_factored_neutral_zero
   state_degreeM_neutral_eq_constant momentum_degreeM_neutral_eq_constant
   output_degreeM_neutral_eq_constant momentumOutput_degreeM_neutral_eq_constant
   hamiltonianOutput_degreeM_neutral_eq_constant
   inputLift_degreeM_neutral_eq_constant momentumLift_degreeM_neutral_eq_constant
   clockKineticEnergy_degreeM_neutral_eq_constant
   clockKineticResponse_degreeM_neutral_eq_constant
   potentialEnergy_degreeM_neutral_eq_constant
   potentialResponse_degreeM_neutral_eq_constant
   fullEnergy_degreeM_neutral_eq_constant fullResponse_degreeM_neutral_eq_constant
   fullEnergy_degreeM_common_amp_eq
   cauchySchwarzWeightRatio_mul_incoherent_le_degreeM_fullEnergy
   cauchySchwarzWeightRatio_mul_unit_le_degreeM_fullEnergy
   clockKinetic_lower_degreeM_neutral full_bound_degreeM_neutral)
open KFCausalReciprocalNeutralSuperposition (state momentum output momentumOutput)
open KFCausalReciprocalNeutralHamiltonian (inputLift momentumLift fullEnergy fullResponse)
open KFCausalReciprocalNeutralKineticResponse (clockKineticEnergy clockKineticResponse)
open KFCausalWeightedReciprocalNeutralPotentialTransport (potentialEnergy potentialResponse)
open KFCausalReciprocalNeutralStrongHamiltonian (seconds hamiltonianOutput)

/-! ### 1. Standard Model 3-Generation Weight and Amplitude Arrays on `Fin 3` -/

def smThreeGenWeights : Fin 3 → ℂ := fun _ => 1

def smThreeGenAmplitudes (z : ℂ) : Fin 3 → ℂ := fun _ => z

theorem smThreeGenWeights_apply (i : Fin 3) : smThreeGenWeights i = 1 := rfl

theorem smThreeGenAmplitudes_apply (z : ℂ) (i : Fin 3) : smThreeGenAmplitudes z i = z := rfl

theorem smThreeGenWeights_sum : ∑ i : Fin 3, smThreeGenWeights i = 3 := by
  simp only [smThreeGenWeights, Fin.sum_univ_three]
  norm_num

theorem smThreeGenWeights_sum_eq_generationCount :
    ∑ i : Fin 3, smThreeGenWeights i = (generationCount 3 : ℂ) := by
  rw [smThreeGenWeights_sum, three_generations]
  norm_num

theorem smThreeGenWeights_norm_sq_sum :
    ∑ i : Fin 3, ‖smThreeGenWeights i‖ ^ 2 = 3 := by
  simp only [smThreeGenWeights, Fin.sum_univ_three, norm_one, one_pow]
  norm_num

theorem smThreeGenWeights_norm_sq_sum_eq_generationCount :
    ∑ i : Fin 3, ‖smThreeGenWeights i‖ ^ 2 = (generationCount 3 : ℝ) := by
  rw [smThreeGenWeights_norm_sq_sum, three_generations]
  norm_num

theorem smThreeGenWeights_norm_sq_sum_ge_one :
    1 ≤ ∑ i : Fin 3, ‖smThreeGenWeights i‖ ^ 2 := by
  rw [smThreeGenWeights_norm_sq_sum]
  norm_num

theorem smThreeGenWeights_re_sum :
    ∑ i : Fin 3, (smThreeGenWeights i).re = 3 := by
  simp only [smThreeGenWeights, Fin.sum_univ_three, Complex.one_re]
  norm_num

theorem smThreeGenWeights_re_sum_sq :
    (∑ i : Fin 3, (smThreeGenWeights i).re) ^ 2 = 9 := by
  rw [smThreeGenWeights_re_sum]
  norm_num

theorem smThreeGenWeights_norm_sum_sq :
    ‖∑ i : Fin 3, smThreeGenWeights i‖ ^ 2 = 9 := by
  rw [smThreeGenWeights_sum]
  norm_num

theorem smThreeGenWeights_cauchySchwarzRatio :
    cauchySchwarzWeightRatio smThreeGenWeights = 3 := by
  unfold cauchySchwarzWeightRatio
  rw [smThreeGenWeights_norm_sq_sum, smThreeGenWeights_re_sum_sq]
  norm_num

theorem smThreeGenWeights_cauchySchwarzRatio_eq_generationCount :
    cauchySchwarzWeightRatio smThreeGenWeights = (generationCount 3 : ℝ) := by
  rw [smThreeGenWeights_cauchySchwarzRatio, three_generations]
  norm_num

theorem smThreeGenWeights_cauchySchwarzRatio_eq_spatial_dim :
    cauchySchwarzWeightRatio smThreeGenWeights = (Module.finrank ℝ (Fin 3 → ℝ) : ℝ) := by
  rw [smThreeGenWeights_cauchySchwarzRatio, spatial_dim_3]
  norm_num

theorem smThreeGenWeights_cauchySchwarzRatio_eq_nAngles :
    cauchySchwarzWeightRatio smThreeGenWeights = (nAngles 3 : ℝ) := by
  rw [smThreeGenWeights_cauchySchwarzRatio, ckm_params_3.1]
  norm_num

theorem smThreeGen_weighted_sum_eq (c : Fin 3 → ℂ) :
    ∑ i : Fin 3, smThreeGenWeights i * c i = c 0 + c 1 + c 2 := by
  simp only [smThreeGenWeights, Fin.sum_univ_three, one_mul]

theorem smThreeGen_neutral_iff_sum_zero (c : Fin 3 → ℂ) :
    (∑ i : Fin 3, smThreeGenWeights i * c i = 0) ↔ c 0 + c 1 + c 2 = 0 := by
  rw [smThreeGen_weighted_sum_eq]

/-! ### 2. 3-Generation Factored and Neutral Polynomial Superposition Identities -/

variable (ε h a₀ w₀ p₀ : ℝ) (b₀ : ℂ) (c : Fin 3 → ℂ) (Q : Polynomial ℂ)
  (hε : 0 < ε) (ha₀ : 0 < a₀) (hh : h ≠ 0) (hw₀ : 1 ≤ w₀)
  (hb : |h| ≤ 2 * Real.pi * ε / 3)

theorem smThreeGen_state_factored_eq :
    state 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀) =
      (c 0 + c 1 + c 2) •
        state 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
          (fun _ => Q) hε (fun _ => ha₀) hh (fun _ => hw₀) := by
  rw [state_factored_eq_sum_smul, smThreeGen_weighted_sum_eq]

theorem smThreeGen_momentum_factored_eq :
    momentum 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀) =
      (c 0 + c 1 + c 2) •
        momentum 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
          (fun _ => Q) hε (fun _ => ha₀) hh (fun _ => hw₀) := by
  rw [momentum_factored_eq_sum_smul, smThreeGen_weighted_sum_eq]

theorem smThreeGen_output_factored_eq (j : Fin 8) :
    output 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀) hb j =
      (c 0 + c 1 + c 2) •
        output 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
          (fun _ => Q) hε (fun _ => ha₀) hh (fun _ => hw₀) hb j := by
  rw [output_factored_eq_sum_smul, smThreeGen_weighted_sum_eq]

theorem smThreeGen_momentumOutput_factored_eq (j : Fin 8) :
    momentumOutput 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀) hb j =
      (c 0 + c 1 + c 2) •
        momentumOutput 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
          (fun _ => Q) hε (fun _ => ha₀) hh (fun _ => hw₀) hb j := by
  rw [momentumOutput_factored_eq_sum_smul, smThreeGen_weighted_sum_eq]

theorem smThreeGen_seconds_factored_eq (hb_narrow : |h| ≤ Real.pi * ε / 3) (j : Fin 8) :
    seconds 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀) hb_narrow j =
      (c 0 + c 1 + c 2) •
        seconds 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
          (fun _ => Q) hε (fun _ => ha₀) hh (fun _ => hw₀) hb_narrow j := by
  rw [seconds_factored_eq_sum_smul, smThreeGen_weighted_sum_eq]

theorem smThreeGen_state_factored_neutral_zero (hc : c 0 + c 1 + c 2 = 0) :
    state 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀) = 0 :=
  state_factored_neutral_zero 3 ε h a₀ w₀ p₀ b₀ smThreeGenWeights c Q hε ha₀ hh hw₀
    ((smThreeGen_weighted_sum_eq c).trans hc)

theorem smThreeGen_momentum_factored_neutral_zero (hc : c 0 + c 1 + c 2 = 0) :
    momentum 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀) = 0 :=
  momentum_factored_neutral_zero 3 ε h a₀ w₀ p₀ b₀ smThreeGenWeights c Q hε ha₀ hh hw₀
    ((smThreeGen_weighted_sum_eq c).trans hc)

theorem smThreeGen_output_factored_neutral_zero (hc : c 0 + c 1 + c 2 = 0) (j : Fin 8) :
    output 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀) hb j = 0 :=
  output_factored_neutral_zero 3 ε h a₀ w₀ p₀ b₀ smThreeGenWeights c Q hε ha₀ hh hw₀ hb
    ((smThreeGen_weighted_sum_eq c).trans hc) j

theorem smThreeGen_momentumOutput_factored_neutral_zero (hc : c 0 + c 1 + c 2 = 0) (j : Fin 8) :
    momentumOutput 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀) hb j = 0 :=
  momentumOutput_factored_neutral_zero 3 ε h a₀ w₀ p₀ b₀ smThreeGenWeights c Q hε ha₀ hh hw₀ hb
    ((smThreeGen_weighted_sum_eq c).trans hc) j

theorem smThreeGen_hamiltonianOutput_factored_neutral_zero (hc : c 0 + c 1 + c 2 = 0)
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    hamiltonianOutput 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb_narrow mass2 quartic vacuum t = 0 :=
  hamiltonianOutput_factored_neutral_zero 3 ε h a₀ w₀ p₀ b₀ smThreeGenWeights c Q hε ha₀ hh hw₀
    ((smThreeGen_weighted_sum_eq c).trans hc) hb_narrow mass2 quartic vacuum t

theorem smThreeGen_fullEnergy_factored_neutral_zero (hc : c 0 + c 1 + c 2 = 0)
    (mass2 quartic vacuum t : ℝ) :
    fullEnergy 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t = 0 :=
  fullEnergy_factored_neutral_zero 3 ε h a₀ w₀ p₀ b₀ smThreeGenWeights c Q hε ha₀ hh hw₀ hb
    ((smThreeGen_weighted_sum_eq c).trans hc) mass2 quartic vacuum t

theorem smThreeGen_fullResponse_factored_neutral_zero (hc : c 0 + c 1 + c 2 = 0)
    (mass2 quartic vacuum t : ℝ) :
    fullResponse 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (factoredPolyProfile c Q) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t = 0 :=
  fullResponse_factored_neutral_zero 3 ε h a₀ w₀ p₀ b₀ smThreeGenWeights c Q hε ha₀ hh hw₀ hb
    ((smThreeGen_weighted_sum_eq c).trans hc) mass2 quartic vacuum t

/-! ### 3. 3-Generation Degree-`M` Polynomial Response Lower Bounds & Fiber Synthesis -/

theorem smThreeGen_state_degreeM_eq_constant (M : ℕ) (z : ℂ) (d : Fin M → Fin 3 → ℂ)
    (hd : ∀ r : Fin M, d r 0 + d r 1 + d r 2 = 0) :
    state 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (degreeMPolyProfile M (smThreeGenAmplitudes z) d) hε (fun _ => ha₀) hh (fun _ => hw₀) =
      state 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (fun i => Polynomial.C (smThreeGenAmplitudes z i)) hε (fun _ => ha₀) hh (fun _ => hw₀) :=
  state_degreeM_neutral_eq_constant 3 ε h a₀ w₀ p₀ b₀ smThreeGenWeights
    (smThreeGenAmplitudes z) hε ha₀ hh hw₀ M d
    (fun r => (smThreeGen_weighted_sum_eq (d r)).trans (hd r))

theorem smThreeGen_fullEnergy_degreeM_eq (M : ℕ) (z : ℂ) (d : Fin M → Fin 3 → ℂ)
    (hd : ∀ r : Fin M, d r 0 + d r 1 + d r 2 = 0)
    (mass2 quartic vacuum t : ℝ) :
    fullEnergy 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (degreeMPolyProfile M (smThreeGenAmplitudes z) d) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t =
      9 * ‖z‖ ^ 2 *
        fullEnergy 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
          (fun _ => 1) hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t := by
  have h1 := fullEnergy_degreeM_common_amp_eq 3 ε h a₀ w₀ p₀ b₀ smThreeGenWeights
    hε ha₀ hh hw₀ hb M z d
    (fun r => (smThreeGen_weighted_sum_eq (d r)).trans (hd r)) mass2 quartic vacuum t
  rw [smThreeGenWeights_norm_sum_sq] at h1
  exact h1

theorem smThreeGen_degreeM_fullEnergy_lower_incoherent (M : ℕ) (z : ℂ) (d : Fin M → Fin 3 → ℂ)
    (hd : ∀ r : Fin M, d r 0 + d r 1 + d r 2 = 0)
    (mass2 quartic vacuum t : ℝ) :
    3 * ‖z‖ ^ 2 *
        ((∑ i : Fin 3, ‖smThreeGenWeights i‖ ^ 2) *
          fullEnergy 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
            (fun _ => 1) hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t) ≤
      fullEnergy 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (degreeMPolyProfile M (smThreeGenAmplitudes z) d) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t := by
  have hC0 : ∑ i : Fin 3, ‖smThreeGenWeights i‖ ^ 2 ≠ 0 := by
    rw [smThreeGenWeights_norm_sq_sum]
    norm_num
  have hle := cauchySchwarzWeightRatio_mul_incoherent_le_degreeM_fullEnergy
    3 ε h a₀ w₀ p₀ b₀ smThreeGenWeights hε ha₀ hh hw₀ hb M z d hC0
    (fun r => (smThreeGen_weighted_sum_eq (d r)).trans (hd r)) mass2 quartic vacuum t
  rwa [smThreeGenWeights_cauchySchwarzRatio] at hle

theorem smThreeGen_degreeM_fullEnergy_lower_unit (M : ℕ) (z : ℂ) (d : Fin M → Fin 3 → ℂ)
    (hd : ∀ r : Fin M, d r 0 + d r 1 + d r 2 = 0)
    (mass2 quartic vacuum t : ℝ) :
    3 * ‖z‖ ^ 2 *
        fullEnergy 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
          (fun _ => 1) hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t ≤
      fullEnergy 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (degreeMPolyProfile M (smThreeGenAmplitudes z) d) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t := by
  have hle := cauchySchwarzWeightRatio_mul_unit_le_degreeM_fullEnergy
    3 ε h a₀ w₀ p₀ b₀ smThreeGenWeights hε ha₀ hh hw₀ hb M z d
    smThreeGenWeights_norm_sq_sum_ge_one
    (fun r => (smThreeGen_weighted_sum_eq (d r)).trans (hd r)) mass2 quartic vacuum t
  rwa [smThreeGenWeights_cauchySchwarzRatio] at hle

theorem smThreeGen_degreeM_fullEnergy_lower_generationCount (M : ℕ) (z : ℂ)
    (d : Fin M → Fin 3 → ℂ) (hd : ∀ r : Fin M, d r 0 + d r 1 + d r 2 = 0)
    (mass2 quartic vacuum t : ℝ) :
    (generationCount 3 : ℝ) * ‖z‖ ^ 2 *
        fullEnergy 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
          (fun _ => 1) hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t ≤
      fullEnergy 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (degreeMPolyProfile M (smThreeGenAmplitudes z) d) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t := by
  rw [three_generations]
  exact_mod_cast smThreeGen_degreeM_fullEnergy_lower_unit ε h a₀ w₀ p₀ b₀
    hε ha₀ hh hw₀ hb M z d hd mass2 quartic vacuum t

theorem smThreeGen_clockKinetic_lower_degreeM (M : ℕ) (z : ℂ) (d : Fin M → Fin 3 → ℂ)
    (hd : ∀ r : Fin M, d r 0 + d r 1 + d r 2 = 0) (t : ℝ) :
    -(1 / (4 * ε)) *
        clockKineticEnergy 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
          smThreeGenWeights (fun _ => b₀)
          (degreeMPolyProfile M (smThreeGenAmplitudes z) d)
          hε (fun _ => ha₀) hh (fun _ => hw₀) hb t ≤
      clockKineticResponse 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
        smThreeGenWeights (fun _ => b₀)
        (degreeMPolyProfile M (smThreeGenAmplitudes z) d)
        hε (fun _ => ha₀) hh (fun _ => hw₀) hb t :=
  clockKinetic_lower_degreeM_neutral 3 ε h a₀ w₀ p₀ b₀ smThreeGenWeights
    (smThreeGenAmplitudes z) hε ha₀ hh hw₀ hb M d
    (fun r => (smThreeGen_weighted_sum_eq (d r)).trans (hd r)) t

theorem smThreeGen_full_bound_degreeM :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (mass2 quartic vacuum : ℝ),
      0 ≤ mass2 → 0 ≤ quartic → 0 ≤ vacuum →
      ∀ (M : ℕ) (ε h a₀ w₀ p₀ : ℝ) (b₀ z : ℂ)
      (d : Fin M → Fin 3 → ℂ)
      (hε : 0 < ε) (ha₀ : 0 < a₀) (hh : h ≠ 0) (hw₀ : 1 ≤ w₀)
      (hb : |h| ≤ 2 * Real.pi * ε / 3)
      (_hd : ∀ r : Fin M, d r 0 + d r 1 + d r 2 = 0) (t : ℝ),
      -(K / ε) * fullEnergy 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
        smThreeGenWeights (fun _ => b₀)
        (degreeMPolyProfile M (smThreeGenAmplitudes z) d)
        hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t ≤
      fullResponse 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
        smThreeGenWeights (fun _ => b₀)
        (degreeMPolyProfile M (smThreeGenAmplitudes z) d)
        hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t := by
  let hfull := full_bound_degreeM_neutral
  let K := Classical.choose hfull
  have hK := Classical.choose_spec hfull
  refine ⟨K, hK.1, ?_⟩
  intro mass2 quartic vacuum hmass hquartic hvacuum M ε h a₀ w₀ p₀ b₀ z d
    hε ha₀ hh hw₀ hb hd t
  exact hK.2 mass2 quartic vacuum hmass hquartic hvacuum 3 M ε h a₀ w₀ p₀ b₀
    smThreeGenWeights (smThreeGenAmplitudes z) d hε ha₀ hh hw₀ hb
    (fun r => (smThreeGen_weighted_sum_eq (d r)).trans (hd r)) t

theorem smThreeGen_fiber_dimension_ckm_synthesis :
    (generationCount 3 = 3) ∧
      (∀ Nc : ℕ, generationCount Nc = Nc) ∧
      (∃ z : Fin 2 → ℂ, charge (swap_gauge z) ≠ charge z) ∧
      ((bettiCP 2 0, bettiCP 2 1, bettiCP 2 2, bettiCP 2 3, bettiCP 2 4) =
        (1, 0, 1, 0, 1)) ∧
      (nAngles 3 = 3 ∧ nPhases 3 = 1) ∧
      (nPhases 3 ≥ 1 ∧ nPhases 2 = 0) ∧
      (∀ d : ℕ, nPhases d ≥ 1 → d ≥ 3) ∧
      (∀ a b c : ℝ, (a + c) ^ 2 - 4 * (a * c - b ^ 2) ≥ 0) :=
  ⟨three_generations,
   generations_eq_colors,
   charge_not_gauge_invariant,
   betti_CP2,
   ckm_params_3,
   d3_minimal_for_cp,
   cp_violation_requires_d_ge_3,
   sym_2x2_has_real_eigenvalues⟩

theorem smThreeGen_multiPacket_master_synthesis :
    (generationCount 3 = 3) ∧
      (cauchySchwarzWeightRatio smThreeGenWeights = (generationCount 3 : ℝ)) ∧
      (nAngles 3 = 3 ∧ nPhases 3 = 1) ∧
      (Fintype.card (Fin 3) = 3 ∧ Module.finrank ℝ (Fin 3 → ℝ) = 3) ∧
      (∀ (M : ℕ) (ε h a₀ w₀ p₀ : ℝ) (b₀ z : ℂ) (d : Fin M → Fin 3 → ℂ)
        (hε : 0 < ε) (ha₀ : 0 < a₀) (hh : h ≠ 0) (hw₀ : 1 ≤ w₀)
        (hb : |h| ≤ 2 * Real.pi * ε / 3),
        (∀ r : Fin M, d r 0 + d r 1 + d r 2 = 0) →
        ∀ (mass2 quartic vacuum t : ℝ),
        3 * ‖z‖ ^ 2 *
          fullEnergy 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
            (fun _ => 1) hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t ≤
        fullEnergy 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
          (degreeMPolyProfile M (smThreeGenAmplitudes z) d) hε (fun _ => ha₀) hh (fun _ => hw₀)
          hb mass2 quartic vacuum t) :=
  ⟨three_generations,
   smThreeGenWeights_cauchySchwarzRatio_eq_generationCount,
   ckm_params_3,
   ⟨three_eigenvalues, spatial_dim_3⟩,
   fun M ε h a₀ w₀ p₀ b₀ z d hε ha₀ hh hw₀ hb hd mass2 quartic vacuum t =>
     smThreeGen_degreeM_fullEnergy_lower_unit ε h a₀ w₀ p₀ b₀ hε ha₀ hh hw₀ hb
       M z d hd mass2 quartic vacuum t⟩

#print axioms smThreeGenWeights_apply
#print axioms smThreeGenAmplitudes_apply
#print axioms smThreeGenWeights_sum
#print axioms smThreeGenWeights_sum_eq_generationCount
#print axioms smThreeGenWeights_norm_sq_sum
#print axioms smThreeGenWeights_norm_sq_sum_eq_generationCount
#print axioms smThreeGenWeights_norm_sq_sum_ge_one
#print axioms smThreeGenWeights_re_sum
#print axioms smThreeGenWeights_re_sum_sq
#print axioms smThreeGenWeights_norm_sum_sq
#print axioms smThreeGenWeights_cauchySchwarzRatio
#print axioms smThreeGenWeights_cauchySchwarzRatio_eq_generationCount
#print axioms smThreeGenWeights_cauchySchwarzRatio_eq_spatial_dim
#print axioms smThreeGenWeights_cauchySchwarzRatio_eq_nAngles
#print axioms smThreeGen_weighted_sum_eq
#print axioms smThreeGen_neutral_iff_sum_zero
#print axioms smThreeGen_state_factored_eq
#print axioms smThreeGen_momentum_factored_eq
#print axioms smThreeGen_output_factored_eq
#print axioms smThreeGen_momentumOutput_factored_eq
#print axioms smThreeGen_seconds_factored_eq
#print axioms smThreeGen_state_factored_neutral_zero
#print axioms smThreeGen_momentum_factored_neutral_zero
#print axioms smThreeGen_output_factored_neutral_zero
#print axioms smThreeGen_momentumOutput_factored_neutral_zero
#print axioms smThreeGen_hamiltonianOutput_factored_neutral_zero
#print axioms smThreeGen_fullEnergy_factored_neutral_zero
#print axioms smThreeGen_fullResponse_factored_neutral_zero
#print axioms smThreeGen_state_degreeM_eq_constant
#print axioms smThreeGen_fullEnergy_degreeM_eq
#print axioms smThreeGen_degreeM_fullEnergy_lower_incoherent
#print axioms smThreeGen_degreeM_fullEnergy_lower_unit
#print axioms smThreeGen_degreeM_fullEnergy_lower_generationCount
#print axioms smThreeGen_clockKinetic_lower_degreeM
#print axioms smThreeGen_full_bound_degreeM
#print axioms smThreeGen_fiber_dimension_ckm_synthesis
#print axioms smThreeGen_multiPacket_master_synthesis
end
end UnifiedTheory.Audit.KFCausalSMThreeGenerationFiberMultiPacketInstantiation
