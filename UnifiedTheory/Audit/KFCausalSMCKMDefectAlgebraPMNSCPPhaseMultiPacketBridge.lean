/- Bridge connecting the defect composition algebra and CKM holonomy hierarchy
(`CKMFromDefects`, `CKMRefined`), the Wolfenstein `A = √6 / 3` and `λ = √5 / 10`
parameters (`WolfensteinA`), and the K/P-derived PMNS Dirac CP phase
`δ_CP = -π / 2` and Jarlskog invariant `J² = 1936 / 1771875` (`PMNSCPPhase`)
with 3-generation (`Fin 3`) multi-packet degree-`M` polynomial superpositions and
arbitrary-source dominant-constant-mode lower bounds. -/
import UnifiedTheory.LayerB.CKMFromDefects
import UnifiedTheory.LayerB.CKMRefined
import UnifiedTheory.LayerB.WolfensteinA
import UnifiedTheory.LayerB.PMNSCPPhase
import UnifiedTheory.Audit.KFCausalSMYukawaHierarchyMultiPacketSynthesis
import UnifiedTheory.Audit.KFCausalArbitrarySourceDominantConstantModeResponseLowerBound

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalSMCKMDefectAlgebraPMNSCPPhaseMultiPacketBridge
noncomputable section
open UnifiedTheory.LayerB
open UnifiedTheory.LayerB.MassAndMixing (IsUnitary ckmMatrix)
open UnifiedTheory.LayerB.MetricDefects (Perturbation K_proj)
open UnifiedTheory.LayerB.HistoryAmplitudes (stepAmplitude)
open UnifiedTheory.LayerB.CKMFromDefects
  (compose_assoc_perturbation compose_comm_perturbation
   charge_assoc conjugate_involution
   ckm_unitary_from_defects ckm_unitary_general aligned_defects_no_mixing
   diagonal_bound_trivial adjacent_dominates_distant suppression_ratio
   γ₄ γ₄_pos exp_neg_γ₄)
open UnifiedTheory.LayerB.CKMRefined
  (estimates_ordered honest_status)
open UnifiedTheory.LayerB.WolfensteinA
  (wolfenstein_A A_eq_sqrt6_over_3 wolfenstein_A_sq
   wolfenstein_A_satisfies_law wolfenstein_A_pos
   wolfenstein_A_bracket wolfenstein_A_within_PDG_2sigma
   wolfenstein_lambda wolfenstein_lambda_closed
   wolfenstein_lambda_bracket wolfenstein_A_master)
open UnifiedTheory.LayerB.PMNSCPPhase
  (cp_phase_real_part_zero arg_pos_imag_unit arg_neg_imag_unit
   delta_CP_PMNS abs_delta_CP_PMNS sin_delta_CP cos_delta_CP
   master_cp_derivation master_cp_magnitude
   jarlskog_PMNS_sq jarlskog_PMNS_sq_numerical jarlskog_PMNS_sq_bracket
   jarlskog_PMNS jarlskog_PMNS_neg PMNS_CPPhase_master)
open KFCausalReciprocalNeutralSuperposition (state)
open KFCausalReciprocalNeutralHamiltonian (fullEnergy fullResponse)
open KFCausalReciprocalNeutralArbitrarySourceClockKineticResponse (scaleAmplitude)
open KFCausalReciprocalNeutralArbitraryDegreePolynomialDecomposition (unitMonomialPolyProfile)
open KFCausalCommonComplexDegreeMPolynomialResponseLowerBound
  (degreeMPolyProfile full_bound_degreeM_neutral)
open KFCausalSMThreeGenerationFiberMultiPacketInstantiation
  (smThreeGenWeights smThreeGen_degreeM_fullEnergy_lower_unit)
open KFCausalArbitrarySourceDominantConstantModeResponseLowerBound
  (state_degreeM_dominant_constant_norm_ge
   state_degreeM_half_dominant_constant_norm_ge
   state_degreeM_arbitrary_source_norm_sq_ge
   constant_mode_fullResponse_zero_couplings_lower_arbitrary_source)

/-! ### 1. Defect Composition Algebra and CKM Unitarity / Holonomy Hierarchy -/

section DefectAlgebra
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem defect_compose_assoc_perturbation (db : ComposableDefectBlock V)
    (d₁ d₂ d₃ : db.Defect) :
    db.perturbation (db.compose (db.compose d₁ d₂) d₃) =
      db.perturbation (db.compose d₁ (db.compose d₂ d₃)) :=
  compose_assoc_perturbation db d₁ d₂ d₃

theorem defect_compose_comm_perturbation (db : ComposableDefectBlock V)
    (d₁ d₂ : db.Defect) :
    db.perturbation (db.compose d₁ d₂) =
      db.perturbation (db.compose d₂ d₁) :=
  compose_comm_perturbation db d₁ d₂

theorem defect_charge_assoc (db : ComposableDefectBlock V)
    (d₁ d₂ d₃ : db.Defect) :
    charge db (db.compose (db.compose d₁ d₂) d₃) =
      charge db (db.compose d₁ (db.compose d₂ d₃)) :=
  charge_assoc db d₁ d₂ d₃

theorem defect_conjugate_involution (db : ComposableDefectBlock V)
    (d : db.Defect) :
    db.perturbation (db.conjugate (db.conjugate d)) = db.perturbation d :=
  conjugate_involution db d

end DefectAlgebra

theorem defect_ckm_unitary_three_gen (V_u V_d : Matrix (Fin 3) (Fin 3) ℂ)
    (hU : IsUnitary V_u) (hD : IsUnitary V_d) :
    IsUnitary (ckmMatrix V_u V_d) :=
  ckm_unitary_from_defects V_u V_d hU hD

theorem defect_ckm_unitary_general (n : ℕ) (V_u V_d : Matrix (Fin n) (Fin n) ℂ)
    (hU : IsUnitary V_u) (hD : IsUnitary V_d) :
    IsUnitary (ckmMatrix V_u V_d) :=
  ckm_unitary_general n V_u V_d hU hD

theorem defect_aligned_no_mixing (V : Matrix (Fin 3) (Fin 3) ℂ)
    (hV : IsUnitary V) :
    ckmMatrix V V = 1 :=
  aligned_defects_no_mixing V hV

theorem defect_holonomy_diagonal_bound_one (γ : ℝ) (i : Fin 3) :
    Real.exp (-γ * |(↑i : ℤ) - ↑i|) = 1 :=
  diagonal_bound_trivial γ i

theorem defect_holonomy_adjacent_dominates_distant (γ : ℝ) (hγ : 0 < γ) :
    Real.exp (-γ * 2) < Real.exp (-γ * 1) :=
  adjacent_dominates_distant γ hγ

theorem defect_holonomy_suppression_ratio (γ : ℝ) (hγ : 0 < γ) :
    Real.exp (-γ * 2) / Real.exp (-γ * 1) = Real.exp (-γ) :=
  suppression_ratio γ hγ

theorem defect_holonomy_gamma4_pos : 0 < γ₄ :=
  γ₄_pos

theorem defect_holonomy_exp_neg_gamma4 : Real.exp (-γ₄) = 3 / 5 :=
  exp_neg_γ₄

theorem ckm_refined_estimates_ordered :
    (1 : ℝ) / 3 < Real.sqrt (1 / 6) ∧
      Real.sqrt (1 / 6) < 1 / 2 ∧
      (1 : ℝ) / 2 < 3 / 5 :=
  estimates_ordered

/-! ### 2. Wolfenstein `A` and `λ` Parameters from CKM Magnitudes -/

theorem wolfenstein_A_eq_sqrt6_div_3 :
    wolfenstein_A = Real.sqrt 6 / 3 :=
  A_eq_sqrt6_over_3

theorem wolfenstein_A_sq_eq_two_thirds :
    wolfenstein_A ^ 2 = 2 / 3 :=
  wolfenstein_A_sq

theorem wolfenstein_A_quadratic_law :
    3 * wolfenstein_A ^ 2 - 2 = 0 :=
  wolfenstein_A_satisfies_law

theorem wolfenstein_A_positive : 0 < wolfenstein_A :=
  wolfenstein_A_pos

theorem wolfenstein_A_numerical_bracket :
    0.816 < wolfenstein_A ∧ wolfenstein_A < 0.817 :=
  wolfenstein_A_bracket

theorem wolfenstein_A_pdg_2sigma :
    0.785 < wolfenstein_A ∧ wolfenstein_A < 0.837 :=
  wolfenstein_A_within_PDG_2sigma

theorem wolfenstein_lambda_eq_sqrt5_div_10 :
    wolfenstein_lambda = Real.sqrt 5 / 10 :=
  wolfenstein_lambda_closed

theorem wolfenstein_lambda_numerical_bracket :
    0.2236 < wolfenstein_lambda ∧ wolfenstein_lambda < 0.2237 :=
  wolfenstein_lambda_bracket

/-! ### 3. PMNS Dirac CP Phase `δ_CP = -π / 2` and Squared Jarlskog Invariant -/

theorem pmns_cp_phase_real_part_zero {m : ℕ}
    (D : Perturbation (m + 2) → ℝ) (h : Perturbation (m + 2))
    (hP : K_proj m h = 0) :
    (stepAmplitude D h).re = 0 :=
  cp_phase_real_part_zero D h hP

theorem pmns_arg_pos_imag_unit :
    Complex.arg Complex.I = Real.pi / 2 :=
  arg_pos_imag_unit

theorem pmns_arg_neg_imag_unit :
    Complex.arg (-Complex.I) = -(Real.pi / 2) :=
  arg_neg_imag_unit

theorem pmns_abs_delta_CP_eq_pi_div_two :
    |delta_CP_PMNS| = Real.pi / 2 :=
  abs_delta_CP_PMNS

theorem pmns_sin_delta_CP_eq_neg_one :
    Real.sin delta_CP_PMNS = -1 :=
  sin_delta_CP

theorem pmns_cos_delta_CP_eq_zero :
    Real.cos delta_CP_PMNS = 0 :=
  cos_delta_CP

theorem pmns_master_cp_derivation {m : ℕ}
    (D : Perturbation (m + 2) → ℝ) (h : Perturbation (m + 2))
    (hP : K_proj m h = 0) (hD : D h < 0) :
    Complex.arg (stepAmplitude D h) = delta_CP_PMNS :=
  master_cp_derivation D h hP hD

theorem pmns_master_cp_magnitude {m : ℕ}
    (D : Perturbation (m + 2) → ℝ) (h : Perturbation (m + 2))
    (hP : K_proj m h = 0) (hDne : D h ≠ 0) :
    |Complex.arg (stepAmplitude D h)| = Real.pi / 2 :=
  master_cp_magnitude D h hP hDne

theorem pmns_jarlskog_sq_closed :
    jarlskog_PMNS_sq = 1936 / 1771875 :=
  jarlskog_PMNS_sq_numerical

theorem pmns_jarlskog_sq_bracket :
    1.09e-3 < jarlskog_PMNS_sq ∧ jarlskog_PMNS_sq < 1.10e-3 :=
  jarlskog_PMNS_sq_bracket

theorem pmns_jarlskog_negative :
    jarlskog_PMNS < 0 :=
  jarlskog_PMNS_neg

/-! ### 4. 3-Generation (`Fin 3`) Multi-Packet Degree-`M` and Dominant-Mode Bridge -/

variable (M : ℕ) (ε h : ℝ) (a w p : Fin 3 → ℝ) (b c₀ : Fin 3 → ℂ)
  (d : Fin M → Fin 3 → ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0)
  (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ 2 * Real.pi * ε / 3)

theorem smThreeGen_arbitrary_source_dominant_constant_state_norm_ge (θ : ℝ)
    (hdom : ∑ r : Fin M,
        ‖state 3 ε h a w p (scaleAmplitude smThreeGenWeights (d r)) b
          (unitMonomialPolyProfile 3 ((r : ℕ) + 1)) hε ha hh hw‖ ≤
      θ * ‖state 3 ε h a w p (scaleAmplitude smThreeGenWeights c₀) b
          (fun _ => 1) hε ha hh hw‖) :
    (1 - θ) * ‖state 3 ε h a w p (scaleAmplitude smThreeGenWeights c₀) b
        (fun _ => 1) hε ha hh hw‖ ≤
      ‖state 3 ε h a w p smThreeGenWeights b (degreeMPolyProfile M c₀ d) hε ha hh hw‖ :=
  state_degreeM_dominant_constant_norm_ge 3 M ε h a w p smThreeGenWeights b c₀ d
    hε ha hh hw θ hdom

theorem smThreeGen_arbitrary_source_half_dominant_state_norm_ge
    (hdom : ∑ r : Fin M,
        ‖state 3 ε h a w p (scaleAmplitude smThreeGenWeights (d r)) b
          (unitMonomialPolyProfile 3 ((r : ℕ) + 1)) hε ha hh hw‖ ≤
      (1 / 2) * ‖state 3 ε h a w p (scaleAmplitude smThreeGenWeights c₀) b
          (fun _ => 1) hε ha hh hw‖) :
    (1 / 2) * ‖state 3 ε h a w p (scaleAmplitude smThreeGenWeights c₀) b
        (fun _ => 1) hε ha hh hw‖ ≤
      ‖state 3 ε h a w p smThreeGenWeights b (degreeMPolyProfile M c₀ d) hε ha hh hw‖ :=
  state_degreeM_half_dominant_constant_norm_ge 3 M ε h a w p smThreeGenWeights b c₀ d
    hε ha hh hw hdom

theorem smThreeGen_arbitrary_source_state_norm_sq_ge :
    (1 / 2) * ‖state 3 ε h a w p (scaleAmplitude smThreeGenWeights c₀) b
        (fun _ => 1) hε ha hh hw‖ ^ 2 -
        (∑ r : Fin M,
          ‖state 3 ε h a w p (scaleAmplitude smThreeGenWeights (d r)) b
            (unitMonomialPolyProfile 3 ((r : ℕ) + 1)) hε ha hh hw‖) ^ 2 ≤
      ‖state 3 ε h a w p smThreeGenWeights b (degreeMPolyProfile M c₀ d) hε ha hh hw‖ ^ 2 :=
  state_degreeM_arbitrary_source_norm_sq_ge 3 M ε h a w p smThreeGenWeights b c₀ d
    hε ha hh hw

theorem smThreeGen_arbitrary_source_fullResponse_zero_couplings_lower (t : ℝ) :
    -(1 / (4 * ε)) *
        fullEnergy 3 ε h a w p smThreeGenWeights b
          (fun i => Polynomial.C (c₀ i)) hε ha hh hw hb 0 0 0 t ≤
      fullResponse 3 ε h a w p smThreeGenWeights b
        (fun i => Polynomial.C (c₀ i)) hε ha hh hw hb 0 0 0 t :=
  constant_mode_fullResponse_zero_couplings_lower_arbitrary_source
    3 ε h a w p smThreeGenWeights b c₀ hε ha hh hw hb t

theorem ckm_pmns_yukawa_multiPacket_degreeM_bridge
    (a₀ w₀ p₀ : ℝ) (b₀ z : ℂ) (ha₀ : 0 < a₀) (hw₀ : 1 ≤ w₀)
    (hneutral : ∀ r : Fin M, d r 0 + d r 1 + d r 2 = 0)
    (mass2 quartic vacuum t : ℝ) :
    wolfenstein_A ^ 2 = 2 / 3 ∧
    delta_CP_PMNS = -(Real.pi / 2) ∧
    jarlskog_PMNS_sq = 1936 / 1771875 ∧
    3 * ‖z‖ ^ 2 *
        fullEnergy 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
          (fun _ => 1) hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t ≤
      fullEnergy 3 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) smThreeGenWeights (fun _ => b₀)
        (degreeMPolyProfile M (fun _ => z) d) hε (fun _ => ha₀) hh (fun _ => hw₀)
        hb mass2 quartic vacuum t :=
  ⟨wolfenstein_A_sq,
   rfl,
   jarlskog_PMNS_sq_numerical,
   smThreeGen_degreeM_fullEnergy_lower_unit ε h a₀ w₀ p₀ b₀ hε ha₀ hh hw₀ hb M z d
     hneutral mass2 quartic vacuum t⟩

theorem sm_ckm_defect_pmns_cp_multiPacket_master_synthesis :
    (∀ V_u V_d : Matrix (Fin 3) (Fin 3) ℂ,
      IsUnitary V_u → IsUnitary V_d → IsUnitary (ckmMatrix V_u V_d)) ∧
    (wolfenstein_A = Real.sqrt 6 / 3 ∧
     wolfenstein_A ^ 2 = 2 / 3 ∧
     wolfenstein_lambda = Real.sqrt 5 / 10) ∧
    (delta_CP_PMNS = -(Real.pi / 2) ∧
     Real.sin delta_CP_PMNS = -1 ∧
     Real.cos delta_CP_PMNS = 0 ∧
     jarlskog_PMNS_sq = 1936 / 1771875 ∧
     jarlskog_PMNS < 0) ∧
    (∃ K : ℝ, 0 ≤ K ∧ ∀ (mass2 quartic vacuum : ℝ),
      0 ≤ mass2 → 0 ≤ quartic → 0 ≤ vacuum →
      ∀ (n' M' : ℕ) (ε' h' a₀' w₀' p₀' : ℝ) (b₀' : ℂ) (C' c₀' : Fin n' → ℂ)
      (d' : Fin M' → Fin n' → ℂ)
      (hε' : 0 < ε') (ha₀' : 0 < a₀') (hh' : h' ≠ 0) (hw₀' : 1 ≤ w₀')
      (hb' : |h'| ≤ 2 * Real.pi * ε' / 3)
      (_hneutral : ∀ r : Fin M', ∑ i : Fin n', C' i * d' r i = 0) (t' : ℝ),
      -(K / ε') * fullEnergy n' ε' h' (fun _ => a₀') (fun _ => w₀') (fun _ => p₀') C' (fun _ => b₀')
        (degreeMPolyProfile M' c₀' d') hε' (fun _ => ha₀') hh' (fun _ => hw₀')
        hb' mass2 quartic vacuum t' ≤
      fullResponse n' ε' h' (fun _ => a₀') (fun _ => w₀') (fun _ => p₀') C' (fun _ => b₀')
        (degreeMPolyProfile M' c₀' d') hε' (fun _ => ha₀') hh' (fun _ => hw₀')
        hb' mass2 quartic vacuum t') :=
  ⟨ckm_unitary_from_defects,
   ⟨A_eq_sqrt6_over_3, wolfenstein_A_sq, wolfenstein_lambda_closed⟩,
   ⟨rfl, sin_delta_CP, cos_delta_CP, jarlskog_PMNS_sq_numerical, jarlskog_PMNS_neg⟩,
   full_bound_degreeM_neutral⟩

#print axioms defect_compose_assoc_perturbation
#print axioms defect_compose_comm_perturbation
#print axioms defect_charge_assoc
#print axioms defect_conjugate_involution
#print axioms defect_ckm_unitary_three_gen
#print axioms defect_ckm_unitary_general
#print axioms defect_aligned_no_mixing
#print axioms defect_holonomy_diagonal_bound_one
#print axioms defect_holonomy_adjacent_dominates_distant
#print axioms defect_holonomy_suppression_ratio
#print axioms defect_holonomy_gamma4_pos
#print axioms defect_holonomy_exp_neg_gamma4
#print axioms ckm_refined_estimates_ordered
#print axioms wolfenstein_A_eq_sqrt6_div_3
#print axioms wolfenstein_A_sq_eq_two_thirds
#print axioms wolfenstein_A_quadratic_law
#print axioms wolfenstein_A_positive
#print axioms wolfenstein_A_numerical_bracket
#print axioms wolfenstein_A_pdg_2sigma
#print axioms wolfenstein_lambda_eq_sqrt5_div_10
#print axioms wolfenstein_lambda_numerical_bracket
#print axioms pmns_cp_phase_real_part_zero
#print axioms pmns_arg_pos_imag_unit
#print axioms pmns_arg_neg_imag_unit
#print axioms pmns_abs_delta_CP_eq_pi_div_two
#print axioms pmns_sin_delta_CP_eq_neg_one
#print axioms pmns_cos_delta_CP_eq_zero
#print axioms pmns_master_cp_derivation
#print axioms pmns_master_cp_magnitude
#print axioms pmns_jarlskog_sq_closed
#print axioms pmns_jarlskog_sq_bracket
#print axioms pmns_jarlskog_negative
#print axioms smThreeGen_arbitrary_source_dominant_constant_state_norm_ge
#print axioms smThreeGen_arbitrary_source_half_dominant_state_norm_ge
#print axioms smThreeGen_arbitrary_source_state_norm_sq_ge
#print axioms smThreeGen_arbitrary_source_fullResponse_zero_couplings_lower
#print axioms ckm_pmns_yukawa_multiPacket_degreeM_bridge
#print axioms sm_ckm_defect_pmns_cp_multiPacket_master_synthesis
end
end UnifiedTheory.Audit.KFCausalSMCKMDefectAlgebraPMNSCPPhaseMultiPacketBridge
