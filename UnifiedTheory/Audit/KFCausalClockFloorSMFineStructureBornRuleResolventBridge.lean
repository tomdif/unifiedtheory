/- Standard Model Fine-Structure Unification Coupling, Spectral-Gap Independence,
Born Rule SO(2) Quadratic Uniqueness, and Five-Operator Clock-Floor Resolvent Bridge:
1. Connects the unification-scale electromagnetic fine-structure constant
   alpha_unification = 3 / (32 * π), the d = 4 chamber spectral gap
   gamma_4 = log (5 / 3) (with exp(gamma_4) = 5 / 3), and the rigorous
   independence boundary separating alpha_unification and c₁_exact from simple
   algebraic functions of gamma_4.
2. Connects the Born rule SO(2) rotation-invariance uniqueness theorem
   (so2_invariant_quadratic_unique, born_rule_from_invariance,
   normSq_is_SO2_invariant, quartic_invariant) to the clock-floor Hilbert-space
   norm-squared probability functional and complex inner-product transition
   amplitudes preserved under the nonautonomous unitary evolution family
   evolutionFamily s t.
3. Instantiates the five-operator clock-floor resolvents R_T, R_P, R_G, R_{S(t)},
   and R_{H(t)} at the two fundamental dimensionless positive scales
   (a, b) = (alpha_unification, gamma_4), establishing exact first resolvent
   identities, resolvent commutativity, 10-domain second-power regularity, and
   two-parameter (alpha_unification, gamma_4) cross-operator second resolvent
   identities. -/
import UnifiedTheory.LayerA.FineStructureFromGap
import UnifiedTheory.LayerA.BornRuleUnique
import UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorFirstResolventIdentity
import UnifiedTheory.Audit.KFCausalClockFloorSMElectroweakHiggsPotentialBridge

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorSMFineStructureBornRuleResolventBridge
noncomputable section
open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open UnifiedTheory.LayerA.LatticeMatching (c₁_exact)
open UnifiedTheory.LayerA.FineStructureFromGap
  (alpha_unification gamma_4 alpha_pos gamma_4_pos
   alpha_lt_one_over_32 alpha_gt_one_over_128
   gamma_4_ge gamma_4_le exp_gamma_4
   alpha_not_simple_function_of_gamma c1_ne_exp_gamma c1_ne_inv_gamma_sq)
open UnifiedTheory.LayerA.BornRuleUnique
  (QuadForm normSqForm normSq_eval
   so2_invariant_quadratic_unique so2_invariant_eval
   born_rule_from_invariance normSq_is_SO2_invariant quartic_invariant)
open KFCausalClockFloorIteratedResolventSecondPowerCore
  (staticSecondPowerDomain potentialSecondPowerDomain growingSecondPowerDomain
   residualSecondPowerDomain hamiltonianSecondPowerDomain
   hamiltonian_iterated_resolvent_mem_ten_domains)
open KFCausalClockFloorSMElectroweakHiggsPotentialBridge
  (spectralGapHiggs evolutionFamily higgsDressedFormEnergy
   evolutionFamily_preserves_higgs_potential_energy)
open KFCausalClockFloorFiveOperatorFirstResolventIdentity
  (quarterStripResolvent_sub_quarterStripResolvent quarterStripResolvent_comm
   potentialResolvent_sub_potentialResolvent potentialResolvent_comm
   staticGeneratorResolvent_sub_staticGeneratorResolvent staticGeneratorResolvent_comm
   staticResidualResolvent_sub_staticResidualResolvent staticResidualResolvent_comm
   hamiltonianResolvent_sub_hamiltonianResolvent hamiltonianResolvent_comm
   hamiltonianResolvent_sub_mem_hamiltonianSecondPowerDomain
   potential_sub_growing_two_param_resolvent_eq
   residual_sub_hamiltonian_two_param_resolvent_eq)

/-! ### 1. Fine-Structure Unification Coupling, Spectral Gap `γ₄`, and Honest Boundary -/

theorem alpha_unification_eq :
    alpha_unification = 3 / (32 * Real.pi) := rfl

theorem alpha_unification_pos :
    0 < alpha_unification := alpha_pos

theorem alpha_unification_lt_one_over_32 :
    alpha_unification < 1 / 32 := alpha_lt_one_over_32

theorem alpha_unification_gt_one_over_128 :
    1 / 128 < alpha_unification := alpha_gt_one_over_128

theorem alpha_unification_lt_one :
    alpha_unification < 1 := by
  linarith [alpha_lt_one_over_32]

theorem gamma_4_def_eq :
    gamma_4 = Real.log (5 / 3) := rfl

theorem gamma_4_positive :
    0 < gamma_4 := gamma_4_pos

theorem gamma_4_two_sided_bounds :
    2 / 5 ≤ gamma_4 ∧ gamma_4 ≤ 2 / 3 :=
  ⟨gamma_4_ge, gamma_4_le⟩

theorem exp_gamma_4_eq_five_thirds :
    Real.exp gamma_4 = 5 / 3 := exp_gamma_4

theorem alpha_unification_lt_gamma_4 :
    alpha_unification < gamma_4 := by
  linarith [alpha_lt_one_over_32, gamma_4_ge]

theorem alpha_gap_bridge_summary :
    (alpha_unification ≠ gamma_4 ∧
     alpha_unification ≠ gamma_4 / (2 * Real.pi) ∧
     alpha_unification ≠ gamma_4 ^ 2 ∧
     alpha_unification ≠ 1 / gamma_4) ∧
    c₁_exact ≠ Real.exp gamma_4 ∧
    c₁_exact ≠ 1 / gamma_4 ^ 2 :=
  ⟨alpha_not_simple_function_of_gamma, c1_ne_exp_gamma, c1_ne_inv_gamma_sq⟩

/-! ### 2. Born Rule SO(2) Quadratic Uniqueness and Unitary Probability Conservation -/

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k t : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RT" => KFCausalClockFloorStaticClockCore.resolvent ε hε h hh hw m g k 0
local notation "RP" => KFCausalClockFloorPotentialClockResolvent.resolvent ε hε h hh hw m g k
local notation "RG" => KFCausalClockFloorGrowingYosida.resolvent ε hε h hh hw m g k
local notation "RS" => KFCausalClockFloorResidualClockCore.resolvent ε hε h hh hw m g k
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "Kroot" => KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Tgrow" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (hamiltonian_bound ε h hw) hh m g k

theorem born_quadratic_uniqueness
    (f : QuadForm) (hinv : f.IsSO2Invariant) :
    f.b = 0 ∧ f.a = f.c :=
  so2_invariant_quadratic_unique f hinv

theorem born_normalized_eval_eq
    (f : QuadForm) (hinv : f.IsSO2Invariant) (hnorm : f.a = 1) (Q P_coord : ℝ) :
    f.eval Q P_coord = Q ^ 2 + P_coord ^ 2 :=
  born_rule_from_invariance f hinv hnorm Q P_coord

theorem born_normSq_is_SO2_invariant :
    normSqForm.IsSO2Invariant :=
  normSq_is_SO2_invariant

theorem born_quartic_rotation_invariant (θ Q P_coord : ℝ) :
    ((Q * Real.cos θ - P_coord * Real.sin θ) ^ 2 +
     (Q * Real.sin θ + P_coord * Real.cos θ) ^ 2) ^ 2 =
    (Q ^ 2 + P_coord ^ 2) ^ 2 :=
  quartic_invariant θ Q P_coord

theorem born_hilbert_eval_eq_scaled_norm_sq
    (f : QuadForm) (hinv : f.IsSO2Invariant) (ψ : Hilbert) :
    f.eval ‖ψ‖ 0 = f.a * ‖ψ‖ ^ 2 := by
  rw [so2_invariant_eval f hinv ‖ψ‖ 0]
  ring

theorem born_normalized_hilbert_eval_eq_norm_sq
    (f : QuadForm) (hinv : f.IsSO2Invariant) (hnorm : f.a = 1) (ψ : Hilbert) :
    f.eval ‖ψ‖ 0 = ‖ψ‖ ^ 2 := by
  rw [born_normalized_eval_eq f hinv hnorm ‖ψ‖ 0]
  ring

theorem born_hilbert_eval_conserved_under_evolution
    (f : QuadForm) (hinv : f.IsSO2Invariant) (s : ℝ) (ψ : Hilbert) :
    f.eval ‖evolutionFamily ε hε h hh hb m g k s t ψ‖ 0 = f.a * ‖ψ‖ ^ 2 := by
  rw [born_hilbert_eval_eq_scaled_norm_sq f hinv, LinearIsometryEquiv.norm_map]

theorem born_normalized_hilbert_conserved_under_evolution
    (s : ℝ) (ψ : Hilbert) :
    normSqForm.eval ‖evolutionFamily ε hε h hh hb m g k s t ψ‖ 0 = ‖ψ‖ ^ 2 := by
  rw [normSq_eval, LinearIsometryEquiv.norm_map]
  ring

theorem born_complex_pairing_re_im_conserved_under_evolution
    (f : QuadForm) (hinv : f.IsSO2Invariant) (s : ℝ) (u v : Hilbert) :
    f.eval
      (inner ℂ (evolutionFamily ε hε h hh hb m g k s t u)
        (evolutionFamily ε hε h hh hb m g k s t v)).re
      (inner ℂ (evolutionFamily ε hε h hh hb m g k s t u)
        (evolutionFamily ε hε h hh hb m g k s t v)).im =
      f.a * ((inner ℂ u v).re ^ 2 + (inner ℂ u v).im ^ 2) := by
  rw [LinearIsometryEquiv.inner_map_map, so2_invariant_eval f hinv]

/-! ### 3. Five-Operator Resolvents Instantiated at `(alpha_unification, gamma_4)` -/

theorem static_resolvent_alpha_sub_gamma_eq (f : Hilbert) :
    RT alpha_unification f - RT gamma_4 f =
      ((gamma_4 - alpha_unification : ℝ) : ℂ) •
        RT alpha_unification (RT gamma_4 f) :=
  quarterStripResolvent_sub_quarterStripResolvent ε hε h hh hb m g k
    alpha_unification gamma_4 alpha_pos gamma_4_pos f

theorem static_resolvent_alpha_gamma_comm (f : Hilbert) :
    RT alpha_unification (RT gamma_4 f) =
      RT gamma_4 (RT alpha_unification f) :=
  quarterStripResolvent_comm ε hε h hh hb m g k
    alpha_unification gamma_4 alpha_pos gamma_4_pos f

theorem potential_resolvent_alpha_sub_gamma_eq (f : Hilbert) :
    RP alpha_unification f - RP gamma_4 f =
      ((gamma_4 - alpha_unification : ℝ) : ℂ) •
        RP alpha_unification (RP gamma_4 f) :=
  potentialResolvent_sub_potentialResolvent ε hε h hh hb m g k
    alpha_unification gamma_4 alpha_pos gamma_4_pos f

theorem potential_resolvent_alpha_gamma_comm (f : Hilbert) :
    RP alpha_unification (RP gamma_4 f) =
      RP gamma_4 (RP alpha_unification f) :=
  potentialResolvent_comm ε hε h hh hb m g k
    alpha_unification gamma_4 alpha_pos gamma_4_pos f

theorem growing_resolvent_alpha_sub_gamma_eq (f : Hilbert) :
    RG alpha_unification f - RG gamma_4 f =
      ((gamma_4 - alpha_unification : ℝ) : ℂ) •
        RG alpha_unification (RG gamma_4 f) :=
  staticGeneratorResolvent_sub_staticGeneratorResolvent ε hε h hh hb m g k
    alpha_unification gamma_4 alpha_pos gamma_4_pos f

theorem growing_resolvent_alpha_gamma_comm (f : Hilbert) :
    RG alpha_unification (RG gamma_4 f) =
      RG gamma_4 (RG alpha_unification f) :=
  staticGeneratorResolvent_comm ε hε h hh hb m g k
    alpha_unification gamma_4 alpha_pos gamma_4_pos f

theorem residual_resolvent_alpha_sub_gamma_eq (f : Hilbert) :
    RS t alpha_unification f - RS t gamma_4 f =
      ((gamma_4 - alpha_unification : ℝ) : ℂ) •
        RS t alpha_unification (RS t gamma_4 f) :=
  staticResidualResolvent_sub_staticResidualResolvent ε hε h hh hb m g k t
    alpha_unification gamma_4 alpha_pos gamma_4_pos f

theorem residual_resolvent_alpha_gamma_comm (f : Hilbert) :
    RS t alpha_unification (RS t gamma_4 f) =
      RS t gamma_4 (RS t alpha_unification f) :=
  staticResidualResolvent_comm ε hε h hh hb m g k t
    alpha_unification gamma_4 alpha_pos gamma_4_pos f

theorem hamiltonian_resolvent_alpha_sub_gamma_eq (f : Hilbert) :
    RH t alpha_unification f - RH t gamma_4 f =
      ((gamma_4 - alpha_unification : ℝ) : ℂ) •
        RH t alpha_unification (RH t gamma_4 f) :=
  hamiltonianResolvent_sub_hamiltonianResolvent ε hε h hh hb m g k t
    alpha_unification gamma_4 alpha_pos gamma_4_pos f

theorem hamiltonian_resolvent_alpha_gamma_comm (f : Hilbert) :
    RH t alpha_unification (RH t gamma_4 f) =
      RH t gamma_4 (RH t alpha_unification f) :=
  hamiltonianResolvent_comm ε hε h hh hb m g k t
    alpha_unification gamma_4 alpha_pos gamma_4_pos f

theorem hamiltonian_resolvent_alpha_sub_gamma_mem_secondPowerDomain (f : Hilbert) :
    RH t alpha_unification f - RH t gamma_4 f ∈
      hamiltonianSecondPowerDomain ε hε h hh hb m g k t :=
  hamiltonianResolvent_sub_mem_hamiltonianSecondPowerDomain ε hε h hh hb m g k t
    alpha_unification gamma_4 alpha_pos gamma_4_pos f

theorem hamiltonian_iterated_alpha_gamma_mem_ten_domains
    (s : ℝ) (f : Hilbert) :
    let z : Hilbert := RH t alpha_unification (RH t gamma_4 f)
    z ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t ∧
    z ∈ (H t).domain ∧
    z ∈ (K).domain ∧
    z ∈ (S t).domain ∧
    z ∈ (Eavg s).domain ∧
    z ∈ (Tstat).domain ∧
    z ∈ (Kroot).domain ∧
    z ∈ (Tpot).domain ∧
    z ∈ (Tgrow).domain ∧
    z ∈ (Tres s).domain ∧
    z ∈ (clockHalf ε).domain :=
  hamiltonian_iterated_resolvent_mem_ten_domains ε hε h hh hb m g k t s
    alpha_unification gamma_4 alpha_pos gamma_4_pos f

theorem potential_sub_growing_alpha_gamma_resolvent_eq (f : Hilbert) :
    RP alpha_unification f - RG gamma_4 f =
      RP alpha_unification
        (K ⟨RG gamma_4 f,
          KFCausalClockFloorGrowingComponentResolventBounds.resolvent_mem_radial_domain
            ε hε h hh hb m g k gamma_4 gamma_4_pos f⟩) +
        ((gamma_4 - alpha_unification : ℝ) : ℂ) •
          RP alpha_unification (RG gamma_4 f) :=
  potential_sub_growing_two_param_resolvent_eq ε hε h hh hb m g k
    alpha_unification gamma_4 alpha_pos gamma_4_pos f

theorem residual_sub_hamiltonian_alpha_gamma_resolvent_eq (f : Hilbert) :
    RS t alpha_unification f - RH t gamma_4 f =
      (Real.exp (2 * t) : ℂ) •
        RS t alpha_unification
          (K ⟨RH t gamma_4 f,
            KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_radial_domain
              ε hε h hh hb m g k t gamma_4 gamma_4_pos f⟩) +
        ((gamma_4 - alpha_unification : ℝ) : ℂ) •
          RS t alpha_unification (RH t gamma_4 f) :=
  residual_sub_hamiltonian_two_param_resolvent_eq ε hε h hh hb m g k t
    alpha_unification gamma_4 alpha_pos gamma_4_pos f

theorem sm_fine_structure_born_rule_five_resolvent_master_bridge
    (s mu_sq r : ℝ) (f : Hilbert) :
    (alpha_unification = 3 / (32 * Real.pi) ∧
     0 < alpha_unification ∧
     0 < gamma_4 ∧
     Real.exp gamma_4 = 5 / 3 ∧
     alpha_unification ≠ gamma_4 ∧
     c₁_exact ≠ Real.exp gamma_4) ∧
    (normSqForm.IsSO2Invariant ∧
     normSqForm.eval ‖evolutionFamily ε hε h hh hb m g k s t f‖ 0 = ‖f‖ ^ 2 ∧
     (spectralGapHiggs mu_sq).eval r *
       ‖evolutionFamily ε hε h hh hb m g k s t f‖ ^ 2 =
       (spectralGapHiggs mu_sq).eval r * ‖f‖ ^ 2) ∧
    (RH t alpha_unification f - RH t gamma_4 f =
       ((gamma_4 - alpha_unification : ℝ) : ℂ) •
         RH t alpha_unification (RH t gamma_4 f) ∧
     RH t alpha_unification (RH t gamma_4 f) =
       RH t gamma_4 (RH t alpha_unification f) ∧
     RH t alpha_unification f - RH t gamma_4 f ∈
       hamiltonianSecondPowerDomain ε hε h hh hb m g k t) :=
  ⟨⟨alpha_unification_eq, alpha_pos, gamma_4_pos, exp_gamma_4,
    alpha_not_simple_function_of_gamma.1, c1_ne_exp_gamma⟩,
   ⟨normSq_is_SO2_invariant,
    born_normalized_hilbert_conserved_under_evolution ε hε h hh hb m g k t s f,
    evolutionFamily_preserves_higgs_potential_energy
      ε hε h hh hb m g k s t (spectralGapHiggs mu_sq) r f⟩,
   ⟨hamiltonian_resolvent_alpha_sub_gamma_eq ε hε h hh hb m g k t f,
    hamiltonian_resolvent_alpha_gamma_comm ε hε h hh hb m g k t f,
    hamiltonian_resolvent_alpha_sub_gamma_mem_secondPowerDomain ε hε h hh hb m g k t f⟩⟩

#print axioms alpha_unification_eq
#print axioms alpha_unification_pos
#print axioms alpha_unification_lt_one_over_32
#print axioms alpha_unification_gt_one_over_128
#print axioms alpha_unification_lt_one
#print axioms gamma_4_def_eq
#print axioms gamma_4_positive
#print axioms gamma_4_two_sided_bounds
#print axioms exp_gamma_4_eq_five_thirds
#print axioms alpha_unification_lt_gamma_4
#print axioms alpha_gap_bridge_summary
#print axioms born_quadratic_uniqueness
#print axioms born_normalized_eval_eq
#print axioms born_normSq_is_SO2_invariant
#print axioms born_quartic_rotation_invariant
#print axioms born_hilbert_eval_eq_scaled_norm_sq
#print axioms born_normalized_hilbert_eval_eq_norm_sq
#print axioms born_hilbert_eval_conserved_under_evolution
#print axioms born_normalized_hilbert_conserved_under_evolution
#print axioms born_complex_pairing_re_im_conserved_under_evolution
#print axioms static_resolvent_alpha_sub_gamma_eq
#print axioms static_resolvent_alpha_gamma_comm
#print axioms potential_resolvent_alpha_sub_gamma_eq
#print axioms potential_resolvent_alpha_gamma_comm
#print axioms growing_resolvent_alpha_sub_gamma_eq
#print axioms growing_resolvent_alpha_gamma_comm
#print axioms residual_resolvent_alpha_sub_gamma_eq
#print axioms residual_resolvent_alpha_gamma_comm
#print axioms hamiltonian_resolvent_alpha_sub_gamma_eq
#print axioms hamiltonian_resolvent_alpha_gamma_comm
#print axioms hamiltonian_resolvent_alpha_sub_gamma_mem_secondPowerDomain
#print axioms hamiltonian_iterated_alpha_gamma_mem_ten_domains
#print axioms potential_sub_growing_alpha_gamma_resolvent_eq
#print axioms residual_sub_hamiltonian_alpha_gamma_resolvent_eq
#print axioms sm_fine_structure_born_rule_five_resolvent_master_bridge
end
end UnifiedTheory.Audit.KFCausalClockFloorSMFineStructureBornRuleResolventBridge
