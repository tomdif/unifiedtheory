/- Standard Model GUT-Scale Unification Coupling, Dyson-Resummed J4 Running,
Infrared Fine-Structure Spectral-Gap Formula, Octonion 4-Form Normalization,
and Five-Operator Iterated and Squared Resolvent Calculus Bridge:
1. Re-exports and connects the GUT-scale unified coupling alpha_GUT_framework = 3 / (32 * π)
   (with 1 / alpha_GUT_framework = 32 * π / 3 ∈ (33, 34) ⊂ [33, 37] and sin²θ_W = 3 / 8)
   from LayerA.AlphaGUT and the Dyson-resummed photon vacuum-polarization running
   alpha_J4(q²) = alpha_em_planck / (1 - Pi_J4(q²)) with Vieta residue completeness
   r1 + r23 = 1 and universal pre-factor C_int = 3 / 20 from LayerA.AlphaRunning.
2. Connects the infrared spectral-gap formula alphaIR = gamma_4 / 70 = log(5 / 3) / (2 * 5 * 7)
   from LayerA.FineStructureIRFromGap and its octonionic 4-form identification
   70 = C(dim_O, d_eff) = C(8, 4) = 35 + 35 from LayerA.FineStructureOctonionBridge.
3. Instantiates the five-operator clock-floor first resolvent identities, squared-resolvent
   Hilbert difference identities R_A(a)² f - R_A(b)² f, r-fold iteratedResolventPower
   commutativity, 10-domain third-power regularity, and unitary evolution norm preservation
   at the UV (alpha_GUT_framework), running (alpha_J4(q²)), and IR (alphaIR) scales. -/
import UnifiedTheory.LayerA.AlphaGUT
import UnifiedTheory.LayerA.AlphaRunning
import UnifiedTheory.LayerA.FineStructureIRFromGap
import UnifiedTheory.LayerA.FineStructureOctonionBridge
import UnifiedTheory.Audit.KFCausalClockFloorSMFineStructureBornRuleResolventBridge
import UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorIteratedResolventCommutativity

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorSMAlphaRunningOctonionFineStructureBridge
noncomputable section
open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open UnifiedTheory.LayerA.FineStructure (alpha_em_planck)
open UnifiedTheory.LayerA.AlphaGUT
  (alpha_GUT_framework inv_alpha_GUT_framework sin2_weinberg_GUT gut_window
   alpha_GUT_eq_alpha_em_planck alpha_GUT_pos inv_alpha_GUT_pos inv_alpha_GUT_eq
   inv_alpha_GUT_bracket inv_alpha_GUT_in_window framework_not_in_susy_window
   alpha2_at_unification_eq alpha1_GUT_eq_alpha2_GUT gap_closed_by_running_shift
   framework_GUT_scale_couplings)
open UnifiedTheory.LayerA.AlphaRunning
  (sigma_loop r1 r23 residue_complete Pi_J4 Pi_J4_at_zero Pi_J4_lt_one Pi_J4_mono
   alpha_J4 alpha_J4_at_zero alpha_J4_pos alpha_J4_mono alpha_J4_ge_planck
   inv_alpha_J4 C_int_alpha running_prefactor_is_Cint)
open UnifiedTheory.LayerA.FineStructureIRFromGap
  (atom_N_W atom_N_total atom_disc alphaIR inv_alphaIR
   seventy_atomic alphaIR_eq_gamma4_over_70 alphaIR_atomic alphaIR_mul_seventy
   alphaIR_pos log_5_3_bracket inv_alphaIR_bracket prediction_matches_PDG)
open UnifiedTheory.LayerA.FineStructureOctonionBridge
  (dim_O d_eff disc N_c N_W N_total
   choose_eight_four seventy_two_readings eight_atomic_readings
   four_form_selfdual_split alphaIR_eq_gamma4_over_choose alpha_octonion_master)
open KFCausalClockFloorSMElectroweakHiggsPotentialBridge
  (evolutionFamily)
open KFCausalClockFloorHigherPowerOperatorCores
  (iteratedResolventPower staticPowerDomain potentialPowerDomain
   growingPowerDomain residualPowerDomain hamiltonianPowerDomain)
open KFCausalClockFloorFiveOperatorFirstResolventIdentity
  (quarterStripResolvent_sub_quarterStripResolvent
   potentialResolvent_sub_potentialResolvent
   staticGeneratorResolvent_sub_staticGeneratorResolvent
   staticResidualResolvent_sub_staticResidualResolvent
   hamiltonianResolvent_sub_hamiltonianResolvent)
open KFCausalClockFloorFiveOperatorIteratedResolventCommutativity
  (staticResolvent_iteratedResolventPower_comm
   staticResolvent_squared_sub_eq
   staticResolvent_squared_sub_mem_thirdPowerDomain
   potentialResolvent_iteratedResolventPower_comm
   potentialResolvent_squared_sub_eq
   potentialResolvent_squared_sub_mem_thirdPowerDomain
   growingResolvent_iteratedResolventPower_comm
   growingResolvent_squared_sub_eq
   growingResolvent_squared_sub_mem_thirdPowerDomain
   residualResolvent_iteratedResolventPower_comm
   residualResolvent_squared_sub_eq
   residualResolvent_squared_sub_mem_thirdPowerDomain
   hamiltonianResolvent_iteratedResolventPower_comm
   hamiltonianResolvent_squared_sub_eq
   hamiltonianResolvent_squared_sub_mem_thirdPowerDomain
   hamiltonianResolvent_squared_sub_mem_ten_domains)

/-! ### 1. GUT Unification Coupling, Dyson-Resummed J4 Running, and IR Octonion Bridge -/

theorem alpha_GUT_eq_unification :
    alpha_GUT_framework = UnifiedTheory.LayerA.FineStructureFromGap.alpha_unification :=
  rfl

theorem inv_alpha_GUT_window_and_bracket :
    (33 < inv_alpha_GUT_framework ∧ inv_alpha_GUT_framework < 34) ∧
    gut_window inv_alpha_GUT_framework ∧
    ¬ ((24 : ℝ) ≤ inv_alpha_GUT_framework ∧ inv_alpha_GUT_framework ≤ 26) :=
  ⟨inv_alpha_GUT_bracket, inv_alpha_GUT_in_window, framework_not_in_susy_window⟩

theorem gut_gauge_couplings_unification_identity :
    sin2_weinberg_GUT = 3 / 8 ∧
    alpha_GUT_framework / sin2_weinberg_GUT = (8 / 3) * alpha_GUT_framework ∧
    (5 / 3) * alpha_GUT_framework / (1 - sin2_weinberg_GUT) = (8 / 3) * alpha_GUT_framework :=
  ⟨rfl, alpha2_at_unification_eq, alpha1_GUT_eq_alpha2_GUT⟩

theorem j4_vacuum_polarization_properties (qsq : ℝ) (hq : 0 ≤ qsq) :
    Pi_J4 0 = 0 ∧ Pi_J4 qsq < 1 ∧ r1 + r23 = 1 ∧ C_int_alpha = 3 / 20 :=
  ⟨Pi_J4_at_zero, Pi_J4_lt_one qsq hq, residue_complete, rfl⟩

theorem dyson_running_alpha_J4_properties (qsq : ℝ) (hq : 0 ≤ qsq) :
    alpha_J4 0 = alpha_GUT_framework ∧
    0 < alpha_J4 qsq ∧
    alpha_GUT_framework ≤ alpha_J4 qsq ∧
    1 / alpha_J4 qsq = (1 - Pi_J4 qsq) / alpha_GUT_framework := by
  rw [alpha_GUT_eq_alpha_em_planck]
  exact ⟨alpha_J4_at_zero, alpha_J4_pos qsq hq, alpha_J4_ge_planck qsq hq, inv_alpha_J4 qsq hq⟩

theorem dyson_running_alpha_J4_monotone {q1 q2 : ℝ} (h1 : 0 ≤ q1) (h12 : q1 ≤ q2) :
    Pi_J4 q1 ≤ Pi_J4 q2 ∧ alpha_J4 q1 ≤ alpha_J4 q2 :=
  ⟨Pi_J4_mono h1 h12, alpha_J4_mono h1 h12⟩

theorem gamma_4_ir_eq_gap :
    UnifiedTheory.LayerA.FineStructureIRFromGap.gamma_4 =
      UnifiedTheory.LayerA.FineStructureFromGap.gamma_4 :=
  rfl

theorem alphaIR_atomic_and_octonion_identities :
    alphaIR = UnifiedTheory.LayerA.FineStructureIRFromGap.gamma_4 / 70 ∧
    alphaIR = UnifiedTheory.LayerA.FineStructureIRFromGap.gamma_4 /
      (atom_N_W * atom_N_total * atom_disc) ∧
    alphaIR = UnifiedTheory.LayerA.FineStructureIRFromGap.gamma_4 /
      (Nat.choose dim_O d_eff : ℝ) ∧
    alphaIR * (atom_N_W * atom_N_total * atom_disc) =
      UnifiedTheory.LayerA.FineStructureIRFromGap.gamma_4 :=
  ⟨alphaIR_eq_gamma4_over_70, alphaIR_atomic, alphaIR_eq_gamma4_over_choose, alphaIR_mul_seventy⟩

theorem octonion_four_form_combinatorics :
    Nat.choose dim_O d_eff = 70 ∧
    Nat.choose dim_O d_eff = N_W * N_total * disc ∧
    (dim_O = disc + 1 ∧ dim_O = N_c + N_total ∧ dim_O = 2 * d_eff ∧ dim_O = N_W ^ 3) ∧
    (Nat.choose dim_O d_eff = Nat.choose disc N_c + Nat.choose disc d_eff ∧
     Nat.choose disc N_c = 35 ∧ Nat.choose disc d_eff = 35) :=
  ⟨choose_eight_four, seventy_two_readings, eight_atomic_readings, four_form_selfdual_split⟩

theorem alphaIR_numerical_brackets :
    0 < alphaIR ∧
    (0.51080 < Real.log (5 / 3) ∧ Real.log (5 / 3) < 0.51084) ∧
    (137.028 < inv_alphaIR ∧ inv_alphaIR < 137.041) ∧
    |inv_alphaIR - 137.035999084| < 0.01 :=
  ⟨alphaIR_pos, log_5_3_bracket, inv_alphaIR_bracket, prediction_matches_PDG⟩

theorem alphaIR_lt_alpha_GUT_framework :
    alphaIR < alpha_GUT_framework := by
  have h1 : alphaIR < 1 / 128 := by
    unfold alphaIR
    have hhi := log_5_3_bracket.2
    linarith
  have h2 : 1 / 128 < alpha_GUT_framework := by
    rw [alpha_GUT_eq_unification]
    exact UnifiedTheory.LayerA.FineStructureFromGap.alpha_gt_one_over_128
  exact h1.trans h2

theorem alphaIR_lt_alpha_J4 (qsq : ℝ) (hq : 0 ≤ qsq) :
    alphaIR < alpha_J4 qsq :=
  (alphaIR_lt_alpha_GUT_framework).trans_le (dyson_running_alpha_J4_properties qsq hq).2.2.1

/-! ### 2. Five-Operator First and Squared Resolvent Calculus at UV (`alpha_GUT`) and IR (`alphaIR`) -/

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

theorem staticResolvent_gut_sub_ir_eq (f : Hilbert) :
    RT alpha_GUT_framework f - RT alphaIR f =
      ((alphaIR - alpha_GUT_framework : ℝ) : ℂ) • RT alpha_GUT_framework (RT alphaIR f) :=
  quarterStripResolvent_sub_quarterStripResolvent ε hε h hh hb m g k
    alpha_GUT_framework alphaIR alpha_GUT_pos alphaIR_pos f

theorem potentialResolvent_gut_sub_ir_eq (f : Hilbert) :
    RP alpha_GUT_framework f - RP alphaIR f =
      ((alphaIR - alpha_GUT_framework : ℝ) : ℂ) • RP alpha_GUT_framework (RP alphaIR f) :=
  potentialResolvent_sub_potentialResolvent ε hε h hh hb m g k
    alpha_GUT_framework alphaIR alpha_GUT_pos alphaIR_pos f

theorem growingResolvent_gut_sub_ir_eq (f : Hilbert) :
    RG alpha_GUT_framework f - RG alphaIR f =
      ((alphaIR - alpha_GUT_framework : ℝ) : ℂ) • RG alpha_GUT_framework (RG alphaIR f) :=
  staticGeneratorResolvent_sub_staticGeneratorResolvent ε hε h hh hb m g k
    alpha_GUT_framework alphaIR alpha_GUT_pos alphaIR_pos f

theorem residualResolvent_gut_sub_ir_eq (f : Hilbert) :
    RS t alpha_GUT_framework f - RS t alphaIR f =
      ((alphaIR - alpha_GUT_framework : ℝ) : ℂ) • RS t alpha_GUT_framework (RS t alphaIR f) :=
  staticResidualResolvent_sub_staticResidualResolvent ε hε h hh hb m g k t
    alpha_GUT_framework alphaIR alpha_GUT_pos alphaIR_pos f

theorem hamiltonianResolvent_gut_sub_ir_eq (f : Hilbert) :
    RH t alpha_GUT_framework f - RH t alphaIR f =
      ((alphaIR - alpha_GUT_framework : ℝ) : ℂ) • RH t alpha_GUT_framework (RH t alphaIR f) :=
  hamiltonianResolvent_sub_hamiltonianResolvent ε hε h hh hb m g k t
    alpha_GUT_framework alphaIR alpha_GUT_pos alphaIR_pos f

theorem staticResolvent_squared_gut_sub_ir_eq (f : Hilbert) :
    RT alpha_GUT_framework (RT alpha_GUT_framework f) - RT alphaIR (RT alphaIR f) =
      ((alphaIR - alpha_GUT_framework : ℝ) : ℂ) •
        (RT alpha_GUT_framework (RT alpha_GUT_framework (RT alphaIR f)) +
          RT alpha_GUT_framework (RT alphaIR (RT alphaIR f))) :=
  staticResolvent_squared_sub_eq ε hε h hh hb m g k
    alpha_GUT_framework alphaIR alpha_GUT_pos alphaIR_pos f

theorem potentialResolvent_squared_gut_sub_ir_eq (f : Hilbert) :
    RP alpha_GUT_framework (RP alpha_GUT_framework f) - RP alphaIR (RP alphaIR f) =
      ((alphaIR - alpha_GUT_framework : ℝ) : ℂ) •
        (RP alpha_GUT_framework (RP alpha_GUT_framework (RP alphaIR f)) +
          RP alpha_GUT_framework (RP alphaIR (RP alphaIR f))) :=
  potentialResolvent_squared_sub_eq ε hε h hh hb m g k
    alpha_GUT_framework alphaIR alpha_GUT_pos alphaIR_pos f

theorem growingResolvent_squared_gut_sub_ir_eq (f : Hilbert) :
    RG alpha_GUT_framework (RG alpha_GUT_framework f) - RG alphaIR (RG alphaIR f) =
      ((alphaIR - alpha_GUT_framework : ℝ) : ℂ) •
        (RG alpha_GUT_framework (RG alpha_GUT_framework (RG alphaIR f)) +
          RG alpha_GUT_framework (RG alphaIR (RG alphaIR f))) :=
  growingResolvent_squared_sub_eq ε hε h hh hb m g k
    alpha_GUT_framework alphaIR alpha_GUT_pos alphaIR_pos f

theorem residualResolvent_squared_gut_sub_ir_eq (f : Hilbert) :
    RS t alpha_GUT_framework (RS t alpha_GUT_framework f) - RS t alphaIR (RS t alphaIR f) =
      ((alphaIR - alpha_GUT_framework : ℝ) : ℂ) •
        (RS t alpha_GUT_framework (RS t alpha_GUT_framework (RS t alphaIR f)) +
          RS t alpha_GUT_framework (RS t alphaIR (RS t alphaIR f))) :=
  residualResolvent_squared_sub_eq ε hε h hh hb m g k t
    alpha_GUT_framework alphaIR alpha_GUT_pos alphaIR_pos f

theorem hamiltonianResolvent_squared_gut_sub_ir_eq (f : Hilbert) :
    RH t alpha_GUT_framework (RH t alpha_GUT_framework f) - RH t alphaIR (RH t alphaIR f) =
      ((alphaIR - alpha_GUT_framework : ℝ) : ℂ) •
        (RH t alpha_GUT_framework (RH t alpha_GUT_framework (RH t alphaIR f)) +
          RH t alpha_GUT_framework (RH t alphaIR (RH t alphaIR f))) :=
  hamiltonianResolvent_squared_sub_eq ε hε h hh hb m g k t
    alpha_GUT_framework alphaIR alpha_GUT_pos alphaIR_pos f

theorem staticResolvent_gut_ir_iteratedPower_comm (r s : ℕ) (f : Hilbert) :
    iteratedResolventPower (RT alpha_GUT_framework) r (iteratedResolventPower (RT alphaIR) s f) =
      iteratedResolventPower (RT alphaIR) s (iteratedResolventPower (RT alpha_GUT_framework) r f) :=
  staticResolvent_iteratedResolventPower_comm ε hε h hh hb m g k
    alpha_GUT_framework alphaIR alpha_GUT_pos alphaIR_pos r s f

theorem potentialResolvent_gut_ir_iteratedPower_comm (r s : ℕ) (f : Hilbert) :
    iteratedResolventPower (RP alpha_GUT_framework) r (iteratedResolventPower (RP alphaIR) s f) =
      iteratedResolventPower (RP alphaIR) s (iteratedResolventPower (RP alpha_GUT_framework) r f) :=
  potentialResolvent_iteratedResolventPower_comm ε hε h hh hb m g k
    alpha_GUT_framework alphaIR alpha_GUT_pos alphaIR_pos r s f

theorem growingResolvent_gut_ir_iteratedPower_comm (r s : ℕ) (f : Hilbert) :
    iteratedResolventPower (RG alpha_GUT_framework) r (iteratedResolventPower (RG alphaIR) s f) =
      iteratedResolventPower (RG alphaIR) s (iteratedResolventPower (RG alpha_GUT_framework) r f) :=
  growingResolvent_iteratedResolventPower_comm ε hε h hh hb m g k
    alpha_GUT_framework alphaIR alpha_GUT_pos alphaIR_pos r s f

theorem residualResolvent_gut_ir_iteratedPower_comm (r s : ℕ) (f : Hilbert) :
    iteratedResolventPower (RS t alpha_GUT_framework) r (iteratedResolventPower (RS t alphaIR) s f) =
      iteratedResolventPower (RS t alphaIR) s (iteratedResolventPower (RS t alpha_GUT_framework) r f) :=
  residualResolvent_iteratedResolventPower_comm ε hε h hh hb m g k t
    alpha_GUT_framework alphaIR alpha_GUT_pos alphaIR_pos r s f

theorem hamiltonianResolvent_gut_ir_iteratedPower_comm (r s : ℕ) (f : Hilbert) :
    iteratedResolventPower (RH t alpha_GUT_framework) r (iteratedResolventPower (RH t alphaIR) s f) =
      iteratedResolventPower (RH t alphaIR) s (iteratedResolventPower (RH t alpha_GUT_framework) r f) :=
  hamiltonianResolvent_iteratedResolventPower_comm ε hε h hh hb m g k t
    alpha_GUT_framework alphaIR alpha_GUT_pos alphaIR_pos r s f

theorem hamiltonianResolvent_running_alpha_J4_squared_sub_eq
    (q1 q2 : ℝ) (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) (f : Hilbert) :
    RH t (alpha_J4 q1) (RH t (alpha_J4 q1) f) - RH t (alpha_J4 q2) (RH t (alpha_J4 q2) f) =
      ((alpha_J4 q2 - alpha_J4 q1 : ℝ) : ℂ) •
        (RH t (alpha_J4 q1) (RH t (alpha_J4 q1) (RH t (alpha_J4 q2) f)) +
          RH t (alpha_J4 q1) (RH t (alpha_J4 q2) (RH t (alpha_J4 q2) f))) :=
  hamiltonianResolvent_squared_sub_eq ε hε h hh hb m g k t
    (alpha_J4 q1) (alpha_J4 q2) (alpha_J4_pos q1 hq1) (alpha_J4_pos q2 hq2) f

theorem hamiltonianResolvent_running_alpha_J4_iteratedPower_comm
    (q1 q2 : ℝ) (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) (r s : ℕ) (f : Hilbert) :
    iteratedResolventPower (RH t (alpha_J4 q1)) r (iteratedResolventPower (RH t (alpha_J4 q2)) s f) =
      iteratedResolventPower (RH t (alpha_J4 q2)) s (iteratedResolventPower (RH t (alpha_J4 q1)) r f) :=
  hamiltonianResolvent_iteratedResolventPower_comm ε hε h hh hb m g k t
    (alpha_J4 q1) (alpha_J4 q2) (alpha_J4_pos q1 hq1) (alpha_J4_pos q2 hq2) r s f

theorem hamiltonianResolvent_squared_gut_sub_ir_mem_ten_domains
    (s : ℝ) (f : Hilbert) :
    let d : Hilbert :=
      RH t alpha_GUT_framework (RH t alpha_GUT_framework f) - RH t alphaIR (RH t alphaIR f)
    d ∈ hamiltonianPowerDomain ε hε h hh hb m g k t 3 ∧
    d ∈ (H t).domain ∧
    d ∈ (K).domain ∧
    d ∈ (S t).domain ∧
    d ∈ (Eavg s).domain ∧
    d ∈ (Tstat).domain ∧
    d ∈ (Kroot).domain ∧
    d ∈ (Tpot).domain ∧
    d ∈ (Tgrow).domain ∧
    d ∈ (Tres s).domain ∧
    d ∈ (clockHalf ε).domain :=
  hamiltonianResolvent_squared_sub_mem_ten_domains ε hε h hh hb m g k t s
    alpha_GUT_framework alphaIR alpha_GUT_pos alphaIR_pos f

theorem evolutionFamily_preserves_alpha_J4_weighted_norm_sq
    (qsq s : ℝ) (ψ : Hilbert) :
    alpha_J4 qsq * ‖evolutionFamily ε hε h hh hb m g k s t ψ‖ ^ 2 =
      alpha_J4 qsq * ‖ψ‖ ^ 2 := by
  rw [LinearIsometryEquiv.norm_map]

theorem evolutionFamily_preserves_alphaIR_octonion_weighted_norm_sq
    (s : ℝ) (ψ : Hilbert) :
    (UnifiedTheory.LayerA.FineStructureIRFromGap.gamma_4 / (Nat.choose dim_O d_eff : ℝ)) *
      ‖evolutionFamily ε hε h hh hb m g k s t ψ‖ ^ 2 =
      alphaIR * ‖ψ‖ ^ 2 := by
  rw [LinearIsometryEquiv.norm_map, ← alphaIR_eq_gamma4_over_choose]

theorem sm_alpha_running_octonion_fine_structure_resolvent_master_bridge
    (qsq s : ℝ) (hq : 0 ≤ qsq) (r_pow s_pow : ℕ) (f : Hilbert) :
    (0 < alpha_GUT_framework ∧
     33 < inv_alpha_GUT_framework ∧ inv_alpha_GUT_framework < 34 ∧
     sin2_weinberg_GUT = 3 / 8 ∧
     alpha_J4 0 = alpha_GUT_framework ∧
     0 < alpha_J4 qsq ∧
     alpha_GUT_framework ≤ alpha_J4 qsq) ∧
    (alphaIR = UnifiedTheory.LayerA.FineStructureIRFromGap.gamma_4 /
       (Nat.choose dim_O d_eff : ℝ) ∧
     Nat.choose dim_O d_eff = 70 ∧
     Nat.choose dim_O d_eff = N_W * N_total * disc ∧
     |inv_alphaIR - 137.035999084| < 0.01 ∧
     alphaIR < alpha_GUT_framework) ∧
    (RH t alpha_GUT_framework (RH t alpha_GUT_framework f) - RH t alphaIR (RH t alphaIR f) =
       ((alphaIR - alpha_GUT_framework : ℝ) : ℂ) •
         (RH t alpha_GUT_framework (RH t alpha_GUT_framework (RH t alphaIR f)) +
           RH t alpha_GUT_framework (RH t alphaIR (RH t alphaIR f))) ∧
     RH t alpha_GUT_framework (RH t alpha_GUT_framework f) - RH t alphaIR (RH t alphaIR f) ∈
       hamiltonianPowerDomain ε hε h hh hb m g k t 3 ∧
     iteratedResolventPower (RH t alpha_GUT_framework) r_pow
         (iteratedResolventPower (RH t alphaIR) s_pow f) =
       iteratedResolventPower (RH t alphaIR) s_pow
         (iteratedResolventPower (RH t alpha_GUT_framework) r_pow f) ∧
     alpha_J4 qsq * ‖evolutionFamily ε hε h hh hb m g k s t f‖ ^ 2 =
       alpha_J4 qsq * ‖f‖ ^ 2) :=
  ⟨⟨alpha_GUT_pos, inv_alpha_GUT_bracket.1, inv_alpha_GUT_bracket.2, rfl,
    (dyson_running_alpha_J4_properties qsq hq).1,
    (dyson_running_alpha_J4_properties qsq hq).2.1,
    (dyson_running_alpha_J4_properties qsq hq).2.2.1⟩,
   ⟨alphaIR_eq_gamma4_over_choose, choose_eight_four, seventy_two_readings,
    prediction_matches_PDG, alphaIR_lt_alpha_GUT_framework⟩,
   ⟨hamiltonianResolvent_squared_gut_sub_ir_eq ε hε h hh hb m g k t f,
    hamiltonianResolvent_squared_sub_mem_thirdPowerDomain ε hε h hh hb m g k t
      alpha_GUT_framework alphaIR alpha_GUT_pos alphaIR_pos f,
    hamiltonianResolvent_gut_ir_iteratedPower_comm ε hε h hh hb m g k t r_pow s_pow f,
    evolutionFamily_preserves_alpha_J4_weighted_norm_sq ε hε h hh hb m g k t qsq s f⟩⟩

#print axioms alpha_GUT_eq_unification
#print axioms inv_alpha_GUT_window_and_bracket
#print axioms gut_gauge_couplings_unification_identity
#print axioms j4_vacuum_polarization_properties
#print axioms dyson_running_alpha_J4_properties
#print axioms dyson_running_alpha_J4_monotone
#print axioms gamma_4_ir_eq_gap
#print axioms alphaIR_atomic_and_octonion_identities
#print axioms octonion_four_form_combinatorics
#print axioms alphaIR_numerical_brackets
#print axioms alphaIR_lt_alpha_GUT_framework
#print axioms alphaIR_lt_alpha_J4
#print axioms staticResolvent_gut_sub_ir_eq
#print axioms potentialResolvent_gut_sub_ir_eq
#print axioms growingResolvent_gut_sub_ir_eq
#print axioms residualResolvent_gut_sub_ir_eq
#print axioms hamiltonianResolvent_gut_sub_ir_eq
#print axioms staticResolvent_squared_gut_sub_ir_eq
#print axioms potentialResolvent_squared_gut_sub_ir_eq
#print axioms growingResolvent_squared_gut_sub_ir_eq
#print axioms residualResolvent_squared_gut_sub_ir_eq
#print axioms hamiltonianResolvent_squared_gut_sub_ir_eq
#print axioms staticResolvent_gut_ir_iteratedPower_comm
#print axioms potentialResolvent_gut_ir_iteratedPower_comm
#print axioms growingResolvent_gut_ir_iteratedPower_comm
#print axioms residualResolvent_gut_ir_iteratedPower_comm
#print axioms hamiltonianResolvent_gut_ir_iteratedPower_comm
#print axioms hamiltonianResolvent_running_alpha_J4_squared_sub_eq
#print axioms hamiltonianResolvent_running_alpha_J4_iteratedPower_comm
#print axioms hamiltonianResolvent_squared_gut_sub_ir_mem_ten_domains
#print axioms evolutionFamily_preserves_alpha_J4_weighted_norm_sq
#print axioms evolutionFamily_preserves_alphaIR_octonion_weighted_norm_sq
#print axioms sm_alpha_running_octonion_fine_structure_resolvent_master_bridge
end
end UnifiedTheory.Audit.KFCausalClockFloorSMAlphaRunningOctonionFineStructureBridge
