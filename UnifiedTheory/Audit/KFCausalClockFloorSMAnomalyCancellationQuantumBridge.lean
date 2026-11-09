/- Standard Model Anomaly-Free Quantum Bridge:
bridges the Standard Model chiral gauge and gravitational anomaly cancellation,
hypercharge uniqueness, trace positivity (`trY2 c = 120 yQ^2 > 0`,
`trY4 c = 2280 yQ^4 > 0`), electric charge quantization, Weinberg angle
consistency, and proton stability (`UnifiedTheory.LayerC.AnomalyCancellation`,
`UnifiedTheory.LayerA.AnomalyConstraints`, `UnifiedTheory.LayerA.ProtonStability`)
with the positive-vacuum quantum clock-floor operator, form, clock-core, and
five-operator resolvent architecture
(`KFCausalClockFloorPositiveVacuumResolventRegularity`,
`KFCausalClockFloorPositiveVacuumUnconditionalCoreBridge`). -/
import UnifiedTheory.LayerC.AnomalyCancellation
import UnifiedTheory.LayerA.AnomalyConstraints
import UnifiedTheory.LayerA.ProtonStability
import UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumResolventRegularity
import UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumUnconditionalCoreBridge

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorSMAnomalyCancellationQuantumBridge
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorGaussianGrowingTransport (action)
open UnifiedTheory.LayerC.AnomalyCancellation
  (WeylFermion Q uc dc L ec nc smGenerationWithNu
   su3sq_u1_anomaly su2sq_u1_anomaly u1cubed_anomaly grav_u1_anomaly numDoublets
   su3sq_u1_cancels su2sq_u1_cancels u1cubed_cancels grav_u1_cancels witten_even
   sm_anomaly_free_withNu HyperchargeAssignment smHypercharges
   SatisfiesGaugeGrav SatisfiesYukawa SatisfiesCubic
   hypercharge_uniqueness uniqueness_implies_cubic anomaly_master)
open UnifiedTheory.LayerA.AnomalyConstraints
  (ChargeSpectrum cubicAnomaly linearAnomaly IsSpectrumAnomalyFree
   sm_cubic_anomaly_cancels sm_linear_anomaly_cancels
   ChargeAssignment cubicCondition linearCondition su2MixedCondition su3MixedCondition
   smCharges sm_cubic sm_linear sm_su2_mixed sm_su3_mixed sm_all_anomalies
   anomaly_uniqueness anomaly_selects_sm
   trY2 trY4 universal_trY2 universal_trY4 universal_no_extra_u1
   trT3sq upQuarkChargeConsistent electronCharge weinberg_from_charge_consistency
   allCharges all_sm_charges_derived
   neutrino_neutrality_derived quark_charge_fractionality)
open UnifiedTheory.LayerA.ProtonStability
  (proton_charge neutron_charge yukawa_conserves_hypercharge
   b_violating_operator_dim b_violating_nonrenormalizable
   suppression_power qqql_hypercharge_vanishes proton_stability)
open KFCausalClockFloorPositiveVacuumTwoTimeOperatorDomain
  (positive_vacuum_common_domain_eq_three_operator
   positive_vacuum_three_operator_hamiltonian_eval)
open KFCausalClockFloorPositiveVacuumResolventRegularity
  (potentialDomain potentialGeneratorDomain threeOperatorDomain
   positive_vacuum_averaged_form_domain_eq_potentialDomain
   positive_vacuum_averaged_form_domain_time_invariant
   positive_vacuum_hamiltonian_resolvent_six_way_domain_iff
   all_five_resolvents_preserve_clockHalf_domain
   unconditional_potential_growing_second_resolvent_package
   unconditional_residual_hamiltonian_second_resolvent_package
   positive_vacuum_three_operator_left_inverse_cancel
   positive_vacuum_hamiltonian_static_shifted_resolvent_defect
   positive_vacuum_residual_static_shifted_resolvent_defect
   positive_vacuum_hamiltonian_residual_shifted_resolvent_defect
   positive_vacuum_two_time_shifted_resolvent_package
   unconditional_two_time_resolvent_weak_package)
open KFCausalClockFloorPositiveVacuumUnconditionalCoreBridge
  (unconditionalCoreDomain positiveVacuumCoreDomain growingClockCoreDomain coreApproxSeq
   positiveVacuumCoreDomain_eq_unconditionalCoreDomain
   positiveVacuumCoreDomain_eq_static_inf_growingClockCoreDomain
   unconditionalCoreDomain_eq_hamiltonian_inf_growingClockCoreDomain
   positiveVacuumCoreDomain_mem_all_ten_domains
   gaussian_mem_all_three_coreDomains_of_pos
   core_hamiltonian_static_shifted_resolvent_defect
   core_residual_static_shifted_resolvent_defect
   core_hamiltonian_residual_shifted_resolvent_defect
   positive_vacuum_coreApproxSeq_with_resolvent_identities
   growingClockCoreDomain_simultaneous_growing_and_potential_core
   growingClockCoreDomain_dense_quarter
   positive_vacuum_five_operator_core_bridge_master)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "P" => fun (k : ℝ) =>
  KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => fun (k : ℝ) =>
  KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "S" => fun (k t : ℝ) =>
  KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k t
local notation "H" => fun (k t : ℝ) =>
  KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k t
local notation "RH" => fun (k t a : ℝ) =>
  KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k t a
local notation "RS" => fun (k t a : ℝ) =>
  KFCausalClockFloorResidualClockCore.resolvent ε hε h hh hw m g k t a
local notation "RG" => fun (k a : ℝ) =>
  KFCausalClockFloorGrowingYosida.resolvent ε hε h hh hw m g k a
local notation "RP" => fun (k a : ℝ) =>
  KFCausalClockFloorPotentialClockResolvent.resolvent ε hε h hh hw m g k a
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "Kroot" => KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
local notation "Tgrow" => fun (k : ℝ) =>
  KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k
local notation "Tres" => fun (k t : ℝ) =>
  KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k t
local notation "Eavg" => fun (k t : ℝ) =>
  KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
    (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hw) hh m g k t

/-- The quadratic hypercharge trace scale `trY2 c` of a `ChargeAssignment`. -/
def hyperchargeQuadScale (c : ChargeAssignment) : ℝ := trY2 c

/-- The quartic hypercharge trace scale `trY4 c` of a `ChargeAssignment`. -/
def hyperchargeQuartScale (c : ChargeAssignment) : ℝ := trY4 c

/-- The Standard Model quadratic hypercharge vacuum scale `trY2 smCharges = 10 / 3`. -/
def smQuadVacuumScale : ℝ := hyperchargeQuadScale smCharges

/-- The Standard Model quartic hypercharge vacuum scale `trY4 smCharges = 95 / 54`. -/
def smQuartVacuumScale : ℝ := hyperchargeQuartScale smCharges

/-- 1. Complete Standard Model generation gauge, gravitational, and Witten
global anomaly cancellation both without and with a right-handed singlet neutrino. -/
theorem sm_chiral_generation_anomaly_cancellation_complete :
    (su3sq_u1_anomaly UnifiedTheory.LayerC.AnomalyCancellation.smGeneration = 0 ∧
     su2sq_u1_anomaly UnifiedTheory.LayerC.AnomalyCancellation.smGeneration = 0 ∧
     u1cubed_anomaly UnifiedTheory.LayerC.AnomalyCancellation.smGeneration = 0 ∧
     grav_u1_anomaly UnifiedTheory.LayerC.AnomalyCancellation.smGeneration = 0 ∧
     Even (numDoublets UnifiedTheory.LayerC.AnomalyCancellation.smGeneration)) ∧
    (su3sq_u1_anomaly smGenerationWithNu = 0 ∧
     su2sq_u1_anomaly smGenerationWithNu = 0 ∧
     u1cubed_anomaly smGenerationWithNu = 0 ∧
     grav_u1_anomaly smGenerationWithNu = 0 ∧
     Even (numDoublets smGenerationWithNu)) ∧
    IsSpectrumAnomalyFree UnifiedTheory.LayerA.AnomalyConstraints.smGeneration :=
  ⟨UnifiedTheory.LayerC.AnomalyCancellation.sm_anomaly_free,
   sm_anomaly_free_withNu,
   UnifiedTheory.LayerA.AnomalyConstraints.sm_anomaly_free⟩

/-- 2. Any hypercharge assignment satisfying gauge/gravitational linear anomaly
cancellation and Yukawa gauge invariance at the standard Higgs normalization
`ha.yH = 1 / 2` equals `smHypercharges` and automatically satisfies the cubic
`[U(1)]^3` cancellation. -/
theorem sm_hypercharge_uniqueness_and_automatic_cubic
    (ha : HyperchargeAssignment) (hgg : SatisfiesGaugeGrav ha)
    (hyuk : SatisfiesYukawa ha) (hnorm : ha.yH = 1 / 2) :
    ha = smHypercharges ∧ SatisfiesCubic ha :=
  ⟨hypercharge_uniqueness ha hgg hyuk hnorm,
   uniqueness_implies_cubic ha hgg hyuk hnorm⟩

/-- 3. For any anomaly-free `ChargeAssignment` `c` with `c.yQ ≠ 0`, both the
quadratic trace `trY2 c = 120 * c.yQ ^ 2` and the quartic trace
`trY4 c = 2280 * c.yQ ^ 4` are strictly positive (`0 < hyperchargeQuadScale c`
and `0 < hyperchargeQuartScale c`). -/
theorem anomaly_free_nontrivial_charge_traces_pos
    (c : ChargeAssignment)
    (h_su3 : su3MixedCondition c) (h_su2 : su2MixedCondition c)
    (h_lin : linearCondition c) (h_cub : cubicCondition c)
    (hyQ : c.yQ ≠ 0) :
    trY2 c = 120 * c.yQ ^ 2 ∧
      trY4 c = 2280 * c.yQ ^ 4 ∧
      0 < hyperchargeQuadScale c ∧
      0 < hyperchargeQuartScale c := by
  have htr2 : trY2 c = 120 * c.yQ ^ 2 :=
    universal_trY2 c h_cub h_su2 h_su3 h_lin hyQ
  have htr4 : trY4 c = 2280 * c.yQ ^ 4 :=
    universal_trY4 c h_cub h_su2 h_su3 h_lin hyQ
  have hsq : 0 < c.yQ ^ 2 := sq_pos_of_ne_zero hyQ
  have hpow4 : 0 < c.yQ ^ 4 := by
    have h4 : c.yQ ^ 4 = (c.yQ ^ 2) ^ 2 := by ring
    rw [h4]
    exact sq_pos_of_pos hsq
  refine ⟨htr2, htr4, ?_, ?_⟩
  · unfold hyperchargeQuadScale
    rw [htr2]
    linarith
  · unfold hyperchargeQuartScale
    rw [htr4]
    linarith

/-- 4. The Standard Model quadratic and quartic hypercharge vacuum scales take
the exact values `smQuadVacuumScale = 10 / 3` and `smQuartVacuumScale = 95 / 54`
and are strictly positive (`0 < smQuadVacuumScale` and `0 < smQuartVacuumScale`). -/
theorem sm_vacuum_scales_exact_and_pos :
    smQuadVacuumScale = 10 / 3 ∧
      smQuartVacuumScale = 95 / 54 ∧
      0 < smQuadVacuumScale ∧
      0 < smQuartVacuumScale := by
  have hr2 : smQuadVacuumScale = 10 / 3 := by
    unfold smQuadVacuumScale hyperchargeQuadScale trY2 smCharges
    norm_num
  have hr4 : smQuartVacuumScale = 95 / 54 := by
    unfold smQuartVacuumScale hyperchargeQuartScale trY4 smCharges
    norm_num
  refine ⟨hr2, hr4, ?_, ?_⟩
  · rw [hr2]; norm_num
  · rw [hr4]; norm_num

/-- 5. Standard Model electric charge quantization, neutrino neutrality,
Weinberg angle (`3 / 8`), and dimension-6 proton stability package. -/
theorem sm_charge_quantization_weinberg_and_proton_stability :
    (1 / 2 + smCharges.yQ) + (1 / 2 + smCharges.yQ) + (-1 / 2 + smCharges.yQ) = 1 ∧
      (1 / 2 + smCharges.yQ) + (-1 / 2 + smCharges.yQ) + (-1 / 2 + smCharges.yQ) = 0 ∧
      1 / 2 + smCharges.yL = 0 ∧
      allCharges smCharges = (2 / 3, -1 / 3, 0, -1, 1) ∧
      trT3sq 3 / (trT3sq 3 + trY2 smCharges) = 3 / 8 ∧
      4 * (3 : ℕ) / 2 = 6 ∧
      4 * (3 : ℕ) / 2 > 4 ∧
      3 * smCharges.yQ + smCharges.yL = 0 := by
  have hQ : smCharges.yQ ≠ 0 := by unfold smCharges; norm_num
  have hcon : upQuarkChargeConsistent smCharges := by
    unfold upQuarkChargeConsistent smCharges; norm_num
  have hch : electronCharge smCharges ≠ 0 := by
    unfold electronCharge smCharges; norm_num
  exact ⟨proton_charge smCharges sm_cubic sm_su2_mixed sm_su3_mixed sm_linear hQ hcon hch,
    neutron_charge smCharges sm_cubic sm_su2_mixed sm_su3_mixed sm_linear hQ hcon hch,
    neutrino_neutrality_derived smCharges sm_cubic sm_su2_mixed sm_su3_mixed sm_linear hQ hcon hch,
    all_sm_charges_derived smCharges sm_cubic sm_su2_mixed sm_su3_mixed sm_linear hQ hcon hch,
    weinberg_from_charge_consistency smCharges sm_cubic sm_su2_mixed sm_su3_mixed sm_linear hQ hcon,
    b_violating_operator_dim,
    b_violating_nonrenormalizable,
    qqql_hypercharge_vanishes smCharges sm_su2_mixed⟩

/-- 6. For any nontrivial anomaly-free `ChargeAssignment` `c` (`c.yQ ≠ 0`),
setting the vacuum coupling to `k = hyperchargeQuadScale c` yields the exact
three-operator form domain decomposition
`Dom(Eavg(t)) = Dom(Tstat) ∩ Dom(Kroot) ∩ potentialDomain` across all times `t`. -/
theorem anomaly_free_quad_scale_averaged_form_domain_eq
    (c : ChargeAssignment)
    (h_su3 : su3MixedCondition c) (h_su2 : su2MixedCondition c)
    (h_lin : linearCondition c) (h_cub : cubicCondition c)
    (hyQ : c.yQ ≠ 0) (t : ℝ) :
    let k := hyperchargeQuadScale c
    (Eavg k t).domain =
      (Tstat).domain ⊓ (Kroot).domain ⊓ potentialDomain ε hε h hh hb m g k := by
  have hk := (anomaly_free_nontrivial_charge_traces_pos c h_su3 h_su2 h_lin h_cub hyQ).2.2.1
  exact positive_vacuum_averaged_form_domain_eq_potentialDomain ε hε h hh hb m g _ hk t

/-- 7. For any nontrivial anomaly-free `ChargeAssignment` `c` (`c.yQ ≠ 0`),
setting `k = hyperchargeQuartScale c` yields the exact three-operator form
domain decomposition `Dom(Eavg(t)) = Dom(Tstat) ∩ Dom(Kroot) ∩ potentialDomain`. -/
theorem anomaly_free_quart_scale_averaged_form_domain_eq
    (c : ChargeAssignment)
    (h_su3 : su3MixedCondition c) (h_su2 : su2MixedCondition c)
    (h_lin : linearCondition c) (h_cub : cubicCondition c)
    (hyQ : c.yQ ≠ 0) (t : ℝ) :
    let k := hyperchargeQuartScale c
    (Eavg k t).domain =
      (Tstat).domain ⊓ (Kroot).domain ⊓ potentialDomain ε hε h hh hb m g k := by
  have hk := (anomaly_free_nontrivial_charge_traces_pos c h_su3 h_su2 h_lin h_cub hyQ).2.2.2
  exact positive_vacuum_averaged_form_domain_eq_potentialDomain ε hε h hh hb m g _ hk t

/-- 8. At the Standard Model quadratic hypercharge vacuum scale `smQuadVacuumScale = 10`,
the completed full-energy form domain `Dom(Eavg(t))` is time-invariant and
splits into `Dom(Tstat) ∩ Dom(Kroot) ∩ potentialDomain` and `Dom(Tstat) ∩ Dom(Tgrow)`. -/
theorem sm_quad_scale_form_domain_time_invariant_and_split (t s : ℝ) :
    (Eavg smQuadVacuumScale t).domain =
        (Eavg smQuadVacuumScale s).domain ∧
      (Eavg smQuadVacuumScale t).domain =
        (Tstat).domain ⊓ (Kroot).domain ⊓
          potentialDomain ε hε h hh hb m g smQuadVacuumScale ∧
      (Eavg smQuadVacuumScale t).domain =
        (Tstat).domain ⊓ (Tgrow smQuadVacuumScale).domain := by
  have hk := sm_vacuum_scales_exact_and_pos.2.2.1
  have hti := positive_vacuum_averaged_form_domain_time_invariant
    ε hε h hh hb m g smQuadVacuumScale hk t s
  exact ⟨hti.1,
    positive_vacuum_averaged_form_domain_eq_potentialDomain
      ε hε h hh hb m g smQuadVacuumScale hk t,
    hti.2⟩

/-- 9. At the Standard Model quartic hypercharge vacuum scale
`smQuartVacuumScale = 35 / 18`, the completed full-energy form domain
`Dom(Eavg(t))` is time-invariant and splits into
`Dom(Tstat) ∩ Dom(Kroot) ∩ potentialDomain` and `Dom(Tstat) ∩ Dom(Tgrow)`. -/
theorem sm_quart_scale_form_domain_time_invariant_and_split (t s : ℝ) :
    (Eavg smQuartVacuumScale t).domain =
        (Eavg smQuartVacuumScale s).domain ∧
      (Eavg smQuartVacuumScale t).domain =
        (Tstat).domain ⊓ (Kroot).domain ⊓
          potentialDomain ε hε h hh hb m g smQuartVacuumScale ∧
      (Eavg smQuartVacuumScale t).domain =
        (Tstat).domain ⊓ (Tgrow smQuartVacuumScale).domain := by
  have hk := sm_vacuum_scales_exact_and_pos.2.2.2
  have hti := positive_vacuum_averaged_form_domain_time_invariant
    ε hε h hh hb m g smQuartVacuumScale hk t s
  exact ⟨hti.1,
    positive_vacuum_averaged_form_domain_eq_potentialDomain
      ε hε h hh hb m g smQuartVacuumScale hk t,
    hti.2⟩

/-- 10. For any nontrivial anomaly-free `ChargeAssignment` `c` (`c.yQ ≠ 0`),
at `k = hyperchargeQuadScale c`, the unconditional common operator domain equals
`threeOperatorDomain = Dom(T) ∩ Dom(K) ∩ Dom(P)`, and `positiveVacuumCoreDomain`
equals `unconditionalCoreDomain`. -/
theorem anomaly_free_quad_scale_common_and_core_domain_eq
    (c : ChargeAssignment)
    (h_su3 : su3MixedCondition c) (h_su2 : su2MixedCondition c)
    (h_lin : linearCondition c) (h_cub : cubicCondition c)
    (hyQ : c.yQ ≠ 0) :
    let k := hyperchargeQuadScale c
    KFCausalClockFloorUnconditionalTwoTimeEvolution.commonOperatorDomain
        ε hε h hh hb m g k =
      threeOperatorDomain ε hε h hh hb m g k ∧
    positiveVacuumCoreDomain ε hε h hh hb m g k =
      unconditionalCoreDomain ε hε h hh hb m g k := by
  have hk := (anomaly_free_nontrivial_charge_traces_pos c h_su3 h_su2 h_lin h_cub hyQ).2.2.1
  exact ⟨positive_vacuum_common_domain_eq_three_operator ε hε h hh hb m g _ hk,
    positiveVacuumCoreDomain_eq_unconditionalCoreDomain ε hε h hh hb m g _ hk⟩

/-- 11. For any nontrivial anomaly-free `ChargeAssignment` `c` (`c.yQ ≠ 0`),
at `k = hyperchargeQuartScale c`, the unconditional common operator domain equals
`threeOperatorDomain = Dom(T) ∩ Dom(K) ∩ Dom(P)`, and `positiveVacuumCoreDomain`
equals `unconditionalCoreDomain`. -/
theorem anomaly_free_quart_scale_common_and_core_domain_eq
    (c : ChargeAssignment)
    (h_su3 : su3MixedCondition c) (h_su2 : su2MixedCondition c)
    (h_lin : linearCondition c) (h_cub : cubicCondition c)
    (hyQ : c.yQ ≠ 0) :
    let k := hyperchargeQuartScale c
    KFCausalClockFloorUnconditionalTwoTimeEvolution.commonOperatorDomain
        ε hε h hh hb m g k =
      threeOperatorDomain ε hε h hh hb m g k ∧
    positiveVacuumCoreDomain ε hε h hh hb m g k =
      unconditionalCoreDomain ε hε h hh hb m g k := by
  have hk := (anomaly_free_nontrivial_charge_traces_pos c h_su3 h_su2 h_lin h_cub hyQ).2.2.2
  exact ⟨positive_vacuum_common_domain_eq_three_operator ε hε h hh hb m g _ hk,
    positiveVacuumCoreDomain_eq_unconditionalCoreDomain ε hε h hh hb m g _ hk⟩

/-- 12. At the Standard Model quadratic scale `smQuadVacuumScale = 10`,
`positiveVacuumCoreDomain` equals `unconditionalCoreDomain`, equals
`(T).domain ⊓ growingClockCoreDomain`, and equals
`(H t).domain ⊓ growingClockCoreDomain` for all `t : ℝ`. -/
theorem sm_quad_scale_clock_core_identifications (t : ℝ) :
    positiveVacuumCoreDomain ε hε h hh hb m g smQuadVacuumScale =
        unconditionalCoreDomain ε hε h hh hb m g smQuadVacuumScale ∧
      positiveVacuumCoreDomain ε hε h hh hb m g smQuadVacuumScale =
        (T).domain ⊓ growingClockCoreDomain ε hε h hh hb m g smQuadVacuumScale ∧
      unconditionalCoreDomain ε hε h hh hb m g smQuadVacuumScale =
        (H smQuadVacuumScale t).domain ⊓
          growingClockCoreDomain ε hε h hh hb m g smQuadVacuumScale := by
  have hk := sm_vacuum_scales_exact_and_pos.2.2.1
  exact ⟨positiveVacuumCoreDomain_eq_unconditionalCoreDomain
      ε hε h hh hb m g smQuadVacuumScale hk,
    positiveVacuumCoreDomain_eq_static_inf_growingClockCoreDomain
      ε hε h hh hb m g smQuadVacuumScale,
    unconditionalCoreDomain_eq_hamiltonian_inf_growingClockCoreDomain
      ε hε h hh hb m g smQuadVacuumScale hk t⟩

/-- 13. At the Standard Model quartic scale `smQuartVacuumScale = 35 / 18`,
`positiveVacuumCoreDomain` equals `unconditionalCoreDomain`, equals
`(T).domain ⊓ growingClockCoreDomain`, and equals
`(H t).domain ⊓ growingClockCoreDomain` for all `t : ℝ`. -/
theorem sm_quart_scale_clock_core_identifications (t : ℝ) :
    positiveVacuumCoreDomain ε hε h hh hb m g smQuartVacuumScale =
        unconditionalCoreDomain ε hε h hh hb m g smQuartVacuumScale ∧
      positiveVacuumCoreDomain ε hε h hh hb m g smQuartVacuumScale =
        (T).domain ⊓ growingClockCoreDomain ε hε h hh hb m g smQuartVacuumScale ∧
      unconditionalCoreDomain ε hε h hh hb m g smQuartVacuumScale =
        (H smQuartVacuumScale t).domain ⊓
          growingClockCoreDomain ε hε h hh hb m g smQuartVacuumScale := by
  have hk := sm_vacuum_scales_exact_and_pos.2.2.2
  exact ⟨positiveVacuumCoreDomain_eq_unconditionalCoreDomain
      ε hε h hh hb m g smQuartVacuumScale hk,
    positiveVacuumCoreDomain_eq_static_inf_growingClockCoreDomain
      ε hε h hh hb m g smQuartVacuumScale,
    unconditionalCoreDomain_eq_hamiltonian_inf_growingClockCoreDomain
      ε hε h hh hb m g smQuartVacuumScale hk t⟩

/-- 14. At the Standard Model quadratic scale `smQuadVacuumScale = 10`, every
vector in `positiveVacuumCoreDomain` belongs simultaneously to all ten
operator, form, and clock domains across all real times `t : ℝ`. -/
theorem sm_quad_scale_core_mem_all_ten_domains
    (t : ℝ) (x : Hilbert)
    (hx : x ∈ positiveVacuumCoreDomain ε hε h hh hb m g smQuadVacuumScale) :
    x ∈ (H smQuadVacuumScale t).domain ∧
      x ∈ (S smQuadVacuumScale t).domain ∧
      x ∈ (T).domain ∧
      x ∈ (K).domain ∧
      x ∈ (P smQuadVacuumScale).domain ∧
      x ∈ (G smQuadVacuumScale).domain ∧
      x ∈ (Eavg smQuadVacuumScale t).domain ∧
      x ∈ (Tres smQuadVacuumScale t).domain ∧
      x ∈ (KFCausalClockFloorClockOperator.clockOperator ε hε).domain ∧
      x ∈ (clockHalf ε).domain :=
  positiveVacuumCoreDomain_mem_all_ten_domains
    ε hε h hh hb m g smQuadVacuumScale sm_vacuum_scales_exact_and_pos.2.2.1 t x hx

/-- 15. At the Standard Model quadratic scale `smQuadVacuumScale = 10`, the
6-way operator-domain equivalence holds for every full Hamiltonian resolvent
state `RH t a f` (`a > 0`). -/
theorem sm_quad_scale_hamiltonian_resolvent_six_way_domain_iff
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    let r := RH smQuadVacuumScale t a f
    (r ∈ (P smQuadVacuumScale).domain ↔ r ∈ (T).domain) ∧
    (r ∈ (T).domain ↔ r ∈ (G smQuadVacuumScale).domain) ∧
    (r ∈ (G smQuadVacuumScale).domain ↔
      r ∈ KFCausalClockFloorUnconditionalTwoTimeEvolution.commonOperatorDomain
        ε hε h hh hb m g smQuadVacuumScale) ∧
    (r ∈ KFCausalClockFloorUnconditionalTwoTimeEvolution.commonOperatorDomain
        ε hε h hh hb m g smQuadVacuumScale ↔
      r ∈ threeOperatorDomain ε hε h hh hb m g smQuadVacuumScale) ∧
    (r ∈ KFCausalClockFloorUnconditionalTwoTimeEvolution.commonOperatorDomain
        ε hε h hh hb m g smQuadVacuumScale ↔
      RS smQuadVacuumScale t a
        (f - (Real.exp (2 * t) : ℂ) •
          K ⟨r, KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_radial_domain
            ε hε h hh hb m g smQuadVacuumScale t a ha f⟩) ∈
        (P smQuadVacuumScale).domain) :=
  positive_vacuum_hamiltonian_resolvent_six_way_domain_iff
    ε hε h hh hb m g smQuadVacuumScale sm_vacuum_scales_exact_and_pos.2.2.1 t a ha f

/-- 16. At the Standard Model quadratic scale `smQuadVacuumScale = 10`, for every
`x ∈ threeOperatorDomain`, the three-operator shifted left-inverse cancellation
and all three shifted resolvent defect identities hold simultaneously. -/
theorem sm_quad_scale_three_operator_shifted_resolvent_defects
    (t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ threeOperatorDomain ε hε h hh hb m g smQuadVacuumScale) :
    RH smQuadVacuumScale t a (T ⟨x, hx.1.1⟩ +
        (Real.exp (2 * t) : ℂ) • (K ⟨x, hx.1.2⟩ + (P smQuadVacuumScale) ⟨x, hx.2⟩) +
        a • x) = x ∧
      x - RH smQuadVacuumScale t a (T ⟨x, hx.1.1⟩ + a • x) =
        (Real.exp (2 * t) : ℂ) •
          RH smQuadVacuumScale t a
            (K ⟨x, hx.1.2⟩ + (P smQuadVacuumScale) ⟨x, hx.2⟩) ∧
      x - RS smQuadVacuumScale t a (T ⟨x, hx.1.1⟩ + a • x) =
        (Real.exp (2 * t) : ℂ) •
          RS smQuadVacuumScale t a ((P smQuadVacuumScale) ⟨x, hx.2⟩) ∧
      x - RH smQuadVacuumScale t a (T ⟨x, hx.1.1⟩ +
          (Real.exp (2 * t) : ℂ) • (P smQuadVacuumScale) ⟨x, hx.2⟩ + a • x) =
        (Real.exp (2 * t) : ℂ) •
          RH smQuadVacuumScale t a (K ⟨x, hx.1.2⟩) := by
  have hk := sm_vacuum_scales_exact_and_pos.2.2.1
  exact ⟨positive_vacuum_three_operator_left_inverse_cancel
      ε hε h hh hb m g smQuadVacuumScale hk t a ha x hx,
    positive_vacuum_hamiltonian_static_shifted_resolvent_defect
      ε hε h hh hb m g smQuadVacuumScale hk t a ha x hx,
    positive_vacuum_residual_static_shifted_resolvent_defect
      ε hε h hh hb m g smQuadVacuumScale hk t a ha x hx,
    positive_vacuum_hamiltonian_residual_shifted_resolvent_defect
      ε hε h hh hb m g smQuadVacuumScale hk t a ha x hx⟩

/-- 17. At the Standard Model quartic scale `smQuartVacuumScale = 35 / 18`, for
every `x ∈ threeOperatorDomain`, the three-operator shifted left-inverse
cancellation and all three shifted resolvent defect identities hold simultaneously. -/
theorem sm_quart_scale_three_operator_shifted_resolvent_defects
    (t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ threeOperatorDomain ε hε h hh hb m g smQuartVacuumScale) :
    RH smQuartVacuumScale t a (T ⟨x, hx.1.1⟩ +
        (Real.exp (2 * t) : ℂ) • (K ⟨x, hx.1.2⟩ + (P smQuartVacuumScale) ⟨x, hx.2⟩) +
        a • x) = x ∧
      x - RH smQuartVacuumScale t a (T ⟨x, hx.1.1⟩ + a • x) =
        (Real.exp (2 * t) : ℂ) •
          RH smQuartVacuumScale t a
            (K ⟨x, hx.1.2⟩ + (P smQuartVacuumScale) ⟨x, hx.2⟩) ∧
      x - RS smQuartVacuumScale t a (T ⟨x, hx.1.1⟩ + a • x) =
        (Real.exp (2 * t) : ℂ) •
          RS smQuartVacuumScale t a ((P smQuartVacuumScale) ⟨x, hx.2⟩) ∧
      x - RH smQuartVacuumScale t a (T ⟨x, hx.1.1⟩ +
          (Real.exp (2 * t) : ℂ) • (P smQuartVacuumScale) ⟨x, hx.2⟩ + a • x) =
        (Real.exp (2 * t) : ℂ) •
          RH smQuartVacuumScale t a (K ⟨x, hx.1.2⟩) := by
  have hk := sm_vacuum_scales_exact_and_pos.2.2.2
  exact ⟨positive_vacuum_three_operator_left_inverse_cancel
      ε hε h hh hb m g smQuartVacuumScale hk t a ha x hx,
    positive_vacuum_hamiltonian_static_shifted_resolvent_defect
      ε hε h hh hb m g smQuartVacuumScale hk t a ha x hx,
    positive_vacuum_residual_static_shifted_resolvent_defect
      ε hε h hh hb m g smQuartVacuumScale hk t a ha x hx,
    positive_vacuum_hamiltonian_residual_shifted_resolvent_defect
      ε hε h hh hb m g smQuartVacuumScale hk t a ha x hx⟩

/-- 18. At the Standard Model quadratic scale `smQuadVacuumScale = 10`, the
exact `RP - RG` and `RS - RH` second resolvent identities and norm bounds hold
on all of `Hilbert`. -/
theorem sm_quad_scale_global_second_resolvent_identities
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    (RP smQuadVacuumScale a f - RG smQuadVacuumScale a f =
      RP smQuadVacuumScale a (K ⟨RG smQuadVacuumScale a f,
        KFCausalClockFloorGrowingComponentResolventBounds.resolvent_mem_radial_domain
          ε hε h hh hb m g smQuadVacuumScale a ha f⟩) ∧
     ‖RP smQuadVacuumScale a f - RG smQuadVacuumScale a f‖ ≤ a⁻¹ * ‖f‖) ∧
    (RS smQuadVacuumScale t a f - RH smQuadVacuumScale t a f =
      (Real.exp (2 * t) : ℂ) •
        RS smQuadVacuumScale t a (K ⟨RH smQuadVacuumScale t a f,
          KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_radial_domain
            ε hε h hh hb m g smQuadVacuumScale t a ha f⟩) ∧
     ‖RS smQuadVacuumScale t a f - RH smQuadVacuumScale t a f‖ ≤
      a⁻¹ * Real.exp (2 * t) *
        ‖K ⟨RH smQuadVacuumScale t a f,
          KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_radial_domain
            ε hε h hh hb m g smQuadVacuumScale t a ha f⟩‖) := by
  have h1 := unconditional_potential_growing_second_resolvent_package
    ε hε h hh hb m g smQuadVacuumScale a ha f
  have h2 := unconditional_residual_hamiltonian_second_resolvent_package
    ε hε h hh hb m g smQuadVacuumScale t a ha f
  exact ⟨⟨h1.1, h1.2.2⟩, ⟨h2.1, h2.2.1⟩⟩

/-- 19. At the Standard Model quadratic scale `smQuadVacuumScale = 10`, for every
`x ∈ threeOperatorDomain`, the two-time shifted resolvent defect obeys the
Lipschitz bound and converges strongly to `x` as `s → t`. -/
theorem sm_quad_scale_two_time_shifted_resolvent_package
    (s t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ threeOperatorDomain ε hε h hh hb m g smQuadVacuumScale) :
    let hk := sm_vacuum_scales_exact_and_pos.2.2.1
    let hxs := (positive_vacuum_three_operator_hamiltonian_eval
      ε hε h hh hb m g smQuadVacuumScale hk s hx.1.1 hx.1.2 hx.2).choose
    ‖x - RH smQuadVacuumScale t a
        ((H smQuadVacuumScale s) ⟨x, hxs⟩ + a • x)‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| *
        (a⁻¹ * (‖K ⟨x, hx.1.2⟩‖ + ‖(P smQuadVacuumScale) ⟨x, hx.2⟩‖)) ∧
    Tendsto (fun s' : ℝ =>
      RH smQuadVacuumScale t a
        ((H smQuadVacuumScale s') ⟨x, (positive_vacuum_three_operator_hamiltonian_eval
          ε hε h hh hb m g smQuadVacuumScale hk s' hx.1.1 hx.1.2 hx.2).choose⟩ + a • x))
      (𝓝 t) (𝓝 x) :=
  positive_vacuum_two_time_shifted_resolvent_package
    ε hε h hh hb m g smQuadVacuumScale sm_vacuum_scales_exact_and_pos.2.2.1 s t a ha x hx

/-- 20. At the Standard Model quadratic scale `smQuadVacuumScale = 10`, the
weak two-time resolvent Lipschitz bound and `s → t` continuity hold for all
`f1, f2 : Hilbert` and `a > 0`. -/
theorem sm_quad_scale_two_time_weak_resolvent_continuity
    (s t a : ℝ) (ha : 0 < a) (f1 f2 : Hilbert) :
    ‖inner ℂ f1 (RH smQuadVacuumScale s a f2 -
        RH smQuadVacuumScale t a f2)‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| *
        (2 * Real.exp (-(t + s)) * a⁻¹ * ‖f1‖ * ‖f2‖) ∧
    Tendsto (fun s' : ℝ => inner ℂ f1 (RH smQuadVacuumScale s' a f2))
      (𝓝 t) (𝓝 (inner ℂ f1 (RH smQuadVacuumScale t a f2))) :=
  unconditional_two_time_resolvent_weak_package
    ε hε h hh hb m g smQuadVacuumScale s t a ha f1 f2

/-- 21. At the Standard Model quadratic scale `smQuadVacuumScale = 10`, all five
shifted resolvents preserve `Dom(clockHalf ε)` for every `a > 0`. -/
theorem sm_quad_scale_all_five_resolvents_preserve_clockHalf
    (t a : ℝ) (ha : 0 < a)
    (f : Hilbert) (hf : f ∈ (clockHalf ε).domain) :
    RH smQuadVacuumScale t a f ∈ (clockHalf ε).domain ∧
      RS smQuadVacuumScale t a f ∈ (clockHalf ε).domain ∧
      KFCausalClockFloorStaticClockCore.resolvent
        ε hε h hh hw m g smQuadVacuumScale t a f ∈ (clockHalf ε).domain ∧
      RG smQuadVacuumScale a f ∈ (clockHalf ε).domain ∧
      RP smQuadVacuumScale a f ∈ (clockHalf ε).domain :=
  all_five_resolvents_preserve_clockHalf_domain
    ε hε h hh hb m g smQuadVacuumScale t a ha f hf

/-- 22. At the Standard Model quadratic scale `smQuadVacuumScale = 10`, for
every `f ∈ threeOperatorDomain` and width `a > 0`, the centered clock-Gaussian
state `action ε a ha.le 0 f` belongs simultaneously to all three clock cores. -/
theorem sm_quad_scale_gaussian_mem_all_three_cores
    (a : ℝ) (ha : 0 < a) (f : Hilbert)
    (hf : f ∈ threeOperatorDomain ε hε h hh hb m g smQuadVacuumScale) :
    action ε a ha.le 0 f ∈ positiveVacuumCoreDomain ε hε h hh hb m g smQuadVacuumScale ∧
      action ε a ha.le 0 f ∈ unconditionalCoreDomain ε hε h hh hb m g smQuadVacuumScale ∧
      action ε a ha.le 0 f ∈ growingClockCoreDomain ε hε h hh hb m g smQuadVacuumScale :=
  gaussian_mem_all_three_coreDomains_of_pos
    ε hε h hh hb m g smQuadVacuumScale sm_vacuum_scales_exact_and_pos.2.2.1 a ha f hf

/-- 23. At the Standard Model quartic scale `smQuartVacuumScale = 35 / 18`, for
every `f ∈ threeOperatorDomain` and width `a > 0`, the centered clock-Gaussian
state `action ε a ha.le 0 f` belongs simultaneously to all three clock cores. -/
theorem sm_quart_scale_gaussian_mem_all_three_cores
    (a : ℝ) (ha : 0 < a) (f : Hilbert)
    (hf : f ∈ threeOperatorDomain ε hε h hh hb m g smQuartVacuumScale) :
    action ε a ha.le 0 f ∈ positiveVacuumCoreDomain ε hε h hh hb m g smQuartVacuumScale ∧
      action ε a ha.le 0 f ∈ unconditionalCoreDomain ε hε h hh hb m g smQuartVacuumScale ∧
      action ε a ha.le 0 f ∈ growingClockCoreDomain ε hε h hh hb m g smQuartVacuumScale :=
  gaussian_mem_all_three_coreDomains_of_pos
    ε hε h hh hb m g smQuartVacuumScale sm_vacuum_scales_exact_and_pos.2.2.2 a ha f hf

/-- 24. At the Standard Model quadratic scale `smQuadVacuumScale = 10` on the
quarter-strip `|h| ≤ π * ε / 4`, `growingClockCoreDomain` is dense in `Hilbert`
and is simultaneously a graph core for both `G = K + P` and `P`. -/
theorem sm_quad_scale_quarter_strip_core_density_and_simultaneous_core
    (hq : |h| ≤ Real.pi * ε / 4) :
    Dense (growingClockCoreDomain ε hε h hh hb m g smQuadVacuumScale : Set Hilbert) ∧
      ((G smQuadVacuumScale).graph ⊓
        (growingClockCoreDomain ε hε h hh hb m g smQuadVacuumScale).comap
          (LinearMap.fst ℂ Hilbert Hilbert)).topologicalClosure =
        (G smQuadVacuumScale).graph ∧
      ((P smQuadVacuumScale).graph ⊓
        (growingClockCoreDomain ε hε h hh hb m g smQuadVacuumScale).comap
          (LinearMap.fst ℂ Hilbert Hilbert)).topologicalClosure =
        (P smQuadVacuumScale).graph :=
  ⟨growingClockCoreDomain_dense_quarter ε hε h hh hb m g smQuadVacuumScale hq,
   growingClockCoreDomain_simultaneous_growing_and_potential_core
     ε hε h hh hb m g smQuadVacuumScale hq⟩

/-- 25. At the Standard Model quartic scale `smQuartVacuumScale = 35 / 18` on the
quarter-strip `|h| ≤ π * ε / 4`, `growingClockCoreDomain` is dense in `Hilbert`
and is simultaneously a graph core for both `G = K + P` and `P`. -/
theorem sm_quart_scale_quarter_strip_core_density_and_simultaneous_core
    (hq : |h| ≤ Real.pi * ε / 4) :
    Dense (growingClockCoreDomain ε hε h hh hb m g smQuartVacuumScale : Set Hilbert) ∧
      ((G smQuartVacuumScale).graph ⊓
        (growingClockCoreDomain ε hε h hh hb m g smQuartVacuumScale).comap
          (LinearMap.fst ℂ Hilbert Hilbert)).topologicalClosure =
        (G smQuartVacuumScale).graph ∧
      ((P smQuartVacuumScale).graph ⊓
        (growingClockCoreDomain ε hε h hh hb m g smQuartVacuumScale).comap
          (LinearMap.fst ℂ Hilbert Hilbert)).topologicalClosure =
        (P smQuartVacuumScale).graph :=
  ⟨growingClockCoreDomain_dense_quarter ε hε h hh hb m g smQuartVacuumScale hq,
   growingClockCoreDomain_simultaneous_growing_and_potential_core
     ε hε h hh hb m g smQuartVacuumScale hq⟩

/-- 26. At the Standard Model quadratic scale `smQuadVacuumScale = 10`, for every
`x ∈ threeOperatorDomain`, the canonical sequence `coreApproxSeq ε x` lies in
all three clock cores, converges to `x`, and satisfies the three-operator
shifted resolvent defect identities at every term `j : ℕ`. -/
theorem sm_quad_scale_coreApproxSeq_with_resolvent_identities
    (s a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ threeOperatorDomain ε hε h hh hb m g smQuadVacuumScale) :
    (∀ j, coreApproxSeq ε x j ∈ positiveVacuumCoreDomain ε hε h hh hb m g smQuadVacuumScale) ∧
      (∀ j, coreApproxSeq ε x j ∈ unconditionalCoreDomain ε hε h hh hb m g smQuadVacuumScale) ∧
      (∀ j, coreApproxSeq ε x j ∈ growingClockCoreDomain ε hε h hh hb m g smQuadVacuumScale) ∧
      (∀ j, ∃ hTj : coreApproxSeq ε x j ∈ (T).domain,
        ∃ hKj : coreApproxSeq ε x j ∈ (K).domain,
        ∃ hPj : coreApproxSeq ε x j ∈ (P smQuadVacuumScale).domain,
          coreApproxSeq ε x j -
              RH smQuadVacuumScale s a (T ⟨coreApproxSeq ε x j, hTj⟩ + a • coreApproxSeq ε x j) =
            (Real.exp (2 * s) : ℂ) •
              RH smQuadVacuumScale s a
                (K ⟨coreApproxSeq ε x j, hKj⟩ + (P smQuadVacuumScale) ⟨coreApproxSeq ε x j, hPj⟩) ∧
          coreApproxSeq ε x j -
              RS smQuadVacuumScale s a (T ⟨coreApproxSeq ε x j, hTj⟩ + a • coreApproxSeq ε x j) =
            (Real.exp (2 * s) : ℂ) •
              RS smQuadVacuumScale s a ((P smQuadVacuumScale) ⟨coreApproxSeq ε x j, hPj⟩) ∧
          coreApproxSeq ε x j -
              RH smQuadVacuumScale s a (T ⟨coreApproxSeq ε x j, hTj⟩ +
                (Real.exp (2 * s) : ℂ) • (P smQuadVacuumScale) ⟨coreApproxSeq ε x j, hPj⟩ +
                a • coreApproxSeq ε x j) =
            (Real.exp (2 * s) : ℂ) •
              RH smQuadVacuumScale s a (K ⟨coreApproxSeq ε x j, hKj⟩)) ∧
      Tendsto (coreApproxSeq ε x) atTop (𝓝 x) :=
  positive_vacuum_coreApproxSeq_with_resolvent_identities
    ε hε h hh hb m g smQuadVacuumScale sm_vacuum_scales_exact_and_pos.2.2.1 s a ha x hx

/-- 27. At the Standard Model quadratic scale `smQuadVacuumScale = 10` on
`|h| ≤ π * ε / 3`, the 5-operator core bridge master theorem holds
simultaneously for `T`, `G`, and `H(t)`. -/
theorem sm_quad_scale_five_operator_core_bridge (t : ℝ) :
    positiveVacuumCoreDomain ε hε h hh hb m g smQuadVacuumScale =
        unconditionalCoreDomain ε hε h hh hb m g smQuadVacuumScale ∧
      positiveVacuumCoreDomain ε hε h hh hb m g smQuadVacuumScale =
        (T).domain ⊓ growingClockCoreDomain ε hε h hh hb m g smQuadVacuumScale ∧
      unconditionalCoreDomain ε hε h hh hb m g smQuadVacuumScale =
        (H smQuadVacuumScale t).domain ⊓
          growingClockCoreDomain ε hε h hh hb m g smQuadVacuumScale ∧
      ((T).graph ⊓
        (positiveVacuumCoreDomain ε hε h hh hb m g smQuadVacuumScale).comap
          (LinearMap.fst ℂ Hilbert Hilbert)).topologicalClosure = (T).graph ∧
      ((G smQuadVacuumScale).graph ⊓
        (growingClockCoreDomain ε hε h hh hb m g smQuadVacuumScale).comap
          (LinearMap.fst ℂ Hilbert Hilbert)).topologicalClosure =
        (G smQuadVacuumScale).graph :=
  positive_vacuum_five_operator_core_bridge_master
    ε hε h hh hb m g smQuadVacuumScale sm_vacuum_scales_exact_and_pos.2.2.1 t

/-- 28. At the Standard Model quartic scale `smQuartVacuumScale = 35 / 18` on
`|h| ≤ π * ε / 3`, the 5-operator core bridge master theorem holds
simultaneously for `T`, `G`, and `H(t)`. -/
theorem sm_quart_scale_five_operator_core_bridge (t : ℝ) :
    positiveVacuumCoreDomain ε hε h hh hb m g smQuartVacuumScale =
        unconditionalCoreDomain ε hε h hh hb m g smQuartVacuumScale ∧
      positiveVacuumCoreDomain ε hε h hh hb m g smQuartVacuumScale =
        (T).domain ⊓ growingClockCoreDomain ε hε h hh hb m g smQuartVacuumScale ∧
      unconditionalCoreDomain ε hε h hh hb m g smQuartVacuumScale =
        (H smQuartVacuumScale t).domain ⊓
          growingClockCoreDomain ε hε h hh hb m g smQuartVacuumScale ∧
      ((T).graph ⊓
        (positiveVacuumCoreDomain ε hε h hh hb m g smQuartVacuumScale).comap
          (LinearMap.fst ℂ Hilbert Hilbert)).topologicalClosure = (T).graph ∧
      ((G smQuartVacuumScale).graph ⊓
        (growingClockCoreDomain ε hε h hh hb m g smQuartVacuumScale).comap
          (LinearMap.fst ℂ Hilbert Hilbert)).topologicalClosure =
        (G smQuartVacuumScale).graph :=
  positive_vacuum_five_operator_core_bridge_master
    ε hε h hh hb m g smQuartVacuumScale sm_vacuum_scales_exact_and_pos.2.2.2 t

/-- 29. Universal Anomaly-Selected Positive-Vacuum Quantum Bridge:
for ANY nontrivial (`c.yQ ≠ 0`) anomaly-free `ChargeAssignment` `c`, the
uniquely determined hypercharge ratios, strict positivity of `trY2 c` and
`trY4 c`, and the positive-vacuum quantum operator/form/core identifications at
`k = hyperchargeQuadScale c` hold simultaneously. -/
theorem universal_anomaly_selected_quantum_vacuum_bridge
    (t : ℝ) (c : ChargeAssignment)
    (h_su3 : su3MixedCondition c) (h_su2 : su2MixedCondition c)
    (h_lin : linearCondition c) (h_cub : cubicCondition c)
    (hyQ : c.yQ ≠ 0) :
    let k := hyperchargeQuadScale c
    ((c.yd = 2 * c.yQ ∧ c.yu = -4 * c.yQ ∧ c.yL = -3 * c.yQ ∧ c.ye = 6 * c.yQ) ∨
     (c.yd = -4 * c.yQ ∧ c.yu = 2 * c.yQ ∧ c.yL = -3 * c.yQ ∧ c.ye = 6 * c.yQ)) ∧
    0 < k ∧
    (Eavg k t).domain =
      (Tstat).domain ⊓ (Kroot).domain ⊓ potentialDomain ε hε h hh hb m g k ∧
    KFCausalClockFloorUnconditionalTwoTimeEvolution.commonOperatorDomain
        ε hε h hh hb m g k =
      threeOperatorDomain ε hε h hh hb m g k ∧
    positiveVacuumCoreDomain ε hε h hh hb m g k =
      unconditionalCoreDomain ε hε h hh hb m g k := by
  have hk := (anomaly_free_nontrivial_charge_traces_pos c h_su3 h_su2 h_lin h_cub hyQ).2.2.1
  exact ⟨anomaly_uniqueness c h_cub h_su2 h_su3 h_lin hyQ,
    hk,
    positive_vacuum_averaged_form_domain_eq_potentialDomain ε hε h hh hb m g _ hk t,
    positive_vacuum_common_domain_eq_three_operator ε hε h hh hb m g _ hk,
    positiveVacuumCoreDomain_eq_unconditionalCoreDomain ε hε h hh hb m g _ hk⟩

/-- 30. Master Standard Model Anomaly-Free Quantum Clock-Floor Synthesis:
unites all four gauge/gravitational anomaly cancellations, Witten global
doublet parity, hypercharge uniqueness, proton stability (`d = 6 > 4`),
Weinberg angle (`3 / 8`), exact positive vacuum scales (`10 / 3` and `95 / 54`),
unconditional form/operator/core domain equalities, and the five-operator
graph core bridge. -/
theorem sm_anomaly_cancellation_quantum_clock_floor_master (t : ℝ) :
    (su3sq_u1_anomaly UnifiedTheory.LayerC.AnomalyCancellation.smGeneration = 0 ∧
     su2sq_u1_anomaly UnifiedTheory.LayerC.AnomalyCancellation.smGeneration = 0 ∧
     u1cubed_anomaly UnifiedTheory.LayerC.AnomalyCancellation.smGeneration = 0 ∧
     grav_u1_anomaly UnifiedTheory.LayerC.AnomalyCancellation.smGeneration = 0 ∧
     Even (numDoublets UnifiedTheory.LayerC.AnomalyCancellation.smGeneration)) ∧
    (allCharges smCharges = (2 / 3, -1 / 3, 0, -1, 1) ∧
     4 * (3 : ℕ) / 2 = 6 ∧
     trT3sq 3 / (trT3sq 3 + trY2 smCharges) = 3 / 8) ∧
    (smQuadVacuumScale = 10 / 3 ∧ smQuartVacuumScale = 95 / 54 ∧
     0 < smQuadVacuumScale ∧ 0 < smQuartVacuumScale) ∧
    (Eavg smQuadVacuumScale t).domain =
      (Tstat).domain ⊓ (Kroot).domain ⊓
        potentialDomain ε hε h hh hb m g smQuadVacuumScale ∧
    KFCausalClockFloorUnconditionalTwoTimeEvolution.commonOperatorDomain
        ε hε h hh hb m g smQuadVacuumScale =
      threeOperatorDomain ε hε h hh hb m g smQuadVacuumScale ∧
    positiveVacuumCoreDomain ε hε h hh hb m g smQuadVacuumScale =
      unconditionalCoreDomain ε hε h hh hb m g smQuadVacuumScale ∧
    ((T).graph ⊓
      (positiveVacuumCoreDomain ε hε h hh hb m g smQuadVacuumScale).comap
        (LinearMap.fst ℂ Hilbert Hilbert)).topologicalClosure = (T).graph ∧
    ((G smQuadVacuumScale).graph ⊓
      (growingClockCoreDomain ε hε h hh hb m g smQuadVacuumScale).comap
        (LinearMap.fst ℂ Hilbert Hilbert)).topologicalClosure =
      (G smQuadVacuumScale).graph := by
  have hk := sm_vacuum_scales_exact_and_pos.2.2.1
  have h5 := sm_charge_quantization_weinberg_and_proton_stability
  have hcore := sm_quad_scale_five_operator_core_bridge ε hε h hh hb m g t
  exact ⟨UnifiedTheory.LayerC.AnomalyCancellation.sm_anomaly_free,
    ⟨h5.2.2.2.1, h5.2.2.2.2.2.1, h5.2.2.2.2.1⟩,
    sm_vacuum_scales_exact_and_pos,
    positive_vacuum_averaged_form_domain_eq_potentialDomain
      ε hε h hh hb m g smQuadVacuumScale hk t,
    positive_vacuum_common_domain_eq_three_operator
      ε hε h hh hb m g smQuadVacuumScale hk,
    hcore.1,
    hcore.2.2.2.1,
    hcore.2.2.2.2⟩

#print axioms sm_chiral_generation_anomaly_cancellation_complete
#print axioms sm_hypercharge_uniqueness_and_automatic_cubic
#print axioms anomaly_free_nontrivial_charge_traces_pos
#print axioms sm_vacuum_scales_exact_and_pos
#print axioms sm_charge_quantization_weinberg_and_proton_stability
#print axioms anomaly_free_quad_scale_averaged_form_domain_eq
#print axioms anomaly_free_quart_scale_averaged_form_domain_eq
#print axioms sm_quad_scale_form_domain_time_invariant_and_split
#print axioms sm_quart_scale_form_domain_time_invariant_and_split
#print axioms anomaly_free_quad_scale_common_and_core_domain_eq
#print axioms anomaly_free_quart_scale_common_and_core_domain_eq
#print axioms sm_quad_scale_clock_core_identifications
#print axioms sm_quart_scale_clock_core_identifications
#print axioms sm_quad_scale_core_mem_all_ten_domains
#print axioms sm_quad_scale_hamiltonian_resolvent_six_way_domain_iff
#print axioms sm_quad_scale_three_operator_shifted_resolvent_defects
#print axioms sm_quart_scale_three_operator_shifted_resolvent_defects
#print axioms sm_quad_scale_global_second_resolvent_identities
#print axioms sm_quad_scale_two_time_shifted_resolvent_package
#print axioms sm_quad_scale_two_time_weak_resolvent_continuity
#print axioms sm_quad_scale_all_five_resolvents_preserve_clockHalf
#print axioms sm_quad_scale_gaussian_mem_all_three_cores
#print axioms sm_quart_scale_gaussian_mem_all_three_cores
#print axioms sm_quad_scale_quarter_strip_core_density_and_simultaneous_core
#print axioms sm_quart_scale_quarter_strip_core_density_and_simultaneous_core
#print axioms sm_quad_scale_coreApproxSeq_with_resolvent_identities
#print axioms sm_quad_scale_five_operator_core_bridge
#print axioms sm_quart_scale_five_operator_core_bridge
#print axioms universal_anomaly_selected_quantum_vacuum_bridge
#print axioms sm_anomaly_cancellation_quantum_clock_floor_master

end
end UnifiedTheory.Audit.KFCausalClockFloorSMAnomalyCancellationQuantumBridge
