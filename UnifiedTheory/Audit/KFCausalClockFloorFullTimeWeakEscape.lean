/- Full-time weak escape of each actual finite-energy zero-charge quantum
trajectory. A fixed-overlap revival would consume a nonvanishing tail
dissipation budget. This still does not prove decay of clock error. -/
import UnifiedTheory.Audit.KFCausalGraphDetectionModulus
import UnifiedTheory.Audit.KFCausalExponentialNoSpikes
import UnifiedTheory.Audit.KFCausalClockFloorExponentialVariation
import UnifiedTheory.Audit.KFCausalClockFloorDissipationTail
import UnifiedTheory.Audit.KFCausalClockFloorQuantumWeakEscape

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorFullTimeWeakEscape
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolutionProjection
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorVacuumObservation
open UnifiedTheory.Audit.KFCausalClockFloorDriftDetection
open UnifiedTheory.Audit.KFCausalClockFloorQuantumWeakEscape
open UnifiedTheory.Audit.KFCausalClockFloorExponentialVariation
open UnifiedTheory.Audit.KFCausalClockFloorDefectDissipationBudget (dissipation dissipation_continuous)
open UnifiedTheory.Audit.KFCausalStandingChargeOperator (zeroSector)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "J" => embedding ε hε h hne hb m g k 0
local notation "F" => formFlow ε hε h hne hb m g k
local notation "U" => evolution ε hε h hne hb m g k
local notation "E" => timeEnergy ε hε h hne hb m g k
local notation "v" => vacuum ε hε h hne hb m g k 0
local notation "B" => KFCausalClockFloorDefectTransportOperator.driftOperator ε hε

theorem probe_detection (hk : 0 < k) (s : ℝ) (w : V)
    (hw : J w ∈ zeroSector h hne) (z : Hilbert) (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, s ≤ t → η ≤ ‖inner ℂ (U s t (J w)) z‖ →
      Real.exp (2*t)*δ ≤ dissipation ε hε h hne hb m g k s t w := by
  let c : ℂ := energyWeight m g k 0 7
  have hc : c ≠ 0 := KFCausalClockFloorVacuumOutputFaithful.vacuum_weight_ne_zero m g k 0 hk
  let C := Real.exp (-2*s)*E s w+1
  have hC : 0 ≤ C := add_nonneg
    (mul_nonneg (Real.exp_pos _).le (timeEnergy_nonneg ε hε h hne hb m g k s w)) zero_le_one
  have hbound (t : ℝ) (ht : s ≤ t) : ‖v (F s t w)‖ ≤ C := by
    have hv := vacuum_square_bound ε hε h hne hb m g k s t ht w
    dsimp [C]
    nlinarith [sq_nonneg (‖v (F s t w)‖-1)]
  have hg (t : ℝ) : (c • U s t (J w),v (F s t w)) ∈
      (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h).graph := by
    have he := evolution_embedding ε hε h hne hb m g k s t w
    have hv := vacuum_graph ε hε h hne hb m g k 0 (F s t w)
      (formFlow_zero_sector ε hε h hne hb m g k s t w hw)
    exact (congrArg (fun f : Hilbert => (c • f,v (F s t w)) ∈
      (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h).graph) he).mpr hv
  obtain ⟨δ,hδ,hd⟩ := KFCausalGraphDetectionModulus.detector_lower
    (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h)
    (KFCausalClockFloorBoundedInverse.orderedExponential_closed ε hε h)
    (KFCausalClockFloorVacuumOutputFaithful.ordered_graph_zero ε hε h)
    B (drift_injective ε hε) (‖c‖*‖J w‖) C (by positivity) hC z (‖c‖*η)
    (mul_pos (norm_pos_iff.mpr hc) hη)
  refine ⟨ε*δ^2,mul_pos hε (sq_pos_of_pos hδ),?_⟩
  intro t ht hqt
  have hx : ‖c • U s t (J w)‖ ≤ ‖c‖*‖J w‖ :=
    (norm_smul c (U s t (J w))).le.trans
      (congrArg (fun r : ℝ => ‖c‖*r) (evolution_norm ε hε h hne hb m g k s t (J w))).le
  have hi : ‖c‖*η ≤ ‖inner ℂ (c • U s t (J w)) z‖ := by
    rw [inner_smul_left,norm_mul,Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left hqt (norm_nonneg c)
  have hn : δ ≤ ‖B (v (F s t w))‖ :=
    hd (c • U s t (J w)) (v (F s t w)) hx (hbound t ht) (hg t) hi
  have hs := pow_le_pow_left₀ hδ.le hn 2
  have hb' : ‖B (v (F s t w))‖^2 ≤ detection ε hε (v (F s t w))/ε := by
    simpa only [one_div_mul_eq_div] using drift_norm_sq_bound ε hε (v (F s t w))
  have hd' : ε*δ^2 ≤ detection ε hε (v (F s t w)) := by
    have hmul := (le_div_iff₀ hε).mp hb'
    have hsq := mul_le_mul_of_nonneg_left hs hε.le
    linarith
  exact (mul_le_mul_of_nonneg_left hd' (Real.exp_pos _).le).trans
    (weighted_detection_bound ε hε h hne hb m g k s t w hw)

theorem form_test_decay (hk : 0 < k) (s : ℝ) (w z : V)
    (hw : J w ∈ zeroSector h hne) :
    Tendsto (fun t => inner ℂ (U s t (J w)) (J z)) atTop (𝓝 0) :=
  KFCausalExponentialNoSpikes.tendsto_zero
    (fun t => inner ℂ (U s t (J w)) (J z))
    (fun t => dissipation ε hε h hne hb m g k s t w)
    (dissipation_continuous ε hε h hne hb m g k s w) s
    (variationConstant ε hε h hne hb m g k s w z)
    (variationConstant_nonnegative ε hε h hne hb m g k s w z)
    (fun a b ha hab => pairing_variation ε hε h hne hb m g k s a b ha hab w z)
    (probe_detection ε hε h hne hb m g k hk s w hw (J z))
    (KFCausalClockFloorDissipationTail.tail_budget ε hε h hne hb m g k s w)

theorem weak_decay (hk : 0 < k) (s : ℝ) (w : V)
    (hw : J w ∈ zeroSector h hne) (z : Hilbert) :
    Tendsto (fun t => inner ℂ (U s t (J w)) z) atTop (𝓝 0) := by
  apply tendsto_of_seq_tendsto
  intro τ hτ
  have hd := KFCausalWeakEmbeddingLimit.weak_of_dense_tests J
    (KFCausalClockFloorAveragedFormGeometry.embedding_dense ε hε h hne hb m g k 0)
    (fun n => U s (τ n) (J w)) 0 ‖J w‖ (norm_nonneg _)
    (fun n => (evolution_norm ε hε h hne hb m g k s (τ n) (J w)).le)
    (fun y => by simpa only [inner_zero_left] using
      (form_test_decay ε hε h hne hb m g k hk s w y hw).comp hτ) z
  simpa only [inner_zero_left,Function.comp_def] using hd

theorem finite_probe_decay (hk : 0 < k) (s : ℝ) (w : V)
    (hw : J w ∈ zeroSector h hne) (N : ℕ) (z : Fin N → Hilbert) :
    Tendsto (fun t => ∑ i : Fin N, ‖inner ℂ (U s t (J w)) (z i)‖^2) atTop (𝓝 0) := by
  have hi (i : Fin N) := ((weak_decay ε hε h hne hb m g k hk s w hw (z i)).norm).pow 2
  simpa only [norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),Finset.sum_const_zero] using
    tendsto_finset_sum Finset.univ (fun i _ => hi i)

#print axioms probe_detection
#print axioms form_test_decay
#print axioms weak_decay
#print axioms finite_probe_decay
end
end UnifiedTheory.Audit.KFCausalClockFloorFullTimeWeakEscape
