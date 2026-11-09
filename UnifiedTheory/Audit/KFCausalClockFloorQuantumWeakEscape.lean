/- A single actual zero-charge quantum trajectory has arbitrarily late
times at which it converges weakly to zero. Energy controls the unscaled
vacuum graph, and the dissipation budget supplies vanishing detection.
This does not identify clock-position escape or a zero defect limit. -/
import UnifiedTheory.Audit.KFCausalClockFloorVacuumObservation
import UnifiedTheory.Audit.KFCausalWeightedGraphWeakDecay
import UnifiedTheory.Audit.KFCausalClockFloorDefectDissipationBudget
import UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolutionProjection

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorQuantumWeakEscape
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolutionProjection
open UnifiedTheory.Audit.KFCausalClockFloorVacuumObservation
open UnifiedTheory.Audit.KFCausalClockFloorDriftDetection
open UnifiedTheory.Audit.KFCausalClockFloorDefectDissipationBudget (dissipation arbitrarily_late_small)
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

theorem vacuum_square_bound (s t : ℝ) (hst : s ≤ t) (w : V) :
    ‖v (F s t w)‖^2 ≤ Real.exp (-2*s)*E s w := by
  have he := formFlow_energy_bound ε hε h hne hb m g k s t w
  rw [abs_of_nonneg (sub_nonneg.mpr hst)] at he
  have hx : Real.exp (2*(t-s)) = Real.exp (2*t)*Real.exp (-2*s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hx] at he
  have hv := pow_le_pow_left₀ (norm_nonneg _)
    (vacuum_norm_bound ε hε h hne hb m g k (F s t w)) 2
  have hg : Real.exp (2*t)*‖growingPart ε hε h hne hb m g k (F s t w)‖^2 ≤
      Real.exp (2*t)*(Real.exp (-2*s)*E s w) := by
    have hl : Real.exp (2*t)*‖growingPart ε hε h hne hb m g k (F s t w)‖^2 ≤ E t (F s t w) := by
      exact le_add_of_nonneg_left (sq_nonneg _)
    simpa only [mul_assoc] using hl.trans he
  exact hv.trans ((mul_le_mul_iff_right₀ (Real.exp_pos (2*t))).mp hg)

theorem weighted_detection_bound (s t : ℝ) (w : V) (hw : J w ∈ zeroSector h hne) :
    Real.exp (2*t)*detection ε hε (v (F s t w)) ≤
      dissipation ε hε h hne hb m g k s t w := by
  let y := F s t w
  let u := formTransfer ε hε h hne hb m g k 0 t y
  have hz := formFlow_zero_sector ε hε h hne hb m g k s t w hw
  have hj := transfer_embedding ε hε h hne hb m g k 0 t y
  have ht : embedding ε hε h hne hb m g k t u ∈ zeroSector h hne :=
    (congrArg (fun f : Hilbert => f ∈ zeroSector h hne) hj).mpr hz
  have hd : detection ε hε (vacuum ε hε h hne hb m g k t u) ≤
      dissipation ε hε h hne hb m g k s t w :=
    vacuum_detection_bound ε hε h hne hb m g k t u ht
  have he := vacuum_scaling ε hε h hne hb m g k t y
  have hc : ‖(Real.exp t:ℂ)‖^2 = Real.exp (2*t) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos t),← Real.exp_nat_mul]
    norm_num
  have hs : detection ε hε (vacuum ε hε h hne hb m g k t u) =
      Real.exp (2*t)*detection ε hε (v y) :=
    (congrArg (detection ε hε) he).trans
      ((detection_smul ε hε (Real.exp t:ℂ) (v y)).trans
        (congrArg (fun c : ℝ => c*detection ε hε (v y)) hc))
  exact hs.symm.le.trans hd

theorem late_detected_sequence (s : ℝ) (w : V) (hw : J w ∈ zeroSector h hne) :
    ∃ τ : ℕ → ℝ, Tendsto τ atTop atTop ∧ (∀ n, s ≤ τ n) ∧
      Tendsto (fun n => B (v (F s (τ n) w))) atTop (𝓝 0) := by
  have hex (n : ℕ) := arbitrarily_late_small ε hε h hne hb m g k s
    (max s (n:ℝ)) 1 (by norm_num) w
  choose τ hτ hsmall using hex
  have hnat (n : ℕ) : (n:ℝ) ≤ τ n := (le_max_right _ _).trans (hτ n)
  have ht : Tendsto τ atTop atTop := tendsto_atTop_mono hnat tendsto_natCast_atTop_atTop
  refine ⟨τ,ht,fun n => (le_max_left _ _).trans (hτ n),?_⟩
  apply drift_tendsto_zero ε hε
  have hd (n : ℕ) : detection ε hε (v (F s (τ n) w)) ≤ Real.exp (-2*τ n) := by
    have hh := (weighted_detection_bound ε hε h hne hb m g k s (τ n) w hw).trans (hsmall n).le
    have he : Real.exp (2*τ n)*Real.exp (-2*τ n) = 1 := by
      rw [← Real.exp_add,show 2*τ n+ -2*τ n = 0 by ring,Real.exp_zero]
    exact (mul_le_mul_iff_right₀ (Real.exp_pos (2*τ n))).mp (hh.trans_eq he.symm)
  apply squeeze_zero (fun n => detection_nonnegative ε hε (v (F s (τ n) w))) hd
  exact Real.tendsto_exp_atBot.comp (ht.const_mul_atTop_of_neg (by norm_num : (-2:ℝ) < 0))

theorem exists_weak_escape (hk : 0 < k) (s : ℝ) (w : V) (hw : J w ∈ zeroSector h hne) :
    ∃ τ : ℕ → ℝ, Tendsto τ atTop atTop ∧ (∀ n, s ≤ τ n) ∧
      ∀ z : Hilbert, Tendsto (fun n => inner ℂ (U s (τ n) (J w)) z) atTop (𝓝 0) := by
  obtain ⟨τ,hτ,hs,hdet⟩ := late_detected_sequence ε hε h hne hb m g k s w hw
  let c : ℂ := energyWeight m g k 0 7
  have hc : c ≠ 0 := KFCausalClockFloorVacuumOutputFaithful.vacuum_weight_ne_zero m g k 0 hk
  let C := Real.exp (-2*s)*E s w+1
  have hC : 0 ≤ C := add_nonneg
    (mul_nonneg (Real.exp_pos _).le (timeEnergy_nonneg ε hε h hne hb m g k s w)) zero_le_one
  have hbound (n : ℕ) : ‖v (F s (τ n) w)‖ ≤ C := by
    have hb' := vacuum_square_bound ε hε h hne hb m g k s (τ n) (hs n) w
    have hE := timeEnergy_nonneg ε hε h hne hb m g k s w
    dsimp [C]
    nlinarith [sq_nonneg (‖v (F s (τ n) w)‖-1),Real.exp_pos (-2*s)]
  have hg (n : ℕ) : (c • U s (τ n) (J w),v (F s (τ n) w)) ∈
      (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h).graph := by
    rw [evolution_embedding]
    exact vacuum_graph ε hε h hne hb m g k 0 (F s (τ n) w)
      (formFlow_zero_sector ε hε h hne hb m g k s (τ n) w hw)
  have hweak := KFCausalWeightedGraphWeakDecay.weak_zero
    (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h)
    (KFCausalClockFloorBoundedInverse.orderedExponential_closed ε hε h)
    (KFCausalClockFloorVacuumOutputFaithful.ordered_graph_zero ε hε h)
    B (drift_injective ε hε) (fun n => c • U s (τ n) (J w)) (fun n => v (F s (τ n) w))
    (‖c‖*‖J w‖) C (by positivity) hC
    (fun n => by rw [norm_smul,evolution_norm]) hbound hg hdet
  refine ⟨τ,hτ,hs,?_⟩
  have hw' : ∀ z, Tendsto (fun n => inner ℂ (c • U s (τ n) (J w)) z) atTop
      (𝓝 (inner ℂ (0:Hilbert) z)) := by simpa only [inner_zero_left] using hweak
  intro z
  have hm := KFCausalWeakLimitTransport.weak_map
    (c⁻¹ • ContinuousLinearMap.id ℂ Hilbert) hw' z
  simpa only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,
    smul_smul,inv_mul_cancel₀ hc,one_smul,smul_zero,inner_zero_left] using hm

theorem exists_finite_probe_escape (hk : 0 < k) (s : ℝ) (w : V)
    (hw : J w ∈ zeroSector h hne) :
    ∃ τ : ℕ → ℝ, Tendsto τ atTop atTop ∧ (∀ n, s ≤ τ n) ∧
      ∀ (N : ℕ) (z : Fin N → Hilbert), Tendsto
        (fun n => ∑ i : Fin N, ‖inner ℂ (U s (τ n) (J w)) (z i)‖^2) atTop (𝓝 0) := by
  obtain ⟨τ,ht,hs,hweak⟩ := exists_weak_escape ε hε h hne hb m g k hk s w hw
  refine ⟨τ,ht,hs,?_⟩
  intro N z
  have hi (i : Fin N) := ((hweak (z i)).norm).pow 2
  simpa only [norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),Finset.sum_const_zero] using
    tendsto_finset_sum Finset.univ (fun i _ => hi i)

#print axioms vacuum_square_bound
#print axioms weighted_detection_bound
#print axioms late_detected_sequence
#print axioms exists_weak_escape
#print axioms exists_finite_probe_escape
end
end UnifiedTheory.Audit.KFCausalClockFloorQuantumWeakEscape
