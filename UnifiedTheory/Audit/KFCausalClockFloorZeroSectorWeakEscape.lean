/- Full-time weak escape extends from finite-energy data to every
physical zero-charge state by the proved sector density and unitarity. -/
import UnifiedTheory.Audit.KFCausalClockFloorFullTimeWeakEscape

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorZeroSectorWeakEscape
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalStandingChargeOperator (zeroSector)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "J" => embedding ε hε h hne hb m g k 0
local notation "U" => evolution ε hε h hne hb m g k
local notation "Z" => zeroSector h hne
local notation "D" => KFCausalClockFloorAveragedHamiltonian.formData ε hε h hne hb m g k 0

theorem weak_decay (hk : 0 < k) (s : ℝ) (f : Hilbert) (hf : f ∈ Z) (z : Hilbert) :
    Tendsto (fun t => inner ℂ (U s t f) z) atTop (𝓝 0) := by
  have hd : (Z ⊓ (D).operator.domain).topologicalClosure = Z :=
    KFCausalClockFloorAveragedDensity.zero_energy_domain_closure ε h hε hne hb m g k 0
  have hcl : f ∈ closure ((Z ⊓ (D).operator.domain) : Set Hilbert) :=
    (congrArg (fun S : Submodule ℂ Hilbert => f ∈ S) hd).mpr hf
  apply Metric.tendsto_nhds.mpr
  intro η hη
  have hp : 0 < 2*(‖z‖+1) := by positivity
  obtain ⟨f₀,hg,hfg⟩ := Metric.mem_closure_iff.mp hcl (η/(2*(‖z‖+1))) (div_pos hη hp)
  have herr : ‖f-f₀‖*‖z‖ < η/2 := by
    have hh : ‖f-f₀‖ < η/(2*(‖z‖+1)) := by simpa only [dist_eq_norm] using hfg
    have hb' := (lt_div_iff₀ hp).mp hh
    nlinarith [norm_nonneg (f-f₀)]
  let w := KFCausalClosedGraphForm.graphVector D ⟨f₀,hg.2⟩
  have hj : J w = f₀ := KFCausalClosedGraphForm.graphVector_embedding D ⟨f₀,hg.2⟩
  have hw : J w ∈ Z := (congrArg (fun x : Hilbert => x ∈ Z) hj).mpr hg.1
  have hl := KFCausalClockFloorFullTimeWeakEscape.weak_decay ε hε h hne hb m g k hk s w hw z
  have hl' : Tendsto (fun t => inner ℂ (U s t f₀) z) atTop (𝓝 0) :=
    (congrArg (fun x : Hilbert => Tendsto (fun t => inner ℂ (U s t x) z) atTop (𝓝 0)) hj).mp hl
  filter_upwards [Metric.tendsto_nhds.mp hl' (η/2) (by positivity)] with t ht
  have hi : ‖inner ℂ (U s t f) z-inner ℂ (U s t f₀) z‖ < η/2 := by
    rw [← inner_sub_left,← map_sub]
    exact (norm_inner_le_norm (𝕜 := ℂ) _ z).trans_lt (by simpa only [evolution_norm] using herr)
  have ht' : ‖inner ℂ (U s t f₀) z‖ < η/2 := by simpa only [dist_zero_right] using ht
  have ha := norm_add_le (inner ℂ (U s t f) z-inner ℂ (U s t f₀) z) (inner ℂ (U s t f₀) z)
  rw [sub_add_cancel] at ha
  rw [dist_zero_right]
  linarith

theorem finite_probe_decay (hk : 0 < k) (s : ℝ) (f : Hilbert) (hf : f ∈ Z)
    (N : ℕ) (z : Fin N → Hilbert) :
    Tendsto (fun t => ∑ i : Fin N, ‖inner ℂ (U s t f) (z i)‖^2) atTop (𝓝 0) := by
  have hi (i : Fin N) := ((weak_decay ε hε h hne hb m g k hk s f hf (z i)).norm).pow 2
  simpa only [norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),Finset.sum_const_zero] using
    tendsto_finset_sum Finset.univ (fun i _ => hi i)

#print axioms weak_decay
#print axioms finite_probe_decay
end
end UnifiedTheory.Audit.KFCausalClockFloorZeroSectorWeakEscape
