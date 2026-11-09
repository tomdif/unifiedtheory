/- Strong convergence of the full positive-cutoff family is uniform on
compact final-time sets, for each fixed initial time and L2 initial state. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedJointTimeLimit
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedUniformConvergence
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosidaDynamics
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRealConvergence
open UnifiedTheory.Audit.KFCausalClockFloorAveragedJointTimeLimit

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0)
  (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum : ℝ)
local notation "A" => approximation ε hε hbar hh hbound mass2 quartic vacuum
local notation "U" => evolution ε hε hbar hh hbound mass2 quartic vacuum

theorem dynamics_locally_uniform_limit (s : ℝ) (f : Hilbert) :
    TendstoLocallyUniformly (fun a t => A a s t f) (fun t => U s t f) atTop := by
  apply tendstoLocallyUniformly_iff_forall_tendsto.mpr
  intro t
  apply tendsto_uniformity_iff_dist_tendsto_zero.mpr
  have hg := ((evolution_strong_continuous ε hε hbar hh hbound mass2 quartic vacuum s f).tendsto t).comp
    (show Tendsto (fun p : ℝ × ℝ => p.2) (atTop ×ˢ 𝓝 t) (𝓝 t) from tendsto_snd)
  have hf := dynamics_joint_time_limit ε hε hbar hh hbound mass2 quartic vacuum s t f
  simpa only [dist_self] using hg.dist hf

theorem dynamics_uniform_on_compact (s : ℝ) (f : Hilbert) (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun a t => A a s t f) (fun t => U s t f) atTop K :=
  (tendstoLocallyUniformly_iff_forall_isCompact.mp
    (dynamics_locally_uniform_limit ε hε hbar hh hbound mass2 quartic vacuum s f)) K hK

/-- One cutoff threshold controls every final time in the compact set. -/
theorem dynamics_uniform_eventually_close (s : ℝ) (f : Hilbert) (K : Set ℝ)
    (hK : IsCompact K) (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : ℝ, 0 < B ∧ ∀ a : ℝ, B ≤ a → ∀ ha : 0 < a, ∀ t ∈ K,
      ‖dynamics ε hε hbar hh hbound mass2 quartic vacuum a ha s t f-U s t f‖ < δ := by
  have he := Metric.tendstoUniformlyOn_iff.mp
    (dynamics_uniform_on_compact ε hε hbar hh hbound mass2 quartic vacuum s f K hK) δ hδ
  obtain ⟨B,hB⟩ := eventually_atTop.mp he
  refine ⟨max B 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro a hBa ha t ht
  have hl := hB a ((le_max_left B 1).trans hBa) t ht
  simpa only [approximation_of_pos ε hε hbar hh hbound mass2 quartic vacuum a ha,
    dist_eq_norm,norm_sub_rev] using hl

#print axioms dynamics_locally_uniform_limit
#print axioms dynamics_uniform_on_compact
#print axioms dynamics_uniform_eventually_close

end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedUniformConvergence
