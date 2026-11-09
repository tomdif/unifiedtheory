/- The actual full frozen groups converge to the actual growing group,
uniformly on every bounded interval for each physical Hilbert input.
No static operator is applied to a growing-only form state. -/
import UnifiedTheory.Audit.KFCausalClockFloorResolventFlowData
import UnifiedTheory.Audit.KFCausalStrongResolventFlowLimit

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorFrozenGrowingLimit
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorResolventFlowData

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "U" => frozenGroup ε hε h hne hb m g k
local notation "V" => growingGroup ε hε h hne hb m g k
local notation "R" => KFCausalClockFloorFastResolvent.resolvent ε hε h hne hb m g k
local notation "S" => KFCausalClockFloorFastResolvent.limitResolvent ε hε h hne hb m g k
local notation "c" => (-Complex.I*((1/(2*h):ℝ):ℂ))

theorem uniform_limit (f : Hilbert) (L : ℝ) (hL : 0 ≤ L) :
    TendstoUniformlyOn (fun u t => (U u).action t f) (fun t => (V).action t f)
      atTop (Set.Icc (-L) L) := by
  apply KFCausalStrongResolventFlowLimit.uniform_limit U V R S c atTop 2 (by norm_num)
    _ (KFCausalClockFloorGrowingResolventLimit.physical_strong_limit ε hε h hne hb m g k) _
    (growing_resolvent_derivative ε hε h hne hb m g k)
    (KFCausalClockFloorGrowingEvolution.evolution_commutes_resolvent ε hε h hne hb m g k)
    (limit_resolvent_dense ε hε h hne hb m g k) f L hL
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with u hu
    exact resolvent_difference_bound ε hε h hne hb m g k u hu
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with u hu
    exact frozen_resolvent_derivative ε hε h hne hb m g k u hu

theorem strong_limit (f : Hilbert) (t : ℝ) :
    Tendsto (fun u => (U u).action t f) atTop (𝓝 ((V).action t f)) :=
  (uniform_limit ε hε h hne hb m g k f |t| (abs_nonneg t)).tendsto_at
    (abs_le.mp (le_refl |t|))

#print axioms uniform_limit
#print axioms strong_limit
end
end UnifiedTheory.Audit.KFCausalClockFloorFrozenGrowingLimit
