/- The actual growing Hamiltonian is reduced by the zero-charge projection.
Its inverse commutation is obtained from the proved strong limit of the
actual rescaled full-Hamiltonian resolvents. This does not assert that the
nonautonomous evolution preserves the growing operator domain. -/
import UnifiedTheory.Audit.KFCausalClockFloorGrowingResolventLimit
import UnifiedTheory.Audit.KFCausalClockFloorAveragedDynamicsProjection

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGrowingProjection
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalStandingChargeOperator
open KFCausalClockFloorFastResolvent
open KFCausalClockFloorFastResolventIdentification

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2 * Real.pi * ε / 3) (m g k : ℝ)
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hb m g k
local notation "R" => limitResolvent ε hε h hh hb m g k
local notation "P" => zeroProjection h hh
local notation "Z" => zeroSector h hh

theorem fast_resolvent_zeroProjection (u : ℝ) (hu : 0 < u) (f : Hilbert) :
    resolvent ε hε h hh hb m g k u (P f) = P (resolvent ε hε h hh hb m g k u f) := by
  change u • KFCausalClockFloorAveragedShiftedResolvent.shiftedResolvent
      ε hε h hh hb m g k u (KFCausalClockFloorFastTimeEnergy.physicalTime u) (P f) =
    P (u • KFCausalClockFloorAveragedShiftedResolvent.shiftedResolvent
      ε hε h hh hb m g k u (KFCausalClockFloorFastTimeEnergy.physicalTime u) f)
  rw [KFCausalClockFloorAveragedDynamicsProjection.shiftedResolvent_zeroProjection
    ε hε h hh hb m g k u hu]
  exact ((P).map_smul_of_tower u _).symm

theorem limit_resolvent_zeroProjection (f : Hilbert) : R (P f) = P (R f) := by
  have he : (fun u => resolvent ε hε h hh hb m g k u (P f)) =ᶠ[atTop]
      (fun u => P (resolvent ε hε h hh hb m g k u f)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    exact fast_resolvent_zeroProjection ε hε h hh hb m g k u hu f
  exact tendsto_nhds_unique
    (KFCausalClockFloorGrowingResolventLimit.physical_strong_limit ε hε h hh hb m g k (P f))
    ((((P).continuous.tendsto (R f)).comp
      (KFCausalClockFloorGrowingResolventLimit.physical_strong_limit ε hε h hh hb m g k f)).congr' he.symm)

theorem limit_resolvent_zero_sector (f : Hilbert) (hf : f ∈ Z) : R f ∈ Z := by
  have he : R f = P (R f) := by
    calc
      R f = R (P f) := congrArg R (zeroProjection_fixes h hh f hf).symm
      _ = P (R f) := limit_resolvent_zeroProjection ε hε h hh hb m g k f
  exact he ▸ zeroProjection_mem h hh (R f)

theorem zeroProjection_growing_graph (x : (G).domain) :
    (P (x : Hilbert), P (G x)) ∈ (G).graph := by
  let z := limitPoint ε hε h hh hb m g k (P (G x + (x : Hilbert)))
  have hx : (z : Hilbert) = P (x : Hilbert) := by
    change R (P (G x + (x : Hilbert))) = _
    rw [limit_resolvent_zeroProjection, limit_left_inverse]
  have hz : G z = P (G x) := by
    have hr := limit_right_inverse ε hε h hh hb m g k (P (G x + (x : Hilbert)))
    change G z + (z : Hilbert) = P (G x + (x : Hilbert)) at hr
    rw [hx, map_add] at hr
    exact add_right_cancel hr
  have hg := (G).mem_graph z
  rw [hx, hz] at hg
  exact hg

theorem zeroProjection_mem_growing_domain (x : (G).domain) :
    P (x : Hilbert) ∈ (G).domain :=
  LinearPMap.mem_domain_of_mem_graph (zeroProjection_growing_graph ε hε h hh hb m g k x)

theorem growing_zeroProjection (x : (G).domain) :
    G ⟨P (x : Hilbert), zeroProjection_mem_growing_domain ε hε h hh hb m g k x⟩ = P (G x) :=
  (G).mem_graph_snd_inj
    ((G).mem_graph ⟨P (x : Hilbert), zeroProjection_mem_growing_domain ε hε h hh hb m g k x⟩)
    (zeroProjection_growing_graph ε hε h hh hb m g k x) rfl

theorem growing_zero_sector (x : (G).domain) (hx : (x : Hilbert) ∈ Z) : G x ∈ Z := by
  have hg := zeroProjection_growing_graph ε hε h hh hb m g k x
  have he := (G).mem_graph_snd_inj hg ((G).mem_graph x) (zeroProjection_fixes h hh _ hx)
  exact (congrArg (fun f : Hilbert => f ∈ Z) he).mp (zeroProjection_mem h hh _)

#print axioms fast_resolvent_zeroProjection
#print axioms limit_resolvent_zeroProjection
#print axioms limit_resolvent_zero_sector
#print axioms zeroProjection_growing_graph
#print axioms zeroProjection_mem_growing_domain
#print axioms growing_zeroProjection
#print axioms growing_zero_sector
end
end UnifiedTheory.Audit.KFCausalClockFloorGrowingProjection
