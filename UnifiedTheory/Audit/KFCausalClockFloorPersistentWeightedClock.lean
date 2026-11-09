/- A positive actual clock residual forces a uniformly nonzero analytic
clock-weighted input at all forward physical times. No moment assumption. -/
import UnifiedTheory.Audit.KFCausalClockFloorWeightedClockControl
import UnifiedTheory.Audit.KFCausalClockFloorLeftTightness
import UnifiedTheory.Audit.KFCausalClockFloorResidualDefect

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorPersistentWeightedClock
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorWeightedClockControl (weighted)
open KFCausalClockFloorDefectOperator (defectOperator)
open KFCausalClockFloorDefectLocalization (lowProjection)
open KFCausalClockFloorCanonicalDefect (defect)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "E" => KFCausalClockFloorAveragedEvolution.evolution ε hε h hne hb m g k
local notation "rho" => KFCausalClockFloorResidualDefect.residual ε hε h hne hb m g k

theorem persistent_weight (s : ℝ) (f : Hilbert) (hp : 0 < rho s f) :
    ∃ η : ℝ, 0 < η ∧ ∀ t, s ≤ t → η ≤ ‖weighted ε hε (E s t f)‖ := by
  let r := rho s f
  have hr : 0 < r := hp
  obtain ⟨L,hL⟩ := KFCausalClockFloorLeftTightness.uniform_left_tail
    ε hε h hne hb m g k s f (r^2/16) (by positivity)
  have hd : Tendsto (fun S => defect ε S*‖f‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using (KFCausalClockFloorDefectLimits.defect_large_clock_limit ε hε.le).mul_const ‖f‖
  obtain ⟨S,hS,hLS⟩ := ((hd.eventually (gt_mem_nhds (show 0 < r/4 by positivity))).and
    (eventually_ge_atTop L)).exists
  obtain ⟨C,hC,hcontrol⟩ := KFCausalClockFloorWeightedClockControl.exists_defect_control ε hε L S hLS
  refine ⟨r/(2*C),by positivity,fun t ht => ?_⟩
  have hl : ‖lowProjection L (E s t f)‖ < r/4 := by
    have hs := hL t ht
    nlinarith [norm_nonneg (lowProjection L (E s t f))]
  have hc := hcontrol (E s t f)
  rw [(E s t).norm_map] at hc
  have hbnd := (KFCausalClockFloorResidualDefect.residual_bounds ε hε h hne hb m g k s t f).2
  change r ≤ ‖defectOperator ε hε (E s t f)‖ at hbnd
  apply (div_le_iff₀ (by positivity : 0 < 2*C)).mpr
  nlinarith only [hc,hbnd,hl,hS]

#print axioms persistent_weight
end
end UnifiedTheory.Audit.KFCausalClockFloorPersistentWeightedClock
