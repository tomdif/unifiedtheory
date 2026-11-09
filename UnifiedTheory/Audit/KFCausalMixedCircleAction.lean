/- The normalized standing-wave rotations give a strongly continuous,
2*pi-periodic unitary group on the full mixed-coordinate L2 space. -/
import UnifiedTheory.Audit.KFCausalNormalizedChargeFlow
import UnifiedTheory.Audit.KFCausalMeasureUnitaryPullback
import UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalMixedCircleAction
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalPairedRotation
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalMeasureUnitaryPullback
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage

def action (c : ℝ) (hc : c ≠ 0) (θ : ℝ) : JointHilbert 2 4 ≃ₗᵢ[ℂ] JointHilbert 2 4 :=
  unitaryPullback (flowEquiv c hc θ) (flow_preserves_volume c hc θ)

theorem action_coe (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (f : JointHilbert 2 4) :
    action c hc θ f =ᵐ[volume] f ∘ flowEquiv c hc θ :=
  unitaryPullback_coe _ _ _

theorem action_zero (c : ℝ) (hc : c ≠ 0) (f : JointHilbert 2 4) : action c hc 0 f = f := by
  apply Lp.ext
  filter_upwards [action_coe c hc 0 f] with x hx
  simpa only [Function.comp_apply, flow_zero] using hx

theorem action_compose (c : ℝ) (hc : c ≠ 0) (θ φ : ℝ) (f : JointHilbert 2 4) :
    action c hc φ (action c hc θ f) = action c hc (θ+φ) f := by
  apply Lp.ext
  filter_upwards [action_coe c hc φ (action c hc θ f),
    (flow_preserves_volume c hc φ).quasiMeasurePreserving.ae (action_coe c hc θ f),
    action_coe c hc (θ+φ) f] with x hx hθ hsum
  simp only [Function.comp_apply] at hx hθ hsum
  rw [flow_compose] at hθ
  exact hx.trans (hθ.trans hsum.symm)

theorem action_period (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (f : JointHilbert 2 4) :
    action c hc (θ+2*Real.pi) f = action c hc θ f := by
  apply Lp.ext
  filter_upwards [action_coe c hc (θ+2*Real.pi) f, action_coe c hc θ f] with x hx hy
  simp only [Function.comp_apply, flow_period] at hx hy
  exact hx.trans hy.symm

theorem action_full_period (c : ℝ) (hc : c ≠ 0) (f : JointHilbert 2 4) :
    action c hc (2*Real.pi) f = f := by
  simpa only [zero_add, action_zero] using action_period c hc 0 f

def continuousFlow (c : ℝ) (hc : c ≠ 0) : C(ℝ,C(Space,Space)) :=
  ContinuousMap.curry ⟨fun p : ℝ × Space => flowEquiv c hc p.1 p.2, flow_continuous c hc⟩

theorem continuous_flow_family (c : ℝ) (hc : c ≠ 0) : Continuous (continuousFlow c hc) :=
  (continuousFlow c hc).continuous

theorem action_strong_continuous (c : ℝ) (hc : c ≠ 0) (f : JointHilbert 2 4) :
    Continuous (fun θ => action c hc θ f) := by
  exact (continuous_const (y := f)).compMeasurePreservingLp
    (continuous_flow_family c hc) (flow_preserves_volume c hc) (by norm_num)

def group (c : ℝ) (hc : c ≠ 0) : StrongUnitaryGroup (JointHilbert 2 4) where
  action := action c hc
  initial := action_zero c hc
  compose := action_compose c hc
  continuous_orbit := action_strong_continuous c hc

#print axioms action
#print axioms action_coe
#print axioms action_zero
#print axioms action_compose
#print axioms action_period
#print axioms action_full_period
#print axioms continuous_flow_family
#print axioms action_strong_continuous
#print axioms group

end
end UnifiedTheory.Audit.KFCausalMixedCircleAction
