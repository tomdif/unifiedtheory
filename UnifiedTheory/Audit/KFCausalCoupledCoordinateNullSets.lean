/- The coupled coordinate change and its inverse preserve null sets.
This is derived from differentiability of the actual maps, and permits
almost-everywhere L2 identities to be pulled through the coordinate map. -/
import UnifiedTheory.Audit.KFCausalCoupledCoordinateHomeomorph
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCoupledCoordinateNullSets
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalCoupledCoordinateHomeomorph

theorem homeomorph_quasiMeasurePreserving {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] (e : E ≃ₜ E) (hi : Differentiable ℝ e.symm) :
    Measure.QuasiMeasurePreserving e μ μ := by
  refine ⟨e.continuous.measurable,Measure.AbsolutelyContinuous.mk ?_⟩
  intro s hs hn
  rw [Measure.map_apply e.continuous.measurable hs]
  have he : e ⁻¹' s = e.symm '' s := by
    ext x
    constructor
    · intro hx
      exact ⟨e x,hx,e.symm_apply_apply x⟩
    · rintro ⟨y,hy,rfl⟩
      simpa only [mem_preimage,e.apply_symm_apply] using hy
  rw [he]
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero μ hi.differentiableOn hn

theorem flow_joint_differentiable : Differentiable ℝ (fun z : ℝ×Transverse => flow z.1 z.2) := by
  apply differentiable_pi.mpr
  intro i
  by_cases hi : i=4
  · simp only [flow,hi,ite_true,scale]
    fun_prop
  · simp only [flow,hi,ite_false,scale]
    fun_prop

theorem coordinate_differentiable (ε : ℝ) (hε : 0 < ε) :
    Differentiable ℝ (coordinateHomeomorph ε hε) := by
  have hc : Differentiable ℝ (chart ε) := fun s => (chart_derivative ε s).differentiableAt
  have hp : Differentiable ℝ (phase ε) := fun s => (phase_derivative ε s).differentiableAt
  change Differentiable ℝ (fun x : Configuration => (chart ε x.1,flow (-phase ε x.1) x.2))
  exact (hc.comp differentiable_fst).prodMk
    (flow_joint_differentiable.comp ((hp.comp differentiable_fst).neg.prodMk differentiable_snd))

theorem coordinate_inverse_differentiable (ε : ℝ) (hε : 0 < ε) :
    Differentiable ℝ (coordinateHomeomorph ε hε).symm := by
  have hc : Differentiable ℝ (chartIso ε hε).symm := fun q => (chartInverse_derivative ε hε q).differentiableAt
  have hp : Differentiable ℝ (phase ε) := fun s => (phase_derivative ε s).differentiableAt
  change Differentiable ℝ (fun x : Configuration =>
    ((chartIso ε hε).symm x.1,flow (phase ε ((chartIso ε hε).symm x.1)) x.2))
  exact (hc.comp differentiable_fst).prodMk
    (flow_joint_differentiable.comp ((hp.comp (hc.comp differentiable_fst)).prodMk differentiable_snd))

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem coordinate_quasiMeasurePreserving (ε : ℝ) (hε : 0 < ε) :
    Measure.QuasiMeasurePreserving (coordinateHomeomorph ε hε) volume volume :=
  homeomorph_quasiMeasurePreserving volume _ (coordinate_inverse_differentiable ε hε)

theorem coordinate_inverse_quasiMeasurePreserving (ε : ℝ) (hε : 0 < ε) :
    Measure.QuasiMeasurePreserving (coordinateHomeomorph ε hε).symm volume volume :=
  homeomorph_quasiMeasurePreserving volume _ (coordinate_differentiable ε hε)

#print axioms homeomorph_quasiMeasurePreserving
#print axioms flow_joint_differentiable
#print axioms coordinate_differentiable
#print axioms coordinate_inverse_differentiable
#print axioms coordinate_quasiMeasurePreserving
#print axioms coordinate_inverse_quasiMeasurePreserving

end
end UnifiedTheory.Audit.KFCausalCoupledCoordinateNullSets
