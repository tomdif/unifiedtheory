/- The actual mixed clock chart preserves null sets. Its Fourier-coordinate
scale is the reciprocal of the physical-position scale, derived by composing
the established physical inverse chart with a smooth fibre dilation. -/
import UnifiedTheory.Audit.KFCausalClockFloorPairedStraightening
import UnifiedTheory.Audit.KFCausalCoupledCoordinateNullSets

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalClockFloorMixedChart
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Block)
open UnifiedTheory.Audit.KFCausalClockFloorPairedStraightening
open UnifiedTheory.Audit.KFCausalClockFloorSpectatorChart (backward)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chartIso chartInverse_derivative)
open UnifiedTheory.Audit.KFCausalCoupledCoordinateNullSets (homeomorph_quasiMeasurePreserving)

def fiber (ρ : Block 4 → ℝ) (hρ : Continuous ρ) : (Block 2 × Block 4) ≃ₜ (Block 2 × Block 4) where
  toFun x := (Real.exp (ρ x.2) • x.1,x.2)
  invFun x := (Real.exp (-ρ x.2) • x.1,x.2)
  left_inv x := by
    simp only [smul_smul,← Real.exp_add,neg_add_cancel,Real.exp_zero,one_smul]
  right_inv x := by
    simp only [smul_smul,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_smul]
  continuous_toFun := ((Real.continuous_exp.comp (hρ.comp continuous_snd)).smul continuous_fst).prodMk continuous_snd
  continuous_invFun := ((Real.continuous_exp.comp (hρ.comp continuous_snd).neg).smul continuous_fst).prodMk continuous_snd

local instance : Measure.IsAddHaarMeasure (volume : Measure (Block 2 × Block 4)) :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem fiber_quasiMeasurePreserving (ρ : Block 4 → ℝ) (hρ : Differentiable ℝ ρ) :
    Measure.QuasiMeasurePreserving (fiber ρ hρ.continuous) volume volume := by
  apply homeomorph_quasiMeasurePreserving
  change Differentiable ℝ (fun x : Block 2 × Block 4 => (Real.exp (-ρ x.2) • x.1,x.2))
  fun_prop

variable (ε : ℝ) (hε : 0 < ε)

theorem clockInverse_differentiable : Differentiable ℝ (clockInverse ε hε) := by
  have hc : Differentiable ℝ ((chartIso ε hε).symm : ℝ → ℝ) :=
    fun q => (chartInverse_derivative ε hε q).differentiableAt
  exact hc.comp (by fun_prop)

def mixedMap (x : Block 2 × Block 4) : Block 2 × Block 4 :=
  ((dilation ε hε x.2)⁻¹ • x.1,backward ε hε x.2)

theorem mixedMap_factor : mixedMap ε hε = inverseMap ε hε ∘
    fiber (fun y => -clockInverse ε hε y) (clockInverse_continuous ε hε).neg := by
  funext x
  simp only [Function.comp_apply,inverseMap_apply,mixedMap]
  change ((dilation ε hε x.2)⁻¹ • x.1,backward ε hε x.2) =
    (dilation ε hε x.2 • (Real.exp (-clockInverse ε hε x.2) • x.1),backward ε hε x.2)
  congr 1
  rw [smul_smul,dilation,← Real.exp_add,← Real.exp_neg]
  congr 2
  ring

theorem mixedMap_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving (mixedMap ε hε) volume volume := by
  rw [mixedMap_factor]
  exact (inverseMap_quasiMeasurePreserving ε hε).comp
    (fiber_quasiMeasurePreserving _ (clockInverse_differentiable ε hε).neg)

#print axioms fiber_quasiMeasurePreserving
#print axioms clockInverse_differentiable
#print axioms mixedMap_factor
#print axioms mixedMap_quasiMeasurePreserving

end
end UnifiedTheory.Audit.KFCausalClockFloorMixedChart
