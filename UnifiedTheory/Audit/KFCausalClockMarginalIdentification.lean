/- The clock axis of the represented ten-dimensional probability and the
actual quantum clock Born law have exactly the same canonical phase tests. -/
import UnifiedTheory.Audit.KFCausalTenProbabilityLimit
import UnifiedTheory.Audit.KFCausalClockPositionLaw
import UnifiedTheory.Audit.KFCausalL2BornLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalClockMarginalIdentification
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTenPhaseProjection
open UnifiedTheory.Audit.KFCausalCanonicalTenCoordinates (Coefficients encode)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (scalar characteristic)
open UnifiedTheory.Audit.KFCausalClockPositionLaw
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockTestControl (clockTest clockTest_modulation)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

def axis : ℝ →L[ℝ] Coefficients where
  toFun u := (Pi.single 0 u,0)
  map_add' u v := by simp [Pi.single_add]
  map_smul' c u := by
    apply Prod.ext
    · funext i
      by_cases hi : i = 0
      · subst i
        simp
      · simp [hi]
    · simp
  cont := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro i
      by_cases hi : i = 0
      · subst i
        simpa only [Pi.single_eq_same] using (continuous_id : Continuous (fun u : ℝ => u))
      · simpa only [Pi.single_eq_of_ne hi] using (continuous_const : Continuous (fun _ : ℝ => (0:ℝ)))
    · exact continuous_const

def clockProjection : TenSpace →L[ℝ] ℝ where
  toFun x := x (Sum.inl 0)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

theorem axis_encode (u : ℝ) : encode (axis u) =
    KFCausalClockFloorDisplacedClockTestControl.frequency u := by
  apply Prod.ext
  · apply ContinuousLinearMap.ext
    intro x
    simp [encode,axis,KFCausalCanonicalTenDirections.frequency,
      KFCausalCanonicalTenDirections.positionLinear,
      KFCausalClockFloorDisplacedClockTestControl.frequency,
      KFCausalClockFloorEvolvedCharacteristics.positionFrequency,
      KFCausalPhysicalGaussianConcentration.dot,Fin.sum_univ_succ]
  · simp [encode,axis,KFCausalCanonicalTenDirections.frequency,
      KFCausalClockFloorDisplacedClockTestControl.frequency]

theorem axis_inner (x : TenSpace) (u : ℝ) :
    inner ℝ x (coefficientVector (axis u)) = u*clockProjection x := by
  simp [PiLp.inner_apply,coefficientVector,axis,clockProjection,RCLike.inner_apply]

def marginal (ν : ProbabilityMeasure TenSpace) : ProbabilityMeasure ℝ :=
  ⟨(ν : Measure TenSpace).map clockProjection,
    Measure.isProbabilityMeasure_map clockProjection.continuous.measurable.aemeasurable⟩

theorem marginal_characteristic (ν : ProbabilityMeasure TenSpace) (u : ℝ) :
    charFun (marginal ν : Measure ℝ) u = charFun (ν : Measure TenSpace) (coefficientVector (axis u)) := by
  rw [charFun_apply_real,charFun_apply]
  simp only [← Complex.ofReal_mul]
  change (∫ x, Complex.exp ((u*x:ℝ)*Complex.I) ∂(ν : Measure TenSpace).map clockProjection) = _
  rw [integral_map clockProjection.continuous.measurable.aemeasurable (by fun_prop)]
  simp only [axis_inner]

theorem born_characteristic (h : ℝ) (f : Hilbert) (u : ℝ) :
    charFun (clockPositionLaw f) u = characteristic volume h f (encode (axis u)) := by
  rw [axis_encode,charFun_apply_real,clockPositionLaw,
    integral_map measurable_fst.aemeasurable (by fun_prop)]
  simp only [← Complex.ofReal_mul]
  have he : (fun x : Configuration => Complex.exp ((u*x.1:ℝ)*Complex.I)) =
      fun x => scalar (u*x.1) := by
    funext x
    unfold scalar
    rw [mul_comm (↑(u*x.1)) Complex.I]
  rw [he]
  change (∫ x, scalar (u*x.1) ∂KFCausalL2BornLaw.law volume f) = _
  rw [KFCausalL2BornLaw.integral_eq_inner volume f (clockTest h u f) _ ?_]
  · rfl
  · rw [clockTest_modulation]
    exact KFCausalLpPhaseTranslation.modulation_coe volume (fun x : Configuration => u*x.1)
      (measurable_const.mul measurable_fst) f

#print axioms axis_encode
#print axioms axis_inner
#print axioms marginal_characteristic
#print axioms born_characteristic

end
end UnifiedTheory.Audit.KFCausalClockMarginalIdentification
