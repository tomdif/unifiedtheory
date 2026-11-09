/- On the initial real line, the mixed-shift state is the actual physical
point-field power times the first shifted Gaussian. This connects the
new contour graph to the existing natural matter outputs. -/
import UnifiedTheory.Audit.KFCausalMixedFieldGaussianSpectral
import UnifiedTheory.Audit.KFCausalClockFloorFieldPolynomials

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalMixedFieldGaussianPhysical
noncomputable section
open MeasureTheory
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalClockFloorGroupedCoordinates
open KFCausalClockFloorLpCoordinates (weightedFunction)
open KFCausalClockFloorCoreMatter (pulledField)
open KFCausalClockFloorFieldPolynomials (pulledField_at_coordinate)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalMixedFieldGaussianStrip (fieldLine degree)
open KFCausalMixedFieldGaussianSpectral (configurationLine state state_coe)

theorem fieldLine_grouping (ε : ℝ) (hε : 0 < ε) (z : Configuration) :
    fieldLine ε 0 (grouping z) = (pulledField ε hε pointField z:ℂ) := by
  change KFCausalMixedFieldGaussianBounds.field
    (KFCausalComplexClockInverse.complexInverse ε ((z.1:ℂ)+(0:ℂ)*Complex.I))
      (transverseGrouping z.2) =
    (pointField (KFCausalTransverseDilationFlow.flow
      ((KFCausalRegularizedLongitudinalChart.chartIso ε hε).symm z.1) z.2):ℂ)
  simp only [zero_mul,add_zero,KFCausalComplexClockInverse.complexInverse_real ε hε]
  rw [KFCausalMixedFieldGaussianBounds.field_real,← transverseGrouping_symm_apply,
    MeasurableEquiv.symm_apply_apply]

theorem coherent_zero_line (ε a α β y : ℝ) (z : Configuration) :
    KFCausalClockFloorCoherentSpectral.configurationLine ε a α β 0 0 y z =
      KFCausalClockFloorFullGaussian.line ε a α β y (grouping z) := by
  simp [KFCausalClockFloorCoherentSpectral.configurationLine,
    KFCausalClockFloorCoherentStrip.line,KFCausalClockFloorCoherentStrip.trial,
    KFCausalClockFloorCoherentStrip.clockPhase,KFCausalClockFloorCoherentBounds.coherentPacket,
    KFCausalClockFloorCoherentBounds.source,
    KFCausalClockFloorFullGaussian.line,KFCausalClockFloorFullGaussian.trial]

theorem configurationLine_zero (ε a α β δ : ℝ) (j : Fin 2) (hε : 0 < ε) (z : Configuration) :
    configurationLine ε a α β δ 0 j z =
      (pulledField ε hε pointField z:ℂ)^degree j*
        KFCausalClockFloorCoherentSpectral.configurationLine ε a α β 0 0 δ z := by
  rw [configurationLine,KFCausalMixedFieldGaussianStrip.line_formula,
    fieldLine_grouping ε hε,zero_add,coherent_zero_line]

theorem weightedLine_zero (ε a α β δ : ℝ) (j : Fin 2) (hε : 0 < ε) (z : Configuration) :
    weightedFunction ε hε (configurationLine ε a α β δ 0 j) z =
      (pointField z.2:ℂ)^degree j*
        weightedFunction ε hε (KFCausalClockFloorCoherentSpectral.configurationLine ε a α β 0 0 δ) z := by
  unfold weightedFunction
  rw [configurationLine_zero ε a α β δ j hε,pulledField_at_coordinate]
  ring

theorem state_zero_coe (ε a α β δ : ℝ) (j : Fin 2) (hε : 0 < ε)
    (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hδ : |δ| ≤ Real.pi*ε/3) :
    state ε a α β δ 0 j hε ha hα hβ hw (by simp; positivity) (by simpa using hδ) =ᵐ[volume]
      fun x => (pointField x.2:ℂ)^degree j*
        KFCausalClockFloorCoherentSpectral.gaussianState ε a α β 0 0 δ hε ha hα hβ hw hδ x := by
  filter_upwards [state_coe ε a α β δ 0 j hε ha hα hβ hw (by simp; positivity) (by simpa using hδ),
    KFCausalClockFloorCoherentSpectral.gaussianState_coe ε a α β 0 0 δ hε ha hα hβ hw hδ]
    with x hx hg
  rw [hx,hg]
  exact weightedLine_zero ε a α β δ j hε x

#print axioms fieldLine_grouping
#print axioms coherent_zero_line
#print axioms configurationLine_zero
#print axioms weightedLine_zero
#print axioms state_zero_coe
end
end UnifiedTheory.Audit.KFCausalMixedFieldGaussianPhysical
