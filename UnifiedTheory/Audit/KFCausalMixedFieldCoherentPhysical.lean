/- On the initial real line, the mixed-shift state is the actual physical
point-field power times the first shifted coherent-source packet. This connects the
new contour graph to the existing natural matter outputs. -/
import UnifiedTheory.Audit.KFCausalMixedFieldCoherentSpectral
import UnifiedTheory.Audit.KFCausalMixedFieldGaussianPhysical

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalMixedFieldCoherentPhysical
noncomputable section
open MeasureTheory
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalClockFloorGroupedCoordinates
open KFCausalClockFloorLpCoordinates (weightedFunction)
open KFCausalClockFloorCoreMatter (pulledField)
open KFCausalClockFloorFieldPolynomials (pulledField_at_coordinate)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalMixedFieldGaussianStrip (fieldLine degree)
open KFCausalMixedFieldGaussianPhysical (fieldLine_grouping)
open KFCausalMixedFieldCoherentSpectral (configurationLine state state_coe)

theorem configurationLine_zero (ε a α β δ p : ℝ) (b : Fin 5 → ℂ) (j : Fin 2) (hε : 0 < ε) (z : Configuration) :
    configurationLine ε a α β δ p b 0 j z =
      (pulledField ε hε pointField z:ℂ)^degree j*
        KFCausalClockFloorCoherentSpectral.configurationLine ε a α β p b δ z := by
  rw [configurationLine,KFCausalMixedFieldCoherentStrip.line_formula,
    fieldLine_grouping ε hε,zero_add]
  rfl

theorem weightedLine_zero (ε a α β δ p : ℝ) (b : Fin 5 → ℂ) (j : Fin 2) (hε : 0 < ε) (z : Configuration) :
    weightedFunction ε hε (configurationLine ε a α β δ p b 0 j) z =
      (pointField z.2:ℂ)^degree j*
        weightedFunction ε hε (KFCausalClockFloorCoherentSpectral.configurationLine ε a α β p b δ) z := by
  unfold weightedFunction
  rw [configurationLine_zero ε a α β δ p b j hε,pulledField_at_coordinate]
  ring

theorem state_zero_coe (ε a α β δ p : ℝ) (b : Fin 5 → ℂ) (j : Fin 2) (hε : 0 < ε)
    (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hδ : |δ| ≤ Real.pi*ε/3) :
    state ε a α β δ p b 0 j hε ha hα hβ hw (by simp; positivity) (by simpa using hδ) =ᵐ[volume]
      fun x => (pointField x.2:ℂ)^degree j*
        KFCausalClockFloorCoherentSpectral.gaussianState ε a α β p b δ hε ha hα hβ hw hδ x := by
  filter_upwards [state_coe ε a α β δ p b 0 j hε ha hα hβ hw (by simp; positivity) (by simpa using hδ),
    KFCausalClockFloorCoherentSpectral.gaussianState_coe ε a α β p b δ hε ha hα hβ hw hδ]
    with x hx hg
  rw [hx,hg]
  exact weightedLine_zero ε a α β δ p b j hε x

#print axioms configurationLine_zero
#print axioms weightedLine_zero
#print axioms state_zero_coe
end
end UnifiedTheory.Audit.KFCausalMixedFieldCoherentPhysical
