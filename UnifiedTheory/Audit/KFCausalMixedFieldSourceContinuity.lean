/- Bounded source curves are continuous in the actual mixed-shift L2
states. The half-width field-power majorant is derived from the Gaussian
contour bounds, including the fourth power needed by the second action. -/
import UnifiedTheory.Audit.KFCausalMixedFieldCoherentSpectral
import UnifiedTheory.Audit.KFCausalClockFloorSourcedMultiplierContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalMixedFieldSourceContinuity
noncomputable section
open MeasureTheory
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalClockFloorGroupedCoordinates (grouping grouping_preserves_volume)
open KFCausalClockFloorLpCoordinates (weightedFunction)
open KFCausalClockFloorUnitaryCoordinates (coordinates)
open KFCausalMixedFieldGaussianStrip (fieldLine degree)
open KFCausalMixedFieldCoherentSpectral (state state_coe)
open KFCausalClockFloorSourcedMultiplierContinuity
open KFCausalClockFloorCoherentBounds (sourceSize)

def multiplier (ε y : ℝ) (j : Fin 2) (x : Configuration) : ℂ :=
  fieldLine ε y (grouping x)^degree j

theorem multiplier_measurable (ε y : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (j : Fin 2) :
    AEStronglyMeasurable (multiplier ε y j) volume :=
  ((KFCausalMixedFieldGaussianStrip.fieldLine_continuous ε y hε hy).pow _).aestronglyMeasurable.comp_measurePreserving
    grouping_preserves_volume

theorem base_memLp (ε a α β δ y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) (hyr : |y+δ| ≤ Real.pi*ε/3) (j : Fin 2) :
    MemLp (fun x => multiplier ε y j x*baseLine ε a α β (y+δ) x) 2 := by
  have hm := (KFCausalMixedFieldGaussianStrip.line_memLp ε a (α/2) (β/2) δ y hε ha
    (by positivity) (by positivity) (by linarith) hy hyr j).comp_measurePreserving
      grouping_preserves_volume
  simpa only [Function.comp_def,KFCausalMixedFieldGaussianStrip.line_formula,multiplier,
    baseLine,KFCausalClockFloorShiftedOutput.configurationLine] using hm

theorem state_eq_outputState (ε a α β δ p : ℝ) (b : Fin 5 → ℂ) (y : ℝ) (j : Fin 2)
    (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) (hyr : |y+δ| ≤ Real.pi*ε/3) :
    state ε a α β δ p b y j hε ha hα hβ hw hy hyr =
      outputState ε a α β (y+δ) hε ha hα hβ hw hyr (multiplier ε y j)
        (multiplier_measurable ε y hε hy j)
        (base_memLp ε a α β δ y hε ha hα hβ hw hy hyr j) 1 p b := by
  apply Lp.ext
  filter_upwards [state_coe ε a α β δ p b y j hε ha hα hβ hw hy hyr,
    outputState_coe ε a α β (y+δ) hε ha hα hβ hw hyr (multiplier ε y j)
      (multiplier_measurable ε y hε hy j)
      (base_memLp ε a α β δ y hε ha hα hβ hw hy hyr j) 1 p b] with x hx hy
  rw [hx,hy]
  simp only [weightedFunction,modifiedLine,KFCausalMixedFieldCoherentSpectral.configurationLine,
    KFCausalMixedFieldCoherentStrip.line_formula,multiplier,
    KFCausalClockFloorCoherentSpectral.configurationLine,one_mul]

theorem state_curve_continuous (ε a α β δ y P B : ℝ) (j : Fin 2)
    (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) (hyr : |y+δ| ≤ Real.pi*ε/3)
    (p : ℝ → ℝ) (b : ℝ → Fin 5 → ℂ) (hp : Continuous p) (hb : Continuous b)
    (hpB : ∀ θ, |p θ| ≤ P) (hbB : ∀ θ, sourceSize (b θ) ≤ B) :
    Continuous (fun θ => state ε a α β δ (p θ) (b θ) y j hε ha hα hβ hw hy hyr) := by
  have hc := (coordinates ε hε).continuous.comp
    (modifiedLine_curve_continuous ε a α β (y+δ) P B hε ha hα hβ hw hyr
      (multiplier ε y j) (multiplier_measurable ε y hε hy j)
      (base_memLp ε a α β δ y hε ha hα hβ hw hy hyr j)
      (fun _ => 1) p b continuous_const hp hb (fun _ => by simp) hpB hbB)
  have he := funext (fun θ => state_eq_outputState ε a α β δ (p θ) (b θ) y j hε ha hα hβ hw hy hyr)
  rw [he]
  exact hc

#print axioms multiplier_measurable
#print axioms base_memLp
#print axioms state_eq_outputState
#print axioms state_curve_continuous
end
end UnifiedTheory.Audit.KFCausalMixedFieldSourceContinuity
