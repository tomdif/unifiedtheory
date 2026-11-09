/- The actual windowed clock marginal and the sharp physical clock law.
Their escape criteria are equivalent for every fixed normalized window. -/
import UnifiedTheory.Audit.KFCausalWindowedPositionMarginal
import UnifiedTheory.Audit.KFCausalProbabilityWindowEscape
import UnifiedTheory.Audit.KFCausalPhysicalWindowedLaw
import UnifiedTheory.Audit.KFCausalClockPositionLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalPhysicalWindowedClock
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalWindowedPositionMarginal
open UnifiedTheory.Audit.KFCausalProbabilityWindowEscape
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (euclideanPullback split split_preserves_volume)
open UnifiedTheory.Audit.KFCausalClockPositionLaw

theorem scalar_marginal (n : ℕ) (i : Fin n) (h : ℝ) (f g : BlockHilbert n) :
    marginal n i h f g = difference (positionLaw n i f) (positionLaw n i g) := by
  letI : IsFiniteMeasure (KFCausalL2BornLaw.law volume f) :=
    ⟨by rw [KFCausalL2BornLaw.law_total]; exact ENNReal.ofReal_lt_top⟩
  letI : IsFiniteMeasure (KFCausalL2BornLaw.law volume g) :=
    ⟨by rw [KFCausalL2BornLaw.law_total]; exact ENNReal.ofReal_lt_top⟩
  rw [marginal_product,difference,positionLaw,positionLaw,
    Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem position_probability (n : ℕ) (i : Fin n) (f : BlockHilbert n) (hf : ‖f‖ = 1) :
    IsProbabilityMeasure (positionLaw n i f) := by
  letI := KFCausalL2BornLaw.law_probability volume f hf
  exact Measure.isProbabilityMeasure_map (by fun_prop)

theorem physical_position (f : Hilbert) :
    positionLaw 6 0 (euclideanPullback f) = clockPositionLaw f := by
  change (KFCausalL2BornLaw.law volume
    (KFCausalMeasureUnitaryPullback.unitaryPullback split split_preserves_volume f)).map
      (fun x : Block 6 => x 0) = _
  rw [KFCausalBornLocalization.law_pullback volume volume,
    Measure.map_map (by fun_prop) split.symm.measurable]
  change (configurationLaw f).map _ = (configurationLaw f).map Prod.fst
  congr 1

def clockLaw (h : ℝ) (f : Hilbert) (w : BlockHilbert 6) : Measure ℝ :=
  (KFCausalPhysicalWindowedLaw.law h f w).map (fun z : Block 6 × Block 6 => z.1 0)

theorem clockLaw_difference (h : ℝ) (f : Hilbert) (w : BlockHilbert 6) :
    clockLaw h f w = difference (clockPositionLaw f) (positionLaw 6 0 w) := by
  change marginal 6 0 h (euclideanPullback f) w = _
  rw [scalar_marginal,physical_position]

theorem clockLaw_upper (h : ℝ) (f : Hilbert) (w : BlockHilbert 6)
    (hf : ‖f‖ = 1) (hw : ‖w‖ = 1) (S R : ℝ) :
    clockLaw h f w (Set.Iic S) ≤ clockPositionLaw f (Set.Iic (S+R))+
      positionLaw 6 0 w (Set.Icc (-R) R)ᶜ := by
  letI := clockPositionLaw_probability f hf
  letI := position_probability 6 0 w hw
  rw [clockLaw_difference]
  exact upper_bound _ _ S R

theorem sharp_clock_upper (h : ℝ) (f : Hilbert) (w : BlockHilbert 6)
    (hf : ‖f‖ = 1) (hw : ‖w‖ = 1) (S R : ℝ) :
    clockPositionLaw f (Set.Iic S) ≤ clockLaw h f w (Set.Iic (S+R))+
      positionLaw 6 0 w (Set.Icc (-R) R)ᶜ := by
  letI := clockPositionLaw_probability f hf
  letI := position_probability 6 0 w hw
  rw [clockLaw_difference]
  exact reverse_bound _ _ S R

theorem clock_escape_iff {ι : Type*} (l : Filter ι) (h : ℝ)
    (f : ι → Hilbert) (hf : ∀ t, ‖f t‖ = 1) (w : BlockHilbert 6) (hw : ‖w‖ = 1) :
    (∀ S, Tendsto (fun t => clockLaw h (f t) w (Set.Iic S)) l (𝓝 0)) ↔
      (∀ S, Tendsto (fun t => clockPositionLaw (f t) (Set.Iic S)) l (𝓝 0)) := by
  letI (t : ι) := clockPositionLaw_probability (f t) (hf t)
  letI := position_probability 6 0 w hw
  simp only [clockLaw_difference]
  exact escape_iff l (fun t => clockPositionLaw (f t)) (positionLaw 6 0 w)

#print axioms scalar_marginal
#print axioms position_probability
#print axioms physical_position
#print axioms clockLaw_difference
#print axioms clockLaw_upper
#print axioms sharp_clock_upper
#print axioms clock_escape_iff

end
end UnifiedTheory.Audit.KFCausalPhysicalWindowedClock
