/- Both exact narrow coordinate charts preserve the spectator clock.
Consequently they intertwine the actual all-L2 clock coordinate unitary
and clock translations. No regularity of a Hilbert representative is assumed. -/
import UnifiedTheory.Audit.KFCausalNarrowFourierGeneralCoordinates
import UnifiedTheory.Audit.KFCausalClockFloorPureClockPartialFourier
import UnifiedTheory.Audit.KFCausalPartialFourierRightTranslation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNarrowFourierClockCoordinates
noncomputable section
open MeasureTheory
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Block ProductHilbert)
open KFCausalNarrowFourierGeneralCoordinates
open KFCausalNarrowFourierCoordinates (pairedCoordinates)
open KFCausalClockFloorPureClockCoordinates (coordinates chartHomeomorph weight)
open KFCausalClockFloorPureClockLpCoordinates (coordinates_coe weightedFunction)
open KFCausalClockFloorPureClockPairedCoordinates
open KFCausalClockFloorSpectatorChart (changeClock)
open KFCausalConfigurationTranslation (clockShift translation)
open KFCausalPartialFourierRightTranslation

def clockBlock (t : ℝ) : Block 4 := WithLp.toLp 2 ![t,0,0,0]

theorem clockBlock_add (t : ℝ) (z : Block 4) :
    z+clockBlock t = changeClock (z 0+t) z := by
  ext i
  fin_cases i <;> simp [clockBlock,changeClock]

theorem paired_clock (z : Product) : (pairedChart.symm z).1 = z.2 0 := by
  rw [pairedChart_symm]

theorem frequency_clock (z : Product) : (frequencyChart.symm z).1 = z.2 0 := by
  rw [frequencyChart_symm]
  rfl

theorem paired_changeClock (r : ℝ) (z : Product) :
    pairedChart.symm (z.1,changeClock r z.2) = (r,(pairedChart.symm z).2) := by
  simp only [pairedChart_symm]
  apply Prod.ext
  · rfl
  · ext i
    fin_cases i <;> rfl

theorem frequency_changeClock (r : ℝ) (z : Product) :
    frequencyChart.symm (z.1,changeClock r z.2) = (r,(frequencyChart.symm z).2) := by
  simp only [frequencyChart_symm]
  apply Prod.ext
  · rfl
  · ext i
    fin_cases i <;> rfl

variable (E : Hilbert ≃ₗᵢ[ℂ] ProductHilbert 2 4) (e : Product → Configuration)
  (he : Measure.QuasiMeasurePreserving e volume volume)
  (hE : ∀ u : Hilbert, E u =ᵐ[volume] u ∘ e)
  (hc : ∀ z, (e z).1 = z.2 0)
  (hs : ∀ r z, e (z.1,changeClock r z.2) = (r,(e z).2))

include he hE hc hs in
theorem coordinates_intertwine (ε : ℝ) (hε : 0 < ε) (u : Hilbert) :
    E (coordinates ε hε u) = pairedUnitary ε hε (E u) := by
  have hg (z : Product) : chartHomeomorph ε hε (e z) = e (pairedMap ε hε z) := by
    rw [pairedMap_apply]
    unfold rightForward
    rw [hs]
    change (KFCausalRegularizedLongitudinalChart.chart ε (e z).1,(e z).2) = _
    rw [hc]
  apply Lp.ext
  filter_upwards [hE (coordinates ε hε u),he.ae (coordinates_coe ε hε u),
    pairedUnitary_coe ε hε (E u), (pairedMap_quasiMeasurePreserving ε hε).ae (hE u)]
    with z hz hu hp hEu
  simp only [Function.comp_apply] at hz hEu
  rw [hz,hu,hp,hEu]
  unfold weightedFunction
  rw [hg]
  change (Real.sqrt (Real.exp (e z).1+ε):ℂ)*_ = _
  rw [hc]
  rfl

include he hE hc hs in
theorem translation_intertwine (t : ℝ) (u : Hilbert) :
    E (translation t u) = rightTranslation 2 4 (clockBlock t) (E u) := by
  have hu : translation t u =ᵐ[volume] u ∘ clockShift t := by
    rw [KFCausalConfigurationTranslation.translation_eq_compMeasurePreserving]
    exact Lp.coeFn_compMeasurePreserving u
      (KFCausalConfigurationTranslation.clockShift_measurePreserving t)
  have hg (z : Product) : clockShift t (e z) = e (z.1,z.2+clockBlock t) := by
    rw [clockBlock_add,hs,KFCausalConfigurationTranslation.clockShift_apply,hc]
  apply Lp.ext
  filter_upwards [hE (translation t u),he.ae hu,
    rightTranslation_coe 2 4 (clockBlock t) (E u),
    (rightShift_preserves 2 4 (clockBlock t)).quasiMeasurePreserving.ae (hE u)] with z hz hu hp hEu
  change translation t u (e z) = u (clockShift t (e z)) at hu
  change E u (z.1,z.2+clockBlock t) = u (e (z.1,z.2+clockBlock t)) at hEu
  change E (translation t u) z = translation t u (e z) at hz
  rw [hz,hu,hp,hEu,hg]

theorem paired_coe (u : Hilbert) : pairedCoordinates u =ᵐ[volume] u ∘ pairedChart.symm := by
  simpa only [Function.comp_def,pairedChart_symm] using pairedCoordinates_coe u

theorem frequency_coe (u : Hilbert) : frequencyCoordinates u =ᵐ[volume] u ∘ frequencyChart.symm := by
  simpa only [Function.comp_def,frequencyChart_symm] using frequencyCoordinates_coe u

theorem paired_coordinates (ε : ℝ) (hε : 0 < ε) (u : Hilbert) :
    pairedCoordinates (coordinates ε hε u) = pairedUnitary ε hε (pairedCoordinates u) :=
  coordinates_intertwine pairedCoordinates pairedChart.symm
    pairedChart_preserves_volume.symm.quasiMeasurePreserving paired_coe paired_clock paired_changeClock ε hε u

theorem frequency_coordinates (ε : ℝ) (hε : 0 < ε) (u : Hilbert) :
    frequencyCoordinates (coordinates ε hε u) = pairedUnitary ε hε (frequencyCoordinates u) :=
  coordinates_intertwine frequencyCoordinates frequencyChart.symm
    frequencyChart_preserves_volume.symm.quasiMeasurePreserving frequency_coe frequency_clock frequency_changeClock ε hε u

theorem paired_translation (t : ℝ) (u : Hilbert) :
    pairedCoordinates (translation t u) = rightTranslation 2 4 (clockBlock t) (pairedCoordinates u) :=
  translation_intertwine pairedCoordinates pairedChart.symm
    pairedChart_preserves_volume.symm.quasiMeasurePreserving paired_coe paired_clock paired_changeClock t u

theorem frequency_translation (t : ℝ) (u : Hilbert) :
    frequencyCoordinates (translation t u) = rightTranslation 2 4 (clockBlock t) (frequencyCoordinates u) :=
  translation_intertwine frequencyCoordinates frequencyChart.symm
    frequencyChart_preserves_volume.symm.quasiMeasurePreserving frequency_coe frequency_clock frequency_changeClock t u

#print axioms clockBlock_add
#print axioms paired_clock
#print axioms frequency_clock
#print axioms paired_changeClock
#print axioms frequency_changeClock
#print axioms coordinates_intertwine
#print axioms translation_intertwine
#print axioms paired_coe
#print axioms frequency_coe
#print axioms paired_coordinates
#print axioms frequency_coordinates
#print axioms paired_translation
#print axioms frequency_translation
end
end UnifiedTheory.Audit.KFCausalNarrowFourierClockCoordinates
