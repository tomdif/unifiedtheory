/- The previously explicit inverse-dressed charge-zero trial is now the
representative of the actual inverse clock-half and inverse coordinate
unitary applied in the prescribed order. This does not yet identify the
partial Fourier formula with the longitudinal spectral operator domain. -/
import UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
import UnifiedTheory.Audit.KFCausalClockFloorClockHalf
import UnifiedTheory.Audit.KFCausalClockFloorGroupedCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorTrialUnitary
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalChargeGaussianIdentities
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalClockFloorChargeTrialBridge
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf
open UnifiedTheory.Audit.KFCausalClockFloorGroupedCoordinates

def dampedState (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) : Hilbert :=
  inverseAction ε hε (trialState ε a hbar hε ha hh)

def dampedProfile (ε a hbar : ℝ) (x : Configuration) : ℂ :=
  (Real.sqrt (Real.exp x.1+ε):ℂ)⁻¹*
    configurationProfile (groundWidth hbar) (neutralWidth hbar) (clockFunction ε a) x

theorem dampedState_graph (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    (trialState ε a hbar hε ha hh,dampedState ε a hbar hε ha hh) ∈
      (inverseClockHalf ε).graph :=
  (inverseClockHalf ε).mem_graph ⟨_,inverseClockHalf_domain ε hε _⟩

theorem dampedState_coe (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    dampedState ε a hbar hε ha hh =ᵐ[volume] dampedProfile ε a hbar := by
  filter_upwards [inverseAction_coe ε hε (trialState ε a hbar hε ha hh),
    trialState_coe ε a hbar hε ha hh] with x hx hy
  exact hx.trans (congrArg (fun z : ℂ => (Real.sqrt (Real.exp x.1+ε):ℂ)⁻¹*z) hy)

theorem inverse_dampedState_coe (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    (coordinates ε hε).symm (dampedState ε a hbar hε ha hh) =ᵐ[volume]
      inverseFunction ε hε (dampedProfile ε a hbar) := by
  filter_upwards [coordinates_inverse_coe ε hε (dampedState ε a hbar hε ha hh),
    (coordinate_inverse_quasiMeasurePreserving ε hε).ae (dampedState_coe ε a hbar hε ha hh)]
    with x hx hy
  rw [hx]
  unfold inverseFunction
  rw [hy]

theorem inverse_dampedProfile_grouping (ε a hbar : ℝ) (hε : 0 < ε)
    (z : ℝ × KFCausalClockFloorShearBounds.Grouped) :
    inverseFunction ε hε (dampedProfile ε a hbar) (grouping.symm z) =
      dressedTrial ε a hbar hε z := by
  rw [grouping_symm_apply]
  rfl

def straightenedState (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    GroupedHilbert :=
  groupedCoordinates ((coordinates ε hε).symm (dampedState ε a hbar hε ha hh))

theorem straightenedState_coe (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    straightenedState ε a hbar hε ha hh =ᵐ[volume] dressedTrial ε a hbar hε := by
  filter_upwards [groupedCoordinates_coe ((coordinates ε hε).symm (dampedState ε a hbar hε ha hh)),
    grouping_preserves_volume.symm.quasiMeasurePreserving.ae (inverse_dampedState_coe ε a hbar hε ha hh)]
    with z hz hz'
  exact hz.trans (hz'.trans (inverse_dampedProfile_grouping ε a hbar hε z))

theorem straightenedState_eq (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    straightenedState ε a hbar hε ha hh =
      (dressedTrial_memLp ε a hbar hε ha hh).toLp (dressedTrial ε a hbar hε) := by
  apply Lp.ext
  exact (straightenedState_coe ε a hbar hε ha hh).trans
    (dressedTrial_memLp ε a hbar hε ha hh).coeFn_toLp.symm

theorem straightenedState_ne_zero (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    straightenedState ε a hbar hε ha hh ≠ 0 := by
  intro hz
  have hd := inverseAction_ne_zero ε hε _ (trialState_ne_zero ε a hbar hε ha hh)
  apply hd
  have h1 : (coordinates ε hε).symm (dampedState ε a hbar hε ha hh) = 0 :=
    groupedCoordinates.injective (hz.trans (map_zero groupedCoordinates).symm)
  exact (coordinates ε hε).symm.injective (h1.trans (map_zero (coordinates ε hε).symm).symm)

theorem straightenedState_square_integral (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    ‖dampedState ε a hbar hε ha hh‖^2 =
      ∫ z, ‖dressedTrial ε a hbar hε z‖^2 := by
  have hn : ‖straightenedState ε a hbar hε ha hh‖ = ‖dampedState ε a hbar hε ha hh‖ := by
    rw [straightenedState,groupedCoordinates_norm,LinearIsometryEquiv.norm_map]
  rw [← hn,straightenedState_eq,KFCausalCoupledFunctionEnergy.toLp_square_integral]

theorem clock_fourier_congr (f g : ℝ × KFCausalClockFloorShearBounds.Grouped → ℂ)
    (h : f =ᵐ[volume] g) :
    (fun w : ℝ × KFCausalClockFloorShearBounds.Grouped => (𝓕 (fun q : ℝ => f (q,w.2))) w.1) =ᵐ[volume]
      fun w => (𝓕 (fun q : ℝ => g (q,w.2))) w.1 := by
  have hs : ∀ᵐ x ∂(volume : Measure KFCausalClockFloorShearBounds.Grouped),
      (fun q : ℝ => f (q,x)) =ᵐ[volume] (fun q => g (q,x)) :=
    ae_ae_of_ae_prod (measurePreserving_swap.quasiMeasurePreserving.ae h)
  have ht : ∀ᵐ w ∂(volume : Measure (ℝ × KFCausalClockFloorShearBounds.Grouped)),
      (fun q : ℝ => f (q,w.2)) =ᵐ[volume] (fun q => g (q,w.2)) :=
    quasiMeasurePreserving_snd.ae hs
  filter_upwards [ht] with w hw
  simp only [Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards [hw] with q hq
  rw [hq]

theorem straightenedState_longitudinal_integrable (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) :
    Integrable (fun w : ℝ × KFCausalClockFloorShearBounds.Grouped => Real.exp (2*Real.pi*hbar*w.1)*
      ‖(𝓕 (fun q : ℝ => straightenedState ε a hbar hε ha hh (q,w.2))) w.1‖^2) := by
  apply (dressedTrial_longitudinal_integrable ε a hbar hε ha hh hbound).congr
  filter_upwards [clock_fourier_congr _ _ (straightenedState_coe ε a hbar hε ha hh)] with w hw
  rw [hw]

#print axioms dampedState_graph
#print axioms dampedState_coe
#print axioms inverse_dampedState_coe
#print axioms inverse_dampedProfile_grouping
#print axioms straightenedState_coe
#print axioms straightenedState_eq
#print axioms straightenedState_ne_zero
#print axioms straightenedState_square_integral
#print axioms clock_fourier_congr
#print axioms straightenedState_longitudinal_integrable

end
end UnifiedTheory.Audit.KFCausalClockFloorTrialUnitary
