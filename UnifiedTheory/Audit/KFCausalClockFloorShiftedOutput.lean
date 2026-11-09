/- The ordered longitudinal exponential has an explicit shifted-Gaussian
output on the physical charge-zero trial. The operator graph, not only
its norm, is identified. Remaining matter/gradient domains are separate. -/
import UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian
open UnifiedTheory.Audit.KFCausalClockFloorGroupedCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf
open UnifiedTheory.Audit.KFCausalClockFloorTrialUnitary
open UnifiedTheory.Audit.KFCausalClockFloorGaussianL1
open UnifiedTheory.Audit.KFCausalClockFloorFullFourierEnergy
open UnifiedTheory.Audit.KFCausalClockFloorFourierCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorFourierMultiplier
open UnifiedTheory.Audit.KFCausalClockFloorExponential
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain
open UnifiedTheory.Audit.KFCausalL2FourierIntegral
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition

def configurationLine (ε a α β y : ℝ) (x : Configuration) : ℂ :=
  line ε a α β y (grouping x)

theorem configurationLine_flatten (ε a α β y : ℝ) :
    configurationLine ε a α β y ∘ split = euclideanLine ε a α β y ∘ euclideanSplit := by
  funext x
  exact congrArg (line ε a α β y) (pairGrouping_euclideanSplit x).symm

theorem configurationLine_integrable (ε a α β y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) :
    Integrable (configurationLine ε a α β y) :=
  grouping_preserves_volume.integrable_comp_of_integrable (line_integrable ε a α β y hε ha hα hβ hw hy)

theorem configurationLine_memLp (ε a α β y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) :
    MemLp (configurationLine ε a α β y) 2 :=
  (line_memLp ε a α β y hε ha hα hβ hw hy).comp_measurePreserving grouping_preserves_volume

def gaussianState (ε a α β y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) : Hilbert :=
  coordinates ε hε ((configurationLine_memLp ε a α β y hε ha hα hβ hw hy).toLp (configurationLine ε a α β y))

theorem gaussianState_coe (ε a α β y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) :
    gaussianState ε a α β y hε ha hα hβ hw hy =ᵐ[volume]
      weightedFunction ε hε (configurationLine ε a α β y) :=
  coordinates_toLp_coe ε hε _ _

theorem gaussianState_fourier (ε a α β y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) :
    coupledFourier ε hε (gaussianState ε a α β y hε ha hα hβ hw hy) =ᵐ[volume]
      𝓕 (euclideanLine ε a α β y ∘ euclideanSplit) := by
  let f := configurationLine ε a α β y
  have hf : MemLp f 2 := configurationLine_memLp ε a α β y hε ha hα hβ hw hy
  have hi : Integrable f := configurationLine_integrable ε a α β y hε ha hα hβ hw hy
  have hp : MemLp (f ∘ split) 2 := hf.comp_measurePreserving split_preserves_volume
  have he : euclideanPullback (hf.toLp f) = hp.toLp (f ∘ split) := by
    apply Lp.ext
    filter_upwards [euclideanPullback_coe (hf.toLp f),
      split_preserves_volume.quasiMeasurePreserving.ae hf.coeFn_toLp,hp.coeFn_toLp] with x hx hy hz
    exact (hx.trans hy).trans hz.symm
  change (Lp.fourierTransformₗᵢ Space ℂ)
    (euclideanPullback ((coordinates ε hε).symm (coordinates ε hε (hf.toLp f)))) =ᵐ[volume] _
  rw [LinearIsometryEquiv.symm_apply_apply,he]
  have hF := fourier_toLp_coe _ (split_preserves_volume.integrable_comp_of_integrable hi) hp
  simpa only [f,configurationLine_flatten] using hF

theorem shift_bound (ε hbar : ℝ) (hbound : |hbar| ≤ 2*Real.pi*ε/3) :
    |-hbar/2| ≤ Real.pi*ε/3 := by
  rw [abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith

def shiftedOutput (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) : Hilbert :=
  gaussianState ε a (groundWidth hbar) (neutralWidth hbar) (-hbar/2) hε ha
    (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh)
    (neutralWidth_bound hbar) (shift_bound ε hbar hbound)

theorem shiftedOutput_coe (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) :
    shiftedOutput ε a hbar hε ha hh hbound =ᵐ[volume]
      weightedFunction ε hε (configurationLine ε a (groundWidth hbar) (neutralWidth hbar) (-hbar/2)) :=
  gaussianState_coe ε a _ _ (-hbar/2) hε ha _ _ _ _

theorem shiftedOutput_graph (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) :
    (dampedState ε a hbar hε ha hh,shiftedOutput ε a hbar hε ha hh hbound) ∈
      (longitudinalExponential ε hε hbar (1/2)).graph := by
  apply (longitudinal_exponential_graph ε hε hbar (1/2) _ _).mpr
  filter_upwards [gaussianState_fourier ε a _ _ (-hbar/2) hε ha (groundWidth_positive hbar hh)
      (neutralWidth_positive hbar hh) (neutralWidth_bound hbar) (shift_bound ε hbar hbound),
    dampedState_fourier_coe ε a hbar hε ha hh] with k hk hf
  unfold shiftedOutput
  rw [hk,hf]
  have hs : (1/2)*symbol hbar k = Real.pi*hbar*k 0 := by unfold symbol; ring
  rw [hs]
  exact (full_fourier_shift ε a _ _ hbar hε ha (groundWidth_positive hbar hh)
    (neutralWidth_positive hbar hh) (neutralWidth_bound hbar) hbound k).symm

theorem trialState_shifted_graph (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) :
    (trialState ε a hbar hε ha hh,shiftedOutput ε a hbar hε ha hh hbound) ∈
      (orderedExponential ε hε hbar).graph := by
  apply (composition_graph _ _ _ _).mpr
  exact ⟨_,dampedState_graph ε a hbar hε ha hh,shiftedOutput_graph ε a hbar hε ha hh hbound⟩

theorem ordered_output_eq (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) :
    orderedExponential ε hε hbar
      ⟨trialState ε a hbar hε ha hh,trialState_ordered_domain ε a hbar hε ha hh hbound⟩ =
      shiftedOutput ε a hbar hε ha hh hbound :=
  (orderedExponential ε hε hbar).mem_graph_snd_inj'
    ((orderedExponential ε hε hbar).mem_graph
      ⟨trialState ε a hbar hε ha hh,trialState_ordered_domain ε a hbar hε ha hh hbound⟩)
    (trialState_shifted_graph ε a hbar hε ha hh hbound) rfl

#print axioms configurationLine_flatten
#print axioms configurationLine_integrable
#print axioms configurationLine_memLp
#print axioms gaussianState_coe
#print axioms gaussianState_fourier
#print axioms shift_bound
#print axioms shiftedOutput_coe
#print axioms shiftedOutput_graph
#print axioms trialState_shifted_graph
#print axioms ordered_output_eq

end
end UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput
