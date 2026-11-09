/- Actual longitudinal exponential graphs for arbitrary sourced Gaussian lines,
and for every member of the total physical charge-modulation family. -/
import UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain
import UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput
import UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary
import UnifiedTheory.Audit.KFCausalClockFloorCoherentFullFourier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip
open UnifiedTheory.Audit.KFCausalClockFloorGroupedCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary
open UnifiedTheory.Audit.KFCausalClockFloorGaussianL1 (pairGrouping_euclideanSplit)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentFullFourier
open UnifiedTheory.Audit.KFCausalClockFloorFourierCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorFourierMultiplier
open UnifiedTheory.Audit.KFCausalClockFloorExponential
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalL2FourierIntegral
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition

def configurationLine (ε a α β p : ℝ) (b : Fin 5 → ℂ) (y : ℝ) (x : Configuration) : ℂ :=
  line ε a α β p b y (grouping x)

theorem configurationLine_flatten (ε a α β p : ℝ) (b : Fin 5 → ℂ) (y : ℝ) :
    configurationLine ε a α β p b y ∘ split = euclideanLine ε a α β p b y ∘ euclideanSplit := by
  funext x
  exact congrArg (line ε a α β p b y) (pairGrouping_euclideanSplit x).symm

theorem configurationLine_integrable (ε a α β p : ℝ) (b : Fin 5 → ℂ) (y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) :
    Integrable (configurationLine ε a α β p b y) :=
  grouping_preserves_volume.integrable_comp_of_integrable (line_integrable ε a α β p b y hε ha hα hβ hw hy)

theorem configurationLine_memLp (ε a α β p : ℝ) (b : Fin 5 → ℂ) (y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) :
    MemLp (configurationLine ε a α β p b y) 2 :=
  (line_memLp ε a α β p b y hε ha hα hβ hw hy).comp_measurePreserving grouping_preserves_volume

def gaussianState (ε a α β p : ℝ) (b : Fin 5 → ℂ) (y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) : Hilbert :=
  coordinates ε hε ((configurationLine_memLp ε a α β p b y hε ha hα hβ hw hy).toLp (configurationLine ε a α β p b y))

theorem gaussianState_coe (ε a α β p : ℝ) (b : Fin 5 → ℂ) (y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) :
    gaussianState ε a α β p b y hε ha hα hβ hw hy =ᵐ[volume]
      weightedFunction ε hε (configurationLine ε a α β p b y) :=
  coordinates_toLp_coe ε hε _ _

theorem gaussianState_fourier (ε a α β p : ℝ) (b : Fin 5 → ℂ) (y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) :
    coupledFourier ε hε (gaussianState ε a α β p b y hε ha hα hβ hw hy) =ᵐ[volume]
      𝓕 (euclideanLine ε a α β p b y ∘ euclideanSplit) := by
  let f := configurationLine ε a α β p b y
  have hf : MemLp f 2 := configurationLine_memLp ε a α β p b y hε ha hα hβ hw hy
  have hi : Integrable f := configurationLine_integrable ε a α β p b y hε ha hα hβ hw hy
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

theorem gaussianState_exponential_graph (ε a α β p : ℝ) (b : Fin 5 → ℂ) (hbar : ℝ)
    (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hbound : |hbar| ≤ 2*Real.pi*ε/3) :
    (gaussianState ε a α β p b 0 hε ha hα hβ hw (by simp; positivity),
      gaussianState ε a α β p b (-hbar/2) hε ha hα hβ hw
        (KFCausalClockFloorShiftedOutput.shift_bound ε hbar hbound)) ∈
      (longitudinalExponential ε hε hbar (1/2)).graph := by
  apply (longitudinal_exponential_graph ε hε hbar (1/2) _ _).mpr
  filter_upwards [gaussianState_fourier ε a α β p b (-hbar/2) hε ha hα hβ hw
      (KFCausalClockFloorShiftedOutput.shift_bound ε hbar hbound),
    gaussianState_fourier ε a α β p b 0 hε ha hα hβ hw (by simp; positivity)] with k hk hf
  rw [hk,hf]
  have hs : (1/2)*symbol hbar k = Real.pi*hbar*k 0 := by unfold symbol; ring
  rw [hs]
  exact (full_fourier_shift ε a α β p b hbar hε ha hα hβ hw hbound k).symm

theorem dampedState_eq (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (k : Joint 2 4) :
    dampedState ε a hbar hε ha hh k = amplitudeConstant hbar k •
      gaussianState ε a (groundWidth hbar) (neutralWidth hbar) (clockFrequency k)
        (sourceCoefficients hbar k) 0 hε ha (groundWidth_positive hbar hh)
        (neutralWidth_positive hbar hh) (neutralWidth_bound hbar) (by simp; positivity) := by
  apply (coordinates ε hε).symm.injective
  rw [map_smul]
  unfold gaussianState
  rw [LinearIsometryEquiv.symm_apply_apply]
  apply Lp.ext
  filter_upwards [inverse_dampedState_coe ε a hbar hε ha hh k,
    Lp.coeFn_smul (amplitudeConstant hbar k)
      ((configurationLine_memLp ε a (groundWidth hbar) (neutralWidth hbar) (clockFrequency k)
        (sourceCoefficients hbar k) 0 hε ha (groundWidth_positive hbar hh)
        (neutralWidth_positive hbar hh) (neutralWidth_bound hbar) (by simp; positivity)).toLp _),
    (configurationLine_memLp ε a (groundWidth hbar) (neutralWidth hbar) (clockFrequency k)
      (sourceCoefficients hbar k) 0 hε ha (groundWidth_positive hbar hh)
      (neutralWidth_positive hbar hh) (neutralWidth_bound hbar) (by simp; positivity)).coeFn_toLp]
    with x hx hy hz
  rw [hx,hy]
  change _ = amplitudeConstant hbar k * _
  rw [hz]
  have he := inverse_dampedProfile_grouping ε a (groundWidth hbar) (neutralWidth hbar) hε
    (KFCausalClockFloorCoherentCoordinates.displacement hbar k)
    (KFCausalClockFloorCoherentCoordinates.spectatorParameter k) (grouping x)
  rw [MeasurableEquiv.symm_apply_apply] at he
  exact he

def shiftedOutput (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (k : Joint 2 4) : Hilbert :=
  amplitudeConstant hbar k • gaussianState ε a (groundWidth hbar) (neutralWidth hbar)
    (clockFrequency k) (sourceCoefficients hbar k) (-hbar/2) hε ha
    (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh)
    (neutralWidth_bound hbar) (KFCausalClockFloorShiftedOutput.shift_bound ε hbar hbound)

theorem shiftedOutput_graph (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (k : Joint 2 4) :
    (dampedState ε a hbar hε ha hh k,shiftedOutput ε a hbar hε ha hh hbound k) ∈
      (longitudinalExponential ε hε hbar (1/2)).graph := by
  rw [dampedState_eq]
  exact (longitudinalExponential ε hε hbar (1/2)).graph.smul_mem (amplitudeConstant hbar k)
    (gaussianState_exponential_graph ε a _ _ (clockFrequency k) (sourceCoefficients hbar k) hbar
      hε ha (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh) (neutralWidth_bound hbar) hbound)

theorem state_ordered_graph (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (k : Joint 2 4) :
    (KFCausalClockFloorCoherentStates.state ε a hbar hε ha hh k,
      shiftedOutput ε a hbar hε ha hh hbound k) ∈ (orderedExponential ε hε hbar).graph := by
  apply (composition_graph _ _ _ _).mpr
  exact ⟨_,dampedState_graph ε a hbar hε ha hh k,shiftedOutput_graph ε a hbar hε ha hh hbound k⟩

theorem state_ordered_domain (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (k : Joint 2 4) :
    KFCausalClockFloorCoherentStates.state ε a hbar hε ha hh k ∈ (orderedExponential ε hε hbar).domain :=
  LinearPMap.mem_domain_of_mem_graph (state_ordered_graph ε a hbar hε ha hh hbound k)

theorem ordered_output_eq (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (k : Joint 2 4) :
    orderedExponential ε hε hbar
      ⟨KFCausalClockFloorCoherentStates.state ε a hbar hε ha hh k,
        state_ordered_domain ε a hbar hε ha hh hbound k⟩ = shiftedOutput ε a hbar hε ha hh hbound k :=
  (orderedExponential ε hε hbar).mem_graph_snd_inj'
    ((orderedExponential ε hε hbar).mem_graph
      ⟨_,state_ordered_domain ε a hbar hε ha hh hbound k⟩)
    (state_ordered_graph ε a hbar hε ha hh hbound k) rfl

#print axioms configurationLine_flatten
#print axioms configurationLine_integrable
#print axioms configurationLine_memLp
#print axioms gaussianState_coe
#print axioms gaussianState_fourier
#print axioms gaussianState_exponential_graph
#print axioms dampedState_eq
#print axioms shiftedOutput_graph
#print axioms state_ordered_graph
#print axioms state_ordered_domain
#print axioms ordered_output_eq

end
end UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral
