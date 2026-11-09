/- The mixed field/coherent-source contour identity gives an actual maximal
longitudinal exponential graph in the physical Hilbert space. -/
import UnifiedTheory.Audit.KFCausalMixedFieldCoherentFullFourier
import UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalMixedFieldCoherentSpectral
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalEuclideanConfiguration
open KFCausalEuclideanClockSplit (euclideanSplit)
open KFCausalClockFloorGroupedCoordinates
open KFCausalClockFloorUnitaryCoordinates (coordinates)
open KFCausalClockFloorLpCoordinates (weightedFunction coordinates_toLp_coe)
open KFCausalClockFloorGaussianL1 (pairGrouping_euclideanSplit)
open KFCausalClockFloorFourierCoordinates (coupledFourier)
open KFCausalClockFloorFourierMultiplier (symbol)
open KFCausalClockFloorExponential (longitudinalExponential longitudinal_exponential_graph)
open KFCausalL2FourierIntegral (fourier_toLp_coe)
open KFCausalMixedFieldCoherentStrip
open KFCausalMixedFieldGaussianContour (strip_pair)
open KFCausalMixedFieldCoherentFullFourier (euclideanLine full_fourier_shift)

def configurationLine (ε a α β δ p : ℝ) (b : Fin 5 → ℂ) (y : ℝ) (j : Fin 2) (x : Configuration) : ℂ :=
  line ε a α β δ p b y j (grouping x)

theorem configurationLine_flatten (ε a α β δ p : ℝ) (b : Fin 5 → ℂ) (y : ℝ) (j : Fin 2) :
    configurationLine ε a α β δ p b y j ∘ split =
      euclideanLine ε a α β δ p b y j ∘ euclideanSplit := by
  funext x
  exact congrArg (line ε a α β δ p b y j) (pairGrouping_euclideanSplit x).symm

theorem configurationLine_integrable (ε a α β δ p : ℝ) (b : Fin 5 → ℂ) (y : ℝ) (j : Fin 2) (hε : 0 < ε)
    (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) (hyr : |y+δ| ≤ Real.pi*ε/3) :
    Integrable (configurationLine ε a α β δ p b y j) :=
  grouping_preserves_volume.integrable_comp_of_integrable
    (line_integrable ε a α β δ p b y hε ha hα hβ hw hy hyr j)

theorem configurationLine_memLp (ε a α β δ p : ℝ) (b : Fin 5 → ℂ) (y : ℝ) (j : Fin 2) (hε : 0 < ε)
    (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) (hyr : |y+δ| ≤ Real.pi*ε/3) :
    MemLp (configurationLine ε a α β δ p b y j) 2 :=
  (line_memLp ε a α β δ p b y hε ha hα hβ hw hy hyr j).comp_measurePreserving grouping_preserves_volume

def state (ε a α β δ p : ℝ) (b : Fin 5 → ℂ) (y : ℝ) (j : Fin 2) (hε : 0 < ε)
    (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) (hyr : |y+δ| ≤ Real.pi*ε/3) : Hilbert :=
  coordinates ε hε
    ((configurationLine_memLp ε a α β δ p b y j hε ha hα hβ hw hy hyr).toLp
      (configurationLine ε a α β δ p b y j))

theorem state_coe (ε a α β δ p : ℝ) (b : Fin 5 → ℂ) (y : ℝ) (j : Fin 2) (hε : 0 < ε)
    (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) (hyr : |y+δ| ≤ Real.pi*ε/3) :
    state ε a α β δ p b y j hε ha hα hβ hw hy hyr =ᵐ[volume]
      weightedFunction ε hε (configurationLine ε a α β δ p b y j) :=
  coordinates_toLp_coe ε hε _ _

theorem state_fourier (ε a α β δ p : ℝ) (b : Fin 5 → ℂ) (y : ℝ) (j : Fin 2) (hε : 0 < ε)
    (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) (hyr : |y+δ| ≤ Real.pi*ε/3) :
    coupledFourier ε hε (state ε a α β δ p b y j hε ha hα hβ hw hy hyr) =ᵐ[volume]
      𝓕 (euclideanLine ε a α β δ p b y j ∘ euclideanSplit) := by
  let f := configurationLine ε a α β δ p b y j
  have hf : MemLp f 2 := configurationLine_memLp ε a α β δ p b y j hε ha hα hβ hw hy hyr
  have hi : Integrable f := configurationLine_integrable ε a α β δ p b y j hε ha hα hβ hw hy hyr
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

theorem state_exponential_graph (ε a α β δ p : ℝ) (b : Fin 5 → ℂ) (h : ℝ) (j : Fin 2)
    (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hb : |-h/2|+|δ| ≤ Real.pi*ε/3) :
    (state ε a α β δ p b 0 j hε ha hα hβ hw
        (strip_pair ε δ |-h/2| 0 hb (by simp)).1 (strip_pair ε δ |-h/2| 0 hb (by simp)).2,
      state ε a α β δ p b (-h/2) j hε ha hα hβ hw
        (strip_pair ε δ |-h/2| (-h/2) hb le_rfl).1 (strip_pair ε δ |-h/2| (-h/2) hb le_rfl).2) ∈
        (longitudinalExponential ε hε h (1/2)).graph := by
  have h0 := strip_pair ε δ |-h/2| 0 hb (by simp)
  have hs := strip_pair ε δ |-h/2| (-h/2) hb le_rfl
  apply (longitudinal_exponential_graph ε hε h (1/2) _ _).mpr
  filter_upwards [state_fourier ε a α β δ p b (-h/2) j hε ha hα hβ hw hs.1 hs.2,
    state_fourier ε a α β δ p b 0 j hε ha hα hβ hw h0.1 h0.2] with k hk hf
  rw [hk,hf]
  have he : (1/2)*symbol h k = Real.pi*h*k 0 := by unfold symbol; ring
  rw [he]
  exact (full_fourier_shift ε a α β δ p b h hε ha hα hβ hw hb j k).symm

#print axioms configurationLine_flatten
#print axioms configurationLine_integrable
#print axioms configurationLine_memLp
#print axioms state_coe
#print axioms state_fourier
#print axioms state_exponential_graph
end
end UnifiedTheory.Audit.KFCausalMixedFieldCoherentSpectral
