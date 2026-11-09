/- The bounded analytic multiplier estimate is transported through the full
six-dimensional Fourier unitary to the actual physical exponential graph. -/
import UnifiedTheory.Audit.KFCausalClockFloorAnalyticMultiplier
import UnifiedTheory.Audit.KFCausalClockFloorCoherentFullFourier
import UnifiedTheory.Audit.KFCausalClockFloorExponential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorMultiplierGraph
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalClockFloorAnalyticMultiplier
open UnifiedTheory.Audit.KFCausalClockFourierFubini
open UnifiedTheory.Audit.KFCausalClockFloorGaussianL1
  (pairGrouping pairGrouping_preserves_volume tailGrouping_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorFourierCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorFourierMultiplier
open UnifiedTheory.Audit.KFCausalClockFloorExponential
open UnifiedTheory.Audit.KFCausalL2FourierIntegral

def euclideanLine (F : ℂ → ℂ) (ε a α β p : ℝ) (b : Fin 5 → ℂ) (y : ℝ)
    (z : ℝ × TailSpace) : ℂ := line F ε a α β p b y (pairGrouping z)

def spectralLine (F : ℂ → ℂ) (ε a α β p : ℝ) (b : Fin 5 → ℂ) (y : ℝ) : Space → ℂ :=
  euclideanLine F ε a α β p b y ∘ euclideanSplit

variable (F : ℂ → ℂ) (ε a α β p M : ℝ) (b : Fin 5 → ℂ)
  (hε : 0 < ε)
  (hF : ∀ q : ℂ, |q.im| ≤ Real.pi*ε/3 → AnalyticAt ℂ F q)
  (hM : 0 ≤ M) (hB : ∀ q : ℂ, |q.im| ≤ Real.pi*ε/3 → ‖F q‖ ≤ M)
  (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)

include hε hF in
theorem euclideanLine_continuous (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) :
    Continuous (euclideanLine F ε a α β p b y) :=
  (line_continuous F ε a α β p b hε hF y hy).comp
    (continuous_fst.prodMk (tailGrouping_continuous.comp continuous_snd))

include hε hF hB ha hα hβ hw in
theorem euclideanLine_integrable (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) :
    Integrable (euclideanLine F ε a α β p b y) :=
  pairGrouping_preserves_volume.integrable_comp_of_integrable
    (line_integrable F ε a α β p M b hε hF hB ha hα hβ hw y hy)

include hε hF hB ha hα hβ hw in
theorem spectralLine_integrable (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) :
    Integrable (spectralLine F ε a α β p b y) :=
  euclideanSplit_preserves_volume.integrable_comp_of_integrable
    (euclideanLine_integrable F ε a α β p M b hε hF hB ha hα hβ hw y hy)

include hε hF hM hB ha hα hβ hw in
theorem spectralLine_memLp (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) :
    MemLp (spectralLine F ε a α β p b y) 2 :=
  ((line_memLp F ε a α β p M b hε hF hM hB ha hα hβ hw y hy).comp_measurePreserving
    pairGrouping_preserves_volume).comp_measurePreserving euclideanSplit_preserves_volume

include hε hF hM hB ha hα hβ hw in
theorem full_fourier_shift (hbar : ℝ) (hh : |hbar| ≤ 2*Real.pi*ε/3) (k : Space) :
    (Real.exp (Real.pi*hbar*k 0):ℂ)*(𝓕 (spectralLine F ε a α β p b 0)) k =
      (𝓕 (spectralLine F ε a α β p b (-hbar/2))) k := by
  have h0 : |(0:ℝ)| ≤ Real.pi*ε/3 := by simp; positivity
  have hs : |-hbar/2| ≤ Real.pi*ε/3 := by
    rw [abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  have hpoint (q : ℝ) (z : TailSpace) :
      (Real.exp (Real.pi*hbar*q):ℂ)*clockFourier (euclideanLine F ε a α β p b 0) (q,z) =
        clockFourier (euclideanLine F ε a α β p b (-hbar/2)) (q,z) :=
    exponential_fourier_identity F ε a α β p M b hε hF hM hB ha hα hβ hw hbar hh (pairGrouping (q,z)).2 q
  unfold spectralLine
  rw [fourier_iterated _ (euclideanLine_continuous F ε a α β p b hε hF 0 h0)
      (euclideanLine_integrable F ε a α β p M b hε hF hB ha hα hβ hw 0 h0),
    fourier_iterated _ (euclideanLine_continuous F ε a α β p b hε hF (-hbar/2) hs)
      (euclideanLine_integrable F ε a α β p M b hε hF hB ha hα hβ hw (-hbar/2) hs)]
  simp only [Real.fourier_eq,Circle.smul_def,smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [← hpoint]
  ring

def physicalState (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) : Hilbert :=
  coordinates ε hε (euclideanPullback.symm
    ((spectralLine_memLp F ε a α β p M b hε hF hM hB ha hα hβ hw y hy).toLp _))

theorem physicalState_fourier (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) :
    coupledFourier ε hε (physicalState F ε a α β p M b hε hF hM hB ha hα hβ hw y hy)
      =ᵐ[volume] 𝓕 (spectralLine F ε a α β p b y) := by
  change (Lp.fourierTransformₗᵢ Space ℂ) (euclideanPullback
    ((coordinates ε hε).symm (coordinates ε hε (euclideanPullback.symm _)))) =ᵐ[volume] _
  rw [LinearIsometryEquiv.symm_apply_apply,LinearIsometryEquiv.apply_symm_apply]
  exact fourier_toLp_coe _ (spectralLine_integrable F ε a α β p M b hε hF hB ha hα hβ hw y hy)
    (spectralLine_memLp F ε a α β p M b hε hF hM hB ha hα hβ hw y hy)

theorem physicalState_half_graph (hbar : ℝ) (hh : |hbar| ≤ 2*Real.pi*ε/3)
    (h0 : |(0:ℝ)| ≤ Real.pi*ε/3) (hs : |-hbar/2| ≤ Real.pi*ε/3) :
    (physicalState F ε a α β p M b hε hF hM hB ha hα hβ hw 0 h0,
      physicalState F ε a α β p M b hε hF hM hB ha hα hβ hw (-hbar/2) hs) ∈
      (longitudinalExponential ε hε hbar (1/2)).graph := by
  apply (longitudinal_exponential_graph ε hε hbar (1/2) _ _).mpr
  filter_upwards [physicalState_fourier F ε a α β p M b hε hF hM hB ha hα hβ hw 0 h0,
    physicalState_fourier F ε a α β p M b hε hF hM hB ha hα hβ hw (-hbar/2) hs] with k hk hl
  rw [hk,hl,← full_fourier_shift F ε a α β p M b hε hF hM hB ha hα hβ hw hbar hh k]
  congr 3
  unfold symbol
  ring

#print axioms euclideanLine_continuous
#print axioms euclideanLine_integrable
#print axioms spectralLine_integrable
#print axioms spectralLine_memLp
#print axioms full_fourier_shift
#print axioms physicalState_fourier
#print axioms physicalState_half_graph

end
end UnifiedTheory.Audit.KFCausalClockFloorMultiplierGraph
