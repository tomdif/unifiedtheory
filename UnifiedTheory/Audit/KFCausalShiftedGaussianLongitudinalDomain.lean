/- Actual longitudinal momentum graphs for sourced Gaussian states at
every point of the existing closed imaginary strip. No strict-strip or
extra momentum-domain hypothesis is imposed. -/
import UnifiedTheory.Audit.KFCausalShiftedGaussianLongitudinalDifferential
import UnifiedTheory.Audit.KFCausalGaussianClockMoment

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalShiftedGaussianLongitudinalDomain
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential (profile profile_smooth slope)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (scale scale_smooth scale_bound)
open UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile
open UnifiedTheory.Audit.KFCausalShiftedGaussianLongitudinalDifferential
open UnifiedTheory.Audit.KFCausalClockFloorDifferentialMomentum (differential differential_graph)
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum (longitudinalMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral (gaussianState shiftedOutput)

variable (ε a α β p y : ℝ) (b : Fin 5 → ℂ)
variable (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
variable (hy : |y| ≤ Real.pi*ε/3)
local notation "F" => profile (clockAmplitude ε a p y) (scale ε y) α β b

include hε ha hα hβ hw hy in
theorem differential_memLp : MemLp (differential ε F) 2 volume := by
  have hf := profile_memLp ε a α β p y b hε ha hα hβ hw hy
  have hq := profile_quadratic_memLp ε a α β p y b hε ha hα hβ hw hy
  have hs := KFCausalRelativeGaussianShearDomain.slope_memLp (scale ε y)
    (scale_smooth ε y hε hy).continuous (Real.exp (|y|/(2*ε))) (Real.exp_pos _).le
    (fun s => scale_bound ε y s hε hy) F hf hq α β b
  have hi := KFCausalShearPolynomialMoments.clock_mul_memLp (inverseClock ε y)
    (inverseClock_continuous ε y hε hy) (1/ε) (by positivity)
    (fun s => inverseClock_bound ε y s hε hy)
  have hm := KFCausalGaussianClockMoment.profile_moment_memLp ε a α β p y b hε ha hα hβ hw hy
  convert (((hi F hf).const_mul ((p:ℂ)*Complex.I)).sub
    (hm.const_mul (2*(a:ℂ)))).add (hi _ hs) using 1
  funext x
  rw [profile_differential ε a α β p y b hε hy x]
  simp only [Pi.add_apply,Pi.sub_apply]
  ring

def output (h : ℝ) : Hilbert := (-Complex.I*(h:ℂ)) •
  (differential_memLp ε a α β p y b hε ha hα hβ hw hy).toLp (differential ε F)

theorem gaussianState_graph (h : ℝ) (hh : h ≠ 0) :
    (gaussianState ε a α β p b y hε ha hα hβ hw hy,
      output ε a α β p y b hε ha hα hβ hw hy h) ∈ (longitudinalMomentum ε hε h).graph := by
  have hf := profile_memLp ε a α β p y b hε ha hα hβ hw hy
  have he : gaussianState ε a α β p b y hε ha hα hβ hw hy = hf.toLp F :=
    Lp.ext ((gaussianState_profile ε a α β p y b hε ha hα hβ hw hy).trans hf.coeFn_toLp.symm)
  rw [he]
  exact differential_graph ε hε h hh F hf (differential_memLp ε a α β p y b hε ha hα hβ hw hy)
    ((profile_smooth _ _ (clockAmplitude_smooth ε a p y hε hy)
      (scale_smooth ε y hε hy) α β b).differentiable (by norm_num))

theorem gaussianState_domain (h : ℝ) (hh : h ≠ 0) :
    gaussianState ε a α β p b y hε ha hα hβ hw hy ∈ (longitudinalMomentum ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph (gaussianState_graph ε a α β p y b hε ha hα hβ hw hy h hh)

omit α β p y b hα hβ hw hy in
theorem shiftedOutput_domain (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (k : Joint 2 4) :
    shiftedOutput ε a h hε ha hh hb k ∈ (longitudinalMomentum ε hε h).domain := by
  apply (longitudinalMomentum ε hε h).domain.smul_mem
  exact gaussianState_domain ε a _ _ _ (-h/2) _ hε ha
    (KFCausalChargeGaussianGeometry.groundWidth_positive h hh)
    (KFCausalClockFloorInvariantTrial.neutralWidth_positive h hh)
    (KFCausalClockFloorInvariantTrial.neutralWidth_bound h)
    (KFCausalClockFloorShiftedOutput.shift_bound ε h hb) h hh

#print axioms differential_memLp
#print axioms gaussianState_graph
#print axioms gaussianState_domain
#print axioms shiftedOutput_domain
end
end UnifiedTheory.Audit.KFCausalShiftedGaussianLongitudinalDomain
