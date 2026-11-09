/- Actual shear graphs for the existing complex-shifted Gaussian states.
The hypotheses are the previously proved strip and Gaussian-width bounds;
no shear graph or clock-derivative L2 hypothesis is added. -/
import UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalShiftedGaussianShearDomain
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalReconstruction (shearDerivative)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential (profile)
open UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral (gaussianState)

variable (ε a α β p y : ℝ) (b : Fin 5 → ℂ)
variable (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
variable (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3)
include hε ha hα hβ hw hy

theorem shear_memLp :
    MemLp (shearDerivative (profile (clockAmplitude ε a p y) (scale ε y) α β b)) 2 volume :=
  KFCausalRelativeGaussianShearDomain.profile_shear_memLp (scale ε y)
    (scale_smooth ε y hε hy).continuous (Real.exp (|y|/(2*ε))) (Real.exp_pos _).le
    (fun s => scale_bound ε y s hε hy) (clockAmplitude ε a p y)
    (clockAmplitude_smooth ε a p y hε hy) (scale_smooth ε y hε hy) α β b
    (profile_memLp ε a α β p y b hε ha hα hβ hw hy)
    (profile_quadratic_memLp ε a α β p y b hε ha hα hβ hw hy)

def shearOutput (h : ℝ) : Hilbert :=
  (-Complex.I*(h:ℂ)) • (shear_memLp ε a α β p y b hε ha hα hβ hw hy).toLp
    (shearDerivative (profile (clockAmplitude ε a p y) (scale ε y) α β b))

theorem gaussianState_eq_toLp :
    gaussianState ε a α β p b y hε ha hα hβ hw hy =
      (profile_memLp ε a α β p y b hε ha hα hβ hw hy).toLp
        (profile (clockAmplitude ε a p y) (scale ε y) α β b) := by
  apply Lp.ext
  exact (gaussianState_profile ε a α β p y b hε ha hα hβ hw hy).trans
    (profile_memLp ε a α β p y b hε ha hα hβ hw hy).coeFn_toLp.symm

theorem gaussianState_shear_graph (h : ℝ) (hh : h ≠ 0) :
    (gaussianState ε a α β p b y hε ha hα hβ hw hy,
      shearOutput ε a α β p y b hε ha hα hβ hw hy h) ∈ (shearMomentum h).graph := by
  rw [gaussianState_eq_toLp]
  exact KFCausalShearMaximalDifferential.graph_of_shear_differential h hh _
    (KFCausalRelativeGaussianDifferential.profile_smooth _ _
      (clockAmplitude_smooth ε a p y hε hy) (scale_smooth ε y hε hy) α β b)
    (profile_memLp ε a α β p y b hε ha hα hβ hw hy)
    (shear_memLp ε a α β p y b hε ha hα hβ hw hy)

theorem gaussianState_shear_domain (h : ℝ) (hh : h ≠ 0) :
    gaussianState ε a α β p b y hε ha hα hβ hw hy ∈ (shearMomentum h).domain :=
  LinearPMap.mem_domain_of_mem_graph (gaussianState_shear_graph ε a α β p y b hε ha hα hβ hw hy h hh)

theorem shearOutput_coe (h : ℝ) :
    shearOutput ε a α β p y b hε ha hα hβ hw hy h =ᵐ[volume] fun x =>
      (-Complex.I*(h:ℂ))*(KFCausalRelativeGaussianDifferential.slope (scale ε y) α β b x+1)*
        profile (clockAmplitude ε a p y) (scale ε y) α β b x := by
  let hd := shear_memLp ε a α β p y b hε ha hα hβ hw hy
  filter_upwards [Lp.coeFn_smul (-Complex.I*(h:ℂ)) (hd.toLp _),hd.coeFn_toLp] with x hx hy'
  change ((-Complex.I*(h:ℂ)) • hd.toLp _) x = _
  rw [hx]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hy',KFCausalRelativeGaussianDifferential.profile_shear _ _
    (clockAmplitude_smooth ε a p y hε hy) (scale_smooth ε y hε hy)]
  ring

#print axioms shear_memLp
#print axioms gaussianState_eq_toLp
#print axioms gaussianState_shear_graph
#print axioms gaussianState_shear_domain
#print axioms shearOutput_coe
end
end UnifiedTheory.Audit.KFCausalShiftedGaussianShearDomain
