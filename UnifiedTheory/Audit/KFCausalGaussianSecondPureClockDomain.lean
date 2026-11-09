/- Actual second vacuum and matter outputs lie in the pure-clock domain.
The mixed spectral domains and the bounded inverse-clock graph supply
these conclusions; no composition-domain premise is introduced. -/
import UnifiedTheory.Audit.KFCausalMixedFieldPureClockDomain
import UnifiedTheory.Audit.KFCausalGaussianMatterSquare
import UnifiedTheory.Audit.KFCausalClockFloorPureClockInverseHalf

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalGaussianSecondPureClockDomain
noncomputable section
open MeasureTheory
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalClockFloorPureClockInverseHalf (inverse_momentum_domain)
open KFCausalShiftedGaussianPhysicalProfile (clockAmplitude)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalRelativeGaussianDifferential (profile)
open KFCausalClockFloorCoherentSpectral (gaussianState)

theorem gaussian_domain (ε a α β p y : ℝ) (b : Fin 5 → ℂ)
    (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) (h : ℝ) (hh : h ≠ 0) :
    gaussianState ε a α β p b y hε ha hα hβ hw hy ∈ (pureMomentum ε hε h).domain := by
  let F := profile (clockAmplitude ε a p y) (scale ε y) α β b
  have hf := KFCausalShiftedGaussianPhysicalProfile.profile_memLp ε a α β p y b hε ha hα hβ hw hy
  have hd : MemLp (KFCausalClockFloorPureClockDerivative.differential ε F) 2 volume := by
    simpa only [one_mul] using KFCausalMixedFieldPureClockDomain.weightedGaussian_differential_memLp
      ε a α β p y b hε ha hα hβ hw hy (fun _ => 1) (KFCausalRadialMultipliers.controlled_const 1)
  have he : gaussianState ε a α β p b y hε ha hα hβ hw hy = hf.toLp F :=
    Lp.ext ((KFCausalShiftedGaussianPhysicalProfile.gaussianState_profile ε a α β p y b hε ha hα hβ hw hy).trans
      hf.coeFn_toLp.symm)
  rw [he]
  exact KFCausalClockFloorPureClockDifferential.differential_domain ε hε h hh F hf hd
    ((KFCausalRelativeGaussianDifferential.profile_smooth _ _
      (KFCausalShiftedGaussianPhysicalProfile.clockAmplitude_smooth ε a p y hε hy)
      (KFCausalClockFloorRelativeShift.scale_smooth ε y hε hy) α β b).differentiable (by norm_num))

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α)
  (hβ : 0 < β) (hw : 32*β ≤ α) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi*ε/3)
include hh

theorem vacuum_spectral_domain (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) :
    KFCausalGaussianVacuumSquare.doubleOutput ε a α β hε ha hα hβ hw C p b h hb ∈
      (pureMomentum ε hε h).domain :=
  (pureMomentum ε hε h).domain.smul_mem C
    (gaussian_domain ε a α β p (-(2*h)/2) b hε ha hα hβ hw
      (KFCausalClockFloorShiftedOutput.shift_bound ε (2*h) (KFCausalGaussianVacuumSquare.double_strip ε h hb)) h hh)

theorem vacuum_square_domain (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) :
    KFCausalGaussianVacuumSquare.squareOutput ε a α β hε ha hα hβ hw C p b h hb ∈
      (pureMomentum ε hε h).domain :=
  inverse_momentum_domain ε hε h hh _ (vacuum_spectral_domain ε a α β hε ha hα hβ hw h hh hb C p b)

theorem matter_spectral_domain (j : Fin 2) :
    KFCausalGaussianMatterSquare.spectralOutput ε a α β hε ha hα hβ hw h hb j ∈
      (pureMomentum ε hε h).domain :=
  KFCausalMixedFieldPureClockDomain.state_domain ε a α β (-h/2) (-h/2) j hε ha hα hβ hw _ _ h hh

theorem matter_square_domain (j : Fin 2) :
    KFCausalGaussianMatterSquare.output ε a α β hε ha hα hβ hw h hb j ∈
      (pureMomentum ε hε h).domain :=
  inverse_momentum_domain ε hε h hh _ (matter_spectral_domain ε a α β hε ha hα hβ hw h hh hb j)

#print axioms gaussian_domain
#print axioms vacuum_spectral_domain
#print axioms vacuum_square_domain
#print axioms matter_spectral_domain
#print axioms matter_square_domain
end
end UnifiedTheory.Audit.KFCausalGaussianSecondPureClockDomain
