/- Exact pure-clock differential of the mixed field/Gaussian profile.
The two shifted scales and the half-density term are retained. -/
import UnifiedTheory.Audit.KFCausalMixedFieldPhysicalProfile
import UnifiedTheory.Audit.KFCausalShiftedGaussianPureDifferential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalMixedFieldPureClockDifferential
noncomputable section
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalMixedFieldPhysicalProfile (field profile)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalShiftedGaussianLongitudinalDifferential (inverseClock)
open KFCausalShiftedGaussianPureDifferential (realInverse)
open KFCausalCanonicalClockDerivative (clockDerivative)
open KFCausalClockFloorPureClockDerivative (differential)

def fieldSlope (ε y : ℝ) (x : Configuration) : ℂ :=
  3*((((Real.exp x.1+ε:ℝ):ℂ)*inverseClock ε y x.1-1)*scale ε y x.1/2)*
    ((x.2 2:ℂ)+(x.2 3:ℂ))
def fieldRate (ε y : ℝ) (x : Configuration) : ℂ :=
  (3/2:ℂ)*(inverseClock ε y x.1-realInverse ε x.1)*scale ε y x.1*
    ((x.2 2:ℂ)+(x.2 3:ℂ))

theorem field_derivative (ε y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (x : Configuration) :
    HasDerivAt (fun s => field (scale ε y s) x.2) (fieldSlope ε y x) x.1 := by
  exact ((((KFCausalShiftedGaussianLongitudinalDifferential.scale_derivative ε y x.1 hε hy).const_mul 3).sub_const 2).mul_const
     ((x.2 2:ℂ)+(x.2 3:ℂ))).const_add (x.2 4:ℂ)

theorem field_normalized_derivative (ε y : ℝ) (hε : 0 < ε) (x : Configuration) :
    realInverse ε x.1*fieldSlope ε y x = fieldRate ε y x := by
  have hc : ((Real.exp x.1+ε:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  unfold fieldSlope fieldRate realInverse
  field_simp [hc]

theorem profile_differential (ε a α β δ y : ℝ) (k : ℕ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (hyr : |y+δ| ≤ Real.pi*ε/3) (x : Configuration) :
    differential ε (profile ε a α β δ y k) x =
      (k:ℂ)*field (scale ε y x.1) x.2^(k-1)*fieldRate ε y x*
        KFCausalRelativeGaussianDifferential.profile
          (KFCausalShiftedGaussianPhysicalProfile.clockAmplitude ε a 0 (y+δ)) (scale ε (y+δ)) α β 0 x+
      field (scale ε y x.1) x.2^k * differential ε
        (KFCausalRelativeGaussianDifferential.profile
          (KFCausalShiftedGaussianPhysicalProfile.clockAmplitude ε a 0 (y+δ)) (scale ε (y+δ)) α β 0) x := by
  let F := KFCausalRelativeGaussianDifferential.profile
    (KFCausalShiftedGaussianPhysicalProfile.clockAmplitude ε a 0 (y+δ)) (scale ε (y+δ)) α β 0
  have hs := KFCausalRelativeGaussianDifferential.profile_smooth _ _
    (KFCausalShiftedGaussianPhysicalProfile.clockAmplitude_smooth ε a 0 (y+δ) hε hyr)
    (KFCausalClockFloorRelativeShift.scale_smooth ε (y+δ) hε hyr) α β 0
  have hF := (hs.differentiable (by norm_num) x).hasFDerivAt.comp_hasDerivAt x.1
    ((hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2))
  change HasDerivAt (fun s => F (s,x.2)) (clockDerivative F x) x.1 at hF
  have hd := ((field_derivative ε y hε hy x).pow k).mul hF
  have hp := ((KFCausalMixedFieldPhysicalProfile.profile_smooth ε a α β δ y k hε hy hyr).differentiable
    (by norm_num) x).hasFDerivAt.comp_hasDerivAt x.1
      ((hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2))
  change HasDerivAt (fun s => profile ε a α β δ y k (s,x.2))
    (clockDerivative (profile ε a α β δ y k) x) x.1 at hp
  have he := hp.unique hd
  change clockDerivative (profile ε a α β δ y k) x =
    (k:ℂ)*field (scale ε y x.1) x.2^(k-1)*fieldSlope ε y x*F x+
      field (scale ε y x.1) x.2^k*clockDerivative F x at he
  unfold differential
  rw [he]
  change realInverse ε x.1*(_)+_*(field (scale ε y x.1) x.2^k*F x) =
    _+field (scale ε y x.1) x.2^k*(realInverse ε x.1*clockDerivative F x+_*F x)
  linear_combination (k:ℂ)*field (scale ε y x.1) x.2^(k-1)*F x*
    (field_normalized_derivative ε y hε x)

#print axioms field_derivative
#print axioms field_normalized_derivative
#print axioms profile_differential
end
end UnifiedTheory.Audit.KFCausalMixedFieldPureClockDifferential
