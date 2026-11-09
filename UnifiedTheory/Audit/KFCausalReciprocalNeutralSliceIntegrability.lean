/- Actual transverse integrability at every fixed clock value, including
arbitrary neutral exponential-polynomial profiles and unequal reciprocal
widths. This supplies the slice hypotheses for the joint positive form. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralOrderedProfile
import UnifiedTheory.Audit.KFCausalReciprocalNeutralKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralSliceIntegrability
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalReciprocalSqueezeFlow (squeeze squeezeEquiv squeeze_field)
open KFCausalReciprocalSqueezePullback (squeezeCLM squeezeCLM_det)
open KFCausalRelativeGaussianDifferential (position)
open KFCausalReciprocalGaussianCoordinates (exponent)
open KFCausalReciprocalNeutralOrderedProfile (position_rescale polynomial_rescale)
open KFCausalReciprocalNeutralPackets (rescaledPolynomial)
open KFCausalNeutralExponentialProfiles (exponentialProfile profileFactor)
open KFCausalReciprocalNeutralKernel (density)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalQuarticPlaneDomination (potential)

theorem squeeze_volume (t : ℝ) :
    Measure.map (squeeze t) volume =
      ENNReal.ofReal |(Real.exp t)⁻¹| • (volume : Measure Transverse) := by
  have hd : LinearMap.det (squeezeCLM t).toLinearMap ≠ 0 := by
    change (squeezeCLM t).det ≠ 0
    rw [squeezeCLM_det]
    exact Real.exp_ne_zero _
  have hm := Real.map_linearMap_volume_pi_eq_smul_volume_pi hd
  change Measure.map (squeeze t) volume =
    ENNReal.ofReal |((squeezeCLM t).det)⁻¹| • (volume : Measure Transverse) at hm
  rwa [squeezeCLM_det] at hm

theorem squeeze_memLp (t : ℝ) (f : Transverse → ℂ) (hf : MemLp f 2 volume) :
    MemLp (fun q => f (squeeze t q)) 2 volume := by
  have hm : MemLp f 2 (Measure.map (squeeze t) volume) := by
    rw [squeeze_volume]
    exact hf.smul_measure (by finiteness)
  exact hm.comp_of_map (squeezeEquiv t).toContinuousLinearEquiv.continuous.measurable.aemeasurable

def factor (α β w : ℝ) (r b : ℂ) (P : Polynomial ℂ) (n : ℕ) (q : Transverse) : ℂ :=
  (pointField q:ℂ)^n*Complex.exp (exponent α β w r q)*exponentialProfile b 1 P (position r q 4)

theorem factor_squeeze (α β t : ℝ) (r b : ℂ) (P : Polynomial ℂ) (n : ℕ) (q : Transverse) :
    profileFactor α (β*Real.exp (-2*t)) r
      (exponentialProfile ((Real.exp (-t):ℂ)*b) 1 (rescaledPolynomial t P)) n (squeeze t q) =
        (Real.exp t:ℂ)^n*factor α β (Real.exp (2*t)) r b P n q := by
  simp only [profileFactor,KFCausalReciprocalGaussianOutputs.exponent_squeeze,
    exponentialProfile,one_mul,polynomial_rescale,squeeze_field,Complex.ofReal_mul,mul_pow]
  have he : ((Real.exp (-t):ℂ)*b)*position r (squeeze t q) 4 = b*position r q 4 := by
    rw [mul_assoc,mul_comm b,← mul_assoc,position_rescale]
    ring
  rw [he]
  unfold factor exponentialProfile
  ring

theorem factor_memLp (α β ε y s w : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hwidth : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hw : 1 ≤ w)
    (b : ℂ) (P : Polynomial ℂ) (n : ℕ) :
    MemLp (factor α β w (scale ε y s) b P n) 2 volume := by
  let t := Real.log w/2
  have ht : 0 ≤ t := div_nonneg (Real.log_nonneg hw) (by norm_num)
  have hβ' : 0 < β*Real.exp (-2*t) := mul_pos hβ (Real.exp_pos _)
  have he : Real.exp (2*t) = w := by
    rw [show 2*t=Real.log w by dsimp [t]; ring,Real.exp_log (by linarith)]
  have hwidth' : 32*(β*Real.exp (-2*t)) ≤ α := by
    have hb := mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.mpr (by linarith : -2*t ≤ 0)) hβ.le
    nlinarith
  have hm := squeeze_memLp t _
    (KFCausalNeutralExponentialProfiles.exponentialProfile_factor_memLp
      α (β*Real.exp (-2*t)) ε y s hα hβ' hwidth' hε hy
      ((Real.exp (-t):ℂ)*b) 1 (rescaledPolynomial t P) n)
  have hn : (Real.exp t:ℂ)^n ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
  have hi := hm.const_mul ((Real.exp t:ℂ)^n)⁻¹
  simpa only [factor_squeeze,he,inv_mul_cancel_left₀ hn] using hi

theorem density_decomposition (α β w v : ℝ) (r b d : ℂ) (P Q : Polynomial ℂ) (q : Transverse) :
    density α β w v r (exponentialProfile b 1 P) (exponentialProfile d 1 Q) q =
      conj (factor α β w r b P 0 q)*factor α β v r d Q 0 q+
        conj (factor α β w r b P 1 q)*factor α β v r d Q 1 q/2+
        conj (factor α β w r b P 2 q)*factor α β v r d Q 2 q/4 := by
  simp only [density,KFCausalReciprocalCrossKernel.density,factor,potential,
    pow_zero,pow_one,one_mul,map_mul,map_pow,Complex.conj_ofReal]
  push_cast
  ring

theorem density_integrable (α β ε y s w v : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hwidth : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (hw : 1 ≤ w) (hv : 1 ≤ v) (b d : ℂ) (P Q : Polynomial ℂ) :
    Integrable (density α β w v (scale ε y s) (exponentialProfile b 1 P) (exponentialProfile d 1 Q)) := by
  have hi (n : ℕ) : Integrable (fun q =>
      conj (factor α β w (scale ε y s) b P n q)*factor α β v (scale ε y s) d Q n q) := by
    simpa only [Complex.star_def] using
      (factor_memLp α β ε y s w hα hβ hwidth hε hy hw b P n).star.integrable_mul
        (factor_memLp α β ε y s v hα hβ hwidth hε hy hv d Q n)
  apply (((hi 0).add ((hi 1).div_const 2)).add ((hi 2).div_const 4)).congr
  exact Filter.Eventually.of_forall (fun q => (density_decomposition α β w v _ b d P Q q).symm)

#print axioms squeeze_volume
#print axioms squeeze_memLp
#print axioms factor_squeeze
#print axioms factor_memLp
#print axioms density_decomposition
#print axioms density_integrable
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralSliceIntegrability
