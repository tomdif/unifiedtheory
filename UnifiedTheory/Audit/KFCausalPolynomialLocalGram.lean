/- The local projected kernel is a Gram integral, including both charge
angles. Positivity is proved after charge averaging; no pointwise sign
of an individual cross-angle density is assumed. -/
import UnifiedTheory.Audit.KFCausalProjectedPolynomialLocalKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalPolynomialLocalGram
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalChargeResponseFubini (angles)
open UnifiedTheory.Audit.KFCausalPolynomialLocalKernel (Domain measure)
open UnifiedTheory.Audit.KFCausalProjectedPolynomialLocalKernel
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalPolynomialOrbitEnvelope (factor)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)

private theorem angle_pair_integrable (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g) :
    Integrable (fun t : ℝ × ℝ => star (f t.1)*g t.2) angles :=
  ((continuous_angle_memLp f hf).star.integrable (by norm_num)).mul_prod
    ((continuous_angle_memLp g hg).integrable (by norm_num))

theorem angle_pair_integral (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g) :
    (∫ t : ℝ × ℝ, star (f t.1)*g t.2 ∂angles) =
      star (∫ θ, f θ ∂angleMeasure)*(∫ θ, g θ ∂angleMeasure) := by
  change (∫ t : ℝ × ℝ, star (f t.1)*g t.2 ∂angleMeasure.prod angleMeasure) = _
  rw [integral_prod _ (angle_pair_integrable f g hf hg)]
  simp_rw [integral_const_mul]
  rw [integral_mul_const]
  congr 1
  exact integral_conj

variable (ε h : ℝ) (q k : Joint 2 4) (P Q : Polynomial ℂ) (n : Fin 3)

def angleFactor (s : ℝ) (x : Transverse) (θ : ℝ) : ℂ :=
  factor ε (-h/2) (groundWidth h) (neutralWidth h) (sourceCurve h q k θ)
    (amplitudeCurve h q k θ) P pointField n x s
def meanFactor (s : ℝ) (x : Transverse) : ℂ :=
  ∫ θ, angleFactor ε h q k P n s x θ ∂angleMeasure

variable (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)

include hε hb in
theorem angleFactor_continuous (s : ℝ) (x : Transverse) :
    Continuous (angleFactor ε h q k P n s x) :=
  KFCausalPolynomialKernelJointContinuity.factor_continuous ε (-h/2) (groundWidth h) (neutralWidth h)
    hε (shift_bound ε h hb) (fun _ : ℝ => s) (fun _ : ℝ => x)
    (sourceCurve h q k) (amplitudeCurve h q k) continuous_const continuous_const
    (sourceCurve_continuous h q k) (amplitudeCurve_continuous h q k) P pointField n

include hε hb in
theorem angle_value_integral (s : ℝ) (x : Transverse) :
    (∫ t : ℝ × ℝ, value ε h q k P Q n s (t,x) ∂angles) =
      star (meanFactor ε h q k P n s x)*meanFactor ε h q k Q n s x :=
  angle_pair_integral _ _ (angleFactor_continuous ε h q k P n hε hb s x)
    (angleFactor_continuous ε h q k Q n hε hb s x)

include hε hh hb in
theorem gram_integrable (s : ℝ) :
    Integrable (fun x => star (meanFactor ε h q k P n s x)*meanFactor ε h q k Q n s x) volume := by
  have hi := value_integrable ε h q k P Q n hε hh hb s
  change Integrable (value ε h q k P Q n s) (angles.prod volume) at hi
  exact hi.integral_prod_right.congr (Filter.Eventually.of_forall
    (angle_value_integral ε h q k P Q n hε hb s))

include hε hh hb in
theorem localKernel_gram (s : ℝ) :
    localKernel ε h q k P Q n s =
      ∫ x : Transverse, star (meanFactor ε h q k P n s x)*meanFactor ε h q k Q n s x := by
  change (∫ z : Domain, value ε h q k P Q n s z ∂angles.prod volume) = _
  rw [integral_prod_symm _ (value_integrable ε h q k P Q n hε hh hb s)]
  exact integral_congr_ae (Filter.Eventually.of_forall (angle_value_integral ε h q k P Q n hε hb s))

include hε hh hb in
theorem localKernel_conj (s : ℝ) :
    star (localKernel ε h q k P Q n s) = localKernel ε h q k Q P n s := by
  rw [localKernel_gram ε h q k P Q n hε hh hb,localKernel_gram ε h q k Q P n hε hh hb]
  change (starRingEnd ℂ) (∫ x : Transverse, _) = _
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [map_mul,starRingEnd_apply,star_star,mul_comm]

include hε hh hb in
omit Q in
theorem localKernel_self_nonnegative (s : ℝ) : 0 ≤ (localKernel ε h q k P P n s).re := by
  rw [localKernel_gram ε h q k P P n hε hh hb]
  have hi := gram_integrable ε h q k P P n hε hh hb s
  have he : (∫ x : Transverse, (star (meanFactor ε h q k P n s x)*meanFactor ε h q k P n s x).re) =
      (∫ x : Transverse, star (meanFactor ε h q k P n s x)*meanFactor ε h q k P n s x).re :=
    integral_re hi
  rw [← he]
  apply integral_nonneg
  intro x
  change 0 ≤ (star (meanFactor ε h q k P n s x)*meanFactor ε h q k P n s x).re
  simp only [Complex.star_def,Complex.mul_re,Complex.conj_re,Complex.conj_im]
  nlinarith [sq_nonneg (meanFactor ε h q k P n s x).re,
    sq_nonneg (meanFactor ε h q k P n s x).im]

include hε hh hb in
omit Q in
theorem localKernel_self_im (s : ℝ) : (localKernel ε h q k P P n s).im = 0 := by
  have he := congrArg Complex.im (localKernel_conj ε h q k P P n hε hh hb s)
  simp only [Complex.star_def,Complex.conj_im] at he
  linarith

#print axioms angle_pair_integral
#print axioms angleFactor_continuous
#print axioms angle_value_integral
#print axioms gram_integrable
#print axioms localKernel_gram
#print axioms localKernel_conj
#print axioms localKernel_self_nonnegative
#print axioms localKernel_self_im
end
end UnifiedTheory.Audit.KFCausalPolynomialLocalGram
