/- Uniform imaginary-shift response of finite dyadic averages of the
actual radial strip family. At zero phase frequency the response is
8/(epsilon*N), independently of the smallest cutoff and hbar. -/
import UnifiedTheory.Audit.KFCausalRadialStripGeometry
import UnifiedTheory.Audit.KFCausalMixedRadialStripFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalMixedDyadicStripResponse
noncomputable section
open Set
open scoped BigOperators
open UnifiedTheory.Audit.KFCausalDyadicHeatCancellation (width)
open UnifiedTheory.Audit.KFCausalRadialStripGeometry
open UnifiedTheory.Audit.KFCausalComplexClockInverse
open UnifiedTheory.Audit.KFCausalClockInverseStripBounds (inverse_im_third_strip)
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian (third_strip_subset)
open UnifiedTheory.Audit.KFCausalMixedRadialStripFamily (family mixedTail)
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit (TailSpace)
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow (momentumScale)

def responseConstant (ε δ v : ℝ) (N : ℕ) : ℝ :=
  Real.exp (4*v^2/δ)*(8/(ε*(N:ℝ))+2*|v|/(ε*Real.sqrt δ))

theorem responseConstant_nonneg (ε δ v : ℝ) (N : ℕ) (hε : 0 < ε) :
    0 ≤ responseConstant ε δ v N := by unfold responseConstant; positivity

def average (ε δ v : ℝ) (N : ℕ) (p s r : ℝ) (q : ℂ) : ℂ :=
  KFCausalDyadicOscillatoryHeat.average δ v N
    (radius p s (complexInverse ε q)) (phase s r (complexInverse ε q))

theorem average_differentiable (ε δ v : ℝ) (N : ℕ) (p s r : ℝ) (hε : 0 < ε)
    (q : ℂ) (hq : |q.im| ≤ Real.pi*ε/3) : DifferentiableAt ℂ (average ε δ v N p s r) q := by
  have hi := (complexInverse_analytic ε hε q (third_strip_subset ε hε q hq)).differentiableAt.hasDerivAt
  exact (KFCausalDyadicOscillatoryHeat.average_derivative δ v N
    (fun x => radius p s (complexInverse ε x)) (fun x => phase s r (complexInverse ε x)) q _ _
    ((radius_derivative p s _).comp q hi) ((phase_derivative s r _).comp q hi)).differentiableAt

theorem average_derivative_bound (ε δ v : ℝ) (N : ℕ) (p s r : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hN : 0 < N) (q : ℂ) (hq : |q.im| ≤ Real.pi*ε/3) :
    ‖deriv (average ε δ v N p s r) q‖ ≤ responseConstant ε δ v N := by
  let z := complexInverse ε q
  let d := deriv (complexInverse ε) q
  have hz : |z.im| ≤ Real.pi/3 := inverse_im_third_strip ε hε q hq
  have hd : ‖d‖ ≤ 1/ε := inverse_derivative_bound ε hε q hq
  have hi := (complexInverse_analytic ε hε q (third_strip_subset ε hε q hq)).differentiableAt.hasDerivAt
  have hA := (radius_derivative p s z).comp q hi
  have hB := (phase_derivative s r z).comp q hi
  have hD := KFCausalDyadicOscillatoryHeat.average_derivative δ v N
    (fun x => radius p s (complexInverse ε x)) (fun x => phase s r (complexInverse ε x)) q _ _ hA hB
  have hR0 := radius_nonneg p s z hz
  have hw : ‖radiusSlope p s z*d‖ ≤ (2/ε)*(radius p s z).re := by
    rw [norm_mul]
    exact (mul_le_mul (radius_slope_bound p s z hz) hd (norm_nonneg _)
      (by positivity : 0 ≤ 2*(radius p s z).re)).trans_eq (by ring)
  have hu : ‖(2*shear s z)*d‖ ≤ (2/ε)*Real.sqrt (radius p s z).re := by
    rw [norm_mul,norm_mul]
    norm_num
    exact (mul_le_mul (mul_le_mul_of_nonneg_left (shear_bound p s z hz) (by norm_num : (0:ℝ) ≤ 2))
      hd (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hb := KFCausalDyadicOscillatoryHeat.slope_bound δ v (2/ε) (2/ε)
    (Real.sqrt (radius p s z).re) N hδ hN (by positivity) (by positivity) (Real.sqrt_nonneg _)
    (radius p s z) (phase s r z) (radiusSlope p s z*d) ((2*shear s z)*d)
    (Real.sq_sqrt hR0).le (phase_im_bound p s r z hz) hw hu
  change HasDerivAt (average ε δ v N p s r)
    (KFCausalDyadicOscillatoryHeat.slope δ v N (radius p s z) (phase s r z)
      (radiusSlope p s z*d) ((2*shear s z)*d)) q at hD
  rw [hD.deriv]
  exact hb.trans_eq (by unfold responseConstant; ring)

def familyAverage (ε h δ v : ℝ) (N : ℕ) (q : ℂ) (x : TailSpace) : ℂ :=
  (N:ℂ)⁻¹ * ∑ j ∈ Finset.range N, family ε h (width δ j) v q x

theorem familyAverage_eq (ε h δ v : ℝ) (N : ℕ) (q : ℂ) (x : TailSpace) :
    familyAverage ε h δ v N q x = average ε δ v N
      (momentumScale h*(mixedTail x).1 1) ((mixedTail x).2 2) ((mixedTail x).2 3) q := by
  simp only [familyAverage,family,KFCausalClockFloorMixedRadialStrip.multiplier,
    factor_packet,average,KFCausalDyadicOscillatoryHeat.average]

theorem family_derivative_bound (ε h δ v : ℝ) (N : ℕ)
    (hε : 0 < ε) (hδ : 0 < δ) (hN : 0 < N) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/3) (x : TailSpace) :
    ‖deriv (fun q => familyAverage ε h δ v N q x) q‖ ≤ responseConstant ε δ v N := by
  simp only [familyAverage_eq]
  exact average_derivative_bound ε δ v N _ _ _ hε hδ hN q hq

theorem family_vertical_difference (ε h δ v : ℝ) (N : ℕ)
    (hε : 0 < ε) (hδ : 0 < δ) (hN : 0 < N) (a b : ℝ)
    (hb : |b| ≤ 2*Real.pi*ε/3) (x : TailSpace) :
    ‖familyAverage ε h δ v N ((a:ℂ)+(-b/2:ℝ)*Complex.I) x-
      familyAverage ε h δ v N ((a:ℂ)+(b/2:ℝ)*Complex.I) x‖ ≤
      responseConstant ε δ v N*|b| := by
  have hc : Convex ℝ {q : ℂ | |q.im| ≤ Real.pi*ε/3} := by
    have h := (convex_Icc (-(Real.pi*ε/3)) (Real.pi*ε/3)).linear_preimage Complex.imLm
    convert h using 1
    ext q
    change (|q.im| ≤ Real.pi*ε/3) ↔ (-(Real.pi*ε/3) ≤ q.im ∧ q.im ≤ Real.pi*ε/3)
    exact abs_le
  have hm : ((a:ℂ)+(-b/2:ℝ)*Complex.I) ∈ {q : ℂ | |q.im| ≤ Real.pi*ε/3} := by
    simp only [Set.mem_setOf_eq,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
      Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add,abs_div,abs_neg]
    norm_num
    linarith
  have hp : ((a:ℂ)+(b/2:ℝ)*Complex.I) ∈ {q : ℂ | |q.im| ≤ Real.pi*ε/3} := by
    simp only [Set.mem_setOf_eq,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
      Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add,abs_div]
    norm_num
    linarith
  have hD (q : ℂ) (hq : |q.im| ≤ Real.pi*ε/3) :
      DifferentiableAt ℂ (fun q => familyAverage ε h δ v N q x) q := by
    simp only [familyAverage_eq]
    exact average_differentiable ε δ v N _ _ _ hε q hq
  have H := Convex.norm_image_sub_le_of_norm_deriv_le hD
    (fun q hq => family_derivative_bound ε h δ v N hε hδ hN q hq x) hc hp hm
  have he : ((a:ℂ)+(-b/2:ℝ)*Complex.I)-((a:ℂ)+(b/2:ℝ)*Complex.I) = -(b:ℂ)*Complex.I := by
    push_cast
    ring
  rw [he,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one] at H
  exact H

#print axioms responseConstant_nonneg
#print axioms average_differentiable
#print axioms average_derivative_bound
#print axioms familyAverage_eq
#print axioms family_derivative_bound
#print axioms family_vertical_difference

end
end UnifiedTheory.Audit.KFCausalMixedDyadicStripResponse
