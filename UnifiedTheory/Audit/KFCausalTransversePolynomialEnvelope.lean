/- Explicit polynomial bounds and transverse Gaussian moments supply
common envelopes before clock integration. No constant clock function
is treated as an L2 function on the real line. -/
import UnifiedTheory.Audit.KFCausalPolynomialRadiusEnvelope
import UnifiedTheory.Audit.KFCausalBoundedShearSourceContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalTransversePolynomialEnvelope
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalShearRadius (radius radius_one_le radius_positive)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (physicalGaussian)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments (physicalGaussian_memLp)
open UnifiedTheory.Audit.KFCausalGaussianAllRadiusMoments (gaussian_power_memLp radius_power_bound)
open UnifiedTheory.Audit.KFCausalImaginaryShearPathBounds
  (envelope width width_positive constant)

def evalCap (P : Polynomial ℂ) (K : ℝ) : ℝ :=
  ∑ n ∈ P.support, ‖P.coeff n‖*K^n

theorem evalCap_nonnegative (P : Polynomial ℂ) (K : ℝ) (hK : 0 ≤ K) :
    0 ≤ evalCap P K :=
  Finset.sum_nonneg (fun n _ => mul_nonneg (norm_nonneg _) (pow_nonneg hK n))

theorem eval_bound (P : Polynomial ℂ) (K R : ℝ) (hK : 0 ≤ K) (hR : 1 ≤ R)
    (z : ℂ) (hz : ‖z‖ ≤ K*R) : ‖P.eval z‖ ≤ evalCap P K*R^P.natDegree := by
  rw [Polynomial.eval_eq_sum,Polynomial.sum]
  apply (norm_sum_le _ _).trans
  rw [evalCap,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro n hn
  have hd : n ≤ P.natDegree := Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hn)
  have hp := pow_le_pow_left₀ (norm_nonneg z) hz n
  have hr := pow_le_pow_right₀ hR hd
  simp only [norm_mul,norm_pow,mul_pow] at *
  have hz' := hp.trans (mul_le_mul_of_nonneg_left hr (pow_nonneg hK n))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hz' (norm_nonneg (P.coeff n))

theorem radius_gaussian_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (n : ℕ) :
    MemLp (fun q : Transverse => ((radius q)^n:ℝ)*physicalGaussian α β q) 2 volume := by
  cases n with
  | zero => simpa using physicalGaussian_memLp α β hα hβ
  | succ n =>
    have hg := physicalGaussian_memLp α β hα hβ
    have hm := (hg.add (memLp_finset_sum Finset.univ
      (fun i _ => gaussian_power_memLp α β hα hβ i (2*(n+1))))).const_mul ((6:ℂ)^n)
    have hc : Continuous (fun q : Transverse => (((radius q)^(n+1):ℝ):ℂ)) := by
      unfold radius
      fun_prop
    apply hm.of_le (hc.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    filter_upwards [] with q
    have hs : 0 ≤ 1+∑ i : Fin 5, (q i)^(2*(n+1)) :=
      add_nonneg zero_le_one (Finset.sum_nonneg (fun i _ => by rw [pow_mul]; positivity))
    have he : physicalGaussian α β q+∑ i : Fin 5, (q i:ℂ)^(2*(n+1))*physicalGaussian α β q =
        ((1+∑ i : Fin 5, (q i)^(2*(n+1)):ℝ):ℂ)*physicalGaussian α β q := by
      simp only [Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_sum,
        Complex.ofReal_pow,add_mul,one_mul,Finset.sum_mul]
    change ‖(((radius q)^(n+1):ℝ):ℂ)*physicalGaussian α β q‖ ≤
      ‖(6:ℂ)^n*(physicalGaussian α β q+∑ i : Fin 5, (q i:ℂ)^(2*(n+1))*physicalGaussian α β q)‖
    rw [he]
    simp only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (radius_positive q).le,abs_of_nonneg hs]
    convert mul_le_mul_of_nonneg_right (radius_power_bound q n)
      (norm_nonneg (physicalGaussian α β q)) using 1
    ring

def gaussianEnvelope (α β : ℝ) (b : Fin 5 → ℂ) (n : ℕ) (q : Transverse) : ℝ :=
  (radius q)^n*‖envelope (fun _ => 1) α β b (0,q)‖

theorem gaussianEnvelope_nonnegative (α β : ℝ) (b : Fin 5 → ℂ) (n : ℕ) (q : Transverse) :
    0 ≤ gaussianEnvelope α β b n q :=
  mul_nonneg (pow_nonneg (radius_positive q).le n) (norm_nonneg _)

theorem gaussianEnvelope_continuous (α β : ℝ) (b : Fin 5 → ℂ) (n : ℕ) :
    Continuous (gaussianEnvelope α β b n) := by
  unfold gaussianEnvelope radius envelope physicalGaussian
  fun_prop

theorem gaussianEnvelope_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (b : Fin 5 → ℂ) (n : ℕ) :
    MemLp (gaussianEnvelope α β b n) 2 volume := by
  have hm := ((radius_gaussian_memLp (width α β) (width α β)
    (width_positive α β hα hβ) (width_positive α β hα hβ) n).const_mul (constant α β b:ℂ)).norm
  convert hm using 1
  funext q
  simp only [gaussianEnvelope,envelope,one_mul,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (radius_positive q).le n)]
  ring

#print axioms evalCap_nonnegative
#print axioms eval_bound
#print axioms radius_gaussian_memLp
#print axioms gaussianEnvelope_nonnegative
#print axioms gaussianEnvelope_continuous
#print axioms gaussianEnvelope_memLp
end
end UnifiedTheory.Audit.KFCausalTransversePolynomialEnvelope
