/- All polynomial radius moments of the actual interpolation envelope.
These derive the extra domination needed for field-weighted strong
derivatives; they are not bounds by Hamiltonian energy. -/
import UnifiedTheory.Audit.KFCausalGaussianFourthMoments
import Mathlib.Algebra.Order.Chebyshev

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalGaussianAllRadiusMoments
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (physicalGaussian)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments
open UnifiedTheory.Audit.KFCausalGaussianSliceDomain
open UnifiedTheory.Audit.KFCausalChargeGaussianProducts (pi_product_memLp)
open UnifiedTheory.Audit.KFCausalImaginaryShearPathBounds
open UnifiedTheory.Audit.KFCausalPhysicalGaussianDerivative (configuration_product_memLp)
open UnifiedTheory.Audit.KFCausalShearRadius (radius radius_positive)

theorem scalar_power_memLp (b : ℝ) (hb : 0 < b) (n : ℕ) :
    MemLp (fun x : ℝ => (x:ℂ)^n*gaussian (b:ℂ) x) 2 volume := by
  have hc := (Complex.continuous_ofReal.pow n).mul (gaussian_continuous (b:ℂ))
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  have hi := integrable_rpow_mul_exp_neg_mul_sq (by positivity : 0 < 2*b)
    (show (-1:ℝ) < ((2*n:ℕ):ℝ) by exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg _))
  have he (x : ℝ) : ‖(x:ℂ)^n*gaussian (b:ℂ) x‖^2 = x^(2*n)*Real.exp (-(2*b)*x^2) := by
    simp only [norm_mul,mul_pow,norm_pow,Complex.norm_real,Real.norm_eq_abs,
      gaussian_norm_square,Complex.ofReal_re]
    rw [← pow_mul,Nat.mul_comm n 2,pow_mul,sq_abs,← pow_mul]
  simpa only [Pi.mul_apply,he,Real.rpow_natCast] using hi

theorem gaussian_power_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (i : Fin 5) (n : ℕ) :
    MemLp (fun x : Transverse => (x i:ℂ)^n*physicalGaussian α β x) 2 volume := by
  let f : Fin 5 → ℝ → ℂ := fun j t =>
    (if j=i then (t:ℂ)^n else 1)*gaussian (widths α β j:ℂ) t
  have hc : ∀ j, Continuous (f j) := by
    intro j
    by_cases h : j=i
    · simpa only [f,if_pos h] using (Complex.continuous_ofReal.pow n).mul (gaussian_continuous (widths α β j:ℂ))
    · simpa only [f,if_neg h,one_mul] using gaussian_continuous (widths α β j:ℂ)
  have hm : ∀ j, MemLp (f j) 2 volume := by
    intro j
    by_cases h : j=i
    · simpa only [f,if_pos h] using scalar_power_memLp (widths α β j) (widths_positive α β hα hβ j) n
    · simpa only [f,if_neg h,one_mul] using
        (gaussian_memLp_iff (widths α β j:ℂ)).mpr (widths_positive α β hα hβ j)
  have he : (fun x : Transverse => (x i:ℂ)^n*physicalGaussian α β x) =
      fun x : Transverse => ∏ j, f j (x j) := by
    funext x
    simp only [f,Finset.prod_mul_distrib,physicalGaussian_product]
    simp
  rw [he]
  exact pi_product_memLp 5 f hc hm

theorem envelope_power_memLp (A : ℝ → ℂ) (hA : MemLp A 2 volume) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (b : Fin 5 → ℂ) (i : Fin 5) (n : ℕ) :
    MemLp (fun x : Configuration => (x.2 i:ℂ)^n*envelope A α β b x) 2 volume := by
  convert (configuration_product_memLp A _ hA
    (gaussian_power_memLp _ _ (width_positive α β hα hβ) (width_positive α β hα hβ) i n)).const_mul
      (constant α β b:ℂ) using 1
  funext x
  unfold envelope
  ring

theorem radius_power_bound (q : Transverse) (n : ℕ) :
    (radius q)^(n+1) ≤ (6:ℝ)^n*(1+∑ i : Fin 5, (q i)^(2*(n+1))) := by
  let v : Fin 6 → ℝ := Fin.cases 1 (fun i => (q i)^2)
  have hv : ∀ i ∈ (Finset.univ : Finset (Fin 6)), 0 ≤ v i := by
    intro i _
    refine Fin.cases (by norm_num [v]) (fun j => ?_) i
    exact sq_nonneg (q j)
  have he := pow_sum_le_card_mul_sum_pow hv n
  simpa only [v,Fin.sum_univ_succ,Fin.cases_zero,Fin.cases_succ,
    Finset.card_univ,Fintype.card_fin,Nat.cast_ofNat,
    one_pow,← pow_mul,radius] using he

theorem radius_envelope_memLp (A : ℝ → ℂ) (hA : MemLp A 2 volume) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (b : Fin 5 → ℂ) (n : ℕ) :
    MemLp (fun x : Configuration => ((radius x.2)^n:ℝ)*envelope A α β b x) 2 volume := by
  cases n with
  | zero => simpa using envelope_memLp A hA α β hα hβ b
  | succ n =>
    have hm := ((envelope_memLp A hA α β hα hβ b).add
      (memLp_finset_sum Finset.univ (fun i _ => envelope_power_memLp A hA α β hα hβ b i (2*(n+1))))).const_mul ((6:ℂ)^n)
    have hc : Continuous (fun x : Configuration => (((radius x.2)^(n+1):ℝ):ℂ)) := by
      unfold radius
      fun_prop
    apply hm.of_le (hc.aestronglyMeasurable.mul (envelope_memLp A hA α β hα hβ b).aestronglyMeasurable)
    filter_upwards [] with x
    have hs : 0 ≤ 1+∑ i : Fin 5, (x.2 i)^(2*(n+1)) :=
      add_nonneg zero_le_one (Finset.sum_nonneg (fun i _ => by rw [pow_mul]; positivity))
    have he : envelope A α β b x+∑ i : Fin 5, (x.2 i:ℂ)^(2*(n+1))*envelope A α β b x =
        ((1+∑ i : Fin 5, (x.2 i)^(2*(n+1)):ℝ):ℂ)*envelope A α β b x := by
      simp only [Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_sum,Complex.ofReal_pow,add_mul,one_mul,Finset.sum_mul]
    change ‖(((radius x.2)^(n+1):ℝ):ℂ)*envelope A α β b x‖ ≤
      ‖(6:ℂ)^n*(envelope A α β b x+∑ i : Fin 5, (x.2 i:ℂ)^(2*(n+1))*envelope A α β b x)‖
    rw [he]
    simp only [norm_mul,norm_pow,
      Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (radius_positive x.2).le,abs_of_nonneg hs]
    convert mul_le_mul_of_nonneg_right (radius_power_bound x.2 n) (norm_nonneg (envelope A α β b x)) using 1
    ring

#print axioms scalar_power_memLp
#print axioms gaussian_power_memLp
#print axioms envelope_power_memLp
#print axioms radius_power_bound
#print axioms radius_envelope_memLp
end
end UnifiedTheory.Audit.KFCausalGaussianAllRadiusMoments
