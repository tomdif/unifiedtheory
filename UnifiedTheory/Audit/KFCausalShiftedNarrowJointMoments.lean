/- The joint Fourier Gaussian has all transverse radial moments in L2,
with any proved L2 clock coefficient. Controlled polynomial multipliers
therefore preserve the actual joint bound, including the neutral shear. -/
import UnifiedTheory.Audit.KFCausalShiftedNarrowJointGaussian
import UnifiedTheory.Audit.KFCausalRadialMultipliers

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalShiftedNarrowJointMoments
noncomputable section
open MeasureTheory
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalClockFloorShearBounds (physicalGaussian)
open KFCausalShearRadius (radius radius_positive)
open KFCausalGaussianAllRadiusMoments (radius_power_bound gaussian_power_memLp)
open KFCausalShiftedNarrowJointGaussian (gaussian jointWidth sourceBound gaussian_bound gaussian_continuous jointWidth_positive sourceBound_positive)

theorem radial_memLp (F : Configuration → ℂ) (hF : MemLp F 2 volume)
    (hM : ∀ (i : Fin 5) (j : ℕ), MemLp (fun x => (x.2 i:ℂ)^j*F x) 2 volume) (n : ℕ) :
    MemLp (fun x => ((radius x.2)^n:ℝ)*F x) 2 volume := by
  cases n with
  | zero => simpa using hF
  | succ n =>
    have hm := (hF.add (memLp_finset_sum Finset.univ (fun i _ => hM i (2*(n+1))))).const_mul ((6:ℂ)^n)
    have hc : Continuous (fun x : Configuration => (((radius x.2)^(n+1):ℝ):ℂ)) := by
      unfold radius
      fun_prop
    apply hm.of_le (hc.aestronglyMeasurable.mul hF.aestronglyMeasurable)
    filter_upwards [] with x
    have hs : 0 ≤ 1+∑ i : Fin 5, (x.2 i)^(2*(n+1)) :=
      add_nonneg zero_le_one (Finset.sum_nonneg (fun i _ => by rw [pow_mul]; positivity))
    have he : F x+∑ i : Fin 5, (x.2 i:ℂ)^(2*(n+1))*F x =
        ((1+∑ i : Fin 5, (x.2 i)^(2*(n+1)):ℝ):ℂ)*F x := by
      simp only [Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_sum,Complex.ofReal_pow,
        add_mul,one_mul,Finset.sum_mul]
    change ‖(((radius x.2)^(n+1):ℝ):ℂ)*F x‖ ≤
      ‖(6:ℂ)^n*(F x+∑ i : Fin 5, (x.2 i:ℂ)^(2*(n+1))*F x)‖
    rw [he]
    simp only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (radius_positive x.2).le,abs_of_nonneg hs]
    convert mul_le_mul_of_nonneg_right (radius_power_bound x.2 n) (norm_nonneg (F x)) using 1
    ring

theorem isotropic_radial_memLp (γ : ℝ) (hγ : 0 < γ) (c : ℝ → ℂ) (hc : MemLp c 2 volume) (n : ℕ) :
    MemLp (fun x : Configuration => ((radius x.2)^n:ℝ)*(c x.1*physicalGaussian γ γ x.2)) 2 volume := by
  apply radial_memLp _
    (KFCausalPhysicalGaussianDerivative.configuration_product_memLp c _ hc
      (KFCausalPhysicalGaussianMoments.physicalGaussian_memLp γ γ hγ hγ))
  intro i j
  convert KFCausalPhysicalGaussianDerivative.configuration_product_memLp c _ hc
    (gaussian_power_memLp γ γ hγ hγ i j) using 1
  funext x
  ring

theorem joint_radial_memLp (α β ε y : ℝ) (b : ℂ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (c : ℝ → ℂ) (hc : MemLp c 2 volume) (n : ℕ) :
    MemLp (fun x : Configuration => ((radius x.2)^n:ℝ)*(c x.1*gaussian α β ε y b x)) 2 volume := by
  have hrad : Continuous (fun x : Configuration => (((radius x.2)^n:ℝ):ℂ)) := by
    unfold radius
    fun_prop
  apply ((isotropic_radial_memLp (jointWidth α β) (jointWidth_positive α β hα hβ) c hc n).const_mul
    (sourceBound α β b:ℂ)).of_le
    (hrad.aestronglyMeasurable.mul (hc.aestronglyMeasurable.comp_fst.mul
      (gaussian_continuous α β ε y b hε hy).aestronglyMeasurable))
  filter_upwards [] with x
  have hb := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (gaussian_bound α β ε y b hα hβ hw hε hy x) (norm_nonneg (c x.1)))
    (norm_nonneg ((((radius x.2)^n:ℝ):ℂ)))
  simpa only [Pi.mul_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (sourceBound_positive α β b),mul_assoc,mul_left_comm,mul_comm] using hb

theorem controlled_joint_memLp (α β ε y : ℝ) (b : ℂ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (c : ℝ → ℂ) (hc : MemLp c 2 volume) (U : Configuration → ℂ)
    (hU : KFCausalRadialMultipliers.Controlled U) :
    MemLp (fun x => U x*(c x.1*gaussian α β ε y b x)) 2 volume :=
  KFCausalRadialMultipliers.controlled_memLp U _ hU
    (joint_radial_memLp α β ε y b hα hβ hw hε hy c hc)

#print axioms radial_memLp
#print axioms isotropic_radial_memLp
#print axioms joint_radial_memLp
#print axioms controlled_joint_memLp
end
end UnifiedTheory.Audit.KFCausalShiftedNarrowJointMoments
