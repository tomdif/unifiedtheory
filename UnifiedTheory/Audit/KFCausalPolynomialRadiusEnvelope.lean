/- Finite polynomial growth is absorbed by the actual shifted Gaussian
envelope. This derives integrability for polynomial shear corrections;
the constants may depend on the polynomial and its degree. -/
import UnifiedTheory.Audit.KFCausalShiftedPolynomialMoments
import UnifiedTheory.Audit.KFCausalFieldInterpolationBounds
import UnifiedTheory.Audit.KFCausalGaussianShearSlopeBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalPolynomialRadiusEnvelope
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalShearRadius (radius radius_one_le radius_positive)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential (position direction profile profile_smooth)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift
  (relative relative_bound scale scale_smooth)
open UnifiedTheory.Audit.KFCausalImaginaryShearPathBounds (envelope)

def Growth (F : Configuration → ℂ) : Prop :=
  ∃ n : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖F x‖ ≤ M*(radius x.2)^n

theorem growth_const (c : ℂ) : Growth (fun _ => c) :=
  ⟨0,‖c‖,norm_nonneg _,fun _ => by simp⟩

theorem growth_add {F G : Configuration → ℂ} (hF : Growth F) (hG : Growth G) :
    Growth (fun x => F x+G x) := by
  obtain ⟨n,A,hA,hf⟩ := hF
  obtain ⟨m,B,hB,hg⟩ := hG
  refine ⟨n+m,A+B,add_nonneg hA hB,fun x => ?_⟩
  have hn := pow_le_pow_right₀ (radius_one_le x.2) (Nat.le_add_right n m)
  have hm := pow_le_pow_right₀ (radius_one_le x.2) (Nat.le_add_left m n)
  calc
    _ ≤ ‖F x‖+‖G x‖ := norm_add_le _ _
    _ ≤ A*(radius x.2)^(n+m)+B*(radius x.2)^(n+m) :=
      add_le_add ((hf x).trans (mul_le_mul_of_nonneg_left hn hA))
        ((hg x).trans (mul_le_mul_of_nonneg_left hm hB))
    _ = _ := by ring

theorem growth_mul {F G : Configuration → ℂ} (hF : Growth F) (hG : Growth G) :
    Growth (fun x => F x*G x) := by
  obtain ⟨n,A,hA,hf⟩ := hF
  obtain ⟨m,B,hB,hg⟩ := hG
  refine ⟨n+m,A*B,mul_nonneg hA hB,fun x => ?_⟩
  rw [norm_mul,pow_add]
  have hm := mul_le_mul (hf x) (hg x) (norm_nonneg _)
    (mul_nonneg hA (pow_nonneg (radius_positive x.2).le n))
  nlinarith only [hm]

theorem growth_pow {F : Configuration → ℂ} (hF : Growth F) (n : ℕ) :
    Growth (fun x => F x^n) := by
  induction n with
  | zero => simpa only [pow_zero] using growth_const 1
  | succ n ih => simpa only [pow_succ] using growth_mul ih hF

theorem growth_sum {ι : Type*} (s : Finset ι) (F : ι → Configuration → ℂ)
    (hF : ∀ i ∈ s, Growth (F i)) : Growth (fun x => ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using growth_const 0
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      growth_add (hF i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

theorem growth_polynomial {F : Configuration → ℂ} (hF : Growth F) (P : Polynomial ℂ) :
    Growth (fun x => P.eval (F x)) := by
  simpa only [Polynomial.eval_eq_sum,Polynomial.sum] using
    growth_sum P.support (fun n x => P.coeff n*F x^n)
      (fun n _ => growth_mul (growth_const (P.coeff n)) (growth_pow hF n))

theorem growth_position (r : ℝ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hr : ∀ s, ‖r s‖ ≤ M) (i : Fin 5) :
    Growth (fun x => position (r x.1) x.2 i) :=
  ⟨1,4*M+5,by positivity,fun x => by
    simpa only [pow_one] using
      KFCausalShiftedPolynomialMoments.position_radius_bound _ M hM (hr x.1) x.2 i⟩

theorem growth_direction (r : ℝ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hr : ∀ s, ‖r s‖ ≤ M) (i : Fin 5) :
    Growth (fun x => direction (r x.1) x.2 i) :=
  ⟨1,2*M,by positivity,fun x => by
    simpa only [pow_one] using
      KFCausalGaussianShearSlopeBounds.direction_bound _ M hM (hr x.1) x.2 i⟩

theorem growth_slope (r : ℝ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hr : ∀ s, ‖r s‖ ≤ M) (α β : ℝ) (b : Fin 5 → ℂ) :
    Growth (KFCausalRelativeGaussianDifferential.slope r α β b) :=
  ⟨1,KFCausalGaussianShearSlopeBounds.slopeConstant M α β b,
    KFCausalGaussianShearSlopeBounds.slopeConstant_nonnegative M α β hM b,fun x => by
      simpa only [pow_one] using
        KFCausalGaussianShearSlopeBounds.slope_bound r M hM hr α β b x⟩

theorem growth_field (l : Transverse →L[ℝ] ℝ) :
    Growth (fun x => (l x.2:ℂ)) :=
  ⟨1,‖l‖,norm_nonneg _,fun x => by
    simpa only [pow_one,Complex.norm_real,Real.norm_eq_abs] using
      KFCausalFieldInterpolationBounds.linear_bound l x.2⟩

theorem profile_bound (ε y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (A : ℝ → ℂ) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (b : Fin 5 → ℂ) (x : Configuration) :
    ‖profile A (scale ε y) α β b x‖ ≤ ‖envelope A α β b x‖ := by
  have hb (s : ℝ) : ‖relative ε y s‖ ≤ Real.pi/3 :=
    (relative_bound ε y s hε hy).trans ((div_le_iff₀ hε).mpr (by nlinarith only [hy]))
  have he := KFCausalImaginaryShearPathBounds.path_bound A (relative ε y) hb
    α β hα hβ hw b 1 (by constructor <;> norm_num) x
  simpa only [KFCausalImaginaryShearInterpolation.path_one,scale,
    KFCausalClockFloorShearBounds.complexScale] using he

theorem weighted_profile_memLp (ε y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (F : Configuration → ℂ) (hF : Continuous F) (hg : Growth F)
    (A : ℝ → ℂ) (hA : ContDiff ℝ 1 A) (hAm : MemLp A 2 volume)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (b : Fin 5 → ℂ) :
    MemLp (fun x => F x*profile A (scale ε y) α β b x) 2 volume := by
  obtain ⟨n,M,hM,hbound⟩ := hg
  apply ((KFCausalGaussianAllRadiusMoments.radius_envelope_memLp A hAm α β hα hβ b n).const_mul
    (M:ℂ)).of_le
      (hF.mul (profile_smooth A (scale ε y) hA (scale_smooth ε y hε hy) α β b).continuous).aestronglyMeasurable
  filter_upwards [] with x
  simp only [Pi.mul_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hM,abs_of_nonneg (pow_nonneg (radius_positive x.2).le n)]
  have hm := mul_le_mul (hbound x) (profile_bound ε y hε hy A α β hα hβ hw b x)
    (norm_nonneg _) (mul_nonneg hM (pow_nonneg (radius_positive x.2).le n))
  nlinarith only [hm]

#print axioms growth_const
#print axioms growth_add
#print axioms growth_mul
#print axioms growth_pow
#print axioms growth_sum
#print axioms growth_polynomial
#print axioms growth_position
#print axioms growth_direction
#print axioms growth_slope
#print axioms growth_field
#print axioms profile_bound
#print axioms weighted_profile_memLp
end
end UnifiedTheory.Audit.KFCausalPolynomialRadiusEnvelope
