/- Every finite power of the complex shifted coordinate is square
integrable against the physical Gaussian profile. The neutral coordinate
contains its actual shear; no unchanged-neutral approximation is used. -/
import UnifiedTheory.Audit.KFCausalGaussianAllRadiusMoments
import UnifiedTheory.Audit.KFCausalPolynomialGaussianStates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalShiftedPolynomialMoments
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential (position profile exponent)
open UnifiedTheory.Audit.KFCausalShearRadius
open UnifiedTheory.Audit.KFCausalImaginaryShearInterpolation
open UnifiedTheory.Audit.KFCausalImaginaryShearPathBounds
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (timeScale_bound displacement_strip_bound)
open UnifiedTheory.Audit.KFCausalImaginaryShearCoefficient
  (displacement displacement_smooth half_shift_bound)
open UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile (clockAmplitude clockAmplitude_smooth)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (scale)

theorem position_radius_bound (r : ℂ) (M : ℝ) (hM : 0 ≤ M) (hr : ‖r‖ ≤ M)
    (q : Transverse) (i : Fin 5) : ‖position r q i‖ ≤ (4*M+5)*radius q := by
  have hR := (radius_positive q).le
  by_cases hi : i=4
  · subst i
    have hm : ‖(q 2:ℂ)+(q 3:ℂ)‖ ≤ 2*radius q := by
      simpa only [← Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs] using mix_abs_le q
    have hd : ‖r-1‖ ≤ M+1 :=
      (norm_sub_le r 1).trans (by simp only [norm_one]; linarith)
    have hp := mul_le_mul hd hm (norm_nonneg _) (by positivity : 0 ≤ M+1)
    simp only [position,ite_true]
    apply (norm_add_le _ _).trans
    simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs]
    nlinarith [coordinate_abs_le q 4]
  · simp only [position,if_neg hi,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    have hp := mul_le_mul hr (coordinate_abs_le q i) (abs_nonneg _) hM
    nlinarith [mul_nonneg hM hR]

theorem position_continuous (r : ℝ → ℂ) (hr : Continuous r) (i : Fin 5) :
    Continuous (fun x : Configuration => position (r x.1) x.2 i) := by
  unfold position
  split_ifs <;> fun_prop

theorem path_position_power_memLp (A D : ℝ → ℂ) (hA : ContDiff ℝ 1 A)
    (hAm : MemLp A 2 volume) (hD : ContDiff ℝ 1 D) (hDb : ∀ s, ‖D s‖ ≤ Real.pi/3)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (b : Fin 5 → ℂ)
    (t : Set.Icc (0:ℝ) 1) (i : Fin 5) (n : ℕ) :
    MemLp (fun x : Configuration =>
      (position (timeScale D t x.1) x.2 i)^n*path A D α β b t x) 2 volume := by
  let M := Real.exp ((Real.pi/3)/2)
  let K := 4*M+5
  have hM : 0 ≤ M := (Real.exp_pos _).le
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hc := ((position_continuous (timeScale D t)
    (timeScale_smooth D hD t).continuous i).pow n).mul (path_smooth A D hA hD α β b t).continuous
  apply ((KFCausalGaussianAllRadiusMoments.radius_envelope_memLp A hAm α β hα hβ b n).const_mul
    ((K^n:ℝ):ℂ)).of_le hc.aestronglyMeasurable
  filter_upwards [] with x
  have hp := pow_le_pow_left₀ (norm_nonneg _)
    (position_radius_bound _ M hM (timeScale_bound D hDb t x.1) x.2 i) n
  have hm := mul_le_mul hp (path_bound A D hDb α β hα hβ hw b t t.property x)
    (norm_nonneg _) (pow_nonneg (mul_nonneg hK (radius_positive x.2).le) n)
  simpa only [Pi.mul_apply,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,mul_pow,
    abs_of_nonneg hK,abs_of_nonneg (radius_positive x.2).le,mul_assoc,K] using hm

theorem shifted_position_power_memLp (ε a α β p h : ℝ) (b : Fin 5 → ℂ)
    (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hb : |h| ≤ 2*Real.pi*ε/3) (i : Fin 5) (n : ℕ) :
    MemLp (fun x : Configuration => (position (scale ε (-h/2) x.1) x.2 i)^n*
      profile (clockAmplitude ε a p (-h/2)) (scale ε (-h/2)) α β b x) 2 volume := by
  have hm := path_position_power_memLp (clockAmplitude ε a p (-h/2)) (displacement ε h)
    (clockAmplitude_smooth ε a p (-h/2) hε (half_shift_bound ε h hb))
    (KFCausalShiftedClockAmplitude.clockAmplitude_memLp ε a p (-h/2) hε ha (half_shift_bound ε h hb))
    (displacement_smooth ε h hε hb) (displacement_strip_bound ε h hε hb)
    α β hα hβ hw b ⟨1,by constructor <;> norm_num⟩ i n
  simpa only [path_one,timeScale,Complex.ofReal_one,one_mul,scale,
    KFCausalClockFloorShearBounds.complexScale,displacement] using hm

theorem circle_profile (A r : ℝ → ℂ) (α β : ℝ) (b : Fin 5 → ℂ)
    (i : Fin 5) (θ : ℝ) (x : Configuration) :
    profile A r α β (KFCausalPolynomialGaussianStates.circleSource b i θ) x =
      Complex.exp (position (r x.1) x.2 i*KFCausalSourceCircleCoefficients.circle θ)*
        profile A r α β b x := by
  have he : exponent α β (KFCausalPolynomialGaussianStates.circleSource b i θ) (r x.1) x.2 =
      exponent α β b (r x.1) x.2+
        position (r x.1) x.2 i*KFCausalSourceCircleCoefficients.circle θ := by
    simp only [exponent,KFCausalPolynomialGaussianStates.circleSource,
      add_mul,Finset.sum_add_distrib,ite_mul,zero_mul]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    ring
  rw [profile,he,Complex.exp_add]
  unfold profile
  ring

#print axioms position_radius_bound
#print axioms position_continuous
#print axioms path_position_power_memLp
#print axioms shifted_position_power_memLp
#print axioms circle_profile
end
end UnifiedTheory.Audit.KFCausalShiftedPolynomialMoments
