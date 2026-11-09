/- A common transverse L2 envelope for polynomial ordered factors and
their clock derivatives, uniformly over a bounded source family.
The polynomial degree is fixed, and its constants remain explicit. -/
import UnifiedTheory.Audit.KFCausalTransversePolynomialEnvelope
import UnifiedTheory.Audit.KFCausalPolynomialKernelResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalPolynomialOrbitEnvelope
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (scale scale_bound)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential (position direction)
open UnifiedTheory.Audit.KFCausalPolynomialKernelResponse
  (weight weightDerivative transverse transverseDerivative)
open UnifiedTheory.Audit.KFCausalTransversePolynomialEnvelope
open UnifiedTheory.Audit.KFCausalShearRadius (radius radius_positive)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds (sourceSize)
open UnifiedTheory.Audit.KFCausalShearSourceOrbitContinuity (slopeCap)
open UnifiedTheory.Audit.KFCausalClockResponseTransport (clock)
open UnifiedTheory.Audit.KFCausalShiftedGaussianLongitudinalDifferential (inverseClock)
open UnifiedTheory.Audit.KFCausalImaginaryShearPathBounds (envelope)

def scaleCap (ε y : ℝ) : ℝ := Real.exp (|y|/(2*ε))
def positionCap (ε y : ℝ) : ℝ := 4*scaleCap ε y+5
def clockSlope (ε y s : ℝ) : ℂ := (clock ε s:ℂ)*inverseClock ε y s-1

def factor (ε y α β : ℝ) (b : Fin 5 → ℂ) (C : ℂ) (P : Polynomial ℂ)
    (l : Transverse →L[ℝ] ℝ) (n : ℕ) (q : Transverse) (s : ℝ) : ℂ :=
  (l q:ℂ)^n*transverse ε y α β b C P q s

def factorDerivative (ε y α β : ℝ) (b : Fin 5 → ℂ) (C : ℂ) (P : Polynomial ℂ)
    (l : Transverse →L[ℝ] ℝ) (n : ℕ) (q : Transverse) (s : ℝ) : ℂ :=
  (l q:ℂ)^n*transverseDerivative ε y α β b C P q s

def amplitudeEnvelope (ε y α β : ℝ) (c : Fin 5 → ℂ) (P : Polynomial ℂ)
    (l : Transverse →L[ℝ] ℝ) (n : ℕ) (q : Transverse) : ℝ :=
  ‖l‖^n*evalCap P (positionCap ε y)*gaussianEnvelope α β c (n+P.natDegree) q

def correctionEnvelope (ε y α β : ℝ) (c : Fin 5 → ℂ) (P : Polynomial ℂ)
    (l : Transverse →L[ℝ] ℝ) (n : ℕ) (q : Transverse) : ℝ :=
  ‖l‖^n*(evalCap P.derivative (positionCap ε y)*(2*scaleCap ε y)*
      gaussianEnvelope α β c (n+P.derivative.natDegree+1) q+
    evalCap P (positionCap ε y)*slopeCap (scaleCap ε y) α β c*
      gaussianEnvelope α β c (n+P.natDegree+1) q)

theorem factor_derivative (ε y α β : ℝ) (b : Fin 5 → ℂ) (C : ℂ) (P : Polynomial ℂ)
    (l : Transverse →L[ℝ] ℝ) (n : ℕ) (q : Transverse) (s : ℝ)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    HasDerivAt (factor ε y α β b C P l n q) (factorDerivative ε y α β b C P l n q s) s :=
  (KFCausalPolynomialKernelResponse.transverse_derivative ε y α β b C P q s hε hy).const_mul _

theorem amplitudeEnvelope_nonnegative (ε y α β : ℝ) (c : Fin 5 → ℂ) (P : Polynomial ℂ)
    (l : Transverse →L[ℝ] ℝ) (n : ℕ) (q : Transverse) :
    0 ≤ amplitudeEnvelope ε y α β c P l n q :=
  mul_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) n)
    (evalCap_nonnegative P _ (by unfold positionCap scaleCap; positivity)))
    (gaussianEnvelope_nonnegative α β c _ q)

theorem correctionEnvelope_nonnegative (ε y α β : ℝ) (c : Fin 5 → ℂ) (P : Polynomial ℂ)
    (l : Transverse →L[ℝ] ℝ) (n : ℕ) (q : Transverse) :
    0 ≤ correctionEnvelope ε y α β c P l n q := by
  have hM : 0 ≤ scaleCap ε y := (Real.exp_pos _).le
  have hK : 0 ≤ positionCap ε y := by unfold positionCap; positivity
  have hp := evalCap_nonnegative P (positionCap ε y) hK
  have hpd := evalCap_nonnegative P.derivative (positionCap ε y) hK
  have hs := KFCausalGaussianShearSlopeBounds.slopeConstant_nonnegative (scaleCap ε y) α β hM
    (fun _ => ((1+sourceSize c:ℝ):ℂ))
  change 0 ≤ slopeCap (scaleCap ε y) α β c at hs
  have he := gaussianEnvelope_nonnegative α β c (n+P.natDegree+1) q
  have hed := gaussianEnvelope_nonnegative α β c (n+P.derivative.natDegree+1) q
  unfold correctionEnvelope
  positivity

theorem amplitudeEnvelope_continuous (ε y α β : ℝ) (c : Fin 5 → ℂ) (P : Polynomial ℂ)
    (l : Transverse →L[ℝ] ℝ) (n : ℕ) :
    Continuous (amplitudeEnvelope ε y α β c P l n) :=
  continuous_const.mul (gaussianEnvelope_continuous α β c _)

theorem correctionEnvelope_continuous (ε y α β : ℝ) (c : Fin 5 → ℂ) (P : Polynomial ℂ)
    (l : Transverse →L[ℝ] ℝ) (n : ℕ) :
    Continuous (correctionEnvelope ε y α β c P l n) :=
  continuous_const.mul ((continuous_const.mul (gaussianEnvelope_continuous α β c _)).add
    (continuous_const.mul (gaussianEnvelope_continuous α β c _)))

theorem amplitudeEnvelope_memLp (ε y α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (c : Fin 5 → ℂ) (P : Polynomial ℂ) (l : Transverse →L[ℝ] ℝ) (n : ℕ) :
    MemLp (amplitudeEnvelope ε y α β c P l n) 2 volume :=
  (gaussianEnvelope_memLp α β hα hβ c _).const_mul _

theorem correctionEnvelope_memLp (ε y α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (c : Fin 5 → ℂ) (P : Polynomial ℂ) (l : Transverse →L[ℝ] ℝ) (n : ℕ) :
    MemLp (correctionEnvelope ε y α β c P l n) 2 volume :=
  (((gaussianEnvelope_memLp α β hα hβ c _).const_mul _).add
    ((gaussianEnvelope_memLp α β hα hβ c _).const_mul _)).const_mul _

variable (ε y α β : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
  (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
  (b c : Fin 5 → ℂ) (hb : sourceSize b ≤ sourceSize c) (C : ℂ) (hC : ‖C‖ ≤ 1)
  (P : Polynomial ℂ) (l : Transverse →L[ℝ] ℝ) (n : ℕ) (q : Transverse) (s : ℝ)
local notation "M" => scaleCap ε y
local notation "K" => positionCap ε y
local notation "r" => scale ε y
local notation "G" => KFCausalGaussianKernelResponse.transverse ε y α β b C q s
local notation "E" => ‖envelope (fun _ => 1) α β c (0,q)‖

include hε hy hα hβ hw hb hC in
private theorem base_bound : ‖G‖ ≤ E := by
  have he := (KFCausalPolynomialRadiusEnvelope.profile_bound ε y hε hy
    (fun _ => 1) α β hα hβ hw b (s,q)).trans
      (KFCausalBoundedShearSourceContinuity.envelope_bound (fun _ => 1) α β hα hβ b c hb (s,q))
  calc
    _ = ‖C‖*‖KFCausalRelativeGaussianDifferential.profile (fun _ => 1) r α β b (s,q)‖ := norm_mul _ _
    _ ≤ 1*E := mul_le_mul hC he (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

include hε hy in
private theorem polynomial_bound :
    ‖weight ε y P q s‖ ≤ evalCap P K*(radius q)^P.natDegree :=
  eval_bound P K (radius q) (by unfold positionCap scaleCap; positivity)
    (KFCausalShearRadius.radius_one_le q) _ (KFCausalShiftedPolynomialMoments.position_radius_bound
      _ M (Real.exp_pos _).le (scale_bound ε y s hε hy) q 4)

include hε hy hα hβ hw hb hC in
theorem factor_bound : ‖factor ε y α β b C P l n q s‖ ≤ amplitudeEnvelope ε y α β c P l n q := by
  have hp := polynomial_bound ε y hε hy P q s
  have hg := base_bound ε y α β hε hy hα hβ hw b c hb C hC q s
  have hl := pow_le_pow_left₀ (norm_nonneg (l q))
    (show ‖l q‖ ≤ ‖l‖*radius q by simpa only [Real.norm_eq_abs] using
      KFCausalFieldInterpolationBounds.linear_bound l q) n
  have hw0 : 0 ≤ evalCap P K*(radius q)^P.natDegree :=
    mul_nonneg (evalCap_nonnegative P K (by unfold positionCap scaleCap; positivity))
      (pow_nonneg (radius_positive q).le _)
  have hm := mul_le_mul hl (mul_le_mul hp hg (norm_nonneg _) hw0)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (pow_nonneg (mul_nonneg (norm_nonneg _) (radius_positive q).le) n)
  simpa only [factor,transverse,norm_mul,norm_pow,Complex.norm_real,
    amplitudeEnvelope,gaussianEnvelope,mul_pow,pow_add,mul_assoc,mul_left_comm,mul_comm] using hm

include hε hy hα hβ hw hb hC in
theorem factorDerivative_bound :
    ‖factorDerivative ε y α β b C P l n q s‖ ≤
      ‖clockSlope ε y s‖*correctionEnvelope ε y α β c P l n q := by
  have hM : 0 ≤ M := (Real.exp_pos _).le
  have hK : 0 ≤ K := by unfold positionCap; positivity
  have hr (t : ℝ) : ‖r t‖ ≤ M := scale_bound ε y t hε hy
  have hp := polynomial_bound ε y hε hy P q s
  have hpd := polynomial_bound ε y hε hy P.derivative q s
  have hd := KFCausalGaussianShearSlopeBounds.direction_bound _ M hM (hr s) q 4
  have hs := (KFCausalGaussianShearSlopeBounds.slope_bound r M hM hr α β b (s,q)).trans
    (mul_le_mul_of_nonneg_right
      (KFCausalBoundedShearSourceContinuity.slope_cap_bound M α β hM b c hb) (radius_positive q).le)
  have hg := base_bound ε y α β hε hy hα hβ hw b c hb C hC q s
  have hcap := evalCap_nonnegative P K hK
  have hcapd := evalCap_nonnegative P.derivative K hK
  have hr0 := (radius_positive q).le
  have hs0 := KFCausalGaussianShearSlopeBounds.slopeConstant_nonnegative M α β hM
    (fun _ => ((1+sourceSize c:ℝ):ℂ))
  change 0 ≤ slopeCap M α β c at hs0
  have hc : ‖P.derivative.eval (position (r s) q 4)*direction (r s) q 4+
      weight ε y P q s*KFCausalRelativeGaussianDifferential.slope r α β b (s,q)‖ ≤
      evalCap P.derivative K*(radius q)^P.derivative.natDegree*(2*M*radius q)+
        evalCap P K*(radius q)^P.natDegree*(slopeCap M α β c*radius q) := by
    apply (norm_add_le _ _).trans
    simp only [norm_mul]
    exact add_le_add (mul_le_mul hpd hd (norm_nonneg _) (by positivity))
      (mul_le_mul hp hs (norm_nonneg _) (by positivity))
  have hl := pow_le_pow_left₀ (norm_nonneg (l q))
    (show ‖l q‖ ≤ ‖l‖*radius q by simpa only [Real.norm_eq_abs] using
      KFCausalFieldInterpolationBounds.linear_bound l q) n
  have hinner := mul_le_mul hl (mul_le_mul hc hg (norm_nonneg _) (by positivity))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
  have he : factorDerivative ε y α β b C P l n q s =
      clockSlope ε y s*((l q:ℂ)^n*
        ((P.derivative.eval (position (r s) q 4)*direction (r s) q 4+
          weight ε y P q s*KFCausalRelativeGaussianDifferential.slope r α β b (s,q))*G)) := by
    unfold factorDerivative transverseDerivative weightDerivative
      KFCausalGaussianKernelResponse.transverseSlope clockSlope
    ring
  rw [he,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  convert hinner using 1
  · simp only [norm_mul,norm_pow,Complex.norm_real]
  · simp only [correctionEnvelope,gaussianEnvelope,pow_add,pow_one,mul_pow]
    ring

#print axioms factor_derivative
#print axioms amplitudeEnvelope_nonnegative
#print axioms correctionEnvelope_nonnegative
#print axioms amplitudeEnvelope_continuous
#print axioms correctionEnvelope_continuous
#print axioms amplitudeEnvelope_memLp
#print axioms correctionEnvelope_memLp
#print axioms factor_bound
#print axioms factorDerivative_bound
end
end UnifiedTheory.Audit.KFCausalPolynomialOrbitEnvelope
