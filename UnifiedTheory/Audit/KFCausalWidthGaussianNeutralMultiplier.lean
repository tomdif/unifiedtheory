/- Neutral polynomial and source factors, with the actual inverse-clock
frequency phase, remain bounded against the two-shear Gaussian margin.
The bound is uniform in coordinates and angle, but can depend on the
chosen source and polynomial. -/
import UnifiedTheory.Audit.KFCausalComplexPolynomialGaussianAbsorption
import UnifiedTheory.Audit.KFCausalWidthGaussianHolomorphicContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalWidthGaussianNeutralMultiplier
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalComplexClockInverse (complexInverse)
open KFCausalComplexShearPerturbation (Space flow rotatedFlow)
open KFCausalPhysicalReciprocalNormalization (normalize coupling)
open KFCausalNormalizedComplexRotation (rotationIsometry)
open KFCausalWidthGaussianHolomorphicQuotient (baselineVector targetVector)
open KFCausalTwoShearClockQuotient (shift)
open KFCausalClockFloorCoherentStrip (clockPhase)
open KFCausalComplexPolynomialGaussianAbsorption (source_polynomial_bound)

def neutral (ε h α w c η : ℝ) (q : ℂ) (x : Joint 2 4) : ℂ :=
  targetVector ε h α w c η q x 4/(Real.sqrt (α/32):ℂ)

def neutralScale (α : ℝ) : ℝ := (20/17)/Real.sqrt (α/32)

def polynomialCap (α : ℝ) (b : ℂ) (P : Polynomial ℂ) : ℝ :=
  KFCausalTransversePolynomialEnvelope.evalCap P (neutralScale α)*
    Real.exp (((P.natDegree:ℝ)+‖b‖*neutralScale α)^2/(4*(78/289:ℝ)))

def multiplier (ε h a α W w c η : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (q : ℂ) (x : Joint 2 4) : ℂ :=
  (C*clockPhase p (complexInverse ε (shift h q)))*
    (P.eval (neutral ε h α w c η q x)*Complex.exp (b*neutral ε h α w c η q x))*
    KFCausalWidthGaussianHolomorphicQuotient.multiplier ε h a α W w c η q x

def bound (ε h a α W : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ) : ℝ :=
  ‖C‖*Real.exp (|p| *Real.pi/3)*polynomialCap α b P*
    (4*W*ε⁻¹*Real.exp (|h|/ε+4*a*h^2))

theorem target_norm_bound (ε h α w c η : ℝ) (hε : 0 < ε) (hh : |h| ≤ ε/10)
    (hα : 0 < α) (hw : 1 ≤ w) (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    ‖targetVector ε h α w c η q x‖ ≤
      (20/17:ℝ)*‖baselineVector ε α w c (q.re:ℂ) x‖ := by
  let V : Space ≃ₗᵢ[ℂ] Space := LinearIsometryEquiv.refl ℂ Space
  have he : rotatedFlow V (coupling α w) (complexInverse ε q-complexInverse ε (q.re:ℂ))
      (baselineVector ε α w c (q.re:ℂ) x)=baselineVector ε α w c q x := by
    change flow (coupling α w) (complexInverse ε q-complexInverse ε (q.re:ℂ))
      (flow (coupling α w) (complexInverse ε (q.re:ℂ)) (normalize α w c x)) = _
    rw [KFCausalComplexShearGroup.flow_compose,sub_add_cancel]
    rfl
  have hd := KFCausalComplexShearPerturbation.ordered_difference (rotationIsometry η) V
    (coupling α w) (KFCausalPhysicalReciprocalNormalization.coupling_bound α w hα hw)
    (complexInverse ε (shift h q)-complexInverse ε q)
    (complexInverse ε q-complexInverse ε (q.re:ℂ))
    (KFCausalTwoShearClockQuotient.two_increment_bound ε h hε hh q hq)
    (baselineVector ε α w c (q.re:ℂ) x)
  rw [he] at hd
  change ‖targetVector ε h α w c η q x-baselineVector ε α w c (q.re:ℂ) x‖ ≤ _ at hd
  have ht := norm_add_le (targetVector ε h α w c η q x-baselineVector ε α w c (q.re:ℂ) x)
    (baselineVector ε α w c (q.re:ℂ) x)
  rw [sub_add_cancel] at ht
  linarith

theorem neutral_norm_bound (ε h α w c η : ℝ) (hε : 0 < ε) (hh : |h| ≤ ε/10)
    (hα : 0 < α) (hw : 1 ≤ w) (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    ‖neutral ε h α w c η q x‖ ≤
      neutralScale α*‖baselineVector ε α w c (q.re:ℂ) x‖ := by
  rw [neutral,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  have hn := (PiLp.norm_apply_le (targetVector ε h α w c η q x) 4).trans
    (target_norm_bound ε h α w c η hε hh hα hw q hq x)
  have hs := div_le_div_of_nonneg_right hn (Real.sqrt_nonneg (α/32))
  simpa only [neutralScale,div_mul_eq_mul_div] using hs

theorem phase_bound (ε h p : ℝ) (hε : 0 < ε) (hh : |h| ≤ ε/10)
    (q : ℂ) (hq : |q.im| ≤ |h|) :
    ‖clockPhase p (complexInverse ε (shift h q))‖ ≤ Real.exp (|p| *Real.pi/3) := by
  apply KFCausalClockFloorCoherentStrip.clockPhase_bound
  apply KFCausalClockInverseStripBounds.inverse_im_third_strip ε hε
  have hi : |(shift h q).im| ≤ 2*|h| := by
    simp only [shift,Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero]
    exact (abs_sub _ _).trans (by linarith)
  have hp := mul_lt_mul_of_pos_right Real.pi_gt_three hε
  linarith

theorem polynomialCap_nonnegative (α : ℝ) (b : ℂ) (P : Polynomial ℂ) :
    0 ≤ polynomialCap α b P :=
  KFCausalComplexPolynomialGaussianAbsorption.source_polynomial_constant_nonnegative P b _ _
    (by unfold neutralScale; positivity)

theorem bound_nonnegative (ε h a α W : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (hε : 0 < ε) (hW : 0 ≤ W) : 0 ≤ bound ε h a α W C p b P := by
  unfold bound
  exact mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
    (polynomialCap_nonnegative α b P))
    (KFCausalWidthGaussianHolomorphicQuotient.bound_nonnegative ε h a W hε hW)

theorem multiplier_bound (ε h a α W w c η : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (hε : 0 < ε) (hh : |h| ≤ ε/10) (ha : 0 ≤ a) (hα : 0 < α) (hw : 1 ≤ w) (hW : w ≤ W)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    ‖multiplier ε h a α W w c η C p b P q x‖ ≤ bound ε h a α W C p b P := by
  let R := ‖baselineVector ε α w c (q.re:ℂ) x‖
  let M := 4*W*ε⁻¹*Real.exp (|h|/ε+4*a*h^2)
  have hWp : 0 < W := by linarith
  have hM : 0 ≤ M := KFCausalWidthGaussianHolomorphicQuotient.bound_nonnegative ε h a W hε hWp.le
  have hd := source_polynomial_bound P b (neutral ε h α w c η q x)
    (neutralScale α) R (78/289) (by unfold neutralScale; positivity) (norm_nonneg _) (by norm_num)
    (neutral_norm_bound ε h α w c η hε hh hα hw q hq x)
  change _ ≤ polynomialCap α b P at hd
  have hg := KFCausalWidthGaussianHolomorphicQuotient.multiplier_gaussian_bound
    ε h a α W w c η hε hh ha hα hw hW q hq x
  have he : Real.exp (-(a/2)*q.re^2+4*a*h^2) ≤ Real.exp (4*a*h^2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg ha (sq_nonneg q.re)]
  have hg' : ‖KFCausalWidthGaussianHolomorphicQuotient.multiplier ε h a α W w c η q x‖ ≤
      M*Real.exp (-(78/289:ℝ)*R^2) := by
    apply hg.trans
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    calc
      _ ≤ (4*W)*(ε⁻¹*Real.exp (|h|/ε)*Real.exp (4*a*h^2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (by positivity)) (by positivity)
      _ = _ := by dsimp [M]; rw [Real.exp_add]; ring
  have hc : ‖C*clockPhase p (complexInverse ε (shift h q))‖ ≤ ‖C‖*Real.exp (|p| *Real.pi/3) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (phase_bound ε h p hε hh q hq) (norm_nonneg _)
  have hn : 0 ≤ ‖C‖*Real.exp (|p| *Real.pi/3) := by positivity
  unfold multiplier
  rw [norm_mul,norm_mul]
  calc
    _ ≤ (‖C‖*Real.exp (|p| *Real.pi/3))*
        (‖P.eval (neutral ε h α w c η q x)*Complex.exp (b*neutral ε h α w c η q x)‖*
          (M*Real.exp (-(78/289:ℝ)*R^2))) := by
      simpa only [mul_assoc] using mul_le_mul
        (mul_le_mul_of_nonneg_right hc (norm_nonneg _)) hg' (norm_nonneg _)
        (mul_nonneg hn (norm_nonneg _))
    _ = (‖C‖*Real.exp (|p| *Real.pi/3)*M)*
        (‖P.eval (neutral ε h α w c η q x)*Complex.exp (b*neutral ε h α w c η q x)‖*
          Real.exp (-(78/289:ℝ)*R^2)) := by ring
    _ ≤ (‖C‖*Real.exp (|p| *Real.pi/3)*M)*polynomialCap α b P :=
      mul_le_mul_of_nonneg_left hd (mul_nonneg hn hM)
    _ = _ := by unfold bound; dsimp [M]; ring

#print axioms target_norm_bound
#print axioms neutral_norm_bound
#print axioms phase_bound
#print axioms polynomialCap_nonnegative
#print axioms bound_nonnegative
#print axioms multiplier_bound
end
end UnifiedTheory.Audit.KFCausalWidthGaussianNeutralMultiplier
