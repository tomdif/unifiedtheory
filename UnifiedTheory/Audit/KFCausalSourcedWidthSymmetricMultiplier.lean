/- One symmetric position insertion is absorbed together with the neutral
source and polynomial by the same retained Gaussian margin. -/
import UnifiedTheory.Audit.KFCausalSymmetricInsertionCoordinate
import UnifiedTheory.Audit.KFCausalWidthGaussianNeutralAnalytic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalSourcedWidthSymmetricMultiplier
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalSymmetricInsertionCoordinate (coefficient coordinateScale increment coordinateIndex)
open KFCausalWidthGaussianHolomorphicQuotient (baselineVector targetVector)
open KFCausalWidthGaussianNeutralMultiplier (neutral neutralScale)
open KFCausalTransversePolynomialEnvelope (evalCap evalCap_nonnegative eval_bound)
open KFCausalComplexPolynomialGaussianAbsorption (power_radius_bound complete_square_bound)
open KFCausalNormalizedComplexRotation (rotationIsometry)
open KFCausalClockFloorCoherentStrip (clockPhase)
open KFCausalComplexClockInverse (complexInverse)
open KFCausalTwoShearClockQuotient (shift)

def polynomialCap (α : ℝ) (b : ℂ) (P : Polynomial ℂ) : ℝ :=
  evalCap P (neutralScale α)*
    Real.exp (((P.natDegree:ℝ)+1+‖b‖*neutralScale α)^2/(4*(78/289:ℝ)))

def multiplier (ε h a α W w c θ : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (i : Fin 2) (q : ℂ) (x : Joint 2 4) : ℂ :=
  coefficient ε h α w c θ i q x*
    KFCausalWidthGaussianNeutralMultiplier.multiplier ε h a α W w c θ C p b P q x

def bound (ε h a α W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (i : Fin 2) : ℝ :=
  (Real.exp (|h|/(2*ε))*(20/17)/coordinateScale α w i)*
    ‖C‖*Real.exp (|p| *Real.pi/3)*
    (4*W*ε⁻¹*Real.exp (|h|/ε+4*a*h^2))*polynomialCap α b P

theorem radius_source_polynomial_bound (P : Polynomial ℂ) (b z : ℂ)
    (K R d : ℝ) (hK : 0 ≤ K) (hR : 0 ≤ R) (hd : 0 < d) (hz : ‖z‖ ≤ K*R) :
    R*‖P.eval z*Complex.exp (b*z)‖*Real.exp (-d*R^2) ≤
      evalCap P K*Real.exp (((P.natDegree:ℝ)+1+‖b‖*K)^2/(4*d)) := by
  have hp := eval_bound P K (1+R) hK (by linarith) z (hz.trans (by nlinarith))
  have hpow := power_radius_bound P.natDegree R hR
  have hcap := evalCap_nonnegative P K hK
  have hr : R ≤ Real.exp R := by linarith [Real.add_one_le_exp R]
  have hs : ‖Complex.exp (b*z)‖ ≤ Real.exp (‖b‖*K*R) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    calc
      (b*z).re ≤ ‖b*z‖ := Complex.re_le_norm _
      _ = ‖b‖*‖z‖ := norm_mul _ _
      _ ≤ ‖b‖*(K*R) := mul_le_mul_of_nonneg_left hz (norm_nonneg _)
      _ = _ := by ring
  rw [norm_mul]
  calc
    _ ≤ Real.exp R*((evalCap P K*Real.exp ((P.natDegree:ℝ)*R))*
        Real.exp (‖b‖*K*R))*Real.exp (-d*R^2) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul hr (mul_le_mul (hp.trans (mul_le_mul_of_nonneg_left hpow hcap)) hs
        (norm_nonneg _) (mul_nonneg hcap (Real.exp_pos _).le))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Real.exp_pos _).le
    _ = evalCap P K*Real.exp (((P.natDegree:ℝ)+1+‖b‖*K)*R-d*R^2) := by
      rw [show ((P.natDegree:ℝ)+1+‖b‖*K)*R-d*R^2=
        R+((P.natDegree:ℝ)*R+‖b‖*K*R)+(-d*R^2) by ring]
      simp only [Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (complete_square_bound d _ R hd)) hcap

theorem coefficient_bound (ε h α w c θ : ℝ) (i : Fin 2)
    (hε : 0 < ε) (hh : |h| ≤ ε/10) (hα : 0 < α) (hw : 1 ≤ w)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    ‖coefficient ε h α w c θ i q x‖ ≤
      (Real.exp (|h|/(2*ε))*(20/17)/coordinateScale α w i)*
        ‖baselineVector ε α w c (q.re:ℂ) x‖ := by
  have hs := KFCausalSymmetricInsertionCoordinate.coordinateScale_positive α w hα
    (zero_lt_one.trans_le hw) i
  have hd : ‖increment ε h q‖ ≤ |h|/ε := by
    simpa only [increment,norm_sub_rev] using
      KFCausalTwoShearClockQuotient.inverse_increment ε h hε hh q hq
  have he : ‖Complex.exp (-increment ε h q/2)‖ ≤ Real.exp (|h|/(2*ε)) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hn := Complex.re_le_norm (-increment ε h q/2)
    have hn' : ‖-increment ε h q/2‖ = ‖increment ε h q‖/2 := by norm_num
    rw [hn'] at hn
    have hdiv := div_le_div_of_nonneg_right hd (by norm_num : (0:ℝ) ≤ 2)
    calc
      _ ≤ ‖increment ε h q‖/2 := hn
      _ ≤ (|h|/ε)/2 := hdiv
      _ = _ := by ring
  have hz := PiLp.norm_apply_le
    (rotationIsometry θ (targetVector ε h α w c θ q x)) (coordinateIndex i)
  rw [(rotationIsometry θ).norm_map] at hz
  have hb := hz.trans
    (KFCausalWidthGaussianNeutralMultiplier.target_norm_bound ε h α w c θ hε hh hα hw q hq x)
  rw [coefficient,norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs]
  calc
    _ ≤ (Real.exp (|h|/(2*ε))*((20/17:ℝ)*‖baselineVector ε α w c (q.re:ℂ) x‖))/
        coordinateScale α w i :=
      div_le_div_of_nonneg_right (mul_le_mul he hb (norm_nonneg _) (Real.exp_pos _).le) hs.le
    _ = _ := by ring

theorem bound_nonnegative (ε h a α W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (i : Fin 2) (hε : 0 < ε) (hα : 0 < α) (hw : 1 ≤ w)
    (hW : w ≤ W) : 0 ≤ bound ε h a α W w C p b P i := by
  have hs := KFCausalSymmetricInsertionCoordinate.coordinateScale_positive α w hα
    (zero_lt_one.trans_le hw) i
  have hcap := evalCap_nonnegative P (neutralScale α) (by unfold neutralScale; positivity)
  have hWp : 0 < W := (zero_lt_one.trans_le hw).trans_le hW
  unfold bound polynomialCap
  positivity

theorem multiplier_mul_baseline (ε h a α W w c θ : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (i : Fin 2) (hW : W ≠ 0) (q : ℂ) (x : Joint 2 4) :
    multiplier ε h a α W w c θ C p b P i q x*
      KFCausalWidthGaussianHolomorphicQuotient.baseline ε a α W w c q x =
      coefficient ε h α w c θ i q x*
        KFCausalWidthGaussianNeutralMultiplier.numerator ε h a α w c θ C p b P q x := by
  rw [multiplier,mul_assoc,KFCausalWidthGaussianNeutralMultiplier.multiplier_mul_baseline
    ε h a α W w c θ hW C p b P q x]

theorem multiplier_bound (ε h a α W w c θ : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (i : Fin 2) (hε : 0 < ε) (hh : |h| ≤ ε/10)
    (ha : 0 ≤ a) (hα : 0 < α) (hw : 1 ≤ w) (hW : w ≤ W)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    ‖multiplier ε h a α W w c θ C p b P i q x‖ ≤ bound ε h a α W w C p b P i := by
  let R := ‖baselineVector ε α w c (q.re:ℂ) x‖
  let A := Real.exp (|h|/(2*ε))*(20/17)/coordinateScale α w i
  let H := ‖C‖*Real.exp (|p| *Real.pi/3)
  let M := 4*W*ε⁻¹*Real.exp (|h|/ε+4*a*h^2)
  have hs := KFCausalSymmetricInsertionCoordinate.coordinateScale_positive α w hα
    (zero_lt_one.trans_le hw) i
  have hWp : 0 < W := (zero_lt_one.trans_le hw).trans_le hW
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hR : 0 ≤ R := norm_nonneg _
  have hp := radius_source_polynomial_bound P b (neutral ε h α w c θ q x)
    (neutralScale α) R (78/289) (by unfold neutralScale; positivity) hR (by norm_num)
    (KFCausalWidthGaussianNeutralMultiplier.neutral_norm_bound ε h α w c θ hε hh hα hw q hq x)
  change _ ≤ polynomialCap α b P at hp
  have hg := KFCausalWidthGaussianHolomorphicQuotient.multiplier_gaussian_bound
    ε h a α W w c θ hε hh ha hα hw hW q hq x
  have he : Real.exp (-(a/2)*q.re^2+4*a*h^2) ≤ Real.exp (4*a*h^2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg ha (sq_nonneg q.re)]
  have hg' : ‖KFCausalWidthGaussianHolomorphicQuotient.multiplier ε h a α W w c θ q x‖ ≤
      M*Real.exp (-(78/289:ℝ)*R^2) := by
    apply hg.trans
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    calc
      _ ≤ (4*W)*(ε⁻¹*Real.exp (|h|/ε)*Real.exp (4*a*h^2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (by positivity)) (by positivity)
      _ = _ := by dsimp [M]; rw [Real.exp_add]; ring
  have hc : ‖C*clockPhase p (complexInverse ε (shift h q))‖ ≤ H := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (KFCausalWidthGaussianNeutralMultiplier.phase_bound ε h p hε hh q hq) (norm_nonneg _)
  have hi := coefficient_bound ε h α w c θ i hε hh hα hw q hq x
  rw [norm_mul] at hc
  unfold multiplier KFCausalWidthGaussianNeutralMultiplier.multiplier
  simp only [norm_mul]
  calc
    _ ≤ (A*R)*(H*(‖P.eval (neutral ε h α w c θ q x)‖*
        ‖Complex.exp (b*neutral ε h α w c θ q x)‖)*
          (M*Real.exp (-(78/289:ℝ)*R^2))) := by
      exact mul_le_mul hi (mul_le_mul
        (mul_le_mul_of_nonneg_right hc (mul_nonneg (norm_nonneg _) (norm_nonneg _))) hg'
        (norm_nonneg _) (mul_nonneg hH (mul_nonneg (norm_nonneg _) (norm_nonneg _))))
        (by positivity) (mul_nonneg hA hR)
    _ = (A*H*M)*(R*‖P.eval (neutral ε h α w c θ q x)*
        Complex.exp (b*neutral ε h α w c θ q x)‖*Real.exp (-(78/289:ℝ)*R^2)) := by
      rw [norm_mul]
      ring
    _ ≤ (A*H*M)*polynomialCap α b P := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by dsimp [A,H,M,bound]; ring

#print axioms radius_source_polynomial_bound
#print axioms coefficient_bound
#print axioms bound_nonnegative
#print axioms multiplier_mul_baseline
#print axioms multiplier_bound
end
end UnifiedTheory.Audit.KFCausalSourcedWidthSymmetricMultiplier
