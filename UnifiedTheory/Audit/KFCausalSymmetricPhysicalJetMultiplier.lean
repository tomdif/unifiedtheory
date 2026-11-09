/- Uniform real-coordinate and angle bounds for the actual symmetric
derivative multipliers, retaining the full shared Gaussian margin. -/
import UnifiedTheory.Audit.KFCausalSymmetricPhysicalJets
import UnifiedTheory.Audit.KFCausalSymmetricDirectionBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalSymmetricPhysicalJetMultiplier
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalComplexShearPerturbation (Space)
open KFCausalComplexQuadraticPerturbation (bilinear quadratic)
open KFCausalWidthGaussianHolomorphicQuotient (baselineVector targetVector)
open KFCausalWidthGaussianNeutralMultiplier (neutral neutralScale)
open KFCausalSymmetricNormalizedDirection (targetDirection)
open KFCausalSymmetricInsertionAffine (neutralSlope matterSlope)
open KFCausalSymmetricDirectionBounds (directionCap neutralSlopeCap matterSlopeCap)
open KFCausalSymmetricNumeratorJets (slope curvature)
open KFCausalSymmetricPhysicalJets (core actualCore multiplier)
open KFCausalMatterInsertionCoordinate (coefficient)

def slopeCap (α w : ℝ) (b : ℂ) (i : Fin 2) : ℝ :=
  ‖b‖*neutralSlopeCap α w i+2*(20/17)*directionCap α w i

def curvatureCap (α w : ℝ) (i : Fin 2) : ℝ := 2*(directionCap α w i)^2

def jetCap (ε h α w : ℝ) (b : ℂ) (Q P : Polynomial ℂ) (i : Fin 2) (order : Fin 3) : ℝ :=
  let A := KFCausalSourcedWidthMatterMultiplier.coefficientCap ε h α w
  let K := neutralScale α
  let G := slopeCap α w b i
  let da := matterSlopeCap ε h α w i
  let dz := neutralSlopeCap α w i
  ![KFCausalTwoPolynomialSourceAbsorption.cap Q P b A K (78/289) 0,
    KFCausalSymmetricJetBounds.firstCap Q P b A K G da dz (78/289),
    KFCausalSymmetricJetBounds.secondCap Q P b A K G da dz (curvatureCap α w i) (78/289)] order

def bound (ε h a α W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (Q P : Polynomial ℂ) (i : Fin 2) (order : Fin 3) : ℝ :=
  (‖C‖*Real.exp (|p| *Real.pi/3))*(4*W*ε⁻¹*Real.exp (|h|/ε+4*a*h^2))*
    jetCap ε h α w b Q P i order

private theorem bilinear_bound (Z U : Space) :
    ‖bilinear (fun i => Z i) (fun i => U i)‖ ≤ ‖Z‖*‖U‖ := by
  have hs := KFCausalComplexQuadraticPerturbation.bilinear_norm_sq (fun i => Z i) (fun i => U i)
  change _ ≤ (∑ i, ‖Z i‖^2)*(∑ i, ‖U i‖^2) at hs
  rw [← PiLp.norm_sq_eq_of_L2,← PiLp.norm_sq_eq_of_L2] at hs
  nlinarith [norm_nonneg (bilinear (fun i => Z i) (fun i => U i)),
    mul_nonneg (norm_nonneg Z) (norm_nonneg U)]

theorem slope_bound (ε h α w c θ : ℝ) (b : ℂ) (i : Fin 2) (hε : 0 < ε)
    (hb : |h| ≤ ε/10) (hα : 0 < α) (hw : 1 ≤ w) (q : ℂ) (hq : |q.im| ≤ |h|)
    (x : Joint 2 4) :
    ‖slope b (neutralSlope ε h α w θ i q) (fun j => targetVector ε h α w c θ q x j)
      (fun j => targetDirection ε h α w θ i q j)‖ ≤
        slopeCap α w b i*(1+‖baselineVector ε α w c (q.re:ℂ) x‖) := by
  have hd := KFCausalSymmetricDirectionBounds.targetDirection_bound ε h α w θ i hε hb hα hw q hq
  have hz := KFCausalWidthGaussianNeutralMultiplier.target_norm_bound ε h α w c θ hε hb hα hw q hq x
  have hn := KFCausalSymmetricDirectionBounds.neutralSlope_bound ε h α w θ i hε hb hα hw q hq
  have hcaps := KFCausalSymmetricDirectionBounds.caps_nonnegative ε h α w i
  have hbil := (bilinear_bound (targetVector ε h α w c θ q x) (targetDirection ε h α w θ i q)).trans
    (mul_le_mul hz hd (norm_nonneg _) (by positivity))
  apply (norm_sub_le _ _).trans
  simp only [norm_mul]
  norm_num only [Complex.norm_ofNat]
  have hs := add_le_add (mul_le_mul_of_nonneg_left hn (norm_nonneg b))
    (mul_le_mul_of_nonneg_left hbil (by norm_num : (0:ℝ) ≤ 2))
  apply hs.trans
  unfold slopeCap
  nlinarith [mul_nonneg (norm_nonneg b) hcaps.2.1,
    mul_nonneg (mul_nonneg (norm_nonneg b) hcaps.2.1) (norm_nonneg (baselineVector ε α w c (q.re:ℂ) x))]

theorem curvature_bound (ε h α w θ : ℝ) (i : Fin 2) (hε : 0 < ε)
    (hb : |h| ≤ ε/10) (hα : 0 < α) (hw : 1 ≤ w) (q : ℂ) (hq : |q.im| ≤ |h|) :
    ‖curvature (fun j => targetDirection ε h α w θ i q j)‖ ≤ curvatureCap α w i := by
  have hd := KFCausalSymmetricDirectionBounds.targetDirection_bound ε h α w θ i hε hb hα hw q hq
  have hqv := KFCausalComplexQuadraticPerturbation.quadratic_norm
    (fun j => targetDirection ε h α w θ i q j)
  change _ ≤ ∑ j, ‖targetDirection ε h α w θ i q j‖^2 at hqv
  rw [← PiLp.norm_sq_eq_of_L2] at hqv
  unfold curvature curvatureCap
  rw [norm_mul]
  norm_num only [norm_neg,Complex.norm_ofNat]
  exact mul_le_mul_of_nonneg_left
    (hqv.trans (pow_le_pow_left₀ (norm_nonneg _) hd 2)) (by norm_num)

theorem core_bound (ε h α w c θ : ℝ) (b : ℂ) (Q P : Polynomial ℂ)
    (i : Fin 2) (order : Fin 3) (hε : 0 < ε) (hb : |h| ≤ ε/10)
    (hα : 0 < α) (hw : 1 ≤ w) (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    ‖actualCore ε h α w c θ b Q P i order q x*Complex.exp (b*neutral ε h α w c θ q x)‖*
      Real.exp (-(78/289:ℝ)*‖baselineVector ε α w c (q.re:ℂ) x‖^2) ≤
        jetCap ε h α w b Q P i order := by
  have hA : 0 ≤ KFCausalSourcedWidthMatterMultiplier.coefficientCap ε h α w := by
    have hs := KFCausalSymmetricInsertionCoordinate.coordinateScale_positive α w hα (zero_lt_one.trans_le hw) 1
    have hn := KFCausalPointFieldInsertionCoordinate.neutralScale_positive α hα
    unfold KFCausalSourcedWidthMatterMultiplier.coefficientCap KFCausalSourcedWidthPointFieldMultiplier.neutralCap
    positivity
  have hK : 0 ≤ neutralScale α := by unfold neutralScale; positivity
  have hG : 0 ≤ slopeCap α w b i := by
    obtain ⟨hD,hdz,hda⟩ := KFCausalSymmetricDirectionBounds.caps_nonnegative ε h α w i
    unfold slopeCap
    positivity
  have hx := KFCausalSourcedWidthMatterMultiplier.coefficient_bound ε h α w c θ hε hb hα hw q hq x
  have hz := KFCausalWidthGaussianNeutralMultiplier.neutral_norm_bound ε h α w c θ hε hb hα hw q hq x
  have hg := slope_bound ε h α w c θ b i hε hb hα hw q hq x
  have ha := KFCausalSymmetricDirectionBounds.matterSlope_bound ε h α w θ i hε hb hα hw q hq
  have hd := KFCausalSymmetricDirectionBounds.neutralSlope_bound ε h α w θ i hε hb hα hw q hq
  have hc := curvature_bound ε h α w θ i hε hb hα hw q hq
  fin_cases order
  · simpa only [actualCore,core,jetCap,Matrix.cons_val_zero,pow_zero,one_mul] using
      KFCausalTwoPolynomialSourceAbsorption.polynomial_source_bound Q P b _ _ _ _ _ _ 0
        hA hK (norm_nonneg _) (by norm_num) hx hz
  · exact KFCausalSymmetricJetBounds.first_bound Q P b _ _ _ _ _ _ _ _ _ _ _ _
      hA hK hG (norm_nonneg _) (by norm_num) hx hz hg ha hd
  · exact KFCausalSymmetricJetBounds.second_bound Q P b _ _ _ _ _ _ _ _ _ _ _ _ _ _
      hA hK hG (norm_nonneg _) (by norm_num) hx hz hg ha hd hc

theorem multiplier_bound (ε h a α W w c θ : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (Q P : Polynomial ℂ) (i : Fin 2) (order : Fin 3) (hε : 0 < ε) (hb : |h| ≤ ε/10)
    (ha : 0 ≤ a) (hα : 0 < α) (hw : 1 ≤ w) (hW : w ≤ W)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    ‖multiplier ε h a α W w c θ C p b Q P i order q x‖ ≤ bound ε h a α W w C p b Q P i order := by
  let R := ‖baselineVector ε α w c (q.re:ℂ) x‖
  let H := ‖C‖*Real.exp (|p| *Real.pi/3)
  let M := 4*W*ε⁻¹*Real.exp (|h|/ε+4*a*h^2)
  have hWp : 0 < W := (zero_lt_one.trans_le hw).trans_le hW
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hg := KFCausalWidthGaussianHolomorphicQuotient.multiplier_gaussian_bound
    ε h a α W w c θ hε hb ha hα hw hW q hq x
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
  have hp := core_bound ε h α w c θ b Q P i order hε hb hα hw q hq x
  have hc : ‖C*KFCausalClockFloorCoherentStrip.clockPhase p
      (KFCausalComplexClockInverse.complexInverse ε (KFCausalTwoShearClockQuotient.shift h q))‖ ≤ H := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (KFCausalWidthGaussianNeutralMultiplier.phase_bound ε h p hε hb q hq) (norm_nonneg _)
  rw [multiplier,norm_mul,norm_mul]
  calc
    _ ≤ (H*‖actualCore ε h α w c θ b Q P i order q x*Complex.exp (b*neutral ε h α w c θ q x)‖)*
        (M*Real.exp (-(78/289:ℝ)*R^2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hc (norm_nonneg _)) hg' (norm_nonneg _) (by positivity)
    _ = (H*M)*(‖actualCore ε h α w c θ b Q P i order q x*Complex.exp (b*neutral ε h α w c θ q x)‖*
        Real.exp (-(78/289:ℝ)*R^2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (mul_nonneg hH hM)

theorem bound_nonnegative (ε h a α W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (Q P : Polynomial ℂ) (i : Fin 2) (order : Fin 3) (hε : 0 < ε) (hb : |h| ≤ ε/10)
    (ha : 0 ≤ a) (hα : 0 < α) (hw : 1 ≤ w) (hW : w ≤ W) :
    0 ≤ bound ε h a α W w C p b Q P i order :=
  (norm_nonneg _).trans (multiplier_bound ε h a α W w 0 0 C p b Q P i order
    hε hb ha hα hw hW 0 (by simp) 0)

#print axioms slope_bound
#print axioms curvature_bound
#print axioms core_bound
#print axioms multiplier_bound
#print axioms bound_nonnegative
end
end UnifiedTheory.Audit.KFCausalSymmetricPhysicalJetMultiplier
