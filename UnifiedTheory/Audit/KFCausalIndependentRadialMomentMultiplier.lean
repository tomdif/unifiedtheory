/- The complete radial/source/field multiplier for the actual bare
moment input. All polynomial factors share one retained Gaussian margin. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialInsertions
import UnifiedTheory.Audit.KFCausalScalarPowerSourceAbsorption

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000

namespace UnifiedTheory.Audit.KFCausalIndependentRadialMomentMultiplier
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalIndependentRadialHolomorphicQuotient (baselineVector baseline)
open KFCausalIndependentRadialMomentInput (left right neutral numerator)
open KFCausalIndependentRadialInsertions (radialCap neutralCap)
open KFCausalIndependentRadialShiftedField (coefficient cap)
open KFCausalComplexClockInverse (complexInverse)
open KFCausalClockFloorCoherentStrip (clockPhase)
open KFCausalTransversePolynomialEnvelope (evalCap evalCap_nonnegative)

def multiplier (ε h a α W wL wR c : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (m n k : ℕ) (q : ℂ) (x : Joint 2 4) : ℂ :=
  let Y := baselineVector ε α wL wR c q x
  coefficient ε h α wL wR c q x^k*left α wL Y^m*right α wR Y^n*
    (C*clockPhase p (complexInverse ε q))*(P.eval (neutral α Y)*Complex.exp (b*neutral α Y))*
      KFCausalIndependentRadialBareMultiplier.multiplier ε a α W wL wR c q x

def polynomialCap (α : ℝ) (b : ℂ) (P : Polynomial ℂ) (N : ℕ) : ℝ :=
  evalCap P (neutralCap α)*
    Real.exp (((P.natDegree:ℝ)+(N:ℝ)+‖b‖*neutralCap α)^2/(4*(78/289:ℝ)))

def bound (h a α W wL wR : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (m n k : ℕ) : ℝ :=
  (‖C‖*Real.exp (|p| *Real.pi/3))*(4*W*Real.exp ((a/2)*h^2))*
    ((cap α wR)^k*(radialCap (α/wL))^m*(radialCap (α*wR))^n)*
      polynomialCap α b P (k+2*m+2*n)

theorem polynomialCap_nonnegative (α : ℝ) (b : ℂ) (P : Polynomial ℂ) (N : ℕ) :
    0 ≤ polynomialCap α b P N :=
  mul_nonneg (evalCap_nonnegative P _ (KFCausalIndependentRadialInsertions.neutralCap_nonnegative α))
    (Real.exp_pos _).le

theorem bound_nonnegative (h a α W wL wR : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (m n k : ℕ) (hα : 0 < α) (hL : 1 ≤ wL) (hR : 1 ≤ wR)
    (hW : wL ≤ W) : 0 ≤ bound h a α W wL wR C p b P m n k := by
  have hWp : 0 < W := (zero_lt_one.trans_le hL).trans_le hW
  have hlc := KFCausalIndependentRadialInsertions.radialCap_nonnegative (α/wL)
    (div_nonneg hα.le (zero_lt_one.trans_le hL).le)
  have hrc := KFCausalIndependentRadialInsertions.radialCap_nonnegative (α*wR)
    (mul_nonneg hα.le (zero_lt_one.trans_le hR).le)
  have hfc := KFCausalIndependentRadialShiftedField.cap_nonnegative α wR
  have hpc := polynomialCap_nonnegative α b P (k+2*m+2*n)
  unfold bound
  positivity

theorem multiplier_mul_baseline (ε h a α W wL wR c : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (m n k : ℕ) (hW : W ≠ 0) (q : ℂ) (x : Joint 2 4) :
    multiplier ε h a α W wL wR c C p b P m n k q x*baseline ε a α W wL wR c q x =
      coefficient ε h α wL wR c q x^k*numerator ε a α wL wR c C p b P m n q x := by
  dsimp only [multiplier]
  rw [mul_assoc,KFCausalIndependentRadialBareMultiplier.multiplier_mul_baseline
    ε a α W wL wR c hW q x]
  dsimp only [KFCausalIndependentRadialBareMultiplier.numerator,numerator]
  ring

private theorem radial_source_bound (P : Polynomial ℂ) (b z L R O : ℂ)
    (A B F K S : ℝ) (m n k : ℕ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hF : 0 ≤ F)
    (hK : 0 ≤ K) (hS : 0 ≤ S) (hL : ‖L‖ ≤ A*S^2) (hR : ‖R‖ ≤ B*S^2)
    (hO : ‖O‖ ≤ F*S) (hz : ‖z‖ ≤ K*S) :
    ‖(O^k*L^m*R^n)*(P.eval z*Complex.exp (b*z))‖*Real.exp (-(78/289:ℝ)*S^2) ≤
      (F^k*A^m*B^n)*(evalCap P K*
        Real.exp (((P.natDegree:ℝ)+((k+2*m+2*n:ℕ):ℝ)+‖b‖*K)^2/(4*(78/289:ℝ)))) := by
  have hl := pow_le_pow_left₀ (norm_nonneg L) hL m
  have hr := pow_le_pow_left₀ (norm_nonneg R) hR n
  have ho := pow_le_pow_left₀ (norm_nonneg O) hO k
  rw [mul_pow] at hl hr ho
  have hp := KFCausalScalarPowerSourceAbsorption.radius_power_source_bound
    (k+2*m+2*n) P b z K S (78/289) hK hS (by norm_num) hz
  have ht : ‖O^k*L^m*R^n‖ ≤ (F^k*A^m*B^n)*S^(k+2*m+2*n) := by
    simp only [norm_mul,norm_pow]
    calc
      _ ≤ ((F^k*S^k)*(A^m*(S^2)^m))*(B^n*(S^2)^n) := by
        exact mul_le_mul (mul_le_mul ho hl (by positivity) (by positivity)) hr
          (by positivity) (by positivity)
      _ = _ := by rw [pow_add,pow_add,pow_mul,pow_mul]; ring
  rw [norm_mul]
  calc
    _ ≤ ((F^k*A^m*B^n)*S^(k+2*m+2*n))*‖P.eval z*Complex.exp (b*z)‖*
        Real.exp (-(78/289:ℝ)*S^2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht (norm_nonneg _)) (Real.exp_pos _).le
    _ = (F^k*A^m*B^n)*(S^(k+2*m+2*n)*‖P.eval z*Complex.exp (b*z)‖*
        Real.exp (-(78/289:ℝ)*S^2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

theorem multiplier_bound (ε h a α W wL wR c : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (m n k : ℕ) (hε : 0 < ε) (hb : |h| ≤ ε/10) (ha : 0 ≤ a)
    (hα : 0 < α) (hL : 1 ≤ wL) (hR : 1 ≤ wR) (hW : wL ≤ W)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    ‖multiplier ε h a α W wL wR c C p b P m n k q x‖ ≤
      bound h a α W wL wR C p b P m n k := by
  let Y := baselineVector ε α wL wR c q x
  let S := ‖baselineVector ε α wL wR c (q.re:ℂ) x‖
  let T := coefficient ε h α wL wR c q x^k*left α wL Y^m*right α wR Y^n
  let N := P.eval (neutral α Y)*Complex.exp (b*neutral α Y)
  let H := ‖C‖*Real.exp (|p| *Real.pi/3)
  let M := 4*W*Real.exp ((a/2)*h^2)
  have hWp : 0 < W := (zero_lt_one.trans_le hL).trans_le hW
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hp := radial_source_bound P b (neutral α Y) (left α wL Y) (right α wR Y)
    (coefficient ε h α wL wR c q x) (radialCap (α/wL)) (radialCap (α*wR))
    (cap α wR) (neutralCap α) S m n k
    (KFCausalIndependentRadialInsertions.radialCap_nonnegative _ (by positivity))
    (KFCausalIndependentRadialInsertions.radialCap_nonnegative _ (by positivity))
    (KFCausalIndependentRadialShiftedField.cap_nonnegative α wR)
    (KFCausalIndependentRadialInsertions.neutralCap_nonnegative α) (norm_nonneg _)
    (KFCausalIndependentRadialInsertions.left_bound ε h α wL wR c hε hb hα hL hR q hq x)
    (KFCausalIndependentRadialInsertions.right_bound ε h α wL wR c hε hb hα hR q hq x)
    (KFCausalIndependentRadialShiftedField.coefficient_bound ε h α wL wR c hε hb hα hR q hq x)
    (KFCausalIndependentRadialInsertions.neutral_bound ε h α wL wR c hε hb hα hR q hq x)
  change ‖T*N‖*Real.exp (-(78/289:ℝ)*S^2) ≤
    ((cap α wR)^k*(radialCap (α/wL))^m*(radialCap (α*wR))^n)*
      polynomialCap α b P (k+2*m+2*n) at hp
  have hg := KFCausalIndependentRadialBareMultiplier.multiplier_gaussian_bound
    ε h a α W wL wR c hε hb ha hα hL hR hW q hq x
  have hc : ‖C*clockPhase p (complexInverse ε q)‖ ≤ H := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (KFCausalIndependentRadialInsertions.phase_bound ε h p hε hb q hq) (norm_nonneg _)
  have heq : multiplier ε h a α W wL wR c C p b P m n k q x =
      (C*clockPhase p (complexInverse ε q))*(T*N)*
        KFCausalIndependentRadialBareMultiplier.multiplier ε a α W wL wR c q x := by
    dsimp [multiplier,T,N,Y]
    ring
  rw [heq,norm_mul,norm_mul]
  calc
    _ ≤ H*‖T*N‖*(M*Real.exp (-(78/289:ℝ)*S^2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hc (norm_nonneg _)) hg
        (norm_nonneg _) (mul_nonneg hH (norm_nonneg _))
    _ = (H*M)*(‖T*N‖*Real.exp (-(78/289:ℝ)*S^2)) := by ring
    _ ≤ (H*M)*(((cap α wR)^k*(radialCap (α/wL))^m*(radialCap (α*wR))^n)*
      polynomialCap α b P (k+2*m+2*n)) := mul_le_mul_of_nonneg_left hp (mul_nonneg hH hM)
    _ = _ := by dsimp [H,M,bound]; ring

#print axioms polynomialCap_nonnegative
#print axioms bound_nonnegative
#print axioms multiplier_mul_baseline
#print axioms multiplier_bound
end
end UnifiedTheory.Audit.KFCausalIndependentRadialMomentMultiplier
