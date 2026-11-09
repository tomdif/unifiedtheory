/- A derived two-source Gaussian envelope for genuine joint confluence.
Its constants may depend on the fixed order and source increment. -/
import UnifiedTheory.Audit.KFCausalJointSourceConfluenceFactors
import UnifiedTheory.Audit.KFCausalClusteredClockEnvelope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalJointSourceConfluenceEnvelope
noncomputable section
open MeasureTheory
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalClusteredClockFactors (Z N F E B0)
open KFCausalJointSourceConfluenceFactors
open KFCausalClusteredWidthProfiles (quotient)
open KFCausalClusteredWidthDensityIntegrability (Poly chargedPolynomial neutralPolynomial fieldPolynomial weight)
open KFCausalJointPolynomialIntegrability (coordinates)

def qPolynomial (α : ℝ) (r ℓ : ℂ) : Poly :=
  chargedPolynomial α r-MvPolynomial.C ℓ*neutralPolynomial r
def qdPolynomial (α : ℝ) (r v ℓ : ℂ) : Poly :=
  KFCausalClusteredClockEnvelope.chargedSlopePolynomial α r v-
    MvPolynomial.C ℓ*KFCausalClusteredClockEnvelope.neutralSlopePolynomial v
def factorPolynomial (n k : ℕ) (α : ℝ) (r ℓ : ℂ) (P : Polynomial ℂ) : Poly :=
  fieldPolynomial r^k*qPolynomial α r ℓ^n*P.eval₂ MvPolynomial.C (neutralPolynomial r)
def slopePolynomial0 (n k : ℕ) (α β w0 : ℝ) (r v b ℓ : ℂ) (P : Polynomial ℂ) : Poly :=
  qPolynomial α r ℓ^n*KFCausalClusteredClockEnvelope.slopePolynomial0 0 k (w0*α) β r v b P
def slopePolynomial1 (n k : ℕ) (α : ℝ) (r v ℓ : ℂ) (P : Polynomial ℂ) : Poly :=
  qPolynomial α r ℓ^(n-1)*(MvPolynomial.C (n:ℂ)*fieldPolynomial r^k*
    qdPolynomial α r v ℓ*P.eval₂ MvPolynomial.C (neutralPolynomial r))

theorem qPolynomial_eval (α : ℝ) (r ℓ : ℂ) (p : Joint) :
    MvPolynomial.eval (coordinates p) (qPolynomial α r ℓ) = Q α r ℓ p := by
  simp only [qPolynomial,map_sub,map_mul,MvPolynomial.eval_C,
    KFCausalClusteredWidthDensityIntegrability.chargedPolynomial_eval,
    KFCausalClusteredWidthDensityIntegrability.neutralPolynomial_eval]
  rfl

theorem qdPolynomial_eval (α : ℝ) (r v ℓ : ℂ) (p : Joint) :
    MvPolynomial.eval (coordinates p) (qdPolynomial α r v ℓ) = Qd α r v ℓ p := by
  simp only [qdPolynomial,map_sub,map_mul,MvPolynomial.eval_C,
    KFCausalClusteredClockEnvelope.chargedSlopePolynomial_eval,
    KFCausalClusteredClockEnvelope.neutralSlopePolynomial_eval]
  rfl

theorem factorPolynomial_eval (n k : ℕ) (α : ℝ) (r ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) :
    MvPolynomial.eval (coordinates p) (factorPolynomial n k α r ℓ P) =
      (F r p:ℂ)^k*Q α r ℓ p^n*P.eval (N r p) := by
  simp only [factorPolynomial,map_mul,map_pow,qPolynomial_eval,
    KFCausalClusteredWidthDensityIntegrability.fieldPolynomial_eval,
    KFCausalClusteredWidthDensityIntegrability.substitutedPolynomial_eval]
  rfl

theorem slopePolynomial0_eval (n k : ℕ) (α β w0 : ℝ) (r v b ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) :
    MvPolynomial.eval (coordinates p) (slopePolynomial0 n k α β w0 r v b ℓ P) =
      Q α r ℓ p^n*B0 k (w0*α) β r v b P p := by
  simp only [slopePolynomial0,map_mul,map_pow,qPolynomial_eval,
    KFCausalClusteredClockEnvelope.slopePolynomial0_eval,pow_zero,one_mul]

theorem slopePolynomial1_eval (n k : ℕ) (α : ℝ) (r v ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) :
    MvPolynomial.eval (coordinates p) (slopePolynomial1 n k α r v ℓ P) =
      Q α r ℓ p^(n-1)*B1 n k α r v ℓ P p := by
  simp only [slopePolynomial1,map_mul,map_pow,MvPolynomial.eval_C,qPolynomial_eval,qdPolynomial_eval,
    KFCausalClusteredWidthDensityIntegrability.fieldPolynomial_eval,
    KFCausalClusteredWidthDensityIntegrability.substitutedPolynomial_eval]
  rfl

def amplitudeBound (n : ℕ) (α β w0 : ℝ) (r b ℓ : ℂ) (p : Joint) : ℝ :=
  ‖Complex.exp (E (w0*α) β r b p)‖*Real.exp ((n+1:ℕ)*max 0 (ℓ*N r p).re)
def weightSum (n : ℕ) (α β w0 : ℝ) (r b ℓ : ℂ) (p : Joint) : ℝ :=
  weight (w0*α) β r b p+weight (w0*α) β r (b+(n+1:ℕ)*ℓ) p

private theorem powers_bound (n m e : ℕ) (δ : ℝ) (z ξ : ℂ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hz : 0 ≤ z.re) (hm : m+e ≤ n+1) :
    ‖quotient δ (z-ξ)‖^m*‖Complex.exp (-(δ:ℂ)*(z-ξ))‖^e ≤
      ‖z-ξ‖^m*Real.exp ((n+1:ℕ)*max 0 ξ.re) := by
  let J := max 0 ξ.re
  have hJ : 0 ≤ J := le_max_left _ _
  have hq := KFCausalJointSourceConfluenceProfiles.joint_quotient_norm_bound δ z ξ hδ hz
  have he := KFCausalJointSourceConfluenceProfiles.joint_exponential_norm_bound δ z ξ hδ.le hz
  have hprod := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hq m)
    (pow_le_pow_left₀ (norm_nonneg _) he e) (by positivity) (by positivity)
  have hcast : (m:ℝ)+(e:ℝ) ≤ (n+1:ℕ) := by exact_mod_cast hm
  have hExp : ((m:ℝ)+(e:ℝ))*δ*J ≤ (n+1:ℕ)*J := by
    have hmd : ((m:ℝ)+(e:ℝ))*δ ≤ (n+1:ℕ) := by
      nlinarith [show (0:ℝ) ≤ (m:ℝ) by positivity,show (0:ℝ) ≤ (e:ℝ) by positivity]
    exact mul_le_mul_of_nonneg_right hmd hJ
  calc
    _ ≤ (‖z-ξ‖*Real.exp (δ*J))^m*Real.exp (δ*J)^e := hprod
    _ = ‖z-ξ‖^m*Real.exp (((m:ℝ)+(e:ℝ))*δ*J) := by
      rw [mul_pow,← Real.exp_nat_mul,← Real.exp_nat_mul, mul_assoc,← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hExp) (by positivity)

theorem amplitudeBound_sq (n : ℕ) (α β w0 : ℝ) (r b ℓ : ℂ) (p : Joint) :
    amplitudeBound n α β w0 r b ℓ p^2 ≤ weightSum n α β w0 r b ℓ p := by
  rw [weightSum,← KFCausalClusteredClockDensity.base_norm,← KFCausalClusteredClockDensity.base_norm]
  have he : E (w0*α) β r (b+(n+1:ℕ)*ℓ) p =
      E (w0*α) β r b p+(n+1:ℕ)*(ℓ*N r p) := by unfold E; ring
  by_cases ht : (ℓ*N r p).re ≤ 0
  · simp only [amplitudeBound,max_eq_left ht,mul_zero,Real.exp_zero,mul_one]
    exact le_add_of_nonneg_right (sq_nonneg _)
  · have ht' : 0 ≤ (ℓ*N r p).re := (lt_of_not_ge ht).le
    have hb : amplitudeBound n α β w0 r b ℓ p =
        ‖Complex.exp (E (w0*α) β r (b+(n+1:ℕ)*ℓ) p)‖ := by
      unfold amplitudeBound
      rw [max_eq_right ht',he,Complex.exp_add,norm_mul]
      congr 1
      rw [Complex.norm_exp]
      congr 1
      simp
    rw [hb]
    exact le_add_of_nonneg_left (sq_nonneg _)

theorem factor_norm_bound (n k : ℕ) (α β w0 δ : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (p : Joint) (hz : 0 ≤ (Z α r p).re) :
    ‖factor n k α β w0 δ r b ℓ P p‖ ≤ amplitudeBound n α β w0 r b ℓ p*
      ‖MvPolynomial.eval (coordinates p) (factorPolynomial n k α r ℓ P)‖ := by
  have hq := powers_bound n n 0 δ (Z α r p) (ℓ*N r p) hδ hδ1 hz (by omega)
  simp only [pow_zero,mul_one] at hq
  rw [factorPolynomial_eval]
  unfold factor amplitudeBound Q
  simp only [norm_mul,norm_pow]
  nlinarith [mul_le_mul_of_nonneg_left hq
    (mul_nonneg (mul_nonneg (norm_nonneg (Complex.exp (E (w0*α) β r b p)))
      (pow_nonneg (norm_nonneg ((F r p:ℂ))) k)) (norm_nonneg (P.eval (N r p))))]

theorem slope_norm_bound (n k : ℕ) (α β w0 δ : ℝ) (r v b ℓ : ℂ) (P : Polynomial ℂ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (p : Joint) (hz : 0 ≤ (Z α r p).re) :
    ‖slope n k α β w0 δ r v b ℓ P p‖ ≤ amplitudeBound n α β w0 r b ℓ p*
      (‖MvPolynomial.eval (coordinates p) (slopePolynomial0 n k α β w0 r v b ℓ P)‖+
       ‖MvPolynomial.eval (coordinates p) (slopePolynomial1 n k α r v ℓ P)‖) := by
  have hq := powers_bound n n 0 δ (Z α r p) (ℓ*N r p) hδ hδ1 hz (by omega)
  have he := powers_bound n (n-1) 1 δ (Z α r p) (ℓ*N r p) hδ hδ1 hz (by omega)
  simp only [pow_zero,pow_one,mul_one] at hq he
  rw [slopePolynomial0_eval,slopePolynomial1_eval]
  unfold KFCausalJointSourceConfluenceFactors.slope
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)).trans
  simp only [norm_mul,norm_pow]
  unfold amplitudeBound Q
  have h0 := mul_le_mul_of_nonneg_right hq (norm_nonneg (B0 k (w0*α) β r v b P p))
  have h1 := mul_le_mul_of_nonneg_right he (norm_nonneg (B1 n k α r v ℓ P p))
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add h0 h1)
    (norm_nonneg (Complex.exp (E (w0*α) β r b p)))]

def componentBound (n k : ℕ) (α β w0 : ℝ) (r v b ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) : ℝ :=
  weightSum n α β w0 r b ℓ p*
    (‖MvPolynomial.eval (coordinates p) (factorPolynomial n k α r ℓ P)‖^2+
      2*‖MvPolynomial.eval (coordinates p) (slopePolynomial0 n k α β w0 r v b ℓ P)‖^2+
      2*‖MvPolynomial.eval (coordinates p) (slopePolynomial1 n k α r v ℓ P)‖^2)
def responseBound (n : ℕ) (α β w0 : ℝ) (r v b ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) : ℝ :=
  componentBound n 0 α β w0 r v b ℓ P p+
    componentBound n 1 α β w0 r v b ℓ P p/2+componentBound n 2 α β w0 r v b ℓ P p/4

theorem component_pair_bound (n k : ℕ) (α β w0 δ : ℝ) (r v b ℓ : ℂ) (P : Polynomial ℂ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (p : Joint) (hz : 0 ≤ (Z α r p).re) :
    ‖factor n k α β w0 δ r b ℓ P p‖^2+‖KFCausalJointSourceConfluenceFactors.slope n k α β w0 δ r v b ℓ P p‖^2 ≤
      componentBound n k α β w0 r v b ℓ P p := by
  let A := amplitudeBound n α β w0 r b ℓ p
  let X := ‖MvPolynomial.eval (coordinates p) (factorPolynomial n k α r ℓ P)‖
  let B := ‖MvPolynomial.eval (coordinates p) (slopePolynomial0 n k α β w0 r v b ℓ P)‖
  let C := ‖MvPolynomial.eval (coordinates p) (slopePolynomial1 n k α r v ℓ P)‖
  have hf := pow_le_pow_left₀ (norm_nonneg _) (factor_norm_bound n k α β w0 δ r b ℓ P hδ hδ1 p hz) 2
  have hd := pow_le_pow_left₀ (norm_nonneg _) (slope_norm_bound n k α β w0 δ r v b ℓ P hδ hδ1 p hz) 2
  change _ ≤ (A*X)^2 at hf
  change _ ≤ (A*(B+C))^2 at hd
  have hp : (B+C)^2 ≤ 2*B^2+2*C^2 := by nlinarith [sq_nonneg (B-C)]
  have hd' : ‖KFCausalJointSourceConfluenceFactors.slope n k α β w0 δ r v b ℓ P p‖^2 ≤
      A^2*(2*B^2+2*C^2) := by
    exact hd.trans (by rw [mul_pow]; exact mul_le_mul_of_nonneg_left hp (sq_nonneg A))
  rw [mul_pow] at hf
  calc
    _ ≤ A^2*X^2+A^2*(2*B^2+2*C^2) := add_le_add hf hd'
    _ = A^2*(X^2+2*B^2+2*C^2) := by ring
    _ ≤ weightSum n α β w0 r b ℓ p*(X^2+2*B^2+2*C^2) :=
      mul_le_mul_of_nonneg_right (amplitudeBound_sq n α β w0 r b ℓ p) (by positivity)
    _ = _ := rfl

theorem componentBound_integrable (n k : ℕ) (α β w0 : ℝ) (r v b ℓ : ℂ) (P : Polynomial ℂ)
    (hβ : 0 < β) (hA : 0 < (w0*α)*KFCausalReciprocalGaussianCoordinates.area r)
    (hC : 0 < (w0*α)*KFCausalReciprocalGaussianCoordinates.area r-8*β*r.im^2) :
    Integrable (componentBound n k α β w0 r v b ℓ P) jointMeasure := by
  have hi (b' : ℂ) (R : Poly) : Integrable (fun p => ‖MvPolynomial.eval (coordinates p) R‖^2*
      weight (w0*α) β r b' p) jointMeasure :=
    KFCausalJointPolynomialIntegrability.squared_polynomial_integrable _ _ _ _ _ hA hC (by positivity) R
  have hs (b' : ℂ) := ((hi b' (factorPolynomial n k α r ℓ P)).add
    ((hi b' (slopePolynomial0 n k α β w0 r v b ℓ P)).const_mul 2)).add
      ((hi b' (slopePolynomial1 n k α r v ℓ P)).const_mul 2)
  apply ((hs b).add (hs (b+(n+1:ℕ)*ℓ))).congr
  filter_upwards [] with p
  simp only [Pi.add_apply,componentBound,weightSum]
  ring

theorem responseBound_integrable (n : ℕ) (α β w0 : ℝ) (r v b ℓ : ℂ) (P : Polynomial ℂ)
    (hβ : 0 < β) (hA : 0 < (w0*α)*KFCausalReciprocalGaussianCoordinates.area r)
    (hC : 0 < (w0*α)*KFCausalReciprocalGaussianCoordinates.area r-8*β*r.im^2) :
    Integrable (responseBound n α β w0 r v b ℓ P) jointMeasure :=
  ((componentBound_integrable n 0 α β w0 r v b ℓ P hβ hA hC).add
    ((componentBound_integrable n 1 α β w0 r v b ℓ P hβ hA hC).div_const 2)).add
      ((componentBound_integrable n 2 α β w0 r v b ℓ P hβ hA hC).div_const 4)

theorem density_norm_le (n : ℕ) (α β w0 δ : ℝ) (r v b ℓ : ℂ) (P : Polynomial ℂ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 0 ≤ α*KFCausalReciprocalGaussianCoordinates.area r)
    (p : Joint) (hp : 0 ≤ p.2) :
    ‖density n α β w0 δ r b ℓ P p‖ ≤ responseBound n α β w0 r v b ℓ P p := by
  have hz : 0 ≤ (Z α r p).re := by
    rw [Z,KFCausalReciprocalWedgeGeometry.chart_re]
    positivity
  have hk (k : ℕ) : ‖factor n k α β w0 δ r b ℓ P p‖^2 ≤ componentBound n k α β w0 r v b ℓ P p :=
    (le_add_of_nonneg_right (sq_nonneg _)).trans
      (component_pair_bound n k α β w0 δ r v b ℓ P hδ hδ1 p hz)
  have hd : 0 ≤ density n α β w0 δ r b ℓ P p := by unfold density; positivity
  rw [Real.norm_eq_abs,abs_of_nonneg hd]
  exact add_le_add (add_le_add (hk 0) (div_le_div_of_nonneg_right (hk 1) (by norm_num)))
    (div_le_div_of_nonneg_right (hk 2) (by norm_num))

theorem response_norm_le (n : ℕ) (α β w0 δ : ℝ) (r v b ℓ : ℂ) (P : Polynomial ℂ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 0 ≤ α*KFCausalReciprocalGaussianCoordinates.area r)
    (p : Joint) (hp : 0 ≤ p.2) :
    ‖response n α β w0 δ r v b ℓ P p‖ ≤ responseBound n α β w0 r v b ℓ P p := by
  have hz : 0 ≤ (Z α r p).re := by
    rw [Z,KFCausalReciprocalWedgeGeometry.chart_re]
    positivity
  have hk (k : ℕ) : ‖component n k α β w0 δ r v b ℓ P p‖ ≤ componentBound n k α β w0 r v b ℓ P p :=
    (KFCausalCorrelatedClusteredBounds.cross_bound _ _).trans
      (component_pair_bound n k α β w0 δ r v b ℓ P hδ hδ1 p hz)
  unfold response responseBound
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (norm_add_le _ _).trans
    exact add_le_add (hk 0) (by simpa only [norm_div,Real.norm_ofNat] using
      div_le_div_of_nonneg_right (hk 1) (by norm_num : (0:ℝ)≤2))
  · simpa only [norm_div,Real.norm_ofNat] using
      div_le_div_of_nonneg_right (hk 2) (by norm_num : (0:ℝ)≤4)

#print axioms qPolynomial_eval
#print axioms qdPolynomial_eval
#print axioms factorPolynomial_eval
#print axioms slopePolynomial0_eval
#print axioms slopePolynomial1_eval
#print axioms amplitudeBound_sq
#print axioms factor_norm_bound
#print axioms slope_norm_bound
#print axioms component_pair_bound
#print axioms componentBound_integrable
#print axioms responseBound_integrable
#print axioms density_norm_le
#print axioms response_norm_le
end
end UnifiedTheory.Audit.KFCausalJointSourceConfluenceEnvelope
