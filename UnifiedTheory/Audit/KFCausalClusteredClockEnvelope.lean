/- A derived, spacing-independent integrable envelope for the complete
clock density derivative at each fixed geometry and velocity. -/
import UnifiedTheory.Audit.KFCausalClusteredClockDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalClusteredClockEnvelope
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalClusteredClockFactors
open KFCausalClusteredClockDensity
open KFCausalClusteredWidthDensityIntegrability (Poly chargedPolynomial neutralPolynomial fieldPolynomial factorPolynomial)
open KFCausalJointPolynomialIntegrability (coordinates)

def chargedSlopePolynomial (α : ℝ) (r v : ℂ) : Poly :=
  MvPolynomial.C ((α:ℂ)*r*v)*(MvPolynomial.X 0^2+MvPolynomial.X 1^2)+
    MvPolynomial.C (conj ((α:ℂ)*r*v))*MvPolynomial.X 3
def neutralSlopePolynomial (v : ℂ) : Poly := MvPolynomial.C (2*(v.im:ℂ)*Complex.I)*MvPolynomial.X 1
def fieldSlopePolynomial (v : ℂ) : Poly := MvPolynomial.C ((-2*v.re:ℝ):ℂ)*MvPolynomial.X 1
def exponentSlopePolynomial (α β : ℝ) (r v b : ℂ) : Poly :=
  -chargedSlopePolynomial α r v+MvPolynomial.C ((8*β*r.im*v.im:ℝ):ℂ)*MvPolynomial.X 1^2+
    MvPolynomial.C b*neutralSlopePolynomial v
def slopePolynomial0 (n k : ℕ) (α β : ℝ) (r v b : ℂ) (P : Polynomial ℂ) : Poly :=
  chargedPolynomial α r^n*(MvPolynomial.C (k:ℂ)*fieldPolynomial r^(k-1)*fieldSlopePolynomial v*
    P.eval₂ MvPolynomial.C (neutralPolynomial r)+fieldPolynomial r^k*
      (P.derivative.eval₂ MvPolynomial.C (neutralPolynomial r)*neutralSlopePolynomial v+
        exponentSlopePolynomial α β r v b*P.eval₂ MvPolynomial.C (neutralPolynomial r)))
def slopePolynomial1 (n k : ℕ) (α : ℝ) (r v : ℂ) (P : Polynomial ℂ) : Poly :=
  chargedPolynomial α r^(n-1)*(MvPolynomial.C (n:ℂ)*fieldPolynomial r^k*
    chargedSlopePolynomial α r v*P.eval₂ MvPolynomial.C (neutralPolynomial r))

theorem chargedSlopePolynomial_eval (α : ℝ) (r v : ℂ) (p : Joint) :
    MvPolynomial.eval (coordinates p) (chargedSlopePolynomial α r v) = Zd α r v p := by
  simp [chargedSlopePolynomial,coordinates,Zd]

theorem neutralSlopePolynomial_eval (v : ℂ) (p : Joint) :
    MvPolynomial.eval (coordinates p) (neutralSlopePolynomial v) = Nd v p := by
  simp [neutralSlopePolynomial,coordinates,Nd]

theorem fieldSlopePolynomial_eval (v : ℂ) (p : Joint) :
    MvPolynomial.eval (coordinates p) (fieldSlopePolynomial v) = (Fd v p:ℂ) := by
  simp [fieldSlopePolynomial,coordinates,Fd]

theorem exponentSlopePolynomial_eval (α β : ℝ) (r v b : ℂ) (p : Joint) :
    MvPolynomial.eval (coordinates p) (exponentSlopePolynomial α β r v b) = Ed α β r v b p := by
  simp only [exponentSlopePolynomial,map_add,map_neg,map_mul,map_pow,MvPolynomial.eval_C,
    MvPolynomial.eval_X,chargedSlopePolynomial_eval,neutralSlopePolynomial_eval]
  simp [coordinates,Ed,Gd]

theorem slopePolynomial0_eval (n k : ℕ) (α β : ℝ) (r v b : ℂ) (P : Polynomial ℂ) (p : Joint) :
    MvPolynomial.eval (coordinates p) (slopePolynomial0 n k α β r v b P) = Z α r p^n*B0 k α β r v b P p := by
  simp only [slopePolynomial0,map_mul,map_pow,map_add,MvPolynomial.eval_C,
    KFCausalClusteredWidthDensityIntegrability.chargedPolynomial_eval,
    KFCausalClusteredWidthDensityIntegrability.fieldPolynomial_eval,
    KFCausalClusteredWidthDensityIntegrability.substitutedPolynomial_eval,
    fieldSlopePolynomial_eval,neutralSlopePolynomial_eval,exponentSlopePolynomial_eval]
  rfl

theorem slopePolynomial1_eval (n k : ℕ) (α : ℝ) (r v : ℂ) (P : Polynomial ℂ) (p : Joint) :
    MvPolynomial.eval (coordinates p) (slopePolynomial1 n k α r v P) = Z α r p^(n-1)*B1 n k α r v P p := by
  simp only [slopePolynomial1,map_mul,map_pow,MvPolynomial.eval_C,
    KFCausalClusteredWidthDensityIntegrability.chargedPolynomial_eval,
    KFCausalClusteredWidthDensityIntegrability.fieldPolynomial_eval,
    KFCausalClusteredWidthDensityIntegrability.substitutedPolynomial_eval,chargedSlopePolynomial_eval]
  rfl

theorem factor_norm_le (n k : ℕ) (α β δ : ℝ) (hδ : 0 < δ)
    (r b : ℂ) (P : Polynomial ℂ) (p : Joint) (hz : 0 ≤ (Z α r p).re) :
    ‖factor n k α β δ r b P p‖ ≤ ‖limitFactor n k α β r b P p‖ := by
  simp only [factor,limitFactor,norm_mul,norm_pow]
  gcongr
  exact KFCausalClusteredWidthProfiles.quotient_norm_le δ _ hδ hz

theorem slope_norm_le (n k : ℕ) (α β δ : ℝ) (hδ : 0 < δ)
    (r v b : ℂ) (P : Polynomial ℂ) (p : Joint) (hz : 0 ≤ (Z α r p).re) :
    ‖slope n k α β δ r v b P p‖ ≤ ‖Complex.exp (E α β r b p)‖*
      (‖MvPolynomial.eval (coordinates p) (slopePolynomial0 n k α β r v b P)‖+
       ‖MvPolynomial.eval (coordinates p) (slopePolynomial1 n k α r v P)‖) := by
  have hq := KFCausalClusteredWidthProfiles.quotient_norm_le δ (Z α r p) hδ hz
  have he := KFCausalClusteredWidthChargedJet.exponential_norm_le_one δ (Z α r p) hδ.le hz
  rw [slopePolynomial0_eval,slopePolynomial1_eval]
  unfold KFCausalClusteredClockFactors.slope
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_add_le _ _).trans
  simp only [norm_mul,norm_pow]
  have h0 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hq n) (norm_nonneg (B0 k α β r v b P p))
  have h1 := mul_le_mul_of_nonneg_right
    (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hq (n-1)) he
      (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)) (norm_nonneg (B1 n k α r v P p))
  simpa only [mul_one] using add_le_add h0 h1

def componentBound (n k : ℕ) (α β : ℝ) (r v b : ℂ) (P : Polynomial ℂ) (p : Joint) : ℝ :=
  KFCausalClusteredWidthDensityIntegrability.weight α β r b p*
    (‖MvPolynomial.eval (coordinates p) (factorPolynomial n k α r P)‖^2+
      2*‖MvPolynomial.eval (coordinates p) (slopePolynomial0 n k α β r v b P)‖^2+
      2*‖MvPolynomial.eval (coordinates p) (slopePolynomial1 n k α r v P)‖^2)
def responseBound (n : ℕ) (α β : ℝ) (r v b : ℂ) (P : Polynomial ℂ) (p : Joint) : ℝ :=
  componentBound n 0 α β r v b P p+componentBound n 1 α β r v b P p/2+componentBound n 2 α β r v b P p/4

theorem component_norm_le (n k : ℕ) (α β δ : ℝ) (hδ : 0 < δ)
    (r v b : ℂ) (P : Polynomial ℂ) (p : Joint) (hz : 0 ≤ (Z α r p).re) :
    ‖component n k α β δ r v b P p‖ ≤ componentBound n k α β r v b P p := by
  let A := factor n k α β δ r b P p
  let D := slope n k α β δ r v b P p
  let t := ‖Complex.exp (E α β r b p)‖
  let B := ‖MvPolynomial.eval (coordinates p) (slopePolynomial0 n k α β r v b P)‖
  let C := ‖MvPolynomial.eval (coordinates p) (slopePolynomial1 n k α r v P)‖
  have hbasic : ‖2*(conj A*D).re‖ ≤ ‖A‖^2+‖D‖^2 := by
    have hh := Complex.abs_re_le_norm (conj A*D)
    rw [norm_mul,Complex.norm_conj] at hh
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    nlinarith [sq_nonneg (‖A‖-‖D‖)]
  have ha := pow_le_pow_left₀ (norm_nonneg _) (factor_norm_le n k α β δ hδ r b P p hz) 2
  have hd := pow_le_pow_left₀ (norm_nonneg _) (slope_norm_le n k α β δ hδ r v b P p hz) 2
  have hb : (B+C)^2 ≤ 2*B^2+2*C^2 := by nlinarith [sq_nonneg (B-C)]
  have hd' : ‖D‖^2 ≤ t^2*(2*B^2+2*C^2) := by
    exact hd.trans (by rw [mul_pow]; exact mul_le_mul_of_nonneg_left hb (sq_nonneg t))
  calc
    _ ≤ ‖A‖^2+‖D‖^2 := hbasic
    _ ≤ ‖limitFactor n k α β r b P p‖^2+t^2*(2*B^2+2*C^2) := add_le_add ha hd'
    _ = componentBound n k α β r v b P p := by
      dsimp only [t,B,C]
      rw [limitFactor_norm,base_norm]
      unfold componentBound
      ring

theorem componentBound_integrable (n k : ℕ) (α β : ℝ) (r v b : ℂ) (P : Polynomial ℂ)
    (hβ : 0 < β) (hA : 0 < α*KFCausalReciprocalGaussianCoordinates.area r)
    (hC : 0 < α*KFCausalReciprocalGaussianCoordinates.area r-8*β*r.im^2) :
    Integrable (componentBound n k α β r v b P) jointMeasure := by
  have hi (Q : Poly) : Integrable (fun p => ‖MvPolynomial.eval (coordinates p) Q‖^2*
      KFCausalClusteredWidthDensityIntegrability.weight α β r b p) jointMeasure :=
    KFCausalJointPolynomialIntegrability.squared_polynomial_integrable _ _ _ _ _ hA hC (by positivity) Q
  apply (((hi (factorPolynomial n k α r P)).add ((hi (slopePolynomial0 n k α β r v b P)).const_mul 2)).add
    ((hi (slopePolynomial1 n k α r v P)).const_mul 2)).congr
  filter_upwards [] with p
  simp only [Pi.add_apply,componentBound]
  ring

theorem responseBound_integrable (n : ℕ) (α β : ℝ) (r v b : ℂ) (P : Polynomial ℂ)
    (hβ : 0 < β) (hA : 0 < α*KFCausalReciprocalGaussianCoordinates.area r)
    (hC : 0 < α*KFCausalReciprocalGaussianCoordinates.area r-8*β*r.im^2) :
    Integrable (responseBound n α β r v b P) jointMeasure := by
  exact ((componentBound_integrable n 0 α β r v b P hβ hA hC).add
    ((componentBound_integrable n 1 α β r v b P hβ hA hC).div_const 2)).add
    ((componentBound_integrable n 2 α β r v b P hβ hA hC).div_const 4)

theorem response_norm_le (n : ℕ) (α β δ : ℝ) (hδ : 0 < δ) (r v b : ℂ) (P : Polynomial ℂ)
    (hA : 0 ≤ α*KFCausalReciprocalGaussianCoordinates.area r) (p : Joint) (hp : 0 ≤ p.2) :
    ‖response n α β δ r v b P p‖ ≤ responseBound n α β r v b P p := by
  have hz : 0 ≤ (Z α r p).re := by rw [Z,KFCausalReciprocalWedgeGeometry.chart_re]; positivity
  have hk := fun k => component_norm_le n k α β δ hδ r v b P p hz
  unfold response responseBound
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (norm_add_le _ _).trans
    exact add_le_add (hk 0) (by simpa only [norm_div,Real.norm_ofNat] using div_le_div_of_nonneg_right (hk 1) (by norm_num : (0:ℝ)≤2))
  · simpa only [norm_div,Real.norm_ofNat] using div_le_div_of_nonneg_right (hk 2) (by norm_num : (0:ℝ)≤4)

#print axioms chargedSlopePolynomial_eval
#print axioms neutralSlopePolynomial_eval
#print axioms fieldSlopePolynomial_eval
#print axioms exponentSlopePolynomial_eval
#print axioms slopePolynomial0_eval
#print axioms slopePolynomial1_eval
#print axioms factor_norm_le
#print axioms slope_norm_le
#print axioms component_norm_le
#print axioms componentBound_integrable
#print axioms responseBound_integrable
#print axioms response_norm_le
end
end UnifiedTheory.Audit.KFCausalClusteredClockEnvelope
