/- Coefficient differentiation of the exact centered/paired kernel.
The full sesquilinear cross value is retained, so changing clock amplitudes
can be differentiated without treating their coefficients as constant. -/
import UnifiedTheory.Audit.KFCausalPairedSpanGrowth
import Mathlib.Analysis.Calculus.Deriv.Star

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalPairedSpanCoefficientDifferential
noncomputable section
open scoped ComplexConjugate
open KFCausalPairedSpanMoments (Coefficients moment value mixedCoefficient value_smooth)
open KFCausalChargedPairCoordinates (narrowWidth wideWidth)

def crossValue (α β : ℝ) (r : ℂ) (c d : Coefficients) : ℂ :=
  (conj c.1*d.1*(moment α β 0 r:ℂ)+
    (conj c.1*(d.2*r^2)+conj (c.2*r^2)*d.1)*(moment α β 1 r:ℂ)+
      conj (c.2*r^2)*(d.2*r^2)*(moment α β 2 r:ℂ))/2

def coefficientRate (α β : ℝ) (r : ℂ) (c d : Coefficients) : ℝ :=
  2*(crossValue α β r c d).re

theorem crossValue_self (α β : ℝ) (r : ℂ) (c : Coefficients) :
    crossValue α β r c c = (value α β r c:ℂ) := by
  apply Complex.ext
  · simp only [crossValue, value, mixedCoefficient, Complex.div_ofNat_re,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.normSq_apply]
    ring
  · simp only [crossValue, Complex.div_ofNat_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring

theorem crossValue_self_re (α β : ℝ) (r : ℂ) (c : Coefficients) :
    (crossValue α β r c c).re = value α β r c := by
  rw [crossValue_self, Complex.ofReal_re]

theorem crossValue_conj (α β : ℝ) (r : ℂ) (c d : Coefficients) :
    conj (crossValue α β r c d) = crossValue α β r d c := by
  simp only [crossValue, map_div₀, map_add, map_mul, map_ofNat,
    Complex.conj_conj, Complex.conj_ofReal]
  ring

theorem crossValue_add_right (α β : ℝ) (r : ℂ) (c d e : Coefficients) :
    crossValue α β r c (d+e) = crossValue α β r c d+crossValue α β r c e := by
  simp only [crossValue, Prod.fst_add, Prod.snd_add]
  ring

theorem crossValue_smul_right (α β : ℝ) (r : ℂ) (c d : Coefficients) (z : ℂ) :
    crossValue α β r c (z • d) = z*crossValue α β r c d := by
  simp only [crossValue, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem coefficientRate_add (α β : ℝ) (r : ℂ) (c d e : Coefficients) :
    coefficientRate α β r c (d+e) = coefficientRate α β r c d+coefficientRate α β r c e := by
  simp only [coefficientRate, crossValue_add_right, Complex.add_re]
  ring

theorem coefficientRate_real_smul (α β : ℝ) (r : ℂ) (c d : Coefficients) (t : ℝ) :
    coefficientRate α β r c (t • d) = t*coefficientRate α β r c d := by
  have he : t • d = (t:ℂ) • d := by ext <;> simp [Complex.real_smul]
  rw [he, coefficientRate, crossValue_smul_right]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  unfold coefficientRate
  ring

theorem coefficientRate_radial (α β : ℝ) (r : ℂ) (c : Coefficients) (z : ℂ) :
    coefficientRate α β r c (z • c) = 2*z.re*value α β r c := by
  rw [coefficientRate, crossValue_smul_right, crossValue_self]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

theorem crossValue_coefficient_derivative (α β : ℝ) (r : ℂ)
    (c d : ℝ → Coefficients) (c' d' : Coefficients) (s : ℝ)
    (hc : HasDerivAt c c' s) (hd : HasDerivAt d d' s) :
    HasDerivAt (fun t => crossValue α β r (c t) (d t))
      (crossValue α β r c' (d s)+crossValue α β r (c s) d') s := by
  have hc0 : HasDerivAt (fun t => (c t).1) c'.1 s :=
    (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt s hc
  have hc1 : HasDerivAt (fun t => (c t).2) c'.2 s :=
    (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt s hc
  have hd0 : HasDerivAt (fun t => (d t).1) d'.1 s :=
    (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt s hd
  have hd1 : HasDerivAt (fun t => (d t).2) d'.2 s :=
    (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt s hd
  have h0 := (hc0.star.mul hd0).mul_const (moment α β 0 r:ℂ)
  have h1 := ((hc0.star.mul (hd1.mul_const (r^2))).add
    ((hc1.mul_const (r^2)).star.mul hd0)).mul_const (moment α β 1 r:ℂ)
  have h2 := ((hc1.mul_const (r^2)).star.mul (hd1.mul_const (r^2))).mul_const
    (moment α β 2 r:ℂ)
  convert ((h0.add h1).add h2).div_const 2 using 1
  simp only [crossValue, Complex.star_def]
  ring

theorem value_coefficient_derivative (α β : ℝ) (r : ℂ)
    (c : ℝ → Coefficients) (d : Coefficients) (s : ℝ) (hc : HasDerivAt c d s) :
    HasDerivAt (fun t => value α β r (c t)) (coefficientRate α β r (c s) d) s := by
  have hd := crossValue_coefficient_derivative α β r c c d d s hc hc
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hd
  change HasDerivAt (fun t => (crossValue α β r (c t) (c t)).re)
    (crossValue α β r d (c s)+crossValue α β r (c s) d).re s at hr
  have he : (crossValue α β r d (c s)).re = (crossValue α β r (c s) d).re := by
    rw [← crossValue_conj α β r (c s) d, Complex.conj_re]
  simpa only [crossValue_self_re, Complex.add_re,
    he, coefficientRate, two_mul] using hr

theorem joint_coefficient_derivative (α β : ℝ) (r : ℂ) (c d : Coefficients)
    (hA : 0 < narrowWidth α β r) (hB : 0 < wideWidth α r) (hβ : 0 < β) :
    fderiv ℝ (fun z : ℂ × Coefficients => value α β z.1 z.2) (r,c) (0,d) =
      coefficientRate α β r c d := by
  have hc : HasDerivAt (fun t : ℝ => c+t • d) d 0 := by
    simpa only [one_smul] using ((hasDerivAt_id (0:ℝ)).smul_const d).const_add c
  have hj := ((value_smooth α β r (c+(0:ℝ) • d) hA hB hβ).differentiableAt
    (by norm_num : (⊤ : WithTop ℕ∞) ≠ 0)).hasFDerivAt.comp_hasDerivAt 0
      ((hasDerivAt_const (0:ℝ) r).prodMk hc)
  have hf := value_coefficient_derivative α β r _ d 0 hc
  simpa only [zero_smul,add_zero] using hj.unique hf

#print axioms crossValue_self
#print axioms crossValue_self_re
#print axioms crossValue_conj
#print axioms crossValue_add_right
#print axioms crossValue_smul_right
#print axioms coefficientRate_add
#print axioms coefficientRate_real_smul
#print axioms coefficientRate_radial
#print axioms crossValue_coefficient_derivative
#print axioms value_coefficient_derivative
#print axioms joint_coefficient_derivative
end
end UnifiedTheory.Audit.KFCausalPairedSpanCoefficientDifferential
