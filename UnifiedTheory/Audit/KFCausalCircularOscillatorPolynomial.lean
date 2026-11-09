/- Circular coordinates for the anisotropic oscillator. These are exact
polynomial differential identities, prior to identifying a maximal operator. -/
import UnifiedTheory.Audit.KFCausalPlaneOscillatorPolynomial
import UnifiedTheory.Audit.KFCausalScaledCircularPolynomials

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCircularOscillatorPolynomial
noncomputable section
open MvPolynomial
open KFCausalPlanePolynomialGaussian (Poly state)
open KFCausalPlaneOscillatorPolynomial (axis)

def change (c : ℝ) : Poly →ₐ[ℂ] Poly :=
  (KFCausalScaledCircularPolynomials.scale c).comp KFCausalCircularPolynomialBasis.forward

theorem change_C (c : ℝ) (z : ℂ) : change c (C z) = C z := by
  simp [change, KFCausalScaledCircularPolynomials.scale,
    KFCausalCircularPolynomialBasis.forward, AlgHom.comp_apply]

theorem change_zero (c : ℝ) : change c (X 0) = C (c:ℂ)*X 0+C Complex.I*X 1 := by
  simp [change, KFCausalScaledCircularPolynomials.scale,
    KFCausalCircularPolynomialBasis.forward, AlgHom.comp_apply]

theorem change_one (c : ℝ) : change c (X 1) = C (c:ℂ)*X 0-C Complex.I*X 1 := by
  simp [change, KFCausalScaledCircularPolynomials.scale,
    KFCausalCircularPolynomialBasis.forward, AlgHom.comp_apply]

theorem derivative_zero (c : ℝ) (P : Poly) :
    pderiv 0 (change c P) = C (c:ℂ)*change c (pderiv 0 P+pderiv 1 P) := by
  induction P using MvPolynomial.induction_on with
  | C z => simp [change, pderiv_C]
  | add P Q hp hq => simp only [map_add, hp, hq]; ring
  | mul_X P i hp =>
    fin_cases i <;>
      simp [pderiv_mul, hp, change_zero, change_one, pderiv_C_mul, map_sub] <;> ring

theorem derivative_one (c : ℝ) (P : Poly) :
    pderiv 1 (change c P) = C Complex.I*change c (pderiv 0 P-pderiv 1 P) := by
  induction P using MvPolynomial.induction_on with
  | C z => simp [change, pderiv_C]
  | add P Q hp hq => simp only [map_add, hp, hq, map_sub]; ring
  | mul_X P i hp =>
    fin_cases i <;>
      simp [pderiv_mul, hp, change_zero, change_one, pderiv_C_mul, map_sub] <;> ring

theorem mixed_commute (P : Poly) : pderiv 0 (pderiv 1 P) = pderiv 1 (pderiv 0 P) := by
  induction P using MvPolynomial.induction_on' with
  | add P Q hp hq => simp only [map_add, hp, hq]
  | monomial d z =>
    simp only [pderiv_monomial, Finsupp.tsub_apply, Finsupp.single_apply,
      show (0:Fin 2) ≠ 1 by decide, show (1:Fin 2) ≠ 0 by decide,
      ↓reduceIte, Nat.sub_zero]
    rw [tsub_right_comm]
    congr 1
    ring

def oscillator (c b : ℝ) : Poly →ₗ[ℂ] Poly :=
  axis ((b:ℂ)*(c:ℂ)^2) 0 + ((c:ℂ)^2) • axis (b:ℂ) 1

theorem oscillator_symmetric (c : ℝ) (hc : c ≠ 0) (b : ℝ) (hb : 0 < b)
    (P Q : Poly) :
    inner ℂ (state (b*c^2) b (KFCausalScaledCircularPolynomials.width_positive c b hc hb) hb
      (oscillator c b P))
      (state (b*c^2) b (KFCausalScaledCircularPolynomials.width_positive c b hc hb) hb Q) =
    inner ℂ (state (b*c^2) b (KFCausalScaledCircularPolynomials.width_positive c b hc hb) hb P)
      (state (b*c^2) b (KFCausalScaledCircularPolynomials.width_positive c b hc hb) hb
        (oscillator c b Q)) := by
  have h0 := KFCausalPlaneOscillatorPolynomial.axis_symmetric (b*c^2) b
    (KFCausalScaledCircularPolynomials.width_positive c b hc hb) hb 0 P Q
  have h1 := KFCausalPlaneOscillatorPolynomial.axis_symmetric (b*c^2) b
    (KFCausalScaledCircularPolynomials.width_positive c b hc hb) hb 1 P Q
  simp only [oscillator, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
  simpa [Complex.ofReal_mul, Complex.ofReal_pow] using congrArg₂
    (fun x y : ℂ => x+(c:ℂ)^2*y) h0 h1

theorem conjugation (c b : ℝ) (P : Poly) :
    oscillator c b (change c P) = C ((c:ℂ)^2)*change c
      (-4*pderiv 0 (pderiv 1 P)+C (4*(b:ℂ))*(X 0*pderiv 0 P+X 1*pderiv 1 P+P)) := by
  have hI : (C Complex.I : Poly)^2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  simp only [oscillator, LinearMap.add_apply, LinearMap.smul_apply, axis,
    LinearMap.coe_mk, AddHom.coe_mk, derivative_zero, derivative_one, pderiv_C_mul,
    map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, smul_eq_C_mul,
    change_zero, change_one, change_C, mixed_commute]
  linear_combination -(C (c:ℂ))^2 *
    (change c (pderiv 0 (pderiv 0 P))-2*change c (pderiv 1 (pderiv 0 P))+
      change c (pderiv 1 (pderiv 1 P))) * hI

def lower (d : Fin 2 →₀ ℕ) : Fin 2 →₀ ℕ :=
  d-Finsupp.single 0 1-Finsupp.single 1 1

theorem monomial_action (c b : ℝ) (d : Fin 2 →₀ ℕ) :
    oscillator c b (change c (monomial d 1)) =
      (4*(b:ℂ)*(c:ℂ)^2*((d 0:ℂ)+(d 1:ℂ)+1)) • change c (monomial d 1) -
        (4*(c:ℂ)^2*(d 0:ℂ)*(d 1:ℂ)) • change c (monomial (lower d) 1) := by
  have hd : pderiv 0 (pderiv 1 (monomial d (1:ℂ))) =
      C ((d 0:ℂ)*(d 1:ℂ))*monomial (lower d) 1 := by
    simp only [pderiv_monomial, Finsupp.tsub_apply, Finsupp.single_apply,
      show (1:Fin 2) ≠ 0 by decide, ↓reduceIte, Nat.sub_zero, one_mul,
      C_mul_monomial, mul_one, lower, tsub_right_comm]
    congr 1
    ring
  rw [conjugation, hd, X_mul_pderiv_monomial, X_mul_pderiv_monomial]
  simp only [map_add, map_mul, map_neg, map_ofNat, map_nsmul, change_C,
    nsmul_eq_mul, smul_eq_C_mul, map_natCast, map_pow, map_one]
  ring

#print axioms monomial_action

#print axioms oscillator_symmetric
#print axioms conjugation
end
end UnifiedTheory.Audit.KFCausalCircularOscillatorPolynomial
