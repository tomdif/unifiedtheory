/- Polynomially weighted integrability of the literal coherent charged
marginal and both actual derivatives in its score inequality. The strict
Gaussian margin is the original one on each charged width; every cross
term is retained. No boundary decay or derivative-integrability premise
is supplied by the caller. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingMarginalScore
import UnifiedTheory.Audit.KFCausalShiftedComplexGaussianMoments

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedQuarticScoreIntegrability
noncomputable section
open MeasureTheory Matrix
open scoped ComplexConjugate
open KFCausalChargedCoolingWidthPositive (widthSum coolingB coolingC)
open KFCausalChargedCoolingFixedV (widthSum_re dissipation actual_gamma_re_positive)
open KFCausalChargedCoolingDerivative (kernel form)
open KFCausalChargedCoolingBoundaryScore (radialSlope)
open KFCausalChargedCoolingMarginalScore (marginal radialForm)
open KFCausalChargedCoolingMarginalDerivative (coolingForm)
open KFCausalReciprocalWedgeGeometry (gamma)

private theorem gaussian_monomial_integrable (j : ℕ) (S : ℂ) (d q : ℝ)
    (hS : d<S.re) :
    Integrable (fun v : ℝ => (v:ℂ)^j*(Real.exp (d*v^2-q*v):ℂ)*
      Complex.exp (-S*(v^2:ℝ))) := by
  have hi := KFCausalShiftedComplexGaussianMoments.moment_integrable
    (S-(d:ℂ)) (-q:ℂ) (by simpa only [Complex.sub_re,Complex.ofReal_re] using sub_pos.mpr hS) j
  apply hi.congr
  filter_upwards [] with v
  simp only [KFCausalShiftedComplexGaussianMoments.moment,Complex.ofReal_exp]
  rw [mul_assoc,← Complex.exp_add]
  congr 2
  push_cast
  ring

private theorem kernel_monomial_integrable (j : ℕ) (p : ℂ) (d q w z : ℝ)
    (hd : d<(widthSum p w z).re) :
    Integrable (fun v : ℝ => (v:ℂ)^j*(Real.exp (d*v^2-q*v):ℂ)*kernel p w z v) := by
  have hi := (gaussian_monomial_integrable j (widthSum p w z) d q hd).div_const
    (widthSum p w z^(1/2:ℂ)*widthSum (conj p) w z)
  simpa only [kernel,mul_div_assoc] using hi

private theorem radial_monomial_integrable_aux (j : ℕ) (p : ℂ) (d q w z : ℝ)
    (hd : d<(widthSum p w z).re) :
    Integrable (fun v : ℝ => (v:ℂ)^j*(Real.exp (d*v^2-q*v):ℂ)*radialSlope p w z v) := by
  apply ((kernel_monomial_integrable (j+1) p d q w z hd).const_mul
    (-2*widthSum p w z)).congr
  filter_upwards [] with v
  simp only [radialSlope,pow_succ]
  ring

private theorem cooling_monomial_integrable_aux (j : ℕ) (p a : ℂ) (d q w z : ℝ)
    (hd : d<(widthSum p w z).re) :
    Integrable (fun v : ℝ => (v:ℂ)^j*(Real.exp (d*v^2-q*v):ℂ)*dissipation p a w z v) := by
  have hi := ((gaussian_monomial_integrable (j+2) (widthSum p w z) d q hd).mul_const
    (coolingB p a w z)).add
      ((gaussian_monomial_integrable j (widthSum p w z) d q hd).mul_const
        (coolingB p a w z/(2*widthSum p w z)+coolingC p a w z))
  apply hi.congr
  filter_upwards [] with v
  simp only [dissipation,Pi.add_apply,pow_add,Complex.ofReal_pow]
  ring

private theorem finite_form_integrable {ι : Type*} [Fintype ι]
    (K : ι→ι→ℝ→ℂ) (c : ι→ℂ) (j : ℕ) (d q : ℝ)
    (hi : ∀ i k, Integrable (fun v : ℝ =>
      (v:ℂ)^j*(Real.exp (d*v^2-q*v):ℂ)*K i k v)) :
    Integrable (fun v : ℝ => v^j*Real.exp (d*v^2-q*v)*
      (star c ⬝ᵥ ((fun i k => K i k v)*ᵥc)).re) := by
  have h := integrable_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun k _ =>
      ((hi i k).const_mul (star (c i))).mul_const (c k)))
  have he (v : ℝ) :
      (∑ i,∑ k,star (c i)*((v:ℂ)^j*(Real.exp (d*v^2-q*v):ℂ)*K i k v)*c k)=
        ((v^j*Real.exp (d*v^2-q*v):ℝ):ℂ)*
          (star c ⬝ᵥ ((fun i k => K i k v)*ᵥc)) := by
    simp only [dotProduct,Matrix.mulVec,Pi.star_apply,Finset.mul_sum,Complex.ofReal_mul,
      Complex.ofReal_pow]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  apply h.re.congr
  filter_upwards [] with v
  rw [he]
  exact Complex.re_ofReal_mul _ _

variable (n : ℕ) (α : ℝ) (r : ℂ) (d q : ℝ) (w : Fin n→ℝ) (c : Fin n→ℂ)
    (hα : 0<α) (hr : |r.im|<r.re) (hw : ∀i,0<w i)
    (hd : ∀i,d<2*(gamma α r).re*w i)

include hd in
private theorem pair_margin (i k : Fin n) :
    d<(widthSum (conj (gamma α r)) (w i) (w k)).re := by
  rw [widthSum_re,Complex.conj_re]
  linarith [hd i,hd k]

include hα hr hw hd

theorem marginal_monomial_integrable (j : ℕ) :
    Integrable (fun v : ℝ => v^j*Real.exp (d*v^2-q*v)*marginal n α r w c v) := by
  have hi := finite_form_integrable
    (fun i k v => kernel (conj (gamma α r)) (w i) (w k) v) c j d q
    (fun i k => kernel_monomial_integrable j _ d q _ _ (pair_margin n α r d w hd i k))
  apply (hi.const_mul (Real.sqrt Real.pi)).congr
  filter_upwards [] with v
  unfold marginal
  rw [KFCausalChargedCoolingPhysicalMarginal.packet_square_integral n (gamma α r) w c
    (actual_gamma_re_positive α r hα hr) hw v]
  unfold form
  ring

theorem radial_monomial_integrable (j : ℕ) :
    Integrable (fun v : ℝ => v^j*Real.exp (d*v^2-q*v)*deriv (marginal n α r w c) v) := by
  have hi := finite_form_integrable
    (fun i k v => radialSlope (conj (gamma α r)) (w i) (w k) v) c j d q
    (fun i k => radial_monomial_integrable_aux j _ d q _ _ (pair_margin n α r d w hd i k))
  apply (hi.const_mul (Real.sqrt Real.pi)).congr
  filter_upwards [] with v
  rw [(KFCausalChargedCoolingMarginalScore.marginal_radial_derivative
    n α r w c v hα hr hw).deriv]
  unfold radialForm
  ring

theorem cooling_monomial_integrable (j : ℕ) :
    Integrable (fun v : ℝ => v^j*Real.exp (d*v^2-q*v)*
      (-deriv (fun t : ℝ => marginal n α (r+(t:ℂ)) w c v) 0)) := by
  have he : gamma α (conj r)=conj (gamma α r) := by
    simp only [gamma,map_div₀,map_mul,map_pow,Complex.conj_ofReal,Complex.conj_ofNat]
  have hi := finite_form_integrable
    (fun i k v => dissipation (gamma α (conj r)) ((α:ℂ)*conj r) (w i) (w k) v) c j d q
    (fun i k => cooling_monomial_integrable_aux j _ _ d q _ _
      (by rw [he]; exact pair_margin n α r d w hd i k))
  apply (hi.const_mul (Real.sqrt Real.pi)).congr
  filter_upwards [] with v
  rw [(KFCausalChargedCoolingMarginalScore.marginal_real_derivative
    n α r w c v hα hr hw).deriv]
  unfold coolingForm
  ring

theorem polynomial_integrable (P : Polynomial ℝ) :
    Integrable (fun v : ℝ => P.eval v*Real.exp (d*v^2-q*v)*marginal n α r w c v) ∧
    Integrable (fun v : ℝ => P.eval v*Real.exp (d*v^2-q*v)*deriv (marginal n α r w c) v) ∧
    Integrable (fun v : ℝ => P.eval v*Real.exp (d*v^2-q*v)*
      (-deriv (fun t : ℝ => marginal n α (r+(t:ℂ)) w c v) 0)) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    exact ⟨by simpa only [Polynomial.eval_add,add_mul] using hP.1.add hQ.1,
      by simpa only [Polynomial.eval_add,add_mul] using hP.2.1.add hQ.2.1,
      by simpa only [Polynomial.eval_add,add_mul] using hP.2.2.add hQ.2.2⟩
  | monomial j a =>
    exact ⟨by simpa only [Polynomial.eval_monomial,mul_assoc] using
        (marginal_monomial_integrable n α r d q w c hα hr hw hd j).const_mul a,
      by simpa only [Polynomial.eval_monomial,mul_assoc] using
        (radial_monomial_integrable n α r d q w c hα hr hw hd j).const_mul a,
      by simpa only [Polynomial.eval_monomial,mul_assoc] using
        (cooling_monomial_integrable n α r d q w c hα hr hw hd j).const_mul a⟩

#print axioms marginal_monomial_integrable
#print axioms radial_monomial_integrable
#print axioms cooling_monomial_integrable
#print axioms polynomial_integrable
end
end UnifiedTheory.Audit.KFCausalChargedQuarticScoreIntegrability
