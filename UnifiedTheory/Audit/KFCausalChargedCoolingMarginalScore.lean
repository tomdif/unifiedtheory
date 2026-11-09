/- The positive boundary-score kernel gives an inequality for the
literal coherent charged half-plane marginal and its actual derivatives.
No response discriminant or independent coefficient-jet hypothesis is used. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingBoundaryScore

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedCoolingMarginalScore
noncomputable section
open MeasureTheory Matrix Filter
open scoped ComplexConjugate ComplexOrder Topology
open KFCausalChargedCoolingBoundaryScore
open KFCausalChargedCoolingPhysicalMarginal (packetSum packet_square_integral)
open KFCausalChargedCoolingGramIntegral (planeMeasure)
open KFCausalChargedCoolingDerivative (form)
open KFCausalChargedCoolingMarginalDerivative (coolingForm)
open KFCausalChargedCoolingFixedV (dissipation actual_gamma_re_positive)
open KFCausalReciprocalWedgeGeometry (gamma)

def radialForm {n : Type*} [Fintype n] (p : ℂ) (w : n → ℝ) (v : ℝ) (c : n → ℂ) : ℂ :=
  star c ⬝ᵥ ((fun i j => radialSlope p (w i) (w j) v) *ᵥ c)

def marginal (n : ℕ) (α : ℝ) (r : ℂ) (w : Fin n → ℝ) (c : Fin n → ℂ)
    (v : ℝ) : ℝ :=
  ∫ q : ℝ × ℝ, ‖packetSum n (gamma α r) w c q.1 v q.2‖^2 ∂planeMeasure

theorem radial_form_derivative {n : Type*} [Fintype n]
    (p : ℂ) (w : n → ℝ) (v : ℝ) (c : n → ℂ) :
    HasDerivAt (fun t : ℝ => form p w t c) (radialForm p w v c) v := by
  have hd := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    (HasDerivAt.sum (u := Finset.univ) (fun j _ =>
      (radial_kernel_derivative p (w i) (w j) v).mul_const (c j))).const_mul (star (c i)))
  convert hd using 1
  · funext t
    simp only [form,dotProduct,Matrix.mulVec,Pi.star_apply,Finset.sum_apply]

theorem marginal_radial_derivative (n : ℕ) (α : ℝ) (r : ℂ)
    (w : Fin n → ℝ) (c : Fin n → ℂ) (v : ℝ)
    (hα : 0 < α) (hr : |r.im| < r.re) (hw : ∀ i, 0 < w i) :
    HasDerivAt (marginal n α r w c)
      (Real.sqrt Real.pi*(radialForm (conj (gamma α r)) w v c).re) v := by
  have hd := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt v
    (radial_form_derivative (conj (gamma α r)) w v c)).const_mul (Real.sqrt Real.pi)
  apply hd.congr_of_eventuallyEq
  filter_upwards [] with t
  exact packet_square_integral n (gamma α r) w c
    (actual_gamma_re_positive α r hα hr) hw t

theorem marginal_real_derivative (n : ℕ) (α : ℝ) (r : ℂ)
    (w : Fin n → ℝ) (c : Fin n → ℂ) (v : ℝ)
    (hα : 0 < α) (hr : |r.im| < r.re) (hw : ∀ i, 0 < w i) :
    HasDerivAt (fun t : ℝ => marginal n α (r+(t:ℂ)) w c v)
      (-Real.sqrt Real.pi*coolingForm α (conj r) w v c) 0 := by
  have hd := KFCausalChargedCoolingMarginalDerivative.marginal_curve_derivative
    n α r w c 1 0 0 v 0 hα hr hw
  change HasDerivAt (fun t => KFCausalChargedCoolingMarginalDerivative.marginalCurve
    n α r w c 1 0 0 v 0 t) _ _ at hd
  simpa only [KFCausalChargedCoolingMarginalDerivative.marginalCurve,
    KFCausalChargedCoolingMarginalDerivative.marginalSlope,
    KFCausalQuarticPlaneDomination.potential,KFCausalQuarticPlaneDomination.potentialSlope,
    marginal,one_mul,zero_mul,zero_add,add_zero,zero_pow (by decide : (2:ℕ) ≠ 0),
    zero_pow (by decide : (3:ℕ) ≠ 0),zero_pow (by decide : (4:ℕ) ≠ 0),zero_div,
    mul_one,neg_mul,mul_neg] using hd

theorem actual_marginal_score (n : ℕ) (α : ℝ) (r : ℂ)
    (w : Fin n → ℝ) (c : Fin n → ℂ) (v : ℝ)
    (hα : 0 < α) (hr : |r.im| < r.re) (hw : ∀ i, 0 < w i) :
    (scoreRate r/2+1/r.re)*marginal n α r w c v-
      (scoreRate r/2)*v*deriv (marginal n α r w c) v ≤
      -deriv (fun t : ℝ => marginal n α (r+(t:ℂ)) w c v) 0 := by
  have hrc : |(conj r).im| < (conj r).re := by
    simpa only [Complex.conj_im,Complex.conj_re,abs_neg] using hr
  have he (s : ℂ) : conj (gamma α s) = gamma α (conj s) := by
    simp only [gamma,map_div₀,map_mul,map_pow,Complex.conj_ofReal,Complex.conj_ofNat]
  have hs : scoreRate (conj r) = scoreRate r := by
    simp [scoreRate]
  have h := (score_kernel_positive α (conj r) hα hrc w hw v).dotProduct_mulVec_nonneg c |>.1
  have hform :
      (star c ⬝ᵥ ((fun i j => dissipation (gamma α (conj r)) ((α:ℂ)*conj r) (w i) (w j) v-
        ((scoreRate r/2+1/r.re:ℝ):ℂ)*KFCausalChargedCoolingDerivative.kernel
          (gamma α (conj r)) (w i) (w j) v+
        ((scoreRate r/2:ℝ):ℂ)*(v:ℂ)*radialSlope (gamma α (conj r)) (w i) (w j) v) *ᵥ c)).re =
      coolingForm α (conj r) w v c-
        (scoreRate r/2+1/r.re)*(form (gamma α (conj r)) w v c).re+
        (scoreRate r/2)*v*(radialForm (gamma α (conj r)) w v c).re := by
    unfold coolingForm form radialForm
    rw [← Complex.re_ofReal_mul,← Complex.re_ofReal_mul,
      ← Complex.sub_re,← Complex.add_re]
    congr 1
    simp only [Matrix.mulVec,dotProduct,sub_mul,add_mul,mul_sub,mul_add,
      Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.mul_sum]
    simp only [Complex.ofReal_mul,mul_assoc,mul_left_comm,mul_comm]
  simp only [hs,Complex.conj_re,Complex.zero_re] at h
  rw [hform] at h
  have h' := mul_nonneg (Real.sqrt_nonneg Real.pi) h
  rw [(marginal_real_derivative n α r w c v hα hr hw).deriv,
    (marginal_radial_derivative n α r w c v hα hr hw).deriv]
  unfold marginal
  rw [packet_square_integral n (gamma α r) w c
    (actual_gamma_re_positive α r hα hr) hw v,he]
  nlinarith only [h']

#print axioms radial_form_derivative
#print axioms marginal_radial_derivative
#print axioms marginal_real_derivative
#print axioms actual_marginal_score
end
end UnifiedTheory.Audit.KFCausalChargedCoolingMarginalScore
