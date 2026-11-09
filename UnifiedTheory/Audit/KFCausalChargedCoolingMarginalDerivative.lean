/- Differentiation of the actual charged half-plane marginal with the
neutral imaginary coordinate frozen. The positive remainder of charged
cooling is retained explicitly. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingPhysicalMarginal
import UnifiedTheory.Audit.KFCausalChargedCoolingPhysicalClock

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedCoolingMarginalDerivative
noncomputable section
open MeasureTheory Matrix Filter
open scoped ComplexConjugate ComplexOrder Topology
open KFCausalChargedCoolingPhysicalMarginal
open KFCausalChargedCoolingGramIntegral (planeMeasure)
open KFCausalChargedCoolingDerivative (form)
open KFCausalChargedCoolingWidthPositive
open KFCausalChargedCoolingFixedV
open KFCausalPositiveKernelExponential (schur_positive)
open KFCausalReciprocalWedgeGeometry (gamma)
open KFCausalQuarticPlaneDomination (potential potentialSlope)

def coolingForm {n : Type*} [Fintype n] (α : ℝ) (r : ℂ) (w : n → ℝ)
    (v : ℝ) (c : n → ℂ) : ℝ :=
  (star c ⬝ᵥ ((fun i j => dissipation (gamma α r) ((α:ℂ)*r) (w i) (w j) v) *ᵥ c)).re

def widthForm {n : Type*} [Fintype n] (α : ℝ) (r : ℂ) (w : n → ℝ)
    (v : ℝ) (c : n → ℂ) : ℝ :=
  (star c ⬝ᵥ ((fun i j => Complex.exp (-widthSum (gamma α r) (w i) (w j)*(v^2:ℝ))*
    coolingB (gamma α r) ((α:ℂ)*r) (w i) (w j)) *ᵥ c)).re

def marginalCurve (n : ℕ) (α : ℝ) (r : ℂ) (w : Fin n → ℝ) (c : Fin n → ℂ)
    (δ L κ v x t : ℝ) : ℝ :=
  potential (x+(L+κ*t)*v) *
    ∫ q : ℝ × ℝ, ‖packetSum n (gamma α (r+((δ*t:ℝ):ℂ))) w c q.1 v q.2‖^2 ∂planeMeasure

def marginalSlope (n : ℕ) (α : ℝ) (r : ℂ) (w : Fin n → ℝ) (c : Fin n → ℂ)
    (δ L κ v x : ℝ) : ℝ :=
  Real.sqrt Real.pi * (-δ*potential (x+L*v)*coolingForm α (conj r) w v c+
    κ*v*potentialSlope (x+L*v)*(form (conj (gamma α r)) w v c).re)

theorem cooling_remainder_positive {n : Type*} [Fintype n] (α : ℝ) (r : ℂ)
    (hα : 0 < α) (hr : |r.im| < r.re) (w : n → ℝ) (hw : ∀ i, 0 < w i) (v : ℝ) :
    Matrix.PosSemidef (fun i j => dissipation (gamma α r) ((α:ℂ)*r) (w i) (w j) v-
      (v^2:ℝ)*Complex.exp (-widthSum (gamma α r) (w i) (w j)*(v^2:ℝ))*
        coolingB (gamma α r) ((α:ℂ)*r) (w i) (w j)) := by
  have hB := actual_coolingB_positive α r hα hr w hw
  have hC := actual_coolingC_positive α r hα hr w hw
  have hS := inverse_width_positive (gamma α r) (actual_gamma_re_positive α r hα hr) w hw
  have hD := ((schur_positive hB hS).smul (by norm_num : (0:ℝ) ≤ 1/2)).add hC
  have h := schur_positive (gaussian_width_positive (gamma α r) (v^2) w) hD
  convert h using 1
  ext i j
  simp only [dissipation,Matrix.smul_apply,Matrix.add_apply,Complex.real_smul,
    Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,gamma]
  ring

theorem cooling_form_lower {n : Type*} [Fintype n] (α : ℝ) (r : ℂ)
    (hα : 0 < α) (hr : |r.im| < r.re) (w : n → ℝ) (hw : ∀ i, 0 < w i)
    (v : ℝ) (c : n → ℂ) :
    v^2*widthForm α r w v c ≤ coolingForm α r w v c := by
  have h := (cooling_remainder_positive α r hα hr w hw v).dotProduct_mulVec_nonneg c |>.1
  have he :
      (star c ⬝ᵥ ((fun i j => dissipation (gamma α r) ((α:ℂ)*r) (w i) (w j) v-
        (v^2:ℝ)*Complex.exp (-widthSum (gamma α r) (w i) (w j)*(v^2:ℝ))*
          coolingB (gamma α r) ((α:ℂ)*r) (w i) (w j)) *ᵥ c)).re =
      coolingForm α r w v c-v^2*widthForm α r w v c := by
    unfold coolingForm widthForm
    rw [← Complex.re_ofReal_mul, ← Complex.sub_re]
    congr 1
    simp only [Matrix.mulVec,dotProduct,sub_mul,mul_sub,Finset.sum_sub_distrib]
    congr 1
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he] at h
  simp only [Complex.zero_re] at h
  linarith

theorem marginal_curve_zero (n : ℕ) (α : ℝ) (r : ℂ) (w : Fin n → ℝ) (c : Fin n → ℂ)
    (δ L κ v x : ℝ) (hα : 0 < α) (hr : |r.im| < r.re) (hw : ∀ i, 0 < w i) :
    marginalCurve n α r w c δ L κ v x 0 =
      Real.sqrt Real.pi*potential (x+L*v)*(form (conj (gamma α r)) w v c).re := by
  simp only [marginalCurve,mul_zero,add_zero,Complex.ofReal_zero]
  rw [packet_square_integral n (gamma α r) w c (actual_gamma_re_positive α r hα hr) hw v]
  ring

theorem marginal_curve_derivative (n : ℕ) (α : ℝ) (r : ℂ) (w : Fin n → ℝ) (c : Fin n → ℂ)
    (δ L κ v x : ℝ) (hα : 0 < α) (hr : |r.im| < r.re) (hw : ∀ i, 0 < w i) :
    HasDerivAt (marginalCurve n α r w c δ L κ v x)
      (marginalSlope n α r w c δ L κ v x) 0 := by
  have hrc : |(conj r).im| < (conj r).re := by
    simpa only [Complex.conj_re,Complex.conj_im,abs_neg] using hr
  have hK := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0
    (KFCausalChargedCoolingPhysicalClock.rate_form_derivative α (conj r) hα hrc w hw v δ c)
  have hKe : HasDerivAt
      (fun t : ℝ => (form (conj (gamma α (r+((δ*t:ℝ):ℂ)))) w v c).re)
      (-δ*coolingForm α (conj r) w v c) 0 := by
    simpa only [gamma,Function.comp_def,Complex.reCLM_apply,map_div₀,map_mul,map_pow,
      map_add,Complex.conj_ofReal,Complex.conj_ofNat,Complex.real_smul,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.neg_re,zero_mul,sub_zero,
      coolingForm,neg_mul,mul_neg] using hK
  have hP : HasDerivAt (fun t : ℝ => potential (x+(L+κ*t)*v))
      (κ*v*potentialSlope (x+L*v)) 0 := by
    have h := (KFCausalQuarticPlaneDomination.potential_derivative (x+L*v)).comp_of_eq 0
      ((((hasDerivAt_id (0:ℝ)).const_mul κ).const_add L).mul_const v |>.const_add x) (by simp)
    convert h using 1
    ring
  have hd := ((hP.mul hKe).const_mul (Real.sqrt Real.pi)).congr_deriv
    (show Real.sqrt Real.pi*(κ*v*potentialSlope (x+L*v)*
        (form (conj (gamma α (r+((δ*0:ℝ):ℂ)))) w v c).re+
        potential (x+(L+κ*0)*v)*(-δ*coolingForm α (conj r) w v c)) =
        marginalSlope n α r w c δ L κ v x by
      simp only [mul_zero,Complex.ofReal_zero,add_zero,marginalSlope]
      ring)
  apply hd.congr_of_eventuallyEq
  have hp : ∀ᶠ t : ℝ in 𝓝 0, 0 < (gamma α (r+((δ*t:ℝ):ℂ))).re := by
    have hc : Continuous (fun t : ℝ => (gamma α (r+((δ*t:ℝ):ℂ))).re) := by
      unfold gamma
      fun_prop
    have hz : 0 < (gamma α (r+((δ*0:ℝ):ℂ))).re := by
      simpa only [mul_zero,Complex.ofReal_zero,add_zero] using
        actual_gamma_re_positive α r hα hr
    exact hc.continuousAt.eventually (eventually_gt_nhds
      hz)
  filter_upwards [hp] with t ht
  unfold marginalCurve
  rw [packet_square_integral n _ w c ht hw v]
  dsimp only [Pi.mul_apply]
  ring

#print axioms cooling_remainder_positive
#print axioms cooling_form_lower
#print axioms marginal_curve_zero
#print axioms marginal_curve_derivative
end
end UnifiedTheory.Audit.KFCausalChargedCoolingMarginalDerivative
