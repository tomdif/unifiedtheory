/- The original corrected response marginal for arbitrary finite neutral
packets whose charged widths take at most two positive values. -/
import UnifiedTheory.Audit.KFCausalPhysicalCoolingMarginal
import UnifiedTheory.Audit.KFCausalChargedCoolingTwoWidthResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalTwoWidthCoolingMarginalBound
noncomputable section
open MeasureTheory Matrix
open scoped ComplexConjugate ComplexOrder
open KFCausalChargedCoolingMarginalDerivative
open KFCausalChargedCoolingDerivative (form)
open KFCausalChargedCoolingTwoWidthResponse
open KFCausalChargedCoolingPhysicalMarginal
open KFCausalPhysicalCoolingMarginal
open KFCausalChargedCoolingGramIntegral (planeMeasure)
open KFCausalReciprocalWedgeGeometry (gamma)
open KFCausalQuarticPlaneDomination (potential potentialSlope)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalCorrelatedFourierCoolingResponse (cooling)
open KFCausalReciprocalNeutralPositiveForm (positiveDensity)

theorem width_form_lower {n : Type*} [Fintype n] (α : ℝ) (r : ℂ)
    (w : Fin 2 → ℝ) (label : n → Fin 2) (v : ℝ) (f : n → ℂ)
    (hα : 0 < α) (hr : |r.im| < r.re) (hw : ∀ i, 0 < w i) :
    (α*r.re*min (w 0) (w 1)/4)*(form (gamma α r) (w ∘ label) v f).re ≤
      widthForm α r (w ∘ label) v f := by
  have h := (fixed_v_coercivity_pullback α r w label v hα hr hw).dotProduct_mulVec_nonneg f |>.1
  have he :
      (star f ⬝ᵥ ((fun i j =>
        Complex.exp (-KFCausalChargedCoolingWidthPositive.widthSum (gamma α r)
          (w (label i)) (w (label j))*(v^2:ℝ))*
          KFCausalChargedCoolingWidthPositive.coolingB (gamma α r) ((α:ℂ)*r)
            (w (label i)) (w (label j))-
        (α*r.re*min (w 0) (w 1)/4:ℝ)*
          KFCausalChargedCoolingDerivative.kernel (gamma α r) (w (label i)) (w (label j)) v) *ᵥ f)).re =
      widthForm α r (w ∘ label) v f-
        (α*r.re*min (w 0) (w 1)/4)*(form (gamma α r) (w ∘ label) v f).re := by
    rw [show (α*r.re*min (w 0) (w 1)/4)*(form (gamma α r) (w ∘ label) v f).re =
      ((α*r.re*min (w 0) (w 1)/4:ℝ)*(form (gamma α r) (w ∘ label) v f)).re by simp]
    unfold widthForm
    rw [← Complex.sub_re]
    unfold form
    congr 1
    simp only [Function.comp_apply,Matrix.mulVec,dotProduct,sub_mul,mul_sub,Finset.sum_sub_distrib]
    congr 1
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  change 0 ≤ (star f ⬝ᵥ ((fun i j => _) *ᵥ f)).re at h
  dsimp only [gamma] at he
  rw [he] at h
  exact sub_nonneg.mp h

theorem corrected_form_bound {n : Type*} [Fintype n] (α : ℝ) (r : ℂ)
    (w : Fin 2 → ℝ) (label : n → Fin 2) (v x δ κ : ℝ) (f : n → ℂ)
    (hα : 0 < α) (hr : |r.im| < r.re) (hw : ∀ i, 0 < w i) (hδ : 0 < δ) :
    -δ*potential x*coolingForm α r (w ∘ label) v f+
      κ*v*potentialSlope x*(form (gamma α r) (w ∘ label) v f).re ≤
      (4*κ^2/(α*r.re*δ*min (w 0) (w 1)))*potential x*
        (form (gamma α r) (w ∘ label) v f).re := by
  have ha := (KFCausalChargedCoolingTwoWidthNormalization.actual_parameters_positive r hr).1
  have hm : 0 < min (w 0) (w 1) := lt_min (hw 0) (hw 1)
  have hE := (fixed_v_kernel_positive (gamma α r)
    (KFCausalChargedCoolingFixedV.actual_gamma_re_positive α r hα hr)
    (w ∘ label) (fun i => hw (label i)) v).dotProduct_mulVec_nonneg f |>.1
  change 0 ≤ (form (gamma α r) (w ∘ label) v f).re at hE
  have h := scalar_form_absorption δ (α*r.re*min (w 0) (w 1)/4) v (-κ) x
    (form (gamma α r) (w ∘ label) v f).re (widthForm α r (w ∘ label) v f)
    hδ (by positivity) hE (width_form_lower α r w label v f hα hr hw)
  have hc := cooling_form_lower α r hα hr (w ∘ label) (fun i => hw (label i)) v f
  have hW : 0 ≤ potential x := (field_weight_positive x).le
  have hc' := mul_le_mul_of_nonneg_left hc (mul_nonneg hδ.le hW)
  have hcoeff : (-κ)^2/(δ*(α*r.re*min (w 0) (w 1)/4)) =
      4*κ^2/(α*r.re*δ*min (w 0) (w 1)) := by
    field_simp
  rw [hcoeff] at h
  change -(4*κ^2/(α*r.re*δ*min (w 0) (w 1)))*potential x*
      (form (gamma α r) (w ∘ label) v f).re ≤
      δ*v^2*potential x*widthForm α r (w ∘ label) v f+
        (-κ)*v*potentialSlope x*(form (gamma α r) (w ∘ label) v f).re at h
  nlinarith only [h,hc']

theorem marginal_slope_bound (n : ℕ) (α : ℝ) (r : ℂ)
    (w : Fin 2 → ℝ) (label : Fin n → Fin 2) (f : Fin n → ℂ)
    (δ L κ v x : ℝ) (hα : 0 < α) (hr : |r.im| < r.re)
    (hw : ∀ i, 0 < w i) (hδ : 0 < δ) :
    marginalSlope n α r (w ∘ label) f δ L κ v x ≤
      (4*κ^2/(α*r.re*δ*min (w 0) (w 1)))*
        (Real.sqrt Real.pi*potential (x+L*v)*(form (conj (gamma α r)) (w ∘ label) v f).re) := by
  have hrc : |(conj r).im| < (conj r).re := by
    simpa only [Complex.conj_re,Complex.conj_im,abs_neg] using hr
  have h := mul_le_mul_of_nonneg_left
    (corrected_form_bound α (conj r) w label v (x+L*v) δ κ f hα hrc hw hδ)
    (Real.sqrt_nonneg Real.pi)
  convert h using 1
  all_goals simp only [marginalSlope,gamma,map_div₀,map_mul,map_pow,
    Complex.conj_ofReal,Complex.conj_ofNat,Complex.conj_re]
  all_goals ring

theorem physical_marginal_bound (n : ℕ) (α β : ℝ) (w : Fin 2 → ℝ)
    (label : Fin n → Fin 2) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ)
    (r rd : ℂ) (ell v x : ℝ) (hα : 0 < α) (hr : |r.im| < r.re)
    (hw : ∀ i, 0 < w i) (hδ : 0 < rd.re-ell*r.re) :
    (∫ q : ℝ × ℝ, cooling n α β (w ∘ label) b c P r rd ell
      ((q.1,![v,x]),q.2) ∂planeMeasure) ≤
    (4*(-2*(rd.re-ell*r.re)-3*ell)^2/
      (α*r.re*(rd.re-ell*r.re)*min (w 0) (w 1)))*
      ∫ q : ℝ × ℝ, positiveDensity n α β (w ∘ label) r c
        (fun i => KFCausalNeutralExponentialProfiles.exponentialProfile (b i) 1 (P i))
        ((q.1,![v,x]),q.2) ∂planeMeasure := by
  rw [cooling_marginal_integral n α β (w ∘ label) b c P r rd ell hα hr
      (fun i => hw (label i)),
    physical_marginal_integral n α β (w ∘ label) b c P r hα hr (fun i => hw (label i))]
  exact marginal_slope_bound n α r w label
    (neutralCoefficients n β (w ∘ label) b c P r v x)
    (rd.re-ell*r.re) (fieldSlope r) (-2*(rd.re-ell*r.re)-3*ell) v x hα hr hw hδ

#print axioms width_form_lower
#print axioms corrected_form_bound
#print axioms marginal_slope_bound
#print axioms physical_marginal_bound
end
end UnifiedTheory.Audit.KFCausalTwoWidthCoolingMarginalBound
