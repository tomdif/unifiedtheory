/- The actual charged packet energy contracts under a positive real shift.
Field coefficients and the real exponential tilt are fixed throughout;
this is the charged subresponse, not the complete clock response. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingGramIntegral
import UnifiedTheory.Audit.KFCausalChargedCoolingContraction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalChargedCoolingEnergyContraction
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalChargedCoolingGramIntegral
open KFCausalChargedFourierPolynomialGram (Index family)
open KFCausalChargedFourierGaussianMoments (Charged chargedMeasure)
open KFCausalChargedCoolingDerivative (form)
open KFCausalChargedCoolingFixedV (actual_gamma_re_positive)
open KFCausalChargedCoolingContraction

local instance : SFinite planeMeasure := by unfold planeMeasure; infer_instance

def fixedEnergy (n : ℕ) (p : ℂ) (w : Fin n → ℝ) (c : ℝ)
    (a : Fin n → Fin 3 → ℂ) (v : ℝ) : ℝ :=
  ∫ q : ℝ × ℝ, ‖family n p w c a q.1 v q.2‖^2 ∂planeMeasure

def energy (n : ℕ) (p : ℂ) (w : Fin n → ℝ) (c : ℝ)
    (a : Fin n → Fin 3 → ℂ) : ℝ :=
  ∫ q : Charged, ‖family n p w c a q.1.1 q.1.2 q.2‖^2 ∂chargedMeasure

theorem fixed_energy_integrable (n : ℕ) (p : ℂ) (w : Fin n → ℝ) (c : ℝ)
    (a : Fin n → Fin 3 → ℂ) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (v : ℝ) :
    Integrable (fun q : ℝ × ℝ => ‖family n p w c a q.1 v q.2‖^2) planeMeasure :=
  (family_fixed_integrable n p w c a hp hw v).re

theorem fixed_energy_form (n : ℕ) (p : ℂ) (w : Fin n → ℝ) (c : ℝ)
    (a : Fin n → Fin 3 → ℂ) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (v : ℝ) :
    fixedEnergy n p w c a v = Real.sqrt Real.pi *
      (form (conj p) (fun I : Index n => w I.1) v (fixedCoefficients a c v)).re := by
  have hi := family_fixed_integrable n p w c a hp hw v
  have he := congrArg Complex.re (family_fixed_integral n p w c a hp hw v)
  have hr : (∫ q : ℝ × ℝ, (((‖family n p w c a q.1 v q.2‖^2:ℝ):ℂ)).re ∂planeMeasure) =
      (∫ q : ℝ × ℝ, ((‖family n p w c a q.1 v q.2‖^2:ℝ):ℂ) ∂planeMeasure).re := integral_re hi
  rw [← hr] at he
  simpa only [fixedEnergy,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,zero_mul,sub_zero] using he

theorem fixed_energy_contraction (n : ℕ) (α : ℝ) (r : ℂ) (w : Fin n → ℝ) (c : ℝ)
    (a : Fin n → Fin 3 → ℂ) (hα : 0 < α) (hr : |r.im| < r.re) (hw : ∀ i, 0 < w i)
    (v h : ℝ) (hh : 0 ≤ h) :
    fixedEnergy n ((α:ℂ)*(r+(h:ℂ))^2/2) w c a v ≤
      fixedEnergy n ((α:ℂ)*r^2/2) w c a v := by
  rw [fixed_energy_form n _ w c a (actual_gamma_re_positive α _ hα (translated_sector r hr h hh)) hw v,
    fixed_energy_form n _ w c a (actual_gamma_re_positive α r hα hr) hw v]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  have hc : |(conj r).im| < (conj r).re := by simpa only [Complex.conj_im,Complex.conj_re,abs_neg] using hr
  simpa only [map_div₀,map_mul,map_pow,map_add,Complex.conj_ofReal,Complex.conj_ofNat] using
    positive_shift_contraction α (conj r) hα hc (fun I : Index n => w I.1)
      (fun I => hw I.1) v h hh (fixedCoefficients a c v)

private def reorder : Charged ≃ᵐ ℝ × (ℝ × ℝ) :=
  (MeasurableEquiv.prodCongr MeasurableEquiv.prodComm (MeasurableEquiv.refl ℝ)).trans MeasurableEquiv.prodAssoc

private theorem reorder_preserving :
    MeasurePreserving reorder chargedMeasure (volume.prod planeMeasure) :=
  (measurePreserving_prodAssoc volume volume (volume.restrict (Set.Ioi 0))).comp
    (MeasurePreserving.prod Measure.measurePreserving_swap (MeasurePreserving.id _))

theorem reordered_integrable (n : ℕ) (p : ℂ) (w : Fin n → ℝ) (c : ℝ)
    (a : Fin n → Fin 3 → ℂ) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) :
    Integrable (fun q : ℝ × (ℝ × ℝ) => ‖family n p w c a q.2.1 q.1 q.2.2‖^2)
      (volume.prod planeMeasure) := by
  apply (reorder_preserving.integrable_comp_emb reorder.measurableEmbedding).mp
  exact (KFCausalChargedFourierPolynomialGram.family_square_integrable n p w c a hp hw).re

theorem fixed_energy_marginal_integrable (n : ℕ) (p : ℂ) (w : Fin n → ℝ) (c : ℝ)
    (a : Fin n → Fin 3 → ℂ) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) :
    Integrable (fixedEnergy n p w c a) :=
  (reordered_integrable n p w c a hp hw).integral_prod_left

theorem energy_order (n : ℕ) (p : ℂ) (w : Fin n → ℝ) (c : ℝ)
    (a : Fin n → Fin 3 → ℂ) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) :
    energy n p w c a = ∫ v, fixedEnergy n p w c a v := by
  have he := reorder_preserving.integral_comp reorder.measurableEmbedding
    (fun q : ℝ × (ℝ × ℝ) => ‖family n p w c a q.2.1 q.1 q.2.2‖^2)
  change energy n p w c a = _ at he
  rw [he,integral_prod _ (reordered_integrable n p w c a hp hw)]
  rfl

theorem energy_contraction (n : ℕ) (α : ℝ) (r : ℂ) (w : Fin n → ℝ) (c : ℝ)
    (a : Fin n → Fin 3 → ℂ) (hα : 0 < α) (hr : |r.im| < r.re) (hw : ∀ i, 0 < w i)
    (h : ℝ) (hh : 0 ≤ h) :
    energy n ((α:ℂ)*(r+(h:ℂ))^2/2) w c a ≤ energy n ((α:ℂ)*r^2/2) w c a := by
  rw [energy_order n _ w c a (actual_gamma_re_positive α _ hα (translated_sector r hr h hh)) hw,
    energy_order n _ w c a (actual_gamma_re_positive α r hα hr) hw]
  exact integral_mono
    (fixed_energy_marginal_integrable n _ w c a (actual_gamma_re_positive α _ hα (translated_sector r hr h hh)) hw)
    (fixed_energy_marginal_integrable n _ w c a (actual_gamma_re_positive α r hα hr) hw)
    (fun v => fixed_energy_contraction n α r w c a hα hr hw v h hh)

#print axioms fixed_energy_integrable
#print axioms fixed_energy_form
#print axioms fixed_energy_contraction
#print axioms reordered_integrable
#print axioms fixed_energy_marginal_integrable
#print axioms energy_order
#print axioms energy_contraction
end
end UnifiedTheory.Audit.KFCausalChargedCoolingEnergyContraction
