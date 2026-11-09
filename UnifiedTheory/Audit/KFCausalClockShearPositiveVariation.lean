/- A clock-multiplied imaginary-shear curve has nondecreasing weighted
shear expectation. The domain statements and strong derivatives are
explicit hypotheses here, derived for the actual Gaussian in the sequel. -/
import UnifiedTheory.Audit.KFCausalActualImaginaryShearCurve
import UnifiedTheory.Audit.KFCausalClockShearRealMultiplier
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalClockShearPositiveVariation
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (Interval)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum shear_selfAdjoint)
open UnifiedTheory.Audit.KFCausalClockShearRealMultiplier (clock_graph)
open UnifiedTheory.Audit.KFCausalSelfAdjointCoreWeakGraph (graph_iff_weak)

variable (C W : Hilbert →L[ℂ] Hilbert) (c w : ℝ → ℂ)
variable (hC : ∀ f : Hilbert, C f =ᵐ[volume] fun x => c x.1*f x)
variable (hW : ∀ f : Hilbert, W f =ᵐ[volume] fun x => w x.1*f x)

include hC hW in
theorem clock_commute (f : Hilbert) : W (C f) = C (W f) := by
  apply Lp.ext
  filter_upwards [hW (C f),hC f,hC (W f),hW f] with x hwc hc hcw hw
  rw [hwc,hc,hcw,hw]
  ring

private theorem scalar_re (z v : ℂ) : (inner ℂ z (v*z)).re = v.re*‖z‖^2 := by
  change (inner ℂ z (v • z)).re = _
  rw [inner_smul_right,inner_self_eq_norm_sq_to_K]
  change (v*(‖z‖:ℂ)^2).re = _
  rw [← Complex.ofReal_pow]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]

include hC in
theorem density_integrable (f : Hilbert) :
    Integrable (fun x => (c x.1).re*‖f x‖^2) volume := by
  apply ((L2.integrable_inner (𝕜 := ℂ) f (C f)).re).congr
  filter_upwards [hC f] with x hx
  change (inner ℂ (f x) (C f x)).re = _
  rw [hx,scalar_re]

include hC in
theorem pairing_integral (f : Hilbert) :
    (inner ℂ f (C f)).re = ∫ x, (c x.1).re*‖f x‖^2 := by
  have he := integral_re (L2.integrable_inner (𝕜 := ℂ) f (C f))
  change (∫ x, (inner ℂ (f x) (C f x)).re) =
    (∫ x, inner ℂ (f x) (C f x)).re at he
  rw [L2.inner_def,← he]
  apply integral_congr_ae
  filter_upwards [hC f] with x hx
  rw [hx,scalar_re]

include hC in
theorem pairing_nonnegative (hc : ∀ s, 0 ≤ (c s).re) (f : Hilbert) :
    0 ≤ (inner ℂ f (C f)).re := by
  rw [pairing_integral C c hC]
  exact integral_nonneg (fun x => mul_nonneg (hc x.1) (sq_nonneg _))

include hC hW in
theorem weighted_graph_pairing (h : ℝ) (hh : h ≠ 0) (f j k : Hilbert)
    (hf : (f,j) ∈ (shearMomentum h).graph) (hj : (j,k) ∈ (shearMomentum h).graph) :
    inner ℂ (W f) (W (C k)) = inner ℂ (W j) (W (C j)) := by
  have hwf := clock_graph W w hW h hh f j hf
  have hcj := clock_graph C c hC h hh j k hj
  have hwcj := clock_graph W w hW h hh (C j) (C k) hcj
  exact ((graph_iff_weak _ (shear_selfAdjoint h hh) (W (C j)) (W (C k))).mp hwcj
    (W f) (W j) hwf).symm

def expectation (F J : ℝ → Hilbert) (t : ℝ) : ℝ := (inner ℂ (W (F t)) (W (J t))).re

theorem expectation_continuous (F J : ℝ → Hilbert) (hF : Continuous F) (hJ : Continuous J) :
    Continuous (expectation W F J) :=
  Complex.continuous_re.comp ((W.continuous.comp hF).inner (W.continuous.comp hJ))

include hC hW in
theorem expectation_derivative (h : ℝ) (hh : h ≠ 0) (F J : ℝ → Hilbert) (k : Hilbert) (t : ℝ)
    (hF : HasDerivAt F (C (J t)) t) (hJ : HasDerivAt J (C k) t)
    (hf : (F t,J t) ∈ (shearMomentum h).graph) (hj : (J t,k) ∈ (shearMomentum h).graph) :
    HasDerivAt (expectation W F J) (2*(inner ℂ (W (J t)) (C (W (J t)))).re) t := by
  have hdF := (W.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hF
  have hdJ := (W.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hJ
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hdF.inner ℂ hdJ)
  change HasDerivAt (expectation W F J)
    (inner ℂ (W (F t)) (W (C k)) + inner ℂ (W (C (J t))) (W (J t))).re t at hd
  have hs : (inner ℂ (W (C (J t))) (W (J t))).re =
      (inner ℂ (W (J t)) (W (C (J t)))).re := inner_re_symm (𝕜 := ℂ) _ _
  convert hd using 1
  rw [weighted_graph_pairing C W c w hC hW h hh (F t) (J t) k hf hj,Complex.add_re,
    hs,clock_commute C W c w hC hW]
  ring

include hC hW in
theorem expectation_monotone (hc : ∀ s, 0 ≤ (c s).re)
    (h : ℝ) (hh : h ≠ 0) (F J : ℝ → Hilbert) (K : Interval → Hilbert)
    (hF : Continuous F) (hJ : Continuous J)
    (hdF : ∀ t (_ht : t ∈ Ioo (0:ℝ) 1), HasDerivAt F (C (J t)) t)
    (hdJ : ∀ t (ht : t ∈ Ioo (0:ℝ) 1), HasDerivAt J (C (K ⟨t,ht.1.le,ht.2.le⟩)) t)
    (hf : ∀ t : Interval, (F t,J t) ∈ (shearMomentum h).graph)
    (hj : ∀ t : Interval, (J t,K t) ∈ (shearMomentum h).graph) :
    MonotoneOn (expectation W F J) (Icc (0:ℝ) 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
    (expectation_continuous W F J hF hJ).continuousOn
    (f' := fun t => 2*(inner ℂ (W (J t)) (C (W (J t)))).re)
  · intro t ht
    rw [interior_Icc] at ht
    exact (expectation_derivative C W c w hC hW h hh F J (K ⟨t,ht.1.le,ht.2.le⟩) t
      (hdF t ht) (hdJ t ht) (hf ⟨t,ht.1.le,ht.2.le⟩) (hj ⟨t,ht.1.le,ht.2.le⟩)).hasDerivWithinAt
  · intro t _
    exact mul_nonneg (by norm_num) (pairing_nonnegative C c hC hc (W (J t)))

#print axioms clock_commute
#print axioms density_integrable
#print axioms pairing_integral
#print axioms pairing_nonnegative
#print axioms weighted_graph_pairing
#print axioms expectation_continuous
#print axioms expectation_derivative
#print axioms expectation_monotone
end
end UnifiedTheory.Audit.KFCausalClockShearPositiveVariation
