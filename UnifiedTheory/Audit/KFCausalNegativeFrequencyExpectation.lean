/- Exact expectation of actual pure-clock momentum on fixed-source
Gaussian packets. The frequency coefficient is a strictly positive
inverse-clock pairing on every nonzero state. -/
import UnifiedTheory.Audit.KFCausalNegativeFrequencyMomentum
import UnifiedTheory.Audit.KFCausalClockFloorDefectEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalNegativeFrequencyExpectation
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chart)
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf (inverseAction inverseAction_ne_zero)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockCommonDomain (clockInverse clockInverse_coe)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedClockMomentum
  (state state_coe dampedState dampedState_eq_inverseAction)
open UnifiedTheory.Audit.KFCausalPureClockOutputMultipliers (coefficient)
open UnifiedTheory.Audit.KFCausalOriginalPureClockOutput (preOutput preOutput_coe profile_differential)
open UnifiedTheory.Audit.KFCausalSourcedMomentumFactors (pureOutput)

theorem multiplier_real_pairing {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (m : X → ℂ) (f g : Lp ℂ 2 μ) (hg : g =ᵐ[μ] fun x => m x*f x) :
    (inner ℂ f g).re = ∫ x, (m x).re*‖f x‖^2 ∂μ := by
  have he := integral_re (L2.integrable_inner (𝕜 := ℂ) f g)
  change (∫ x, (inner ℂ (f x) (g x)).re ∂μ) = (∫ x, inner ℂ (f x) (g x) ∂μ).re at he
  rw [L2.inner_def,← he]
  apply integral_congr_ae
  filter_upwards [hg] with x hx
  rw [hx]
  change (inner ℂ (f x) (m x • f x)).re = _
  rw [inner_smul_right,inner_self_eq_norm_sq_to_K]
  change (m x*(‖f x‖:ℂ)^2).re = _
  rw [← Complex.ofReal_pow]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]

theorem inverse_pairing (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    (inner ℂ f (clockInverse ε hε f)).re = ‖inverseAction ε hε f‖^2 := by
  have he : inner ℂ f (clockInverse ε hε f) =
      inner ℂ (inverseAction ε hε f) (inverseAction ε hε f) := by
    change inner ℂ f ((1/(ε:ℂ)) • KFCausalClockFloorDefectOperator.defectOperator ε hε f) = _
    rw [inner_smul_right,← KFCausalClockFloorDefectEnergy.inverse_defect_pairing,
      ← mul_assoc,one_div_mul_cancel (Complex.ofReal_ne_zero.mpr hε.ne'),one_mul]
  exact (congrArg Complex.re he).trans (inner_self_eq_norm_sq (𝕜 := ℂ) _)

theorem inverse_pairing_positive (ε : ℝ) (hε : 0 < ε) (f : Hilbert) (hf : f ≠ 0) :
    0 < (inner ℂ f (clockInverse ε hε f)).re := by
  rw [inverse_pairing]
  exact sq_pos_of_pos (norm_pos_iff.mpr (inverseAction_ne_zero ε hε f hf))

theorem inverse_pairing_integral (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    (inner ℂ f (clockInverse ε hε f)).re =
      ∫ x : Configuration, (clock ε x.1)⁻¹*‖f x‖^2 := by
  simpa only [← Complex.ofReal_inv,Complex.ofReal_re] using
    multiplier_real_pairing volume (fun x : Configuration => (clock ε x.1:ℂ)⁻¹) f
      (clockInverse ε hε f) (clockInverse_coe ε hε f)

theorem output_coefficient_real (ε a h p s : ℝ) :
    ((-Complex.I*(h:ℂ))*(coefficient ε p s-2*(a:ℂ)*(chart ε s:ℂ))).re =
      h*p*(clock ε s)⁻¹ := by
  simp [coefficient,← Complex.ofReal_inv,Complex.mul_re,Complex.mul_im]
  ring

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (C : ℂ) (p q : ℝ) (b : Fin 5 → ℂ)
local notation "S" r:arg => state ε a α β hε ha hα hβ hw C r b

theorem inverse_pairing_frequency :
    (inner ℂ (S p) (clockInverse ε hε (S p))).re =
      (inner ℂ (S q) (clockInverse ε hε (S q))).re := by
  rw [inverse_pairing,inverse_pairing,
    ← dampedState_eq_inverseAction,← dampedState_eq_inverseAction]
  congr 1
  exact KFCausalNegativeFrequencyEnergy.profileState_norm_frequency α β hα hβ hw C p q b _ _

theorem pureOutput_density (h : ℝ) :
    pureOutput ε a α β hε ha hα hβ hw C p b h =ᵐ[volume]
      fun x => (-Complex.I*(h:ℂ))*(coefficient ε p x.1-2*(a:ℂ)*(chart ε x.1:ℂ))*(S p) x := by
  filter_upwards [Lp.coeFn_smul (-Complex.I*(h:ℂ)) (preOutput ε a hε ha C p α β hα hβ hw b),
    preOutput_coe ε a hε ha C p α β hα hβ hw b,
    state_coe ε a α β hε ha hα hβ hw C p b] with x hs ho hf
  change ((-Complex.I*(h:ℂ)) • preOutput ε a hε ha C p α β hα hβ hw b) x = _
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul,ho,hf,profile_differential ε a hε C p α β b x,mul_assoc]

theorem pureOutput_expectation (h : ℝ) :
    (inner ℂ (S p) (pureOutput ε a α β hε ha hα hβ hw C p b h)).re =
      h*p*(inner ℂ (S 0) (clockInverse ε hε (S 0))).re := by
  have he := multiplier_real_pairing volume
    (fun x : Configuration => (-Complex.I*(h:ℂ))*(coefficient ε p x.1-2*(a:ℂ)*(chart ε x.1:ℂ)))
    (S p) (pureOutput ε a α β hε ha hα hβ hw C p b h)
    (pureOutput_density ε a α β hε ha hα hβ hw C p b h)
  simp only [output_coefficient_real] at he
  simp only [mul_assoc] at he
  rw [integral_const_mul,integral_const_mul,← inverse_pairing_integral ε hε (S p),
    inverse_pairing_frequency ε a α β hε ha hα hβ hw C p 0 b] at he
  simpa only [mul_assoc] using he

#print axioms multiplier_real_pairing
#print axioms inverse_pairing
#print axioms inverse_pairing_positive
#print axioms inverse_pairing_integral
#print axioms output_coefficient_real
#print axioms inverse_pairing_frequency
#print axioms pureOutput_density
#print axioms pureOutput_expectation
end
end UnifiedTheory.Audit.KFCausalNegativeFrequencyExpectation
