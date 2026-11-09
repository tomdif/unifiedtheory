/- A bounded nonnegative remainder moment with density D^5(1-D).
This is an actual L2 quadratic form, continuous on the whole Hilbert
space. It is not asserted to be controlled by Hamiltonian energy. -/
import UnifiedTheory.Audit.KFCausalLongitudinalResponseCoercivity
import UnifiedTheory.Audit.KFCausalFieldCorrectionRealPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalMatterAbsorptionWeight
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect defect_positive response response_add_defect response_bounds)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalContractiveMultiplier

def weight (ε : ℝ) (x : Configuration) : ℝ := (defect ε x.1)^5*(1-defect ε x.1)

theorem weight_bounds (ε : ℝ) (hε : 0 < ε) (x : Configuration) :
    0 ≤ weight ε x ∧ weight ε x ≤ 1 := by
  have hd := (defect_positive ε x.1 hε).le
  have hr := response_bounds ε x.1 hε
  have he := response_add_defect ε x.1 hε.le
  have hd1 : defect ε x.1 ≤ 1 := by linarith
  have hp : (defect ε x.1)^5 ≤ 1 := pow_le_one₀ hd hd1
  have hn : 0 ≤ 1-defect ε x.1 := sub_nonneg.mpr hd1
  refine ⟨mul_nonneg (pow_nonneg hd 5) hn,?_⟩
  have hm := mul_le_mul_of_nonneg_right hp hn
  unfold weight
  nlinarith only [hm,hd]

theorem weight_continuous (ε : ℝ) (hε : 0 < ε) : Continuous (weight ε) := by
  have hd : Continuous (fun x : Configuration => defect ε x.1) := by
    unfold defect clock
    exact continuous_const.div ((Real.continuous_exp.comp continuous_fst).add continuous_const)
      (fun x => ne_of_gt (by positivity))
  exact (hd.pow 5).mul (continuous_const.sub hd)

def operator (ε : ℝ) (hε : 0 < ε) : Hilbert →L[ℂ] Hilbert :=
  multiplyL (fun x => (weight ε x:ℂ))
    (Complex.continuous_ofReal.comp (weight_continuous ε hε)).measurable
    (fun x => by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (weight_bounds ε hε x).1];
                 exact (weight_bounds ε hε x).2)

def moment (ε : ℝ) (hε : 0 < ε) (f : Hilbert) : ℝ := (inner ℂ f (operator ε hε f)).re

theorem operator_coe (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    operator ε hε f =ᵐ[volume] fun x => (weight ε x:ℂ)*f x := multiplyL_coe _ _ _ f

theorem moment_integral (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    Integrable (fun x => weight ε x*‖f x‖^2) volume ∧
      moment ε hε f = ∫ x, weight ε x*‖f x‖^2 := by
  have he : (fun x => (inner ℂ (f x) (operator ε hε f x)).re) =ᵐ[volume]
      fun x => weight ε x*‖f x‖^2 := by
    filter_upwards [operator_coe ε hε f] with x hx
    rw [hx]
    simpa only [Complex.ofReal_one,one_mul,mul_one,Complex.ofReal_re] using
      KFCausalFieldCorrectionRealPairing.mixed_real_inner 1 1 (weight ε x:ℂ) (f x)
  have hi := (L2.integrable_inner (𝕜 := ℂ) f (operator ε hε f)).re
  have hr := integral_re (L2.integrable_inner (𝕜 := ℂ) f (operator ε hε f))
  change (∫ x, (inner ℂ (f x) (operator ε hε f x)).re) =
    (∫ x, inner ℂ (f x) (operator ε hε f x)).re at hr
  refine ⟨hi.congr he,?_⟩
  unfold moment
  rw [L2.inner_def,← hr]
  exact integral_congr_ae he

theorem moment_bounds (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    0 ≤ moment ε hε f ∧ moment ε hε f ≤ ‖f‖^2 := by
  refine ⟨?_,?_⟩
  · rw [(moment_integral ε hε f).2]
    exact integral_nonneg (fun x => mul_nonneg (weight_bounds ε hε x).1 (sq_nonneg _))
  · have hn : ‖operator ε hε f‖ ≤ ‖f‖ := by
      exact multiply_norm_le (fun x => (weight ε x:ℂ))
        (Complex.continuous_ofReal.comp (weight_continuous ε hε)).measurable
        (fun x => by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (weight_bounds ε hε x).1];
                     exact (weight_bounds ε hε x).2) f
    exact ((re_inner_le_norm (𝕜 := ℂ) f (operator ε hε f)).trans
      (mul_le_mul_of_nonneg_left hn (norm_nonneg f))).trans_eq (by ring)

theorem moment_continuous (ε : ℝ) (hε : 0 < ε) : Continuous (moment ε hε) :=
  Complex.continuous_re.comp (continuous_id.inner (operator ε hε).continuous)

#print axioms weight_bounds
#print axioms weight_continuous
#print axioms operator_coe
#print axioms moment_integral
#print axioms moment_bounds
#print axioms moment_continuous
end
end UnifiedTheory.Audit.KFCausalMatterAbsorptionWeight
