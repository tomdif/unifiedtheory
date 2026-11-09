/- Strong differentiation of a measurable real phase on its exact
weighted L2 domain, using a proved difference-quotient majorant. -/
import UnifiedTheory.Audit.KFCausalDominatedL2Derivative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.RealDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalL2PhaseDerivative
noncomputable section
open MeasureTheory Filter
open scoped Topology
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem phase_slope_bound (t w : ℝ) (z : ℂ) :
    ‖t⁻¹ • (Complex.exp (Complex.I*((t*w:ℝ):ℂ))*z-z)‖ ≤ ‖(w:ℂ)*z‖ := by
  by_cases ht : t=0
  · simpa only [ht,inv_zero,zero_smul,norm_zero] using norm_nonneg ((w:ℂ)*z)
  rw [show Complex.exp (Complex.I*((t*w:ℝ):ℂ))*z-z =
    (Complex.exp (Complex.I*((t*w:ℝ):ℂ))-1)*z by ring,norm_smul,norm_mul]
  have hb := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (Real.norm_exp_I_mul_ofReal_sub_one_le (x := t*w)) (norm_nonneg z))
    (norm_nonneg t⁻¹)
  apply hb.trans_eq
  simp only [norm_inv,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  field_simp [abs_ne_zero.mpr ht]

theorem derivative_zero (u : ℝ → Lp ℂ 2 μ) (w : X → ℝ) (f g : Lp ℂ 2 μ)
    (hu : ∀ t, u t =ᵐ[μ] fun x => Complex.exp (Complex.I*((t*w x:ℝ):ℂ))*f x)
    (hg : g =ᵐ[μ] fun x => (w x:ℂ)*f x) :
    HasDerivAt u (Complex.I • g) 0 := by
  let d : X → ℂ := fun x => Complex.I*((w x:ℂ)*f x)
  have hd : (Complex.I • g : Lp ℂ 2 μ) =ᵐ[μ] d := by
    filter_upwards [Lp.coeFn_smul Complex.I g,hg] with x hx hgx
    simp only [Pi.smul_apply,smul_eq_mul,hgx,d] at hx ⊢
    exact hx
  have hm : MemLp d 2 μ := (Lp.memLp (Complex.I • g)).ae_eq hd
  have he : hm.toLp d = Complex.I • g := Lp.ext (hm.coeFn_toLp.trans hd.symm)
  rw [← he]
  apply KFCausalDominatedL2Derivative.hasDerivAt_represented u _ hu d hm (fun x => ‖g x‖)
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g))
  · exact Eventually.of_forall (fun t => hg.mono (fun x hx => by
      simpa only [zero_mul,Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_mul,hx]
        using phase_slope_bound t (w x) (f x)))
  · filter_upwards [] with x
    have hp := (((hasDerivAt_id (0:ℝ)).mul_const (w x)).ofReal_comp.const_mul Complex.I).cexp.mul_const (f x)
    simpa only [id_eq,zero_mul,Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_mul,d,mul_assoc] using hp

#print axioms phase_slope_bound
#print axioms derivative_zero
end
end UnifiedTheory.Audit.KFCausalL2PhaseDerivative
