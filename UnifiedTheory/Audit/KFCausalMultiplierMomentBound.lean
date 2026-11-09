/- Construct an actual L2 multiplier output from an integrable upper bound
for its squared norm. This is a domain proof, not a moment assumption. -/
import UnifiedTheory.Audit.KFCausalPositiveMultiplierEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalMultiplierMomentBound
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalPositiveMultiplierEnergy (l2_norm_square)

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem multiplier_output (f : Lp ℂ 2 μ) (w : X → ℝ) (hw : Measurable w)
    (F : X → ℝ) (hF : Integrable F μ)
    (hb : ∀ᵐ x ∂μ, (w x)^2*‖f x‖^2 ≤ F x) :
    ∃ q : Lp ℂ 2 μ, q =ᵐ[μ] (fun x => (w x : ℂ)*f x) ∧ ‖q‖^2 ≤ ∫ x, F x ∂μ := by
  let a := fun x => (w x : ℂ)*f x
  have ha : AEStronglyMeasurable a μ :=
    (Complex.continuous_ofReal.measurable.comp hw).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)
  have hn (x : X) : ‖a x‖^2 = (w x)^2*‖f x‖^2 := by
    simp only [a,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have hi : Integrable (fun x => ‖a x‖^2) μ := by
    apply hF.mono' (ha.norm.pow 2)
    filter_upwards [hb] with x hx
    change ‖‖a x‖^2‖ ≤ F x
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),hn]
    exact hx
  have hm : MemLp a 2 μ := (memLp_two_iff_integrable_sq_norm ha).mpr hi
  refine ⟨hm.toLp a,hm.coeFn_toLp,?_⟩
  rw [l2_norm_square]
  have he : (∫ x, ‖(hm.toLp a) x‖^2 ∂μ) = ∫ x, ‖a x‖^2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hm.coeFn_toLp] with x hx
    rw [hx]
  rw [he]
  exact integral_mono_ae hi hF (hb.mono (fun x hx => (hn x).trans_le hx))

#print axioms multiplier_output
end
end UnifiedTheory.Audit.KFCausalMultiplierMomentBound
