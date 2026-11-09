/- A strong L2 derivative agrees almost everywhere with a proved
pointwise derivative of representatives. The exceptional sets may depend
on time: a countable subsequence and convergence in measure handle this. -/
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalLpDerivativeRepresentative
noncomputable section
open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem derivative_representative (u : ℝ → Lp ℂ 2 μ) (v : Lp ℂ 2 μ)
    (F : ℝ → X → ℂ) (g : X → ℂ)
    (hu : ∀ t, (u t : X → ℂ) =ᵐ[μ] F t)
    (hd : HasDerivAt u v 0) (hF : ∀ x, HasDerivAt (fun t => F t x) (g x) 0) :
    (v : X → ℂ) =ᵐ[μ] g := by
  let q : ℝ → Lp ℂ 2 μ := fun t => t⁻¹ • (u t-u 0)
  have hq : Tendsto q (𝓝[≠] 0) (𝓝 v) := by
    simpa only [zero_add] using hd.tendsto_slope_zero
  obtain ⟨ns,hns,hae⟩ := (tendstoInMeasure_of_tendsto_Lp hq).exists_seq_tendsto_ae'
  have hrep : ∀ n : ℕ, (q (ns n) : X → ℂ) =ᵐ[μ]
      fun x => (ns n)⁻¹ • (F (ns n) x-F 0 x) := by
    intro n
    filter_upwards [Lp.coeFn_smul ((ns n)⁻¹) (u (ns n)-u 0),
      Lp.coeFn_sub (u (ns n)) (u 0),hu (ns n),hu 0] with x hs hsub hn hzero
    change ((ns n)⁻¹ • (u (ns n)-u 0) : Lp ℂ 2 μ) x = _
    rw [hs]
    simp only [Pi.smul_apply,hsub,Pi.sub_apply,hn,hzero]
  filter_upwards [hae,ae_all_iff.mpr hrep] with x hx he
  have hp : Tendsto (fun n => (ns n)⁻¹ • (F (ns n) x-F 0 x)) atTop (𝓝 (g x)) := by
    simpa only [zero_add] using (hF x).tendsto_slope_zero.comp hns
  have hh : Tendsto (fun n => (q (ns n) : X → ℂ) x) atTop (𝓝 (g x)) := by
    simpa only [he] using hp
  exact tendsto_nhds_unique hx hh

#print axioms derivative_representative

end
end UnifiedTheory.Audit.KFCausalLpDerivativeRepresentative
