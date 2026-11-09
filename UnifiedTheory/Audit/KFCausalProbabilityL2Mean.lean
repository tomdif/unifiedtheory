/- Bochner averaging on a probability space is a contraction from vector
L2 to its Hilbert target. The integral and the constant-function adjoint
are identified, so no unbounded operator/integral interchange is assumed. -/
import UnifiedTheory.Audit.KFCausalPeriodicUnitaryMean
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalProbabilityL2Mean
noncomputable section
open MeasureTheory

variable {Ω E F : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def mean : Lp E 2 μ →L[ℂ] E := (Lp.constL 2 μ ℂ).adjoint

theorem mean_integral (v : Lp E 2 μ) : mean μ v = ∫ θ, v θ ∂μ := by
  apply ext_inner_left ℂ
  intro x
  rw [mean, ContinuousLinearMap.adjoint_inner_right, L2.inner_def]
  change (∫ θ, inner ℂ ((Lp.const 2 μ x) θ) (v θ) ∂μ) =
    (innerSL ℂ x) (∫ θ, v θ ∂μ)
  rw [← (innerSL ℂ x).integral_comp_comm ((Lp.memLp v).integrable (by norm_num))]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 μ x] with θ hθ
  change inner ℂ ((Lp.const 2 μ x) θ) (v θ) = inner ℂ x (v θ)
  rw [hθ]
  rfl

theorem mean_norm_le (v : Lp E 2 μ) : ‖mean μ v‖ ≤ ‖v‖ := by
  have hc : ‖(Lp.constL 2 μ ℂ : E →L[ℂ] Lp E 2 μ)‖ ≤ 1 := by
    simpa only [probReal_univ, Real.one_rpow] using
      (Lp.norm_constL_le (E := E) (p := 2) (μ := μ) ℂ)
  have he : ‖mean (E := E) μ‖ = ‖(Lp.constL 2 μ ℂ : E →L[ℂ] Lp E 2 μ)‖ :=
    ContinuousLinearMap.adjoint.norm_map (Lp.constL 2 μ ℂ : E →L[ℂ] Lp E 2 μ)
  calc
    ‖mean μ v‖ ≤ ‖mean (E := E) μ‖ * ‖v‖ := (mean μ).le_opNorm v
    _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right (he.le.trans hc) (norm_nonneg v)
    _ = ‖v‖ := one_mul _

theorem mean_const (x : E) : mean μ (Lp.const 2 μ x) = x := by
  rw [mean_integral, integral_congr_ae (Lp.coeFn_const 2 μ x)]
  simp

theorem mean_comp (A : E →L[ℂ] F) (v : Lp E 2 μ) :
    mean μ (A.compLp v) = A (mean μ v) := by
  rw [mean_integral, mean_integral, A.integral_compLp,
    A.integral_comp_comm ((Lp.memLp v).integrable (by norm_num))]

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
theorem const_norm (x : E) : ‖Lp.const 2 μ x‖ = ‖x‖ := by
  simpa using Lp.norm_const' (p := 2) μ x (by norm_num) (by norm_num)

omit [CompleteSpace E] [CompleteSpace F] in
theorem comp_const (A : E →L[ℂ] F) (x : E) :
    A.compLp (Lp.const 2 μ x) = Lp.const 2 μ (A x) := by
  apply Lp.ext
  filter_upwards [A.coeFn_compLp (Lp.const 2 μ x), Lp.coeFn_const 2 μ x,
    Lp.coeFn_const 2 μ (A x)] with θ hA hx hy
  rw [hA, hx, hy]
  rfl

omit [IsProbabilityMeasure μ] [CompleteSpace E] [CompleteSpace F] in
theorem compLp_injective (A : E →L[ℂ] F) (hA : Function.Injective A) :
    Function.Injective (A.compLp : Lp E 2 μ → Lp F 2 μ) := by
  intro v w h
  apply Lp.ext
  have he : A.compLp v =ᵐ[μ] A.compLp w := by rw [h]
  filter_upwards [A.coeFn_compLp v, A.coeFn_compLp w, he] with θ hv hw he
  exact hA (hv.symm.trans (he.trans hw))

#print axioms mean_integral
#print axioms mean_norm_le
#print axioms mean_const
#print axioms mean_comp
#print axioms const_norm
#print axioms comp_const
#print axioms compLp_injective

end
end UnifiedTheory.Audit.KFCausalProbabilityL2Mean
