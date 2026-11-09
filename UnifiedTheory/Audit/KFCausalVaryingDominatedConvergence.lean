/- A nonnegative dominated-convergence lemma with a varying integrable
majorant. Pointwise convergence of the majorant alone is insufficient;
its integrals must also converge. The proof clips against the limit majorant. -/
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalVaryingDominatedConvergence
noncomputable section
open MeasureTheory Filter
open scoped Topology

theorem integral_tendsto {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F G : ℕ → X → ℝ) (f g : X → ℝ)
    (hF : ∀ n, Integrable (F n) μ) (hG : ∀ n, Integrable (G n) μ) (hg : Integrable g μ)
    (h0 : ∀ n x, 0 ≤ F n x) (hFG : ∀ n x, F n x ≤ G n x)
    (hf : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hgp : ∀ x, Tendsto (fun n => G n x) atTop (𝓝 (g x)))
    (hgi : Tendsto (fun n => ∫ x, G n x ∂μ) atTop (𝓝 (∫ x, g x ∂μ))) :
    Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hFm (n : ℕ) : Integrable (fun x => min (F n x) (g x)) μ := by
    simpa only [Pi.inf_apply] using (hF n).inf hg
  have hGm (n : ℕ) : Integrable (fun x => min (G n x) (g x)) μ := by
    simpa only [Pi.inf_apply] using (hG n).inf hg
  have hG0 (n : ℕ) (x : X) : 0 ≤ G n x := (h0 n x).trans (hFG n x)
  have hg0 (x : X) : 0 ≤ g x := le_of_tendsto_of_tendsto' tendsto_const_nhds (hgp x) (fun n => hG0 n x)
  have hfg (x : X) : f x ≤ g x := le_of_tendsto_of_tendsto' (hf x) (hgp x) (fun n => hFG n x)
  have hminF : Tendsto (fun n => ∫ x, min (F n x) (g x) ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence g
      (fun n => (hFm n).aestronglyMeasurable) hg
    · intro n
      exact ae_of_all μ (fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (le_min (h0 n x) (hg0 x))]
        exact min_le_right _ _)
    · exact ae_of_all μ (fun x => by simpa only [min_eq_left (hfg x)] using (hf x).min (tendsto_const_nhds (x := g x)))
  have hminG : Tendsto (fun n => ∫ x, min (G n x) (g x) ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence g
      (fun n => (hGm n).aestronglyMeasurable) hg
    · intro n
      exact ae_of_all μ (fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (le_min (hG0 n x) (hg0 x))]
        exact min_le_right _ _)
    · exact ae_of_all μ (fun x => by simpa only [min_self] using (hgp x).min (tendsto_const_nhds (x := g x)))
  have hu : Tendsto (fun n => (∫ x, min (F n x) (g x) ∂μ)+
      (∫ x, G n x ∂μ)-(∫ x, min (G n x) (g x) ∂μ)) atTop (𝓝 (∫ x, f x ∂μ)) := by
    simpa only [add_sub_cancel_right] using (hminF.add hgi).sub hminG
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hminF hu
  · intro n
    exact integral_mono (hFm n) (hF n) (fun x => min_le_left _ _)
  · intro n
    have hsum : Integrable (fun x => min (F n x) (g x)+G n x) μ := (hFm n).add (hG n)
    dsimp only
    rw [← integral_add (hFm n) (hG n),
      ← integral_sub hsum (hGm n)]
    apply integral_mono (hF n) (hsum.sub (hGm n))
    intro x
    have := hFG n x
    dsimp only [Pi.sub_apply,Pi.add_apply,Pi.inf_apply]
    simp only [min_def]
    split_ifs <;> linarith

#print axioms integral_tendsto

end
end UnifiedTheory.Audit.KFCausalVaryingDominatedConvergence
