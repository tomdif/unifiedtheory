/- An unconditional integrated potential-response bound, uniform over
all reciprocal widths w >= 1, clock locations, positive clock widths,
and real clock frequencies in the established imaginary strip.
Clock integrability is proved, not supplied as a premise. -/
import UnifiedTheory.Audit.KFCausalReciprocalGaussianKernelBound
import UnifiedTheory.Audit.KFCausalGaussianClockResponseIntegrability

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalGaussianClockBound
noncomputable section
open Set MeasureTheory
open KFCausalReciprocalGaussianCoordinates
open KFCausalReciprocalGaussianKernel
open KFCausalReciprocalGaussianKernelBound
open KFCausalClockFloorRelativeShift (scale)
open KFCausalPositiveKernelClockResponse (clockWeight energy weakResponse)

theorem exists_uniform_kernel_bound (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) :
    ∃ M : ℝ, ∀ k ε y s : ℝ, k ∈ Ioc 0 1 → 0 < ε → |y| ≤ Real.pi*ε/3 →
      ‖kernel α β (1/k^2) (scale ε y s)‖ ≤ M := by
  have hc : ContinuousOn (fun p : ℝ × (ℝ × ℂ) =>
      ‖kernelFormula α β (p.1,p.2.2)‖) (region α β) := by
    intro p hp
    obtain ⟨hA,hB⟩ := region_widths α β hα hβ.le p hp
    exact ((kernelFormula_smooth α β (p.1,p.2.2) hA hB hβ).continuousAt.comp (f := fun q : ℝ × (ℝ × ℂ) => (q.1,q.2.2))
      (by fun_prop : ContinuousAt (fun q : ℝ × (ℝ × ℂ) => (q.1,q.2.2)) p)).norm.continuousWithinAt
  obtain ⟨M,hM⟩ := ((region_compact α β).image_of_continuousOn hc).bddAbove
  refine ⟨M,?_⟩
  intro k ε y s hk hε hy
  have he := congrFun (actual_formula α β k ε y hα hβ hw hk hε hy) s
  rw [he]
  exact hM (mem_image_of_mem _
    (actual_mem_region α β k ε y s hα hβ.le hw ⟨hk.1.le,hk.2⟩ hε hy))

theorem clock_integrability (α β k ε a p y : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hk : k ∈ Ioc 0 1) (hε : 0 < ε) (ha : 0 < a)
    (hy : |y| ≤ Real.pi*ε/3) :
    Integrable (energy ε a p y (fun s => kernel α β (1/k^2) (scale ε y s))) volume ∧
      Integrable (weakResponse ε a p y (fun s => kernel α β (1/k^2) (scale ε y s))) volume := by
  obtain ⟨M,hM⟩ := exists_uniform_kernel_bound α β hα hβ hw
  have hK : Continuous (fun s => kernel α β (1/k^2) (scale ε y s)) :=
    (show Differentiable ℝ _ from fun s =>
      (actual_derivative α β k ε y s hα hβ hw hk hε hy).differentiableAt).continuous
  have hb : ∀ᵐ s ∂volume, ‖kernel α β (1/k^2) (scale ε y s)‖ ≤ M :=
    Filter.Eventually.of_forall (fun s => hM k ε y s hk hε hy)
  refine ⟨(KFCausalGaussianClockResponseIntegrability.clockWeight_integrable ε a p y hε ha hy).mul_bdd
    hK.aestronglyMeasurable hb,?_⟩
  have hi := (KFCausalGaussianClockResponseIntegrability.weakWeight_integrable ε a p y hε ha hy).mul_bdd
    hK.aestronglyMeasurable hb
  convert hi using 1
  funext s
  simp only [weakResponse,energy]
  ring

theorem uniform_clock_bound (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ε a p y : ℝ, k ∈ Ioc 0 1 → 0 < ε → 0 < a →
      |y| ≤ Real.pi*ε/3 →
      -((C+2)/ε)*(∫ s, energy ε a p y (fun t => kernel α β (1/k^2) (scale ε y t)) s) ≤
        ∫ s, weakResponse ε a p y (fun t => kernel α β (1/k^2) (scale ε y t)) s := by
  obtain ⟨C,hC,hD⟩ := exists_uniform_derivative α β hα hβ hw
  refine ⟨C,hC,?_⟩
  intro k ε a p y hk hε ha hy
  obtain ⟨hE,hW⟩ := clock_integrability α β k ε a p y hα hβ hw hk hε ha hy
  exact KFCausalOneSidedKernelClockResponse.full_clock_bound ε a p y C _ hε hy hC
    (fun s => (actual_derivative α β k ε y s hα hβ hw hk hε hy).differentiableAt)
    (fun s => (actual_positive α β k ε y s hα hβ hw hk hε hy).le)
    (fun s => (le_abs_self _).trans (hD k ε y s hk hε hy)) hE hW

theorem inverse_sqrt_parameter (w : ℝ) (hw : 1 ≤ w) :
    1/Real.sqrt w ∈ Ioc (0:ℝ) 1 ∧ 1/(1/Real.sqrt w)^2 = w := by
  have hwp : 0 < w := by linarith
  have hs : 0 < Real.sqrt w := Real.sqrt_pos.mpr hwp
  have hs1 : 1 ≤ Real.sqrt w := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hw
  refine ⟨⟨by positivity,(div_le_one hs).mpr hs1⟩,?_⟩
  simp only [one_div,inv_pow,inv_inv,Real.sq_sqrt hwp.le]

theorem uniform_width_clock_bound (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ε a p y : ℝ, 1 ≤ w → 0 < ε → 0 < a →
      |y| ≤ Real.pi*ε/3 →
      -((C+2)/ε)*(∫ s, energy ε a p y (fun t => kernel α β w (scale ε y t)) s) ≤
        ∫ s, weakResponse ε a p y (fun t => kernel α β w (scale ε y t)) s := by
  obtain ⟨C,hC,hB⟩ := uniform_clock_bound α β hα hβ hw
  refine ⟨C,hC,?_⟩
  intro w ε a p y hw' hε ha hy
  obtain ⟨hk,he⟩ := inverse_sqrt_parameter w hw'
  simpa only [he] using hB (1/Real.sqrt w) ε a p y hk hε ha hy

#print axioms exists_uniform_kernel_bound
#print axioms clock_integrability
#print axioms uniform_clock_bound
#print axioms inverse_sqrt_parameter
#print axioms uniform_width_clock_bound
end
end UnifiedTheory.Audit.KFCausalReciprocalGaussianClockBound
