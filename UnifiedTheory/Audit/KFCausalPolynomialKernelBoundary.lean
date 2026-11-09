/- Both clock endpoints vanish for every finite polynomial Gaussian
cross kernel at each transverse point. The polynomial degree and point
may affect the bound; this is not a uniform response estimate. -/
import UnifiedTheory.Audit.KFCausalClockBoundaryDecay
import UnifiedTheory.Audit.KFCausalGaussianBoundaryLimit
import UnifiedTheory.Audit.KFCausalPolynomialKernelResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalPolynomialKernelBoundary
noncomputable section
open Filter MeasureTheory
open scoped Topology
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (scale scale_bound)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential (position exponent profile)
open UnifiedTheory.Audit.KFCausalPolynomialKernelResponse
  (weight transverse kernel kernelDerivative actual_kernel_interval)
open UnifiedTheory.Audit.KFCausalClockResponseTransport (clock pair weakPair reduced)

variable (ε y α β α' β' : ℝ) (b c : Fin 5 → ℂ) (C D : ℂ) (P Q : Polynomial ℂ) (q : Transverse)
  (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)

local notation "K" => kernel ε y α β α' β' b c C D P Q q
local notation "K'" => kernelDerivative ε y α β α' β' b c C D P Q q

theorem weight_bounded (ε y : ℝ) (P : Polynomial ℂ) (q : Transverse)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s, ‖weight ε y P q s‖ ≤ M := by
  let F : ℂ → ℂ := fun r => P.eval (position r q 4)
  have hp : Continuous (fun r : ℂ => position r q 4) := by
    unfold position
    simp only [ite_true]
    fun_prop
  have hf : Continuous F := P.continuous.comp hp
  obtain ⟨M,hM⟩ := (isCompact_closedBall (0:ℂ) (Real.exp (|y|/(2*ε)))).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨max M 0,le_max_right _ _,fun s => ?_⟩
  have hs : scale ε y s ∈ Metric.closedBall (0:ℂ) (Real.exp (|y|/(2*ε))) := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using scale_bound ε y s hε hy
  exact (hM (scale ε y s) hs).trans (le_max_left M 0)

include hε hy in
theorem kernel_bounded : ∃ M : ℝ, 0 ≤ M ∧ ∀ s, ‖K s‖ ≤ M := by
  obtain ⟨A,hA,hP⟩ := weight_bounded ε y P q hε hy
  obtain ⟨B,hB,hQ⟩ := weight_bounded ε y Q q hε hy
  obtain ⟨M,hM,hG⟩ := KFCausalGaussianBoundaryLimit.kernel_bounded
    ε y α β α' β' b c C D q hε hy
  refine ⟨A*B*M,by positivity,fun s => ?_⟩
  rw [KFCausalPolynomialKernelResponse.kernel_factorization,norm_mul,norm_mul,norm_star]
  exact mul_le_mul (mul_le_mul (hP s) (hQ s) (norm_nonneg _) hA)
    (hG s) (norm_nonneg _) (mul_nonneg hA hB)

def boundary (a a' p p' s : ℝ) : ℂ := K s*pair ε a a' p p' y s/(clock ε s:ℂ)

include hε hy in
theorem boundary_bound (a a' p p' : ℝ) (ha : 0 < a+a') :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s, ‖boundary ε y α β α' β' b c C D P Q q a a' p p' s‖ ≤
      M*Real.exp (-KFCausalClockBoundaryDecay.decay ε a a'*s^2) := by
  obtain ⟨M,hM,hK⟩ := kernel_bounded ε y α β α' β' b c C D P Q q hε hy
  refine ⟨M*KFCausalClockBoundaryDecay.constant ε a a' p p' y,
    by unfold KFCausalClockBoundaryDecay.constant; positivity,fun s => ?_⟩
  have hb := KFCausalClockBoundaryDecay.boundary_bound ε a a' p p' y s hε ha hy
  calc
    _ = ‖K s‖*‖KFCausalClockBoundaryDecay.boundary ε a a' p p' y s‖ := by
      simp only [boundary,KFCausalClockBoundaryDecay.boundary,norm_div,norm_mul,mul_div_assoc]
    _ ≤ M*(KFCausalClockBoundaryDecay.constant ε a a' p p' y*
      Real.exp (-KFCausalClockBoundaryDecay.decay ε a a'*s^2)) :=
        mul_le_mul (hK s) hb (norm_nonneg _) hM
    _ = _ := by ring

include hε hy in
private theorem boundary_limit (a a' p p' : ℝ) (l : Filter ℝ)
    (hb : Tendsto (KFCausalClockBoundaryDecay.boundary ε a a' p p' y) l (𝓝 0)) :
    Tendsto (boundary ε y α β α' β' b c C D P Q q a a' p p') l (𝓝 0) := by
  obtain ⟨M,hM,hK⟩ := kernel_bounded ε y α β α' β' b c C D P Q q hε hy
  apply squeeze_zero_norm (fun s => ?_) (by simpa using hb.norm.const_mul M)
  calc
    _ = ‖K s‖*‖KFCausalClockBoundaryDecay.boundary ε a a' p p' y s‖ := by
      simp only [boundary,KFCausalClockBoundaryDecay.boundary,norm_div,norm_mul,mul_div_assoc]
    _ ≤ M*‖KFCausalClockBoundaryDecay.boundary ε a a' p p' y s‖ :=
      mul_le_mul_of_nonneg_right (hK s) (norm_nonneg _)

include hε hy in
theorem boundary_atTop (a a' p p' : ℝ) (ha : 0 < a+a') :
    Tendsto (boundary ε y α β α' β' b c C D P Q q a a' p p') atTop (𝓝 0) :=
  boundary_limit ε y α β α' β' b c C D P Q q hε hy a a' p p' atTop
    (KFCausalClockBoundaryDecay.boundary_atTop ε a a' p p' y hε ha hy)

include hε hy in
theorem boundary_atBot (a a' p p' : ℝ) (ha : 0 < a+a') :
    Tendsto (boundary ε y α β α' β' b c C D P Q q a a' p p') atBot (𝓝 0) :=
  boundary_limit ε y α β α' β' b c C D P Q q hε hy a a' p p' atBot
    (KFCausalClockBoundaryDecay.boundary_atBot ε a a' p p' y hε ha hy)

include hε hy in
theorem interval_difference_atTop (a a' p p' : ℝ) (ha : 0 < a+a') :
    Tendsto (fun R : ℝ => (∫ s in -R..R, K s*weakPair ε a a' p p' y s)-
      ∫ s in -R..R, reduced ε a a' p p' y K K' s) atTop (𝓝 0) := by
  have ht := (boundary_atTop ε y α β α' β' b c C D P Q q hε hy a a' p p' ha).sub
    ((boundary_atBot ε y α β α' β' b c C D P Q q hε hy a a' p p' ha).comp tendsto_neg_atTop_atBot)
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [] with R
  rw [actual_kernel_interval ε y a a' p p' α β α' β' b c C D P Q q hε hy (-R) R]
  simp only [boundary,Function.comp_def,add_sub_cancel_right]

#print axioms weight_bounded
#print axioms kernel_bounded
#print axioms boundary_bound
#print axioms boundary_atTop
#print axioms boundary_atBot
#print axioms interval_difference_atTop
end
end UnifiedTheory.Audit.KFCausalPolynomialKernelBoundary
