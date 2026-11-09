/- The derived dyadic shift constant can be made arbitrarily small
while every radial cutoff stays below any prescribed positive width.
The frequency interval is chosen after the finite collection of scales. -/
import UnifiedTheory.Audit.KFCausalMixedDyadicStripResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalDyadicResponseChoice
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalDyadicHeatCancellation (width)
open UnifiedTheory.Audit.KFCausalMixedDyadicStripResponse (responseConstant)

theorem width_mono (δ : ℝ) (hδ : 0 ≤ δ) (j N : ℕ) (hj : j ≤ N) :
    width δ j ≤ width δ N :=
  mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hj) hδ

theorem response_zero (ε δ : ℝ) (N : ℕ) : responseConstant ε δ 0 N = 8/(ε*(N:ℝ)) := by
  simp [responseConstant]

theorem response_continuous (ε δ : ℝ) (N : ℕ) : Continuous (fun v => responseConstant ε δ v N) := by
  unfold responseConstant
  fun_prop

theorem exists_small_response (ε D η : ℝ) (hε : 0 < ε) (hD : 0 < D) (hη : 0 < η) :
    ∃ N : ℕ, 0 < N ∧ ∃ δ : ℝ, 0 < δ ∧ width δ N < D ∧
      ∃ V : ℝ, 0 < V ∧ ∀ v : ℝ, |v| ≤ V → responseConstant ε δ v N < η := by
  obtain ⟨N,hN⟩ := exists_nat_gt (8/(ε*η))
  have hNp : 0 < N := by
    have hn : (0:ℝ) < N := (by positivity : (0:ℝ) < 8/(ε*η)).trans hN
    exact_mod_cast hn
  have hc : 8/(ε*(N:ℝ)) < η := by
    apply (div_lt_iff₀ (by positivity : 0 < ε*(N:ℝ))).mpr
    have hh := (div_lt_iff₀ (by positivity : 0 < ε*η)).mp hN
    nlinarith
  let δ := D/(2*2^N)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hw : width δ N = D/2 := by
    dsimp [width,δ]
    have hpow : (2:ℝ)^N ≠ 0 := by positivity
    field_simp
  have hc' : responseConstant ε δ 0 N < η := by rw [response_zero]; exact hc
  have he : ∀ᶠ v in 𝓝 (0:ℝ), responseConstant ε δ v N < η :=
    ((response_continuous ε δ N).tendsto 0).eventually (gt_mem_nhds hc')
  obtain ⟨r,hr,hv⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨N,hNp,δ,hδ,by rw [hw]; linarith,r/2,by positivity,?_⟩
  intro v hvr
  apply hv
  simpa only [Real.dist_eq,sub_zero] using (show |v| < r by linarith)

#print axioms width_mono
#print axioms response_zero
#print axioms response_continuous
#print axioms exists_small_response

end
end UnifiedTheory.Audit.KFCausalDyadicResponseChoice
