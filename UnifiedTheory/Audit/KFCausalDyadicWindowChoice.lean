/- Both the matter and kinetic parts of the dyadic time-window bound
can be made arbitrarily small, with all widths below a prescribed limit.
No energy-tail premise is added. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionDyadicWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalDyadicWindowChoice
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalDyadicHeatCancellation (width)
open UnifiedTheory.Audit.KFCausalMixedDyadicStripResponse (responseConstant)
open UnifiedTheory.Audit.KFCausalDyadicResponseChoice (response_zero)
open UnifiedTheory.Audit.KFCausalNeutralPositionDyadicWindow (windowBound)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialFullResponse (kineticConstant)

theorem window_frequency_continuous (ε δ B : ℝ) (N : ℕ) :
    Continuous (fun v => windowBound ε δ v N B) := by
  unfold windowBound responseConstant kineticConstant KFCausalNeutralPositionRadialKineticGraph.responseConstant
  fun_prop

theorem window_radial_zero_continuous (ε B : ℝ) (N : ℕ) :
    Continuous (fun δ => windowBound ε δ 0 N B) := by
  simp only [windowBound,response_zero,kineticConstant,
    KFCausalNeutralPositionRadialKineticGraph.responseConstant,abs_zero,add_zero,width]
  fun_prop

theorem window_zero (ε B : ℝ) (N : ℕ) : windowBound ε 0 0 N B = 8*B/(ε*(N:ℝ)) := by
  simp only [windowBound,response_zero,kineticConstant,
    KFCausalNeutralPositionRadialKineticGraph.responseConstant,width,zero_mul,Real.sqrt_zero,
    mul_zero,abs_zero,add_zero]
  ring

theorem exists_small_window (ε B D η : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) (hD : 0 < D) (hη : 0 < η) :
    ∃ N : ℕ, 0 < N ∧ ∃ δ : ℝ, 0 < δ ∧ width δ N < D ∧
      ∃ V : ℝ, 0 < V ∧ ∀ v : ℝ, |v| ≤ V → windowBound ε δ v N B < η := by
  obtain ⟨N,hN⟩ := exists_nat_gt (16*B/(ε*η))
  have hNp : 0 < N := by
    have hn : (0:ℝ) < N := (by positivity : (0:ℝ) ≤ 16*B/(ε*η)).trans_lt hN
    exact_mod_cast hn
  have hc : 8*B/(ε*(N:ℝ)) < η/2 := by
    apply (div_lt_iff₀ (by positivity : 0 < ε*(N:ℝ))).mpr
    have hh := (div_lt_iff₀ (by positivity : 0 < ε*η)).mp hN
    nlinarith
  have hc' : windowBound ε 0 0 N B < η := by rw [window_zero]; linarith
  have he : ∀ᶠ δ in 𝓝 (0:ℝ), windowBound ε δ 0 N B < η :=
    ((window_radial_zero_continuous ε B N).tendsto 0).eventually (gt_mem_nhds hc')
  obtain ⟨r,hr,hnear⟩ := Metric.eventually_nhds_iff.mp he
  let δ := min (r/2) (D/(2*2^N))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hpow : (2:ℝ)^N ≠ 0 := by positivity
  have hw : width δ N ≤ D/2 := by
    exact (mul_le_mul_of_nonneg_right (min_le_right (r/2) (D/(2*2^N)))
      (by positivity : 0 ≤ (2:ℝ)^N)).trans_eq (by field_simp)
  have hs : windowBound ε δ 0 N B < η := by
    apply hnear
    rw [Real.dist_eq,sub_zero,abs_of_pos hδ]
    exact (min_le_left (r/2) (D/(2*2^N))).trans_lt (by linarith)
  have hv : ∀ᶠ v in 𝓝 (0:ℝ), windowBound ε δ v N B < η :=
    ((window_frequency_continuous ε δ B N).tendsto 0).eventually (gt_mem_nhds hs)
  obtain ⟨V,hV,hv⟩ := Metric.eventually_nhds_iff.mp hv
  refine ⟨N,hNp,δ,hδ,by linarith,V/2,by positivity,?_⟩
  intro v hvr
  apply hv
  simpa only [Real.dist_eq,sub_zero] using (show |v| < V by linarith)

#print axioms window_frequency_continuous
#print axioms window_radial_zero_continuous
#print axioms window_zero
#print axioms exists_small_window

end
end UnifiedTheory.Audit.KFCausalDyadicWindowChoice
