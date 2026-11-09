/- The actual singular angular endpoint moments converge to Gamma
moments. The endpoint tail is controlled independently, while the
interior uses a genuine integrable majorant. No moment limit is a premise. -/
import UnifiedTheory.Audit.KFCausalAngularGammaMomentBounds

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalAngularGammaMomentConvergence
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
open KFCausalAngularGammaMomentBounds

def interior (j : ℕ) (z : ℝ) : ℝ := ∫ u in 0..z, kernel j z u

def normalizedMoment (j : ℕ) (z : ℝ) : ℝ := moment j z/moment 0 z

private theorem density_integral (j : ℕ) :
    (∫ u in Ioi 0, density j u)=Real.Gamma ((j:ℝ)+1/2) := by
  rw [Real.Gamma_eq_integral (by positivity : (0:ℝ)<(j:ℝ)+1/2)]
  apply integral_congr_ae
  filter_upwards [] with u
  unfold density
  congr 2
  ring

private theorem kernel_measurable (j : ℕ) (z : ℝ) : Measurable (kernel j z) := by
  unfold kernel density correction
  fun_prop

private theorem correction_tendsto (u : ℝ) :
    Tendsto (fun z : ℝ => correction z u) atTop (𝓝 1) := by
  have hd : Tendsto (fun z : ℝ => u/(2*z)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<2))
  have hh := ((tendsto_const_nhds (x := (1:ℝ))).sub hd).rpow_const
    (p := -(1/2:ℝ)) (Or.inl (by norm_num : (1:ℝ)-0 ≠ 0))
  simpa only [sub_zero,Real.one_rpow] using hh

theorem interior_tendsto (j : ℕ) :
    Tendsto (interior j) atTop (𝓝 (Real.Gamma ((j:ℝ)+1/2))) := by
  let F : ℝ → ℝ → ℝ := fun z => (Ioc 0 z).indicator (kernel j z)
  have hm (z : ℝ) : AEStronglyMeasurable (F z) (volume.restrict (Ioi 0)) :=
    ((kernel_measurable j z).indicator measurableSet_Ioc).aestronglyMeasurable
  have hb : ∀ᶠ z in atTop, ∀ᵐ u ∂volume.restrict (Ioi 0), ‖F z u‖ ≤ 2*density j u := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with z hz
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [] with u hu
    have hu0 : 0 ≤ u := le_of_lt hu
    have hd : 0 ≤ density j u :=
      mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hu0 _)
    by_cases huz : u ≤ z
    · dsimp only [F]
      rw [indicator_of_mem (show u∈Ioc 0 z from ⟨hu,huz⟩),Real.norm_eq_abs,
        abs_of_nonneg (kernel_nonnegative j z u hu0)]
      exact (mul_le_mul_of_nonneg_left
        (correction_left_bound z u (by linarith) ⟨hu0,huz⟩) hd).trans_eq (by ring)
    · dsimp only [F]
      rw [indicator_of_notMem (show u∉Ioc 0 z from fun h => huz h.2),norm_zero]
      positivity
  have hp : ∀ᵐ u ∂volume.restrict (Ioi 0),
      Tendsto (fun z => F z u) atTop (𝓝 (density j u)) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [] with u hu
    have ht := (correction_tendsto u).const_mul (density j u)
    simp only [mul_one] at ht
    apply ht.congr'
    filter_upwards [eventually_ge_atTop u] with z hz
    dsimp only [F]
    rw [indicator_of_mem (show u∈Ioc 0 z from ⟨hu,hz⟩)]
    rfl
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi 0)) (l := atTop)
    (F := F) (f := density j) (bound := fun u => 2*density j u)
    (Eventually.of_forall hm) hb ((density_integrable j).const_mul 2) hp
  rw [density_integral] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with z hz
  dsimp only [F]
  rw [integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self]
  exact (intervalIntegral.integral_of_le (by linarith : (0:ℝ)≤z)).symm

theorem moment_tendsto (j : ℕ) :
    Tendsto (moment j) atTop (𝓝 (Real.Gamma ((j:ℝ)+1/2))) := by
  have ht := (interior_tendsto j).add (tail_tendsto j)
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with z hz
  have hz0 : 0<z := by linarith
  have hi := kernel_integrable j z hz0
  have hl : IntervalIntegrable (kernel j z) volume 0 z := hi.mono_set (by
    rw [uIcc_of_le hz0.le,uIcc_of_le (by linarith : (0:ℝ)≤2*z)]
    exact Icc_subset_Icc le_rfl (by linarith))
  have hr : IntervalIntegrable (kernel j z) volume z (2*z) := hi.mono_set (by
    rw [uIcc_of_le (by linarith : z≤2*z),uIcc_of_le (by linarith : (0:ℝ)≤2*z)]
    exact Icc_subset_Icc hz0.le le_rfl)
  exact intervalIntegral.integral_add_adjacent_intervals hl hr

theorem moment_eventually_positive (j : ℕ) :
    ∀ᶠ z : ℝ in atTop, 0 < moment j z :=
  (moment_tendsto j).eventually (lt_mem_nhds (Real.Gamma_pos_of_pos (by positivity)))

theorem normalized_tendsto (j : ℕ) :
    Tendsto (normalizedMoment j) atTop
      (𝓝 (Real.Gamma ((j:ℝ)+1/2)/Real.Gamma (1/2))) := by
  have hh := (moment_tendsto j).div (moment_tendsto 0)
    (ne_of_gt (Real.Gamma_pos_of_pos (by norm_num)))
  simpa only [Nat.cast_zero,zero_add,normalizedMoment] using hh

#print axioms interior_tendsto
#print axioms moment_tendsto
#print axioms moment_eventually_positive
#print axioms normalized_tendsto
end
end UnifiedTheory.Audit.KFCausalAngularGammaMomentConvergence
