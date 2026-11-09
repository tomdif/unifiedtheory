/- The clock defect tends to zero along every global reduced classical
vacuum trajectory with positive coupling. This is not quantum strict decay. -/
import UnifiedTheory.Audit.KFCausalClockFloorVacuumDynamics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorVacuumDefectDecay
noncomputable section
open Filter Set
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chart chart_derivative chartIso chartIso_apply)
open UnifiedTheory.Audit.KFCausalClockFloorVacuumReduction
open UnifiedTheory.Audit.KFCausalClockFloorVacuumDynamics

variable (ε κ : ℝ) (hε : 0 < ε) (s L : ℝ → ℝ)
  (hs : ∀ t, HasDerivAt s (amplitude ε κ t (s t) (L t)/clock ε (s t)) t)
  (hL : ∀ t, HasDerivAt L (response ε (s t)*(-1/2+amplitude ε κ t (s t) (L t)/clock ε (s t))) t)

include hε hs hL in
theorem amplitude_monotone (hκ : 0 ≤ κ) : Monotone (fun t => amplitude ε κ t (s t) (L t)) := by
  apply monotone_of_hasDerivAt_nonneg (fun t => amplitude_derivative ε κ hε s L t (hs t) (hL t))
  intro t
  have hr := (response_bounds ε (s t) hε).2
  exact mul_nonneg (by linarith only [hr]) (amplitude_nonnegative ε κ t (s t) (L t) hε hκ)

include hε hs in
theorem chart_trajectory_derivative (t : ℝ) :
    HasDerivAt (fun u => chart ε (s u)) (amplitude ε κ t (s t) (L t)) t := by
  have hd := (chart_derivative ε (s t)).comp t (hs t)
  convert hd using 1
  change _ = clock ε (s t)*(amplitude ε κ t (s t) (L t)/clock ε (s t))
  exact (mul_div_cancel₀ _ (clock_positive ε (s t) hε.le).ne').symm

include hε hs hL in
theorem chart_linear_growth (hκ : 0 ≤ κ) (t : ℝ) (ht : 0 ≤ t) :
    chart ε (s 0)+amplitude ε κ 0 (s 0) (L 0)*t ≤ chart ε (s t) := by
  let A := amplitude ε κ 0 (s 0) (L 0)
  have hd (u : ℝ) : HasDerivAt (fun v => chart ε (s v)-A*v)
      (amplitude ε κ u (s u) (L u)-A) u := by
    simpa only [mul_one] using (chart_trajectory_derivative ε κ hε s L hs u).sub
      ((hasDerivAt_id u).const_mul A)
  have hm : MonotoneOn (fun u => chart ε (s u)-A*u) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      ((continuous_iff_continuousAt.mpr (fun u => (hd u).continuousAt)).continuousOn)
      (fun u _ => (hd u).differentiableAt.differentiableWithinAt)
    intro u hu
    rw [(hd u).deriv]
    exact sub_nonneg.mpr ((amplitude_monotone ε κ hε s L hs hL hκ) (interior_subset hu))
  have hb := hm (by simp : (0:ℝ) ∈ Ici 0) ht ht
  dsimp only at hb
  rw [mul_zero,sub_zero] at hb
  linarith only [hb]

include hε hs hL in
theorem chart_tendsto_atTop (hκ : 0 < κ) : Tendsto (fun t => chart ε (s t)) atTop atTop := by
  have hA : 0 < amplitude ε κ 0 (s 0) (L 0) := by
    unfold amplitude
    exact div_pos (mul_pos hκ (Real.exp_pos _)) (clock_positive ε (s 0) hε.le)
  apply tendsto_atTop_mono' atTop
    ((eventually_ge_atTop (0:ℝ)).mono (fun t ht => chart_linear_growth ε κ hε s L hs hL hκ.le t ht))
  exact tendsto_const_nhds.add_atTop (tendsto_id.const_mul_atTop hA)

include hε hs hL in
theorem logClock_tendsto_atTop (hκ : 0 < κ) : Tendsto s atTop atTop := by
  have h := (chartIso ε hε).symm.tendsto_atTop.comp (chart_tendsto_atTop ε κ hε s L hs hL hκ)
  simpa only [← chartIso_apply ε hε,OrderIso.symm_apply_apply,Function.comp_def] using h

include hε hs hL in
theorem defect_tendsto_zero (hκ : 0 < κ) : Tendsto (fun t => defect ε (s t)) atTop (𝓝 0) := by
  have hc : Tendsto (fun t => clock ε (s t)) atTop atTop :=
    (Real.tendsto_exp_atTop.comp (logClock_tendsto_atTop ε κ hε s L hs hL hκ)).atTop_add tendsto_const_nhds
  exact hc.const_div_atTop ε

theorem zero_coupling_clock_constant (ε : ℝ) (s L : ℝ → ℝ)
    (hs : ∀ t, HasDerivAt s (amplitude ε 0 t (s t) (L t)/clock ε (s t)) t) (t : ℝ) : s t = s 0 := by
  have hd (u : ℝ) : HasDerivAt s 0 u := by simpa only [amplitude,zero_mul,zero_div] using hs u
  exact is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt) (fun u => (hd u).deriv) t 0

theorem zero_coupling_defect_not_zero_limit (ε : ℝ) (hε : 0 < ε) (s L : ℝ → ℝ)
    (hs : ∀ t, HasDerivAt s (amplitude ε 0 t (s t) (L t)/clock ε (s t)) t) :
    ¬Tendsto (fun t => defect ε (s t)) atTop (𝓝 0) := by
  intro hlim
  have he : (fun t => defect ε (s t)) = fun _ : ℝ => defect ε (s 0) :=
    funext (fun t => congrArg (defect ε) (zero_coupling_clock_constant ε s L hs t))
  rw [he] at hlim
  have hz : defect ε (s 0) = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
  exact (defect_positive ε (s 0) hε).ne' hz

theorem exists_global_decay (ε κ s₀ L₀ : ℝ) (hε : 0 < ε) (hκ : 0 < κ) :
    ∃ s L : ℝ → ℝ, s 0 = s₀ ∧ L 0 = L₀ ∧
      (∀ t, HasDerivAt s (amplitude ε κ t (s t) (L t)/clock ε (s t)) t) ∧
      (∀ t, HasDerivAt L (response ε (s t)*(-1/2+amplitude ε κ t (s t) (L t)/clock ε (s t))) t) ∧
      StrictAnti (fun t => defect ε (s t)) ∧ Tendsto (fun t => defect ε (s t)) atTop (𝓝 0) := by
  obtain ⟨s,L,hs0,hL0,hs,hL⟩ := KFCausalClockFloorVacuumReconstruction.exists_global_vacuum ε κ s₀ L₀ hε
  exact ⟨s,L,hs0,hL0,hs,hL,defect_strictAnti ε κ hε s L hs hκ,
    defect_tendsto_zero ε κ hε s L hs hL hκ⟩

#print axioms amplitude_monotone
#print axioms chart_trajectory_derivative
#print axioms chart_linear_growth
#print axioms chart_tendsto_atTop
#print axioms logClock_tendsto_atTop
#print axioms defect_tendsto_zero
#print axioms zero_coupling_clock_constant
#print axioms zero_coupling_defect_not_zero_limit
#print axioms exists_global_decay

end
end UnifiedTheory.Audit.KFCausalClockFloorVacuumDefectDecay
