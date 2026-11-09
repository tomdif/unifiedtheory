/- The actual full scaled resolvents converge uniformly in time on compact
windows, including on continuously moving form states and converging families. -/
import UnifiedTheory.Audit.KFCausalClockFloorFixedResolventWindow
import UnifiedTheory.Audit.KFCausalCompactMovingLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorUniformResolventLimit
noncomputable section
open Set Filter Topology
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorLiftedHamiltonian
open UnifiedTheory.Audit.KFCausalClockFloorFixedFormGenerator
open UnifiedTheory.Audit.KFCausalClockFloorFixedGeneratorResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFixedResolventWindow
variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "R" => fullResolvent ε hε h hne hh m g k
local notation "G" => fixedGenerator ε hε h hne hh m g k
local notation "L" => liftedHamiltonian ε hε h hne hh m g k

theorem uniform_scaled_limit (a s l r : ℝ) (ha : 0 < a) (x : V) :
    TendstoUniformlyOn (fun b t => b • R a b s t x) (fun _ => x) atTop (Icc l r) := by
  obtain ⟨b₀,C,hb₀,hC,hwindow⟩ := uniform_window ε hε h hne hh m g k a s l r ha
  apply KFCausalUniformResolventLimit.uniform_limit (L s).domain
    (fun t x => G a s t x) (fun b t => R a b s t) (Icc l r) b₀ C hb₀ hC
    (lifted_dense ε hε h hne hh m g k s) (fun b hb t ht => (hwindow b hb t ht).2)
  · intro b hb t ht w
    exact full_resolvent_left ε hε h hne hh m g k a b s t ha (hb₀.trans_le hb)
      (hwindow b hb t ht).1 (w:V) (G a s t w) ((G a s t).mem_graph w)
  · intro w
    have hc : Continuous (fun t => G a s t w) := continuous_iff_continuousAt.mpr
      (fun t => (fixed_action_derivative ε hε h hne hh m g k a s t ha w).continuousAt)
    obtain ⟨M,hM⟩ := (isCompact_Icc.image_of_continuousOn hc.norm.continuousOn).bddAbove
    exact ⟨M,fun t ht => hM (mem_image_of_mem _ ht)⟩

theorem moving_scaled_limit (a s l r : ℝ) (ha : 0 < a) (u : ℝ → V)
    (hu : ContinuousOn u (Icc l r)) :
    TendstoUniformlyOn (fun b t => b • R a b s t (u t)) u atTop (Icc l r) := by
  obtain ⟨b₀,C,_hb₀,hC,hwindow⟩ := uniform_window ε hε h hne hh m g k a s l r ha
  apply KFCausalCompactMovingLimit.moving_limit (fun b t => b • R a b s t)
    atTop (Icc l r) isCompact_Icc C hC
  · filter_upwards [eventually_ge_atTop b₀] with b hb
    exact fun t ht => (hwindow b hb t ht).2
  · exact uniform_scaled_limit ε hε h hne hh m g k a s l r ha
  · exact hu

theorem varying_scaled_limit (a s l r : ℝ) (ha : 0 < a)
    (b : ℕ → ℝ) (hb : Tendsto b atTop atTop) (w : ℕ → ℝ → V) (u : ℝ → V)
    (hu : ContinuousOn u (Icc l r)) (hw : TendstoUniformlyOn w u atTop (Icc l r)) :
    TendstoUniformlyOn (fun n t => b n • R a (b n) s t (w n t)) u atTop (Icc l r) := by
  obtain ⟨b₀,C,_hb₀,hC,hwindow⟩ := uniform_window ε hε h hne hh m g k a s l r ha
  apply KFCausalCompactMovingLimit.varying_limit (fun n t => b n • R a (b n) s t)
    atTop (Icc l r) isCompact_Icc C hC
  · filter_upwards [hb.eventually (eventually_ge_atTop b₀)] with n hn
    exact fun t ht => (hwindow (b n) hn t ht).2
  · intro x
    exact (uniform_scaled_limit ε hε h hne hh m g k a s l r ha x).seq_tendstoUniformlyOn b hb
  · exact hu
  · exact hw

#print axioms uniform_scaled_limit
#print axioms moving_scaled_limit
#print axioms varying_scaled_limit
end
end UnifiedTheory.Audit.KFCausalClockFloorUniformResolventLimit
