/- The glued force is the actual local limit on every real time interval.
Its physical time bound and Schwartz balance hold at arbitrary endpoints. -/
import UnifiedTheory.Audit.KFCausalGluedSpacetimeForce
import UnifiedTheory.Audit.KFCausalNeutralConsistentSpacetimeDynamics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalNeutralGlobalForceLimit
noncomputable section
open MeasureTheory Filter Set SchwartzMap
open scoped Topology ZeroAtInfty
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalNeutralForceConsistency (forceBudget)
open UnifiedTheory.Audit.KFCausalNeutralSpacetimeForce
open UnifiedTheory.Audit.KFCausalNeutralIntegratedForce (forceInterval)
open UnifiedTheory.Audit.KFCausalNeutralSpacetimeLimit (windowFamily)
open UnifiedTheory.Audit.KFCausalCompactSpacetimeForce
open UnifiedTheory.Audit.KFCausalCompactTimeRestriction
open UnifiedTheory.Audit.KFCausalLocalSpacetimeTests
open UnifiedTheory.Audit.KFCausalSpacetimeRestriction
open UnifiedTheory.Audit.KFCausalSpacetimeWindowTests
open UnifiedTheory.Audit.KFCausalSpacetimeExhaustion
open UnifiedTheory.Audit.KFCausalConsistentSpacetimeWindows (Family)
open UnifiedTheory.Audit.KFCausalGluedSpacetimeForce
open UnifiedTheory.Audit.KFCausalNeutralSpacetimeConsistency
open UnifiedTheory.Audit.KFCausalNeutralTemporalCompactness (curve)

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0)) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
  (ρ : ℕ → ℕ) (hρ : StrictMono ρ)
  (G : Family (left s) (right s) s (fun T => forceBudget ε a m g k s T p))
  (hP : ∀ i, Tendsto (fun n => compactify
    (windowFamily ε a hε ha m g k s p h hne hh r hr (left s) (right s) (ρ n) i).positive)
      atTop (𝓝 (G.positive i)))
  (hN : ∀ i, Tendsto (fun n => compactify
    (windowFamily ε a hε ha m g k s p h hne hh r hr (left s) (right s) (ρ n) i).negative)
      atTop (𝓝 (G.negative i)))

local notation "W" => fun n b c => forceWindow ε a (h (ρ n)) hε ha (hne (ρ n)) (hh (ρ n))
  m g k s p (r (ρ n)) (hr (ρ n)) b c
local notation "I" => fun n b c => forceInterval ε a (h (ρ n)) hε ha (hne (ρ n)) (hh (ρ n))
  m g k s p (r (ρ n)) (hr (ρ n)) b c

include hz hρ hP hN

theorem window_compact_limits (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
    (i : ℕ) (b c : ℝ) (hbc : b ≤ c) (hb : left s i ≤ b) (hc : c ≤ right s i) :
    Tendsto (fun n => compactify (W n b c).positive) atTop
      (𝓝 ((G.positive i).restrict (timeStrip b c))) ∧
    Tendsto (fun n => compactify (W n b c).negative) atTop
      (𝓝 ((G.negative i).restrict (timeStrip b c))) :=
  subwindow_compact_converges ε a hε ha m g k s p h hne hh hz r hr (left s) (right s)
    ρ hρ G.positive G.negative hP hN hm hg hk i b c hbc hb hc

theorem global_zero_converges (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
    (b c : ℝ) (hbc : b ≤ c) (q : C₀(ℝ × ℝ,ℂ)) :
    Tendsto (fun n => (W n b c).evaluate q.toBCF) atTop
      (𝓝 (((globalForce G).window b c).evaluate q.toBCF)) := by
  obtain ⟨i,hb,hc⟩ := exists_enclosing s b c
  rw [globalForce_subwindow G i b c hb hc]
  exact subwindow_zero_converges ε a hε ha m g k s p h hne hh hz r hr (left s) (right s)
    ρ hρ G.positive G.negative hP hN hm hg hk i b c hbc hb hc q

theorem global_interval_converges (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
    (b c : ℝ) (hbc : b ≤ c) (q : C₀(ℝ,ℂ)) :
    Tendsto (fun n => (I n b c).evaluate q.toBCF) atTop
      (𝓝 (((globalForce G).interval b c).evaluate q.toBCF)) := by
  obtain ⟨i,hb,hc⟩ := exists_enclosing s b c
  obtain ⟨χ,hχ,hzero⟩ := exists_time_cutoff b c
  have hl := window_compact_limits ε a hε ha m g k s p h hne hh hz r hr ρ hρ G hP hN
    hm hg hk i b c hbc hb hc
  have ht := boundary_test_of_compact_limits (fun n => W n b c) _ _ hl.1 hl.2
    (liftTest χ q) (liftTest_boundary χ hzero q)
  have hj : finitePair ((G.positive i).restrict (timeStrip b c))
      ((G.negative i).restrict (timeStrip b c)) = (globalForce G).window b c :=
    (finitePair_restrict _ _ b c).trans (globalForce_subwindow G i b c hb hc).symm
  rw [hj,(globalForce G).window_lift_test b c χ hχ q] at ht
  have he : (fun n => (W n b c).evaluate (pullback (liftTest χ q))) =
      (fun n => (I n b c).evaluate q.toBCF) := by
    funext n
    exact fromCurve_window_test _ _ _ _ _ b c χ hχ q
  rwa [he] at ht

theorem global_window_time_bound (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
    (T b c : ℝ) (hbc : b ≤ c) (hb : |b-s| ≤ T) (hc : |c-s| ≤ T)
    (A : Set ℝ) (hA : MeasurableSet A) :
    ((globalForce G).window b c).positive (A ×ˢ univ)+
      ((globalForce G).window b c).negative (A ×ˢ univ) ≤
        ENNReal.ofReal (forceBudget ε a m g k s T p)*volume (A ∩ Icc b c) := by
  obtain ⟨i,hbi,hci⟩ := exists_enclosing s b c
  have hl := window_compact_limits ε a hε ha m g k s p h hne hh hz r hr ρ hρ G hP hN
    hm hg hk i b c hbc hbi hci
  have ht := KFCausalCompactTimeMarginal.weak_time_domination (fun n => W n b c)
    _ _ hl.1 hl.2 b c (forceBudget ε a m g k s T p) (by
      filter_upwards [hρ.tendsto_atTop.eventually
        (forceWindow_time_window ε a hε ha m g k s p hm hg hk h hne hh hz T)] with n hn
      exact hn (r (ρ n)) (hr (ρ n)) b c hb hc)
  have hj : finitePair ((G.positive i).restrict (timeStrip b c))
      ((G.negative i).restrict (timeStrip b c)) = (globalForce G).window b c :=
    (finitePair_restrict _ _ b c).trans (globalForce_subwindow G i b c hbi hci).symm
  have he := KFCausalLocalTimeMarginal.local_rectangle_bound _ _ _ _ _ ht A hA
  rwa [hj] at he

theorem global_schwartz_balance (hm : 0 < m) (hg : 0 < g) (hk : 0 < k)
    (hrtop : Tendsto r atTop atTop) (ν : ℝ → ProbabilityMeasure ℝ)
    (hchar : ∀ z : ℝ × ℝ, Tendsto (fun n => curve ε a (h (ρ n)) hε ha (hne (ρ n)) (hh (ρ n))
      m g k s p z) atTop (𝓝 (charFun (ν z.1 : Measure ℝ) z.2)))
    (b c : ℝ) (hbc : b ≤ c) (f : 𝓢(ℝ,ℂ)) :
    (∫ x, f x ∂(ν c : Measure ℝ))-(∫ x, f x ∂(ν b : Measure ℝ)) =
      ((globalForce G).interval b c).evaluate (derivCLM ℂ ℂ f).toBoundedContinuousFunction := by
  apply KFCausalWeakForceBalance.schwartz_balance (fun n => I n b c)
    ((globalForce G).interval b c) (ν b) (ν c) _
    (global_interval_converges ε a hε ha m g k s p h hne hh hz r hr ρ hρ G hP hN
      hm.le hg.le hk.le b c hbc) _ f
  · obtain ⟨C,hC⟩ := KFCausalNeutralLocalForceLimit.family_mass_bound
      ε a hε ha m g k s p h hne hh hz r hr (fun _ : Unit => b) (fun _ => c)
      (fun _ => hbc) hm.le hg.le hk.le ()
    exact ⟨C,hρ.tendsto_atTop.eventually hC⟩
  · intro v
    exact KFCausalNeutralIntegratedForce.forceInterval_balance_limit
      ε a hε ha m g k s p hm hg hk h hne hh hz ρ hρ ν hchar
      (fun n => r (ρ n)) (fun n => hr (ρ n)) (hrtop.comp hρ.tendsto_atTop) b c v hbc

#print axioms window_compact_limits
#print axioms global_zero_converges
#print axioms global_interval_converges
#print axioms global_window_time_bound
#print axioms global_schwartz_balance
end
end UnifiedTheory.Audit.KFCausalNeutralGlobalForceLimit
