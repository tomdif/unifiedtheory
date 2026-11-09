/- Every common compactified spacetime limit of the actual dynamics
inherits physical time domination and exact subwindow consistency. -/
import UnifiedTheory.Audit.KFCausalConsistentSpacetimeWindows
import UnifiedTheory.Audit.KFCausalNeutralSpacetimeLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalNeutralSpacetimeConsistency
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ZeroAtInfty
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalNeutralForceConsistency (forceBudget)
open UnifiedTheory.Audit.KFCausalNeutralSpacetimeForce
open UnifiedTheory.Audit.KFCausalNeutralSpacetimeLimit (windowFamily)
open UnifiedTheory.Audit.KFCausalCompactifiedForceMeasure (Spectrum)
open UnifiedTheory.Audit.KFCausalCompactSpacetimeForce
open UnifiedTheory.Audit.KFCausalCompactTimeMarginal
open UnifiedTheory.Audit.KFCausalCompactTimeRestriction
open UnifiedTheory.Audit.KFCausalSpacetimeForcePair (Pair)
open UnifiedTheory.Audit.KFCausalSpacetimeRestriction
open UnifiedTheory.Audit.KFCausalLocalSpacetimeTests
open UnifiedTheory.Audit.KFCausalConsistentSpacetimeWindows (Family)

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0)) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
  {K : Type*} (b c : K → ℝ) (ρ : ℕ → ℕ) (hρ : StrictMono ρ)
  (P N : K → FiniteMeasure Square)

local notation "W" => windowFamily ε a hε ha m g k s p h hne hh r hr b c
local notation "V" => fun n u v => forceWindow ε a (h (ρ n)) hε ha (hne (ρ n)) (hh (ρ n))
  m g k s p (r (ρ n)) (hr (ρ n)) u v

variable (hP : ∀ i, Tendsto (fun n => compactify
    (windowFamily ε a hε ha m g k s p h hne hh r hr b c (ρ n) i).positive) atTop (𝓝 (P i)))
  (hN : ∀ i, Tendsto (fun n => compactify
    (windowFamily ε a hε ha m g k s p h hne hh r hr b c (ρ n) i).negative) atTop (𝓝 (N i)))

include hz hρ hP hN

theorem limit_time_bound (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
    (T : ℝ) (i : K) (hb : |b i-s| ≤ T) (hc : |c i-s| ≤ T) :
    (timeMarginal (P i+N i) : Measure Spectrum) ≤
      (timeBound (b i) (c i) (forceBudget ε a m g k s T p) : Measure Spectrum) := by
  apply weak_time_domination (fun n => W (ρ n) i) (P i) (N i) (hP i) (hN i)
  filter_upwards [hρ.tendsto_atTop.eventually
    (forceWindow_time_window ε a hε ha m g k s p hm hg hk h hne hh hz T)] with n hn
  exact hn (r (ρ n)) (hr (ρ n)) (b i) (c i) hb hc

theorem subwindow_compact_converges (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
    (i : K) (u v : ℝ) (huv : u ≤ v) (hiu : b i ≤ u) (hvi : v ≤ c i) :
    Tendsto (fun n => compactify (V n u v).positive) atTop
      (𝓝 ((P i).restrict (timeStrip u v))) ∧
    Tendsto (fun n => compactify (V n u v).negative) atTop
      (𝓝 ((N i).restrict (timeStrip u v))) := by
  let T := |b i-s|+|c i-s|
  have hb : |b i-s| ≤ T := by dsimp [T]; linarith [abs_nonneg (c i-s)]
  have hc : |c i-s| ≤ T := by dsimp [T]; linarith [abs_nonneg (b i-s)]
  have ht := limit_time_bound ε a hε ha m g k s p h hne hh hz r hr b c ρ hρ P N hP hN
    hm hg hk T i hb hc
  have hl := weak_time_restriction _ _ (P i) (N i) (hP i) (hN i)
    (b i) (c i) (forceBudget ε a m g k s T p) u v ht huv
  have he (n : ℕ) : restrictPair (W (ρ n) i) u v = V n u v :=
    forceWindow_restrict _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hiu hvi
  constructor
  · apply hl.1.congr'
    apply Eventually.of_forall
    intro n
    exact (compactify_time_restrict (W (ρ n) i).positive u v).symm.trans
      (congrArg (fun F : Pair => compactify F.positive) (he n))
  · apply hl.2.congr'
    apply Eventually.of_forall
    intro n
    exact (compactify_time_restrict (W (ρ n) i).negative u v).symm.trans
      (congrArg (fun F : Pair => compactify F.negative) (he n))

theorem limit_full_window (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
    (i : K) (hbc : b i ≤ c i) :
    (P i).restrict (timeStrip (b i) (c i)) = P i ∧
      (N i).restrict (timeStrip (b i) (c i)) = N i := by
  have hl := subwindow_compact_converges ε a hε ha m g k s p h hne hh hz r hr b c ρ hρ P N hP hN
    hm hg hk i (b i) (c i) hbc le_rfl le_rfl
  exact ⟨tendsto_nhds_unique hl.1 (hP i),tendsto_nhds_unique hl.2 (hN i)⟩

theorem limit_overlap (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
    (i j : K) (u v : ℝ) (huv : u ≤ v)
    (hiu : b i ≤ u) (hvi : v ≤ c i) (hju : b j ≤ u) (hvj : v ≤ c j) :
    (P i).restrict (timeStrip u v) = (P j).restrict (timeStrip u v) ∧
      (N i).restrict (timeStrip u v) = (N j).restrict (timeStrip u v) := by
  have hi := subwindow_compact_converges ε a hε ha m g k s p h hne hh hz r hr b c ρ hρ P N hP hN
    hm hg hk i u v huv hiu hvi
  have hj := subwindow_compact_converges ε a hε ha m g k s p h hne hh hz r hr b c ρ hρ P N hP hN
    hm hg hk j u v huv hju hvj
  exact ⟨tendsto_nhds_unique hi.1 hj.1,tendsto_nhds_unique hi.2 hj.2⟩

def consistentFamily (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k) (hbc : ∀ i, b i ≤ c i) :
    Family b c s (fun T => forceBudget ε a m g k s T p) where
  positive := P
  negative := N
  time_bound := limit_time_bound ε a hε ha m g k s p h hne hh hz r hr b c ρ hρ P N hP hN hm hg hk
  full_window := fun i => limit_full_window ε a hε ha m g k s p h hne hh hz r hr b c ρ hρ P N hP hN
    hm hg hk i (hbc i)
  overlap := limit_overlap ε a hε ha m g k s p h hne hh hz r hr b c ρ hρ P N hP hN hm hg hk

theorem subwindow_zero_converges (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
    (i : K) (u v : ℝ) (huv : u ≤ v) (hiu : b i ≤ u) (hvi : v ≤ c i)
    (q : C₀(ℝ × ℝ,ℂ)) :
    Tendsto (fun n => (V n u v).evaluate q.toBCF) atTop
      (𝓝 ((restrictPair (finitePair (P i) (N i)) u v).evaluate q.toBCF)) := by
  have hl := subwindow_compact_converges ε a hε ha m g k s p h hne hh hz r hr b c ρ hρ P N hP hN
    hm hg hk i u v huv hiu hvi
  have ht := zero_test_of_compact_limits (fun n => V n u v) _ _ hl.1 hl.2 q
  rwa [finitePair_restrict] at ht

#print axioms limit_time_bound
#print axioms subwindow_compact_converges
#print axioms limit_full_window
#print axioms limit_overlap
#print axioms consistentFamily
#print axioms subwindow_zero_converges
end
end UnifiedTheory.Audit.KFCausalNeutralSpacetimeConsistency
