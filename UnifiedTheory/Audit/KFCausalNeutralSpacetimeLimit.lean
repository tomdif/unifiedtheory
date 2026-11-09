/- One actual semiclassical subsequence carries the probability curve,
consistent interval forces and finite local spacetime force limits. Time
cutoffs identify the whole-window response with the continuity equation. -/
import UnifiedTheory.Audit.KFCausalNeutralSpacetimeForce
import UnifiedTheory.Audit.KFCausalSpacetimeWindowTests
import UnifiedTheory.Audit.KFCausalNeutralConsistentDynamics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalNeutralSpacetimeLimit
noncomputable section
open MeasureTheory Filter SchwartzMap BoundedContinuousFunction
open scoped Topology ZeroAtInfty
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalNeutralForceConsistency (forceBudget)
open UnifiedTheory.Audit.KFCausalNeutralSpacetimeForce
open UnifiedTheory.Audit.KFCausalSpacetimeForcePair (Pair)
open UnifiedTheory.Audit.KFCausalCompactifiedForceMeasure (Spectrum)
open UnifiedTheory.Audit.KFCausalCompactSpacetimeForce
open UnifiedTheory.Audit.KFCausalLocalSpacetimeTests
open UnifiedTheory.Audit.KFCausalSpacetimeWindowTests
open UnifiedTheory.Audit.KFCausalConsistentForceIntervals (Family)
open UnifiedTheory.Audit.KFCausalNeutralTemporalCompactness (curve)
open UnifiedTheory.Audit.KFCausalNeutralMomentumProbability (snapshot)
open UnifiedTheory.Audit.KFCausalNeutralInitialProbability (initialProbability)

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0)) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
  {K : Type*} [Countable K] (b c : K → ℝ) (hbc : ∀ i, b i ≤ c i)

def windowFamily (n : ℕ) (i : K) : Pair :=
  forceWindow ε a (h n) hε ha (hne n) (hh n) m g k s p (r n) (hr n) (b i) (c i)

local notation "W" => windowFamily ε a hε ha m g k s p h hne hh r hr b c
local notation "I" => KFCausalNeutralLocalForceLimit.family ε a hε ha m g k s p h hne hh r hr b c

include hz hbc

omit [Countable K] in
theorem windowFamily_mass_bound (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k) :
    ∀ i, ∃ C : ℝ, ∀ᶠ n in atTop, (W n i).mass ≤ C := by
  intro i
  let T := |b i-s|+|c i-s|
  have hb : |b i-s| ≤ T := by dsimp [T]; linarith [abs_nonneg (c i-s)]
  have hc : |c i-s| ≤ T := by dsimp [T]; linarith [abs_nonneg (b i-s)]
  refine ⟨(c i-b i)*forceBudget ε a m g k s T p,?_⟩
  filter_upwards [forceWindow_mass_window ε a hε ha m g k s p hm hg hk h hne hh hz T] with n hn
  exact hn (r n) (hr n) (b i) (c i) (hbc i) hb hc

theorem exists_joint_spacetime_limits (hm : 0 < m) (hg : 0 < g) (hk : 0 < k)
    (hrtop : Tendsto r atTop atTop) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : ℝ → ProbabilityMeasure ℝ,
      Continuous ν ∧ ν s = initialProbability p ∧
      (∀ z : ℝ × ℝ, Tendsto (fun n => curve ε a (h (ρ n)) hε ha (hne (ρ n)) (hh (ρ n))
        m g k s p z) atTop (𝓝 (charFun (ν z.1 : Measure ℝ) z.2))) ∧
      (∀ t, Tendsto (fun n => snapshot ε a (h (ρ n)) hε ha (hne (ρ n)) (hh (ρ n))
        m g k s p t) atTop (𝓝 (ν t))) ∧
      ∃ F : Family b c s (fun T => forceBudget ε a m g k s T p),
        (∀ i (q : C₀(ℝ,ℂ)), Tendsto (fun n => (I (ρ n) i).evaluate q.toBCF) atTop
          (𝓝 ((F.local i).evaluate q.toBCF))) ∧
        (∀ i (f : 𝓢(ℝ,ℂ)), (∫ x, f x ∂(ν (c i) : Measure ℝ))-
          (∫ x, f x ∂(ν (b i) : Measure ℝ)) =
          (F.local i).evaluate (derivCLM ℂ ℂ f).toBoundedContinuousFunction) ∧
      ∃ P N : K → FiniteMeasure Square,
        (∀ i, Tendsto (fun n => compactify (W (ρ n) i).positive) atTop (𝓝 (P i))) ∧
        (∀ i, Tendsto (fun n => compactify (W (ρ n) i).negative) atTop (𝓝 (N i))) ∧
        (∀ i (q : C₀(ℝ × ℝ,ℂ)), Tendsto (fun n => (W (ρ n) i).evaluate q.toBCF) atTop
          (𝓝 ((finitePair (P i) (N i)).evaluate q.toBCF))) ∧
        (∀ T i, |b i-s| ≤ T → |c i-s| ≤ T →
          (finitePair (P i) (N i)).mass ≤ (c i-b i)*forceBudget ε a m g k s T p) ∧
        (∀ i (χ : Spectrum →ᵇ ℂ),
          (∀ t ∈ Set.Icc (b i) (c i), χ (KFCausalCompactifiedForceMeasure.embed t) = 1) →
          (∀ x, x ∉ KFCausalLocalForceMeasure.interior → χ x = 0) →
          ∀ q : C₀(ℝ,ℂ), (F.local i).evaluate q.toBCF =
            (finitePair (P i) (N i)).evaluate (pullback (liftTest χ q))) ∧
        (∀ i (f : 𝓢(ℝ,ℂ)), ∃ χ : Spectrum →ᵇ ℂ,
          (∀ t ∈ Set.Icc (b i) (c i), χ (KFCausalCompactifiedForceMeasure.embed t) = 1) ∧
          (∀ x, x ∉ KFCausalLocalForceMeasure.interior → χ x = 0) ∧
          (∫ x, f x ∂(ν (c i) : Measure ℝ))-(∫ x, f x ∂(ν (b i) : Measure ℝ)) =
            (finitePair (P i) (N i)).evaluate
              (pullback (liftTest χ (derivCLM ℂ ℂ f).toZeroAtInfty))) := by
  obtain ⟨φ,hφ,ν,hν,hi,hc,hw,F,_,_,hl,hf⟩ :=
    KFCausalNeutralConsistentDynamics.exists_consistent_weak_dynamics
      ε a hε ha m g k s p h hne hh hz r hr hrtop hm hg hk b c hbc
  have hb (i : K) : ∃ C : ℝ, ∀ᶠ n in atTop, (W (φ n) i).mass ≤ C := by
    obtain ⟨C,hC⟩ := windowFamily_mass_bound ε a hε ha m g k s p h hne hh hz r hr b c hbc
      hm.le hg.le hk.le i
    exact ⟨C,hφ.tendsto_atTop.eventually hC⟩
  obtain ⟨ψ,hψ,P,N,hP,hN,_⟩ := pair_subsequence (fun n => W (φ n)) hb
  let ρ := φ ∘ ψ
  have hρ : StrictMono ρ := hφ.comp hψ
  have hlρ (i : K) (q : C₀(ℝ,ℂ)) : Tendsto (fun n => (I (ρ n) i).evaluate q.toBCF) atTop
      (𝓝 ((F.local i).evaluate q.toBCF)) := (hl i q).comp hψ.tendsto_atTop
  have hidentify (i : K) (χ : Spectrum →ᵇ ℂ)
      (hχ : ∀ t ∈ Set.Icc (b i) (c i), χ (KFCausalCompactifiedForceMeasure.embed t) = 1)
      (hzero : ∀ x, x ∉ KFCausalLocalForceMeasure.interior → χ x = 0)
      (q : C₀(ℝ,ℂ)) : (F.local i).evaluate q.toBCF =
        (finitePair (P i) (N i)).evaluate (pullback (liftTest χ q)) := by
    have hj := boundary_test_of_compact_limits (fun n => W (ρ n) i) (P i) (N i)
      (hP i) (hN i) (liftTest χ q) (liftTest_boundary χ hzero q)
    have he : (fun n => (W (ρ n) i).evaluate (pullback (liftTest χ q))) =
        (fun n => (I (ρ n) i).evaluate q.toBCF) := by
      funext n
      exact fromCurve_window_test _ _ _ _ _ (b i) (c i) χ hχ q
    rw [he] at hj
    exact tendsto_nhds_unique (hlρ i q) hj
  refine ⟨ρ,hρ,ν,hν,hi,(fun z => (hc z).comp hψ.tendsto_atTop),
    (fun t => (hw t).comp hψ.tendsto_atTop),F,hlρ,hf,P,N,hP,hN,?_,?_,hidentify,?_⟩
  · intro i q
    exact zero_test_of_compact_limits (fun n => W (ρ n) i) (P i) (N i) (hP i) (hN i) q
  · intro T i hbi hci
    apply local_limit_mass_bound (fun n => W (ρ n) i) (P i) (N i) (hP i) (hN i)
    filter_upwards [hρ.tendsto_atTop.eventually
      (forceWindow_mass_window ε a hε ha m g k s p hm.le hg.le hk.le h hne hh hz T)] with n hn
    exact hn (r (ρ n)) (hr (ρ n)) (b i) (c i) (hbc i) hbi hci
  · intro i f
    obtain ⟨χ,hχ,hzero⟩ := exists_time_cutoff (b i) (c i)
    exact ⟨χ,hχ,hzero,(hf i f).trans (hidentify i χ hχ hzero (derivCLM ℂ ℂ f).toZeroAtInfty)⟩

#print axioms windowFamily_mass_bound
#print axioms exists_joint_spacetime_limits
end
end UnifiedTheory.Audit.KFCausalNeutralSpacetimeLimit
