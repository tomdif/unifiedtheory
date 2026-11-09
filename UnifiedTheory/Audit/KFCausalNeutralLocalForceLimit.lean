/- One actual semiclassical subsequence carries the neutral probability
curve and local limits of its time-integrated force measures for any
countable interval family. Boundary mass is not assumed absent. The
original Fourier balance is retained separately; classical closure is open. -/
import UnifiedTheory.Audit.KFCausalNeutralIntegratedForce
import UnifiedTheory.Audit.KFCausalLocalForceMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalNeutralLocalForceLimit
noncomputable section
open MeasureTheory Filter BoundedContinuousFunction
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalNeutralForceMeasure (FluxPair)
open UnifiedTheory.Audit.KFCausalNeutralIntegratedForce
open UnifiedTheory.Audit.KFCausalCompactifiedForceMeasure (Spectrum compactify pullback)
open UnifiedTheory.Audit.KFCausalLocalForceMeasure
open UnifiedTheory.Audit.KFCausalNeutralTemporalCompactness (curve)
open UnifiedTheory.Audit.KFCausalNeutralMomentumProbability (snapshot)
open UnifiedTheory.Audit.KFCausalNeutralInitialProbability (initialProbability)

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0)) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
  {K : Type*} [Countable K] (b c : K → ℝ) (hbc : ∀ i, b i ≤ c i)

def family (n : ℕ) (i : K) : FluxPair :=
  forceInterval ε a (h n) hε ha (hne n) (hh n) m g k s p (r n) (hr n) (b i) (c i)

local notation "G" => family ε a hε ha m g k s p h hne hh r hr b c
include hz hbc

omit [Countable K] in
theorem family_mass_bound (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k) :
    ∀ i, ∃ C : ℝ, ∀ᶠ n in atTop, (G n i).mass ≤ C := by
  intro i
  let T := |b i-s|+|c i-s|
  have hb : |b i-s| ≤ T := by dsimp only [T]; linarith [abs_nonneg (c i-s)]
  have hc : |c i-s| ≤ T := by dsimp only [T]; linarith [abs_nonneg (b i-s)]
  refine ⟨(c i-b i)*(2*(1+‖KFCausalNeutralTranslationBounds.weightedLinear
    (KFCausalPhysicalEnergyFactors.energyWeight m g k 0)‖^2)*
    KFCausalClockFloorMovingResolventWindow.windowBudget ε a m g k s T p),?_⟩
  filter_upwards [forceInterval_mass_window ε a hε ha m g k s p hm hg hk h hne hh hz T] with n hn
  exact hn (r n) (hr n) (b i) (c i) (hbc i) hb hc

theorem exists_local_force_limits (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P N : K → FiniteMeasure Spectrum,
      (∀ i, Tendsto (fun n => compactify (G (φ n) i).positive) atTop (𝓝 (P i))) ∧
      (∀ i, Tendsto (fun n => compactify (G (φ n) i).negative) atTop (𝓝 (N i))) ∧
      (∀ i (q : Spectrum →ᵇ ℂ), (∀ x, x ∉ interior → q x = 0) →
        Tendsto (fun n => (G (φ n) i).evaluate (pullback q)) atTop
          (𝓝 ((finitePair (P i) (N i)).evaluate (pullback q)))) :=
  local_pair_subsequence G (family_mass_bound ε a hε ha m g k s p h hne hh hz r hr b c hbc hm hg hk)

theorem exists_joint_local_response (hm : 0 < m) (hg : 0 < g) (hk : 0 < k)
    (hrtop : Tendsto r atTop atTop) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : ℝ → ProbabilityMeasure ℝ,
      Continuous ν ∧ ν s = initialProbability p ∧
      (∀ z : ℝ × ℝ, Tendsto (fun n => curve ε a (h (ρ n)) hε ha (hne (ρ n)) (hh (ρ n))
        m g k s p z) atTop (𝓝 (charFun (ν z.1 : Measure ℝ) z.2))) ∧
      (∀ t, Tendsto (fun n => snapshot ε a (h (ρ n)) hε ha (hne (ρ n)) (hh (ρ n))
        m g k s p t) atTop (𝓝 (ν t))) ∧
      ∃ P N : K → FiniteMeasure Spectrum,
        (∀ i, Tendsto (fun n => compactify (G (ρ n) i).positive) atTop (𝓝 (P i))) ∧
        (∀ i, Tendsto (fun n => compactify (G (ρ n) i).negative) atTop (𝓝 (N i))) ∧
        (∀ i (q : Spectrum →ᵇ ℂ), (∀ x, x ∉ interior → q x = 0) →
          Tendsto (fun n => (G (ρ n) i).evaluate (pullback q)) atTop
            (𝓝 ((finitePair (P i) (N i)).evaluate (pullback q)))) ∧
        (∀ b₀ c₀ v : ℝ, b₀ ≤ c₀ → Tendsto (fun n => Complex.I*(v:ℂ)*
          (forceInterval ε a (h (ρ n)) hε ha (hne (ρ n)) (hh (ρ n)) m g k s p
            (r (ρ n)) (hr (ρ n)) b₀ c₀).fourier v) atTop
          (𝓝 (charFun (ν c₀ : Measure ℝ) v-charFun (ν b₀ : Measure ℝ) v))) := by
  obtain ⟨φ,hφ,ν,hν,hi,hc,_,_,hw,_⟩ :=
    KFCausalNeutralTemporalResponseLimit.exists_probability_dynamics
      ε a hε ha m g k s p hm hg hk h hne hh hz
  obtain ⟨ψ,hψ,P,N,hP,hN,hq⟩ := exists_local_force_limits ε a hε ha m g k s p
    (fun n => h (φ n)) (fun n => hne (φ n)) (fun n => hh (φ n)) (hz.comp hφ.tendsto_atTop)
    (fun n => r (φ n)) (fun n => hr (φ n)) b c hbc hm.le hg.le hk.le
  let ρ := φ ∘ ψ
  have hρ : StrictMono ρ := hφ.comp hψ
  have hcρ (z : ℝ × ℝ) : Tendsto (fun n => curve ε a (h (ρ n)) hε ha (hne (ρ n)) (hh (ρ n))
      m g k s p z) atTop (𝓝 (charFun (ν z.1 : Measure ℝ) z.2)) :=
    (hc z).comp hψ.tendsto_atTop
  refine ⟨ρ,hρ,ν,hν,hi,hcρ,?_,P,N,hP,hN,hq,?_⟩
  · intro t
    exact (hw (fun _ => t) t tendsto_const_nhds).comp hψ.tendsto_atTop
  · intro b₀ c₀ v hb₀c₀
    exact forceInterval_balance_limit ε a hε ha m g k s p hm hg hk h hne hh hz ρ hρ ν hcρ
      (fun n => r (ρ n)) (fun n => hr (ρ n)) (hrtop.comp hρ.tendsto_atTop) b₀ c₀ v hb₀c₀

#print axioms family_mass_bound
#print axioms exists_local_force_limits
#print axioms exists_joint_local_response
end
end UnifiedTheory.Audit.KFCausalNeutralLocalForceLimit
