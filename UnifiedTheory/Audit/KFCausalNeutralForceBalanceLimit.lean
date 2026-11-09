/- The concrete positive force-output measures recover the characteristic
increments of the derived all-time neutral probability curve. This proves
convergence of their time-integrated Fourier response, not convergence of
the force measures themselves or closure as a functional of the probability. -/
import UnifiedTheory.Audit.KFCausalNeutralStructuredResponse
import UnifiedTheory.Audit.KFCausalNeutralTemporalResponseLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalNeutralForceBalanceLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalNeutralStructuredResponse
open UnifiedTheory.Audit.KFCausalNeutralTemporalCompactness (curve)
open UnifiedTheory.Audit.KFCausalNeutralInitialProbability (initialProbability)
open UnifiedTheory.Audit.KFCausalDisplacedNeutralTimeControl (speedConstant)
open UnifiedTheory.Audit.KFCausalNeutralTranslationBounds (weightedLinear)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight)
open UnifiedTheory.Audit.KFCausalClockFloorMovingResolventWindow (windowBudget)

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (hm : 0 < m) (hg : 0 < g) (hk : 0 < k)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0))
local notation "F" => fun n : ℕ => curve ε a (h n) hε ha (hne n) (hh n) m g k s p
local notation "S" => fun n : ℕ => state ε a (h n) hε ha (hne n) (hh n) m g k s p
include hm hg hk hz

theorem force_integral_moving_limit (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (ν : ℝ → ProbabilityMeasure ℝ)
    (hc : ∀ z : ℝ × ℝ, Tendsto (fun n => F (φ n) z) atTop (𝓝 (charFun (ν z.1 : Measure ℝ) z.2)))
    (T V : ℝ) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrtop : Tendsto r atTop atTop)
    (v b c : ℕ → ℝ) (hv : ∀ n, |v n| ≤ V)
    (hb : ∀ n, |b n-s| ≤ T) (hc' : ∀ n, |c n-s| ≤ T)
    (v₀ b₀ c₀ : ℝ) (hvlim : Tendsto v atTop (𝓝 v₀))
    (hblim : Tendsto b atTop (𝓝 b₀)) (hclim : Tendsto c atTop (𝓝 c₀)) :
    Tendsto (fun n => ∫ t in b n..c n,
      Complex.I*(v n:ℂ)*(S (φ n) (r n) t).force.fourier (v n)) atTop
      (𝓝 (charFun (ν c₀ : Measure ℝ) v₀-charFun (ν b₀ : Measure ℝ) v₀)) := by
  simpa only [force_rate] using
    KFCausalNeutralTemporalResponseLimit.response_integral_moving_limit
      ε a hε ha m g k s p hm hg hk h hne hh hz φ hφ ν hc
      T V r hr hrtop v b c hv hb hc' v₀ b₀ c₀ hvlim hblim hclim

theorem force_integral_limit (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (ν : ℝ → ProbabilityMeasure ℝ)
    (hc : ∀ z : ℝ × ℝ, Tendsto (fun n => F (φ n) z) atTop (𝓝 (charFun (ν z.1 : Measure ℝ) z.2)))
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrtop : Tendsto r atTop atTop) (v b c : ℝ) :
    Tendsto (fun n => ∫ t in b..c, Complex.I*(v:ℂ)*(S (φ n) (r n) t).force.fourier v) atTop
      (𝓝 (charFun (ν c : Measure ℝ) v-charFun (ν b : Measure ℝ) v)) := by
  simpa only [force_rate] using KFCausalNeutralTemporalResponseLimit.response_integral_limit
    ε a hε ha m g k s p hm hg hk h hne hh hz φ hφ ν hc r hr hrtop v b c

theorem exists_probability_force_balance :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ν : ℝ → ProbabilityMeasure ℝ,
      Continuous ν ∧ ν s = initialProbability p ∧
      (∀ z : ℝ × ℝ, Tendsto (fun n => F (φ n) z) atTop (𝓝 (charFun (ν z.1 : Measure ℝ) z.2))) ∧
      (∀ K, IsCompact K → TendstoUniformlyOn (fun n => F (φ n))
        (fun z => charFun (ν z.1 : Measure ℝ) z.2) atTop K) ∧
      (∀ T v b c : ℝ, |b-s| ≤ T → |c-s| ≤ T →
        ‖charFun (ν c : Measure ℝ) v-charFun (ν b : Measure ℝ) v‖ ≤
          speedConstant ε a m g k s T p v*|c-b|) ∧
      (∀ r u : ℕ → ℝ, ∀ t : ℝ, Tendsto u atTop (𝓝 t) →
        Tendsto (fun n => (S (φ n) (r n) (u n)).probability) atTop (𝓝 (ν t))) ∧
      (∀ r : ℕ → ℝ, (∀ n, 0 < r n) → Tendsto r atTop atTop → ∀ v b c : ℝ,
        Tendsto (fun n => ∫ t in b..c, Complex.I*(v:ℂ)*(S (φ n) (r n) t).force.fourier v) atTop
          (𝓝 (charFun (ν c : Measure ℝ) v-charFun (ν b : Measure ℝ) v))) ∧
      (∀ T : ℝ, ∀ᶠ n in atTop, ∀ r : ℝ, 0 < r → ∀ t : ℝ, |t-s| ≤ T →
        (S (φ n) r t).force.mass ≤
          2*(1+‖weightedLinear (energyWeight m g k 0)‖^2)*windowBudget ε a m g k s T p) := by
  obtain ⟨φ,hφ,ν,hν,hi,hc,hu,hl,hw,_⟩ :=
    KFCausalNeutralTemporalResponseLimit.exists_probability_dynamics
      ε a hε ha m g k s p hm hg hk h hne hh hz
  refine ⟨φ,hφ,ν,hν,hi,hc,hu,hl,?_,?_,?_⟩
  · intro r u t ht
    exact hw u t ht
  · exact force_integral_limit ε a hε ha m g k s p hm hg hk h hne hh hz φ hφ ν hc
  · exact force_mass_window ε a hε ha m g k s p hm.le hg.le hk.le
      (fun n => h (φ n)) (fun n => hne (φ n)) (fun n => hh (φ n)) (hz.comp hφ.tendsto_atTop)

#print axioms force_integral_moving_limit
#print axioms force_integral_limit
#print axioms exists_probability_force_balance
end
end UnifiedTheory.Audit.KFCausalNeutralForceBalanceLimit
