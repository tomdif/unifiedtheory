/- A constructed limit state with eleven-coordinate probabilities,
the all-time neutral-position curve, and the actual clock balance on one
subsequence. The clock mean is identified at every convergent sampling
family. Neither zero defect nor closed classical transport is asserted. -/
import UnifiedTheory.Audit.KFCausalElevenPositionProbability
import UnifiedTheory.Audit.KFCausalClockFloorGlobalClockLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalElevenProbabilityClockPath
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalElevenPositionProbability (LimitState)
open UnifiedTheory.Audit.KFCausalElevenPhaseProjection (ElevenSpace)
open UnifiedTheory.Audit.KFCausalElevenClockCompatibility (clockProjection)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRates (clockExpectation comparisonRate)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockWindow (speedConstant)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect)

variable {K : Type*}
variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (t : K → ℕ → ℝ)

structure ClockLimitState extends LimitState ε a hε ha m g k s p h hne hh t where
  clock : ℝ → ℝ
  clock_continuous : Continuous clock
  clock_bounds : ∀ b, clock b ∈ Set.Icc (0:ℝ) 1
  clock_limit : ∀ b, Tendsto (fun n => clockExpectation ε a (h (index n)) hε ha
    (hne (index n)) (hh (index n)) m g k s p b) atTop (𝓝 (clock b))
  clock_uniform : ∀ S, IsCompact S → TendstoUniformlyOn
    (fun n => clockExpectation ε a (h (index n)) hε ha (hne (index n)) (hh (index n)) m g k s p)
    clock atTop S
  clock_lipschitz : ∀ T b c : ℝ, |b-s| ≤ T → |c-s| ≤ T →
    |clock c-clock b| ≤ speedConstant ε a m g k s T p * |c-b|
  clock_balance : ∀ b c : ℝ, Tendsto (fun n => ∫ u in b..c,
    comparisonRate ε a (h (index n)) hε ha (hne (index n)) (hh (index n)) m g k s p u)
    atTop (𝓝 (clock c-clock b))
  clock_marginal : ∀ j b, Tendsto (t j) atTop (𝓝 b) →
    (∫ x, defect ε (clockProjection x) ∂(probability j : Measure ElevenSpace)) = clock b

theorem exists_clock_limit [Countable K] (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
    (hz : Tendsto h atTop (𝓝 0)) (T : K → ℝ) (ht : ∀ j n, t j n ∈ Set.Icc s (s+T j)) :
    Nonempty (ClockLimitState ε a hε ha m g k s p h hne hh t) := by
  obtain ⟨α,hα,f,hf,hbounds,hpoint,huniform,hlip,hbalance⟩ :=
    KFCausalClockFloorGlobalClockLimit.clock_global_balance ε a hε ha m g k s p hm hg hk h hne hh hz
  obtain ⟨L⟩ := KFCausalElevenPositionProbability.exists_limit ε a hε ha m g k s p
    (fun n => h (α n)) (fun n => hne (α n)) (fun n => hh (α n)) (fun j n => t j (α n))
    hm hg hk (hz.comp hα.tendsto_atTop) T (fun j n => ht j (α n))
  let φ : ℕ → ℕ := fun n => α (L.index n)
  have hφ : StrictMono φ := hα.comp L.strictMono
  let P : LimitState ε a hε ha m g k s p h hne hh t := {
    index := φ
    strictMono := hφ
    position := L.position
    position_continuous := L.position_continuous
    position_initial := L.position_initial
    position_limit := L.position_limit
    position_uniform := L.position_uniform
    position_moving := L.position_moving
    kernel := L.kernel
    kernel_limit := L.kernel_limit
    kernel_uniform := L.kernel_uniform
    probability := L.probability
    probability_characteristic := L.probability_characteristic
    probability_tight := L.probability_tight
    probability_limit := L.probability_limit
    neutral_marginal := fun j b htb => L.neutral_marginal j b (htb.comp hα.tendsto_atTop)
    clock_mean_limit := L.clock_mean_limit
  }
  have hp (b : ℝ) : Tendsto (fun n => clockExpectation ε a (h (φ n)) hε ha
      (hne (φ n)) (hh (φ n)) m g k s p b) atTop (𝓝 (f b)) :=
    (hpoint b).comp L.strictMono.tendsto_atTop
  refine ⟨{
    toLimitState := P
    clock := f
    clock_continuous := hf
    clock_bounds := hbounds
    clock_limit := hp
    clock_uniform := ?_
    clock_lipschitz := hlip
    clock_balance := fun b c => (hbalance b c).comp L.strictMono.tendsto_atTop
    clock_marginal := ?_
  }⟩
  · intro S hS
    rw [Metric.tendstoUniformlyOn_iff]
    intro η hη
    exact L.strictMono.tendsto_atTop.eventually (Metric.tendstoUniformlyOn_iff.mp (huniform S hS) η hη)
  · intro j b htb
    let F : ℕ → ℝ → ℂ := fun n u =>
      (clockExpectation ε a (h n) hε ha (hne n) (hh n) m g k s p u : ℂ)
    have he := KFCausalClockFloorGlobalClockLimit.clock_equicontinuity
      ε a hε ha m g k s p hm hg hk h hne hh hz
    have hpC (u : ℝ) : Tendsto (fun n => F (φ n) u) atTop (𝓝 (f u : ℂ)) :=
      (Complex.continuous_ofReal.tendsto (f u)).comp (hp u)
    have hmoving := KFCausalCharacteristicCompactUniformity.moving_frequency_limit
      F he φ hφ (fun u => (f u : ℂ)) hpC b (fun n => t j (φ n)) (htb.comp hφ.tendsto_atTop)
    have hreal : Tendsto (fun n => clockExpectation ε a (h (φ n)) hε ha
        (hne (φ n)) (hh (φ n)) m g k s p (t j (φ n))) atTop (𝓝 (f b)) := by
      simpa only [F,Complex.ofReal_re] using (Complex.continuous_re.tendsto (f b : ℂ)).comp hmoving
    exact tendsto_nhds_unique (P.clock_mean_limit j) hreal

#print axioms exists_clock_limit

end
end UnifiedTheory.Audit.KFCausalElevenProbabilityClockPath
