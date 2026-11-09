/- A constructed larger limit state: eleven-coordinate probabilities,
position and momentum probability curves, the global clock balance, and
the actual neutral net force all share one subsequence. Both neutral
marginals and the clock mean agree at convergent sampling families.
The force is not yet identified with a classical joint-state force law. -/
import UnifiedTheory.Audit.KFCausalElevenProbabilityClockPath
import UnifiedTheory.Audit.KFCausalElevenMomentumMarginal
import UnifiedTheory.Audit.KFCausalNeutralTemporalProbability
import UnifiedTheory.Audit.KFCausalNeutralProbabilityDeterminesForce

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalElevenStructuredDynamics
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalElevenProbabilityClockPath (ClockLimitState)
open UnifiedTheory.Audit.KFCausalElevenMomentumMarginal (axis marginal marginal_eq physical_characteristic)
open UnifiedTheory.Audit.KFCausalNeutralTemporalCompactness (curve)
open UnifiedTheory.Audit.KFCausalNeutralMomentumProbability (snapshot snapshot_characteristic)
open UnifiedTheory.Audit.KFCausalNeutralInitialProbability (initialProbability)
open UnifiedTheory.Audit.KFCausalGlobalSpacetimeForce (Force)
open UnifiedTheory.Audit.KFCausalNeutralProbabilityDeterminesForce (Description)

variable {K : Type*}
variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (t : K → ℕ → ℝ)

structure StructuredState extends ClockLimitState ε a hε ha m g k s p h hne hh t where
  momentum : ℝ → ProbabilityMeasure ℝ
  momentum_continuous : Continuous momentum
  momentum_initial : momentum s = initialProbability p
  momentum_limit : ∀ z : ℝ × ℝ, Tendsto (fun n => curve ε a (h (index n)) hε ha
    (hne (index n)) (hh (index n)) m g k s p z) atTop (𝓝 (charFun (momentum z.1 : Measure ℝ) z.2))
  momentum_uniform : ∀ S, IsCompact S → TendstoUniformlyOn
    (fun n => curve ε a (h (index n)) hε ha (hne (index n)) (hh (index n)) m g k s p)
    (fun z => charFun (momentum z.1 : Measure ℝ) z.2) atTop S
  momentum_moving : ∀ u : ℕ → ℝ, ∀ b : ℝ, Tendsto u atTop (𝓝 b) →
    Tendsto (fun n => snapshot ε a (h (index n)) hε ha (hne (index n)) (hh (index n)) m g k s p (u n))
      atTop (𝓝 (momentum b))
  momentum_marginal : ∀ j b, Tendsto (t j) atTop (𝓝 b) → marginal (probability j) = momentum b
  force : Force
  force_description : Description ε a hε ha m g k s p
    (fun n => h (index n)) (fun n => hne (index n)) (fun n => hh (index n)) momentum force

theorem exists_structured_state [Countable K] (hm : 0 < m) (hg : 0 < g) (hk : 0 < k)
    (hz : Tendsto h atTop (𝓝 0)) (T : K → ℝ) (ht : ∀ j n, t j n ∈ Set.Icc s (s+T j)) :
    Nonempty (StructuredState ε a hε ha m g k s p h hne hh t) := by
  obtain ⟨α,hα,ν,hν,hM,hMu,_,_⟩ := KFCausalNeutralTemporalProbability.exists_probability_curve
    ε a hε ha m g k s p hm hg hk h hne hh hz
  obtain ⟨L⟩ := KFCausalElevenProbabilityClockPath.exists_clock_limit ε a hε ha m g k s p
    (fun n => h (α n)) (fun n => hne (α n)) (fun n => hh (α n)) (fun j n => t j (α n))
    hm.le hg.le hk.le (hz.comp hα.tendsto_atTop) T (fun j n => ht j (α n))
  let φ : ℕ → ℕ := fun n => α (L.index n)
  have hφ : StrictMono φ := hα.comp L.strictMono
  let P : ClockLimitState ε a hε ha m g k s p h hne hh t := {
    toLimitState := {
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
    clock := L.clock
    clock_continuous := L.clock_continuous
    clock_bounds := L.clock_bounds
    clock_limit := L.clock_limit
    clock_uniform := L.clock_uniform
    clock_lipschitz := L.clock_lipschitz
    clock_balance := L.clock_balance
    clock_marginal := fun j b htb => L.clock_marginal j b (htb.comp hα.tendsto_atTop)
  }
  let c : ℝ × ℝ → ℂ := fun z => charFun (ν z.1 : Measure ℝ) z.2
  have hp (z : ℝ × ℝ) : Tendsto (fun n => curve ε a (h (φ n)) hε ha (hne (φ n)) (hh (φ n))
      m g k s p z) atTop (𝓝 (c z)) := (hM z).comp L.strictMono.tendsto_atTop
  obtain ⟨_,hi,J,hJ⟩ := KFCausalNeutralProbabilityDeterminesForce.exists_force_of_probability_limit
    ε a hε ha m g k s p (fun n => h (φ n)) (fun n => hne (φ n)) (fun n => hh (φ n))
    (hz.comp hφ.tendsto_atTop) ν hp hm hg hk
  let F := fun n => curve ε a (h n) hε ha (hne n) (hh n) m g k s p
  have he := KFCausalNeutralTemporalCompactness.joint_equicontinuity
    ε a hε ha m g k s p hm hg hk h hne hh hz
  have hc : Continuous c := KFCausalAsymptoticCharacteristicCompactness.continuous_limit
    F he φ hφ c hp
  refine ⟨{
    toClockLimitState := P
    momentum := ν
    momentum_continuous := hν
    momentum_initial := hi
    momentum_limit := hp
    momentum_uniform := ?_
    momentum_moving := ?_
    momentum_marginal := ?_
    force := J
    force_description := hJ
  }⟩
  · intro S hS
    rw [Metric.tendstoUniformlyOn_iff]
    intro η hη
    exact L.strictMono.tendsto_atTop.eventually (Metric.tendstoUniformlyOn_iff.mp (hMu S hS) η hη)
  · intro u b hu
    have he' : KFCausalAsymptoticCharacteristicCompactness.EventuallyLocallyEquicontinuous
        (fun n (z : ℝ × ℝ) => charFun
          (snapshot ε a (h n) hε ha (hne n) (hh n) m g k s p z.1 : Measure ℝ) z.2) := by
      simpa only [snapshot_characteristic] using he
    apply KFCausalTemporalProbabilityRepresentation.moving_time_convergence
      (fun n => snapshot ε a (h n) hε ha (hne n) (hh n) m g k s p) he' φ hφ c hc
      _ ν (fun _ _ => rfl) u b hu
    intro z
    simpa only [snapshot_characteristic] using hp z
  · intro j b htb
    apply marginal_eq (P.probability j) (P.kernel j) (P.probability_characteristic j) (ν b)
    intro v
    have hmoving := KFCausalCharacteristicCompactUniformity.moving_frequency_limit
      F he φ hφ c hp (b,v) (fun n => (t j (φ n),v))
      ((htb.comp hφ.tendsto_atTop).prodMk_nhds (tendsto_const_nhds (x := v)))
    have hcanonical : Tendsto (fun n => F (φ n) (t j (φ n),v)) atTop
        (𝓝 ((P.kernel j).value (axis v))) := by
      simpa only [physical_characteristic] using P.kernel_limit j (axis v)
    exact tendsto_nhds_unique hcanonical hmoving

#print axioms exists_structured_state

end
end UnifiedTheory.Audit.KFCausalElevenStructuredDynamics
