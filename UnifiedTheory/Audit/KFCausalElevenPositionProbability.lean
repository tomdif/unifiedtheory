/- Constructed eleven-coordinate probability limits of positive approximants
of the actual evolved states. Their position marginal equals the derived
all-time position curve. The record is inhabited by a proved extraction;
its convergence and compatibility fields are not supplied assumptions. -/
import UnifiedTheory.Audit.KFCausalElevenPositionLimit
import UnifiedTheory.Audit.KFCausalElevenClockCompatibility
import UnifiedTheory.Audit.KFCausalWindowedApproximation
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalElevenPositionProbability
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalCanonicalElevenCoordinates (Coefficients encode)
open UnifiedTheory.Audit.KFCausalElevenPhaseProjection
open UnifiedTheory.Audit.KFCausalElevenProbabilityRepresentation
open UnifiedTheory.Audit.KFCausalElevenMarginals (neutralMarginal neutral_marginal_eq)
open UnifiedTheory.Audit.KFCausalElevenClockCompatibility (clockProjection)
open UnifiedTheory.Audit.KFCausalElevenCountableCharacteristics (ClassicalKernel)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (characteristic)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail (evolvedState evolvedState_norm)
open UnifiedTheory.Audit.KFCausalNeutralPositionTemporalCompactness (curve)
open UnifiedTheory.Audit.KFCausalNeutralPositionInitialLimit (origin)
open UnifiedTheory.Audit.KFCausalPhysicalWindowedLaw (law phase)
open UnifiedTheory.Audit.KFCausalSemiclassicalWindow (unitWindow unitWindow_norm)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRates (clockExpectation)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

def snapshot (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hne : h ≠ 0)
    (hh : |h| ≤ 2*Real.pi*ε/3) (m g k s : ℝ) (p : Configuration) (n : ℕ) (t : ℝ) :
    ProbabilityMeasure ElevenSpace :=
  projectedProbability (law h (evolvedState ε a h hε ha hne hh m g k s p t) (unitWindow 6 n))
    (KFCausalPhysicalWindowedLaw.law_probability _ _ _
      (evolvedState_norm ε a h hε ha hne hh m g k s p t) (unitWindow_norm 6 n))

theorem snapshot_characteristic (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hne : h ≠ 0)
    (hh : |h| ≤ 2*Real.pi*ε/3) (m g k s : ℝ) (p : Configuration) (n : ℕ) (t : ℝ) (z : ElevenSpace) :
    charFun (snapshot ε a h hε ha hne hh m g k s p n t : Measure ElevenSpace) z =
      ∫ x, phase (encode (coefficients z)) x
        ∂law h (evolvedState ε a h hε ha hne hh m g k s p t) (unitWindow 6 n) :=
  projected_characteristic _ z

variable {K : Type*}
variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (t : K → ℕ → ℝ)

structure LimitState where
  index : ℕ → ℕ
  strictMono : StrictMono index
  position : ℝ → ProbabilityMeasure ℝ
  position_continuous : Continuous position
  position_initial : position s = origin
  position_limit : ∀ z : ℝ × ℝ,
    Tendsto (fun n => curve ε a (h (index n)) hε ha (hne (index n)) (hh (index n)) m g k s p z)
      atTop (𝓝 (charFun (position z.1 : Measure ℝ) z.2))
  position_uniform : ∀ S, IsCompact S → TendstoUniformlyOn
    (fun n => curve ε a (h (index n)) hε ha (hne (index n)) (hh (index n)) m g k s p)
    (fun z => charFun (position z.1 : Measure ℝ) z.2) atTop S
  position_moving : ∀ u : ℕ → ℝ, ∀ b : ℝ, Tendsto u atTop (𝓝 b) →
    Tendsto (fun n => KFCausalNeutralPositionProbability.snapshot ε a (h (index n)) hε ha
      (hne (index n)) (hh (index n)) m g k s p (u n)) atTop (𝓝 (position b))
  kernel : K → ClassicalKernel
  kernel_limit : ∀ j z, Tendsto (fun n => characteristic volume (h (index n))
    (evolvedState ε a (h (index n)) hε ha (hne (index n)) (hh (index n)) m g k s p (t j (index n)))
    (encode z)) atTop (𝓝 ((kernel j).value z))
  kernel_uniform : ∀ j S, IsCompact S → TendstoUniformlyOn
    (fun n z => characteristic volume (h (index n))
      (evolvedState ε a (h (index n)) hε ha (hne (index n)) (hh (index n)) m g k s p (t j (index n)))
      (encode z)) (kernel j).value atTop S
  probability : K → ProbabilityMeasure ElevenSpace
  probability_characteristic : ∀ j z,
    charFun (probability j : Measure ElevenSpace) (coefficientVector z) = (kernel j).value z
  probability_tight : ∀ j, IsTightMeasureSet (Set.range (fun n =>
    (snapshot ε a (h (index n)) hε ha (hne (index n)) (hh (index n)) m g k s p n (t j (index n)) :
      Measure ElevenSpace)))
  probability_limit : ∀ j, Tendsto (fun n =>
    snapshot ε a (h (index n)) hε ha (hne (index n)) (hh (index n)) m g k s p n (t j (index n)))
    atTop (𝓝 (probability j))
  neutral_marginal : ∀ j b, Tendsto (t j) atTop (𝓝 b) → neutralMarginal (probability j) = position b
  clock_mean_limit : ∀ j, Tendsto (fun n => clockExpectation ε a (h (index n)) hε ha
    (hne (index n)) (hh (index n)) m g k s p (t j (index n))) atTop
    (𝓝 (∫ x, defect ε (clockProjection x) ∂(probability j : Measure ElevenSpace)))

theorem exists_limit [Countable K] (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
    (hz : Tendsto h atTop (𝓝 0)) (T : K → ℝ) (ht : ∀ j n, t j n ∈ Set.Icc s (s+T j)) :
    Nonempty (LimitState ε a hε ha m g k s p h hne hh t) := by
  classical
  obtain ⟨α,hα,ρ,hρ,hi,hpos,hposu,_,χ,hχ,hχu,hagree⟩ :=
    KFCausalElevenPositionLimit.common_sampled_limit ε a hε ha m g k s p hm hg hk h hne hh hz T t ht
  obtain ⟨β,hβ,hprob,herror⟩ := KFCausalWindowedApproximation.exists_state_uniform_approximation
    (fun n => h (α n)) (hz.comp hα.tendsto_atTop)
  let φ : ℕ → ℕ := fun n => α (β n)
  have hφ : StrictMono φ := hα.comp hβ
  let ψ n u := evolvedState ε a (h (φ n)) hε ha (hne (φ n)) (hh (φ n)) m g k s p u
  let μ j n := law (h (φ n)) (ψ n (t j (φ n))) (unitWindow 6 n)
  have hμ (j : K) (n : ℕ) : IsProbabilityMeasure (μ j n) :=
    hprob n _ (evolvedState_norm ε a (h (φ n)) hε ha (hne (φ n)) (hh (φ n)) m g k s p (t j (φ n)))
  have hphase (j : K) (z : Coefficients) : Tendsto (fun n => ∫ x, phase (encode z) x ∂μ j n)
      atTop (𝓝 ((χ j).value z)) := by
    have he := KFCausalWindowedApproximation.error_tendsto (fun n => h (α n)) β herror
      (fun n => ψ n (t j (φ n)))
      (fun n => evolvedState_norm ε a (h (φ n)) hε ha (hne (φ n)) (hh (φ n)) m g k s p (t j (φ n)))
      (encode z)
    have hc := (hχ j z).comp hβ.tendsto_atTop
    simpa only [μ,ψ,φ,Function.comp_def,sub_add_cancel,zero_add] using he.add hc
  have hrep (j : K) := tight_and_represented (μ j) (hμ j) (χ j) (hphase j)
  choose ν hν hweak using fun j => (hrep j).2
  let F := fun n => curve ε a (h n) hε ha (hne n) (hh n) m g k s p
  let c : ℝ × ℝ → ℂ := fun z => charFun (ρ z.1 : Measure ℝ) z.2
  have he := KFCausalNeutralPositionTemporalCompactness.joint_equicontinuity
    ε a hε ha m g k s p hm hg hk h hne hh hz
  have hc : Continuous c := KFCausalAsymptoticCharacteristicCompactness.continuous_limit F he α hα c hpos
  have hp (z : ℝ × ℝ) : Tendsto (fun n => F (φ n) z) atTop (𝓝 (c z)) :=
    (hpos z).comp hβ.tendsto_atTop
  refine ⟨{
    index := φ
    strictMono := hφ
    position := ρ
    position_continuous := hρ
    position_initial := hi
    position_limit := hp
    position_uniform := ?_
    position_moving := ?_
    kernel := χ
    kernel_limit := fun j z => (hχ j z).comp hβ.tendsto_atTop
    kernel_uniform := ?_
    probability := ν
    probability_characteristic := hν
    probability_tight := fun j => (hrep j).1
    probability_limit := hweak
    neutral_marginal := fun j b htb => neutral_marginal_eq (ν j) (χ j) (hν j) (ρ b) (hagree j b htb)
    clock_mean_limit := ?_
  }⟩
  · intro S hS
    rw [Metric.tendstoUniformlyOn_iff]
    intro η hη
    exact hβ.tendsto_atTop.eventually (Metric.tendstoUniformlyOn_iff.mp (hposu S hS) η hη)
  · intro u b hu
    exact KFCausalTemporalProbabilityRepresentation.moving_time_convergence
      (fun n => KFCausalNeutralPositionProbability.snapshot ε a (h n) hε ha (hne n) (hh n) m g k s p)
      he φ hφ c hc hp ρ (fun _ _ => rfl) u b hu
  · intro j S hS
    rw [Metric.tendstoUniformlyOn_iff]
    intro η hη
    exact hβ.tendsto_atTop.eventually (Metric.tendstoUniformlyOn_iff.mp (hχu j S hS) η hη)
  · intro j
    exact KFCausalElevenClockCompatibility.defect_mean_limit ε hε (fun n => h (φ n))
      (fun n => ψ n (t j (φ n)))
      (fun n => evolvedState_norm ε a (h (φ n)) hε ha (hne (φ n)) (hh (φ n)) m g k s p (t j (φ n)))
      (χ j) (ν j) (hν j) (fun z => (hχ j z).comp hβ.tendsto_atTop)

#print axioms snapshot_characteristic
#print axioms exists_limit

end
end UnifiedTheory.Audit.KFCausalElevenPositionProbability
