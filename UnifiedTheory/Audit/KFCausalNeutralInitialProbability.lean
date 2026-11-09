/- The initial neutral probability converges to the point mass at the
specified canonical boost momentum. This follows from the actual initial
characteristic limit and the propagator's identity at the initial time. -/
import UnifiedTheory.Audit.KFCausalNeutralMomentumProbability
import UnifiedTheory.Audit.KFCausalNeutralTemporalCompactness
import UnifiedTheory.Audit.KFCausalClockFloorBoostedInitialLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 250000

namespace UnifiedTheory.Audit.KFCausalNeutralInitialProbability
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics
open UnifiedTheory.Audit.KFCausalClockFloorInitialClassicalLaw
open UnifiedTheory.Audit.KFCausalClockFloorBoostedInitialLaw
open UnifiedTheory.Audit.KFCausalClockFloorBoostedKineticLimit (boostedState)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (characteristic scalar operator)
open UnifiedTheory.Audit.KFCausalNeutralCanonicalForm (frequency)
open UnifiedTheory.Audit.KFCausalNeutralTranslationCoordinates (vector)
open UnifiedTheory.Audit.KFCausalNeutralMomentumProbability (snapshot snapshot_characteristic)
open UnifiedTheory.Audit.KFCausalNeutralTemporalCompactness (curve)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem zero_positionFrequency : positionFrequency 0 (0:Transverse) = 0 := by
  apply ContinuousLinearMap.ext
  intro z
  simp [positionFrequency,KFCausalPhysicalGaussianConcentration.dot]

theorem momentum_phase (p : Configuration) (v : ℝ) :
    positionFrequency p.1 p.2 (0,Pi.single 4 v) = v*p.2 4 := by
  simp [positionFrequency,KFCausalPhysicalGaussianConcentration.dot,Fin.sum_univ_succ]
  ring

theorem clock_characteristic_zero (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    clockCharacteristic ε a hε ha 0 = 1 := by
  letI := clockLaw_probability ε a hε ha
  rw [clockCharacteristic_law]
  simp [KFCausalLpPhaseTranslation.phase]

def initialProbability (p : Configuration) : ProbabilityMeasure ℝ :=
  ⟨Measure.dirac (p.2 4),inferInstance⟩

theorem initialProbability_characteristic (p : Configuration) (v : ℝ) :
    charFun (initialProbability p : Measure ℝ) v = scalar (v*p.2 4) := by
  rw [initialProbability,ProbabilityMeasure.coe_mk,charFun_dirac]
  simp only [RCLike.inner_apply,conj_trivial,scalar,Complex.ofReal_mul]
  congr 1
  ring

theorem curve_initial (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hne : h ≠ 0)
    (hh : |h| ≤ 2*Real.pi*ε/3) (m g k s : ℝ) (p : Configuration) (v : ℝ) :
    curve ε a h hε ha hne hh m g k s p (s,v) =
      inner ℂ (boostedState ε a h hε ha hne (positionFrequency p.1 p.2))
        (KFCausalClockFloorInitialCharacteristic.observable h 0 0 0 (Pi.single 4 v)
          (boostedState ε a h hε ha hne (positionFrequency p.1 p.2))) := by
  have hi := evolvedCharacteristic_initial ε hε h hne hh m g k s
    (boostedState ε a h hε ha hne (positionFrequency p.1 p.2)) (frequency v)
  have hop := operator_eq_observable h 0 0 (0:Transverse) (Pi.single 4 v)
  rw [zero_positionFrequency] at hop
  change operator volume h (frequency v) = _ at hop
  simpa only [characteristic,hop] using hi

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0))
include hz

theorem initial_characteristic_limit (v : ℝ) :
    Tendsto (fun n => curve ε a (h n) hε ha (hne n) (hh n) m g k s p (s,v))
      atTop (𝓝 (scalar (v*p.2 4))) := by
  have ht := boosted_characteristic_limit ε a hε ha h hne hz p 0 0 (0:Transverse) (Pi.single 4 v)
  rw [boostedLaw_characteristic ε a hε ha,clock_characteristic_zero ε a hε ha,mul_one,momentum_phase] at ht
  simpa only [curve_initial] using ht

theorem initial_probability_limit :
    Tendsto (fun n => snapshot ε a (h n) hε ha (hne n) (hh n) m g k s p s)
      atTop (𝓝 (initialProbability p)) := by
  apply KFCausalCharacteristicRepresentation.weak_convergence
    (fun n => snapshot ε a (h n) hε ha (hne n) (hh n) m g k s p s)
    (fun v => scalar (v*p.2 4)) (by unfold scalar; fun_prop) (by simp [scalar]) _
    (initialProbability p) (initialProbability_characteristic p)
  intro v
  simpa only [snapshot_characteristic] using initial_characteristic_limit ε a hε ha m g k s p h hne hh hz v

#print axioms zero_positionFrequency
#print axioms momentum_phase
#print axioms clock_characteristic_zero
#print axioms initialProbability_characteristic
#print axioms curve_initial
#print axioms initial_characteristic_limit
#print axioms initial_probability_limit
end
end UnifiedTheory.Audit.KFCausalNeutralInitialProbability
