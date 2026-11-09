/- The actual initial neutral-position marginal converges to the origin.
The canonical boost changes momentum and leaves this position limit
unchanged. The proof uses the existing full initial characteristic limit. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionProbability
import UnifiedTheory.Audit.KFCausalNeutralInitialProbability

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNeutralPositionInitialLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalNeutralPositionCharge (frequency)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCharacteristic (bare bare_canonical)
open UnifiedTheory.Audit.KFCausalNeutralPositionProbability (snapshot snapshot_characteristic)
open UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics
open UnifiedTheory.Audit.KFCausalClockFloorBoostedKineticLimit (boostedState)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedInitialLaw
open UnifiedTheory.Audit.KFCausalClockFloorInitialCharacteristic (observable)
open UnifiedTheory.Audit.KFCausalNeutralInitialProbability (clock_characteristic_zero)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (characteristic scalar operator)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem position_frequency (v : ℝ) : positionFrequency 0 (Pi.single 4 v) = frequency v := by
  apply ContinuousLinearMap.ext
  intro x
  simp [positionFrequency,KFCausalPhysicalGaussianConcentration.dot,
    KFCausalNeutralPositionCharge.frequency_apply,Fin.sum_univ_succ]

def origin : ProbabilityMeasure ℝ := ⟨Measure.dirac 0,inferInstance⟩

theorem origin_characteristic (v : ℝ) : charFun (origin : Measure ℝ) v = 1 := by
  simp [origin,charFun_dirac]

theorem bare_initial (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hne : h ≠ 0)
    (hh : |h| ≤ 2*Real.pi*ε/3) (m g k s : ℝ) (p : Configuration) (v : ℝ) :
    bare ε a h hε ha hne hh m g k s p v s =
      inner ℂ (boostedState ε a h hε ha hne (positionFrequency p.1 p.2))
        (observable h 0 0 (Pi.single 4 v) 0
          (boostedState ε a h hε ha hne (positionFrequency p.1 p.2))) := by
  have hi := evolvedCharacteristic_initial ε hε h hne hh m g k s
    (boostedState ε a h hε ha hne (positionFrequency p.1 p.2)) (frequency v,(0:Configuration))
  have hop := operator_eq_observable h 0 0 (Pi.single 4 v) (0:Transverse)
  rw [position_frequency] at hop
  have hb := (bare_canonical ε a h hε ha hne hh m g k s p v s).trans hi
  exact hb.trans (congrArg (fun U : Hilbert ≃ₗᵢ[ℂ] Hilbert =>
    inner ℂ (boostedState ε a h hε ha hne (positionFrequency p.1 p.2))
      (U (boostedState ε a h hε ha hne (positionFrequency p.1 p.2)))) hop)

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0))
include hz

theorem initial_characteristic_limit (v : ℝ) :
    Tendsto (fun n => bare ε a (h n) hε ha (hne n) (hh n) m g k s p v s)
      atTop (𝓝 (1:ℂ)) := by
  have ht := boosted_characteristic_limit ε a hε ha h hne hz p 0 0 (Pi.single 4 v) (0:Transverse)
  rw [boostedLaw_characteristic ε a hε ha,clock_characteristic_zero ε a hε ha] at ht
  have hz' : positionFrequency p.1 p.2 ((0:ℝ),(0:Transverse)) = 0 := map_zero _
  simpa only [hz',scalar,Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_mul,bare_initial] using ht

theorem initial_probability_limit :
    Tendsto (fun n => snapshot ε a (h n) hε ha (hne n) (hh n) m g k s p s) atTop (𝓝 origin) := by
  apply KFCausalCharacteristicRepresentation.weak_convergence
    (fun n => snapshot ε a (h n) hε ha (hne n) (hh n) m g k s p s)
    (fun _ => (1:ℂ)) continuous_const rfl _ origin origin_characteristic
  intro v
  simpa only [snapshot_characteristic] using
    initial_characteristic_limit ε a hε ha m g k s p h hne hh hz v

#print axioms position_frequency
#print axioms origin_characteristic
#print axioms bare_initial
#print axioms initial_characteristic_limit
#print axioms initial_probability_limit

end
end UnifiedTheory.Audit.KFCausalNeutralPositionInitialLimit
