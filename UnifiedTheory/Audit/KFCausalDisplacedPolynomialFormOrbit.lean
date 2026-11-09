/- Actual energy-factor outputs of displaced neutral polynomial packets
and their pure-clock momenta are continuous around the charge orbit.
The momentum reduction retains all ordered corrections at both widths. -/
import UnifiedTheory.Audit.KFCausalPolynomialFactorContinuity
import UnifiedTheory.Audit.KFCausalDisplacedPolynomialOrbit
import UnifiedTheory.Audit.KFCausalPolynomialMomentumReduction
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedParameterBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalDisplacedPolynomialFormOrbit
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalDisplacedPolynomialOrbit
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedParameterBounds
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalPolynomialMomentumReduction (factorMap)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (q k : Joint 2 4) (P : Polynomial ℂ)

theorem packetFactor_continuous
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) :
    Continuous (fun θ => packetFactor ε a h hε ha hh (parameter θ q) (parameter θ k) P hb v l j) := by
  obtain ⟨B,hB⟩ := source_orbit_bound h q k
  exact KFCausalPolynomialFactorContinuity.output_continuous ε a h hε ha hh hb
    |clockFrequency h k| B
    (fun θ => amplitude h (parameter θ q) (parameter θ k))
    (fun θ => clockFrequency h (parameter θ k))
    (fun θ => source h (parameter θ q) (parameter θ k))
    (amplitude_curve_continuous h q k)
    ((clockFrequency_continuous h).comp (parameter_curve_continuous k))
    (source_curve_continuous h q k)
    (fun θ => by dsimp only; rw [clockFrequency_parameter]) hB 4 P v l j

theorem momentumFactor_reduction (θ : ℝ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) :
    momentumFactor ε a h hε ha hh (parameter θ q) (parameter θ k) P hb v l j =
      factorMap ε a h hε ha hb (clockFrequency h k) j
        (packetFactor ε a h hε ha hh (parameter θ q) (parameter θ k) P hb v l j,
          packetFactor ε (a/2) h hε (by positivity) hh (parameter θ q) (parameter θ k) P hb v l j) := by
  unfold momentumFactor packetFactor
  rw [KFCausalPolynomialMomentumReduction.factor_reduction,clockFrequency_parameter]

theorem momentumFactor_continuous
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) :
    Continuous (fun θ => momentumFactor ε a h hε ha hh (parameter θ q) (parameter θ k) P hb v l j) := by
  simp_rw [momentumFactor_reduction ε a h hε ha hh hb q k P]
  exact (factorMap ε a h hε ha hb (clockFrequency h k) j).continuous.comp
    ((packetFactor_continuous ε a h hε ha hh hb q k P v l j).prodMk
      (packetFactor_continuous ε (a/2) h hε (by positivity) hh hb q k P v l j))

#print axioms packetFactor_continuous
#print axioms momentumFactor_reduction
#print axioms momentumFactor_continuous
end
end UnifiedTheory.Audit.KFCausalDisplacedPolynomialFormOrbit
