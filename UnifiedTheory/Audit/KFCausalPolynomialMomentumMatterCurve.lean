/- The two reverse matter graphs for actual polynomial clock momenta.
The same source circles that define those momenta are used; all mixed
second-shift intermediates have derived L2 continuity. -/
import UnifiedTheory.Audit.KFCausalCoherentMomentumMatterSquare
import UnifiedTheory.Audit.KFCausalCoherentMatterCurve
import UnifiedTheory.Audit.KFCausalVariableWidthPolynomialMomentum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalPolynomialMomentumMatterCurve
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalPolynomialGaussianStates
  (circleSource sourceBound circleSource_continuous circleSource_bound)
open KFCausalSourceCircleCoefficients
open KFCausalVariableWidthPolynomialMomentum (factorCurve factorCurve_continuous)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorExponential (longitudinalExponential longitudinal_exponential_closed)
open KFCausalClockFloorTrialSpectralDomain (reversedExponential)
open KFCausalClockFloorMatterClosure (reversedMatterFactor)
open KFCausalPhysicalField (physicalField physicalField_closed)
open KFCausalTransverseFieldSquare (fieldSquare fieldSquare_selfAdjoint)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalGaussianVacuumSquare (original_strip double_strip)
open KFCausalCoherentMomentumOutputReduction (reducedOutput_continuous)
open KFCausalOrderedOperatorComposition (composition_graph)
open KFCausalProjectedKineticResponse (integral_closed_graph)

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (h : ℝ) (hb : |h| ≤ Real.pi*ε/3)
  (p : ℝ) (b : Fin 5 → ℂ) (i : Fin 5) (n : ℕ)
local notation "hb₀" => original_strip ε h hε hb
local notation "hb₂" => double_strip ε h hb

def inputCurve (j : Fin 2) (θ : ℝ) : Hilbert :=
  KFCausalCoherentMomentumMatterSquare.input ε a α β hε ha hα hβ hw h hb
    (weight n θ) p (circleSource b i θ) j
def spectralCurve (j : Fin 2) (θ : ℝ) : Hilbert :=
  KFCausalCoherentMomentumMatterSquare.spectralOutput ε a α β hε ha hα hβ hw h hb
    (weight n θ) p (circleSource b i θ) j

theorem input_continuous (j : Fin 2) :
    Continuous (inputCurve ε a α β hε ha hα hβ hw h hb p b i n j) := by
  have hc (a' : ℝ) (ha' : 0 < a') := KFCausalCoherentMatterCurve.input_continuous ε a' α β
    hε ha' hα hβ hw h hb |p| (sourceBound b) (weight n) (fun _ => p) (circleSource b i)
    (weight_continuous n) continuous_const (circleSource_continuous b i)
    (fun _ => le_rfl) (circleSource_bound b i) j
  exact reducedOutput_continuous ε a h hε ha hb₀ p _ _ (hc a ha) (hc (a/2) (half_pos ha))

theorem spectral_continuous (j : Fin 2) :
    Continuous (spectralCurve ε a α β hε ha hα hβ hw h hb p b i n j) := by
  have hc (a' : ℝ) (ha' : 0 < a') := KFCausalCoherentMatterCurve.spectral_continuous ε a' α β
    hε ha' hα hβ hw h hb |p| (sourceBound b) (weight n) (fun _ => p) (circleSource b i)
    (weight_continuous n) continuous_const (circleSource_continuous b i)
    (fun _ => le_rfl) (circleSource_bound b i) j
  exact continuous_const.smul
    (reducedOutput_continuous ε a (2*h) hε ha hb₂ p _ _ (hc a ha) (hc (a/2) (half_pos ha)))

def meanInput (j : Fin 2) : Hilbert :=
  ∫ θ, inputCurve ε a α β hε ha hα hβ hw h hb p b i n j θ ∂angleMeasure
def meanSpectral (j : Fin 2) : Hilbert :=
  ∫ θ, spectralCurve ε a α β hε ha hα hβ hw h hb p b i n j θ ∂angleMeasure
def meanOutput (j : Fin 2) : Hilbert :=
  inverseL ε hε (meanSpectral ε a α β hε ha hα hβ hw h hb p b i n j)

theorem mean_exponential_graph (j : Fin 2) :
    (meanInput ε a α β hε ha hα hβ hw h hb p b i n j,
      meanSpectral ε a α β hε ha hα hβ hw h hb p b i n j) ∈
        (longitudinalExponential ε hε h (1/2)).graph :=
  integral_closed_graph _ (longitudinal_exponential_closed ε hε h (1/2)) _ _
    (input_continuous ε a α β hε ha hα hβ hw h hb p b i n j)
    (spectral_continuous ε a α β hε ha hα hβ hw h hb p b i n j)
    (fun θ => KFCausalCoherentMomentumMatterSquare.input_exponential_graph ε a α β hε ha hα hβ hw h hb
      (weight n θ) p (circleSource b i θ) j)

theorem mean_reverse_graph (j : Fin 2) :
    (meanInput ε a α β hε ha hα hβ hw h hb p b i n j,
      meanOutput ε a α β hε ha hα hβ hw h hb p b i n j) ∈ (reversedExponential ε hε h).graph :=
  (KFCausalClockFloorVacuumSquare.reversed_graph ε hε h _ _).mpr
    ⟨_,mean_exponential_graph ε a α β hε ha hα hβ hw h hb p b i n j,rfl⟩

theorem linear_reverse_graph :
    (∫ θ, factorCurve ε a α β hε ha hα hβ hw h p b i hb₀ n modelDirections pointField 5 θ ∂angleMeasure,
      meanOutput ε a α β hε ha hα hβ hw h hb p b i n 0) ∈
        (reversedMatterFactor ε hε h (physicalField pointField)).graph := by
  apply (composition_graph _ _ _ _).mpr
  refine ⟨meanInput ε a α β hε ha hα hβ hw h hb p b i n 0,?_,
    mean_reverse_graph ε a α β hε ha hα hβ hw h hb p b i n 0⟩
  exact integral_closed_graph _ (physicalField_closed pointField) _ _
    (factorCurve_continuous ε a α β hε ha hα hβ hw h p b i hb₀ n modelDirections pointField 5)
    (input_continuous ε a α β hε ha hα hβ hw h hb p b i n 0)
    (fun θ => KFCausalCoherentMomentumMatterSquare.linear_second_field_graph ε a α β hε ha hα hβ hw h hb
      (weight n θ) p (circleSource b i θ))

theorem quadratic_reverse_graph :
    (∫ θ, factorCurve ε a α β hε ha hα hβ hw h p b i hb₀ n modelDirections pointField 6 θ ∂angleMeasure,
      meanOutput ε a α β hε ha hα hβ hw h hb p b i n 1) ∈
        (reversedMatterFactor ε hε h (fieldSquare pointField)).graph := by
  apply (composition_graph _ _ _ _).mpr
  refine ⟨meanInput ε a α β hε ha hα hβ hw h hb p b i n 1,?_,
    mean_reverse_graph ε a α β hε ha hα hβ hw h hb p b i n 1⟩
  exact integral_closed_graph _ (fieldSquare_selfAdjoint pointField).isClosed _ _
    (factorCurve_continuous ε a α β hε ha hα hβ hw h p b i hb₀ n modelDirections pointField 6)
    (input_continuous ε a α β hε ha hα hβ hw h hb p b i n 1)
    (fun θ => KFCausalCoherentMomentumMatterSquare.quadratic_second_field_graph ε a α β hε ha hα hβ hw h hb
      (weight n θ) p (circleSource b i θ))

#print axioms input_continuous
#print axioms spectral_continuous
#print axioms mean_exponential_graph
#print axioms mean_reverse_graph
#print axioms linear_reverse_graph
#print axioms quadratic_reverse_graph
end
end UnifiedTheory.Audit.KFCausalPolynomialMomentumMatterCurve
