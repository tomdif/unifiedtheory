/- Integrate the second ordered matter actions along bounded source
curves. Each unbounded intermediate graph is integrated using its proved
closedness and continuity; no closedness of a composition is assumed. -/
import UnifiedTheory.Audit.KFCausalCoherentMatterSquare
import UnifiedTheory.Audit.KFCausalMixedFieldSourceContinuity
import UnifiedTheory.Audit.KFCausalVariableWidthSourceCurves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalCoherentMatterCurve
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalCoherentMatterSquare (input spectralOutput)
open KFCausalClockFloorCoherentBounds (sourceSize)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorExponential (longitudinalExponential longitudinal_exponential_closed)
open KFCausalClockFloorTrialSpectralDomain (reversedExponential)
open KFCausalClockFloorMatterClosure (reversedMatterFactor)
open KFCausalPhysicalField (physicalField physicalField_closed)
open KFCausalTransverseFieldSquare (fieldSquare fieldSquare_selfAdjoint)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMixedFieldGaussianContour (strip_pair double_shift_bound)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalOrderedOperatorComposition (composition_graph)
open KFCausalProjectedKineticResponse (integral_closed_graph)
open KFCausalVariableWidthSourceCurves (meanFactor factor_continuous)

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (h : ℝ) (hb : |h| ≤ Real.pi*ε/3)
  (P B : ℝ) (C : ℝ → ℂ) (p : ℝ → ℝ) (b : ℝ → Fin 5 → ℂ)
  (hCc : Continuous C) (hpc : Continuous p) (hbc : Continuous b)
  (hC : ∀ θ, ‖C θ‖ ≤ 1) (hp : ∀ θ, |p θ| ≤ P) (hB : ∀ θ, sourceSize (b θ) ≤ B)
local notation "hb₀" => original_strip ε h hε hb
local notation "hd" => double_shift_bound ε h hb
local notation "h0" => strip_pair ε (-h/2) |-h/2| 0 hd (by simp)
local notation "hs" => strip_pair ε (-h/2) |-h/2| (-h/2) hd le_rfl

include hCc hpc hbc hp hB in
theorem input_continuous (j : Fin 2) :
    Continuous (fun θ => input ε a α β hε ha hα hβ hw h hb (C θ) (p θ) (b θ) j) :=
  hCc.smul (KFCausalMixedFieldSourceContinuity.state_curve_continuous ε a α β (-h/2) 0 P B j
    hε ha hα hβ hw h0.1 h0.2 p b hpc hbc hp hB)

include hCc hpc hbc hp hB in
theorem spectral_continuous (j : Fin 2) :
    Continuous (fun θ => spectralOutput ε a α β hε ha hα hβ hw h hb (C θ) (p θ) (b θ) j) :=
  hCc.smul (KFCausalMixedFieldSourceContinuity.state_curve_continuous ε a α β (-h/2) (-h/2) P B j
    hε ha hα hβ hw hs.1 hs.2 p b hpc hbc hp hB)

def meanInput (j : Fin 2) : Hilbert :=
  ∫ θ, input ε a α β hε ha hα hβ hw h hb (C θ) (p θ) (b θ) j ∂angleMeasure

def meanSpectral (j : Fin 2) : Hilbert :=
  ∫ θ, spectralOutput ε a α β hε ha hα hβ hw h hb (C θ) (p θ) (b θ) j ∂angleMeasure

def meanOutput (j : Fin 2) : Hilbert :=
  inverseL ε hε (meanSpectral ε a α β hε ha hα hβ hw h hb C p b j)

include hCc hpc hbc hp hB in
theorem mean_exponential_graph (j : Fin 2) :
    (meanInput ε a α β hε ha hα hβ hw h hb C p b j,
      meanSpectral ε a α β hε ha hα hβ hw h hb C p b j) ∈
        (longitudinalExponential ε hε h (1/2)).graph :=
  integral_closed_graph _ (longitudinal_exponential_closed ε hε h (1/2)) _ _
    (input_continuous ε a α β hε ha hα hβ hw h hb P B C p b hCc hpc hbc hp hB j)
    (spectral_continuous ε a α β hε ha hα hβ hw h hb P B C p b hCc hpc hbc hp hB j)
    (fun θ => KFCausalCoherentMatterSquare.input_exponential_graph ε a α β hε ha hα hβ hw h hb
      (C θ) (p θ) (b θ) j)

include hCc hpc hbc hp hB in
theorem mean_reverse_graph (j : Fin 2) :
    (meanInput ε a α β hε ha hα hβ hw h hb C p b j,
      meanOutput ε a α β hε ha hα hβ hw h hb C p b j) ∈
        (reversedExponential ε hε h).graph :=
  (KFCausalClockFloorVacuumSquare.reversed_graph ε hε h _ _).mpr
    ⟨_,mean_exponential_graph ε a α β hε ha hα hβ hw h hb P B C p b hCc hpc hbc hp hB j,rfl⟩

include hCc hpc hbc hC hp hB in
theorem linear_reverse_graph :
    (meanFactor ε a α β hε ha hα hβ hw h hb₀ C p b modelDirections pointField 5,
      meanOutput ε a α β hε ha hα hβ hw h hb C p b 0) ∈
        (reversedMatterFactor ε hε h (physicalField pointField)).graph := by
  apply (composition_graph _ _ _ _).mpr
  refine ⟨meanInput ε a α β hε ha hα hβ hw h hb C p b 0,?_,
    mean_reverse_graph ε a α β hε ha hα hβ hw h hb P B C p b hCc hpc hbc hp hB 0⟩
  exact integral_closed_graph _ (physicalField_closed pointField) _ _
    (factor_continuous ε a α β hε ha hα hβ hw h hb₀ P B C p b hCc hpc hbc hC hp hB modelDirections pointField 5)
    (input_continuous ε a α β hε ha hα hβ hw h hb P B C p b hCc hpc hbc hp hB 0)
    (fun θ => KFCausalCoherentMatterSquare.linear_second_field_graph ε a α β hε ha hα hβ hw h hb
      (C θ) (p θ) (b θ))

include hCc hpc hbc hC hp hB in
theorem quadratic_reverse_graph :
    (meanFactor ε a α β hε ha hα hβ hw h hb₀ C p b modelDirections pointField 6,
      meanOutput ε a α β hε ha hα hβ hw h hb C p b 1) ∈
        (reversedMatterFactor ε hε h (fieldSquare pointField)).graph := by
  apply (composition_graph _ _ _ _).mpr
  refine ⟨meanInput ε a α β hε ha hα hβ hw h hb C p b 1,?_,
    mean_reverse_graph ε a α β hε ha hα hβ hw h hb P B C p b hCc hpc hbc hp hB 1⟩
  exact integral_closed_graph _ (fieldSquare_selfAdjoint pointField).isClosed _ _
    (factor_continuous ε a α β hε ha hα hβ hw h hb₀ P B C p b hCc hpc hbc hC hp hB modelDirections pointField 6)
    (input_continuous ε a α β hε ha hα hβ hw h hb P B C p b hCc hpc hbc hp hB 1)
    (fun θ => KFCausalCoherentMatterSquare.quadratic_second_field_graph ε a α β hε ha hα hβ hw h hb
      (C θ) (p θ) (b θ))

#print axioms input_continuous
#print axioms spectral_continuous
#print axioms mean_exponential_graph
#print axioms mean_reverse_graph
#print axioms linear_reverse_graph
#print axioms quadratic_reverse_graph
end
end UnifiedTheory.Audit.KFCausalCoherentMatterCurve
