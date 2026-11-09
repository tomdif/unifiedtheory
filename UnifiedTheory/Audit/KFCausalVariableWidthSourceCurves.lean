/- Continuous source curves at arbitrary admissible Gaussian widths
integrate into the actual simultaneous energy graphs. -/
import UnifiedTheory.Audit.KFCausalVariableWidthFieldContinuity
import UnifiedTheory.Audit.KFCausalEnergyFactorGraphIntegration

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalVariableWidthSourceCurves
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalClockFloorCoherentOrbitContinuity (physicalProfile_curve_continuous)
open KFCausalClockFloorCoherentGradientContinuity (derivative_curve_continuous)
open KFCausalClockFloorCoherentBounds (sourceSize)
open KFCausalClockFloorSourcedClockMomentum (state)
open KFCausalClockFloorSourcedCommonDomain (factorOutput factorOutput_graph)
open KFCausalClockFloorInvariantTrial (clockFunction clockFunction_memLp)
open KFCausalClockFloorTrialClockEnergy
  (halfClockFunction halfClockFunction_memLp dampedClockFunction dampedClockFunction_memLp)
open KFCausalClockFloorCommonDomain (energyFactor)

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a)
  (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
  (h : ℝ) (hb : |h| ≤ 2*Real.pi*ε/3)
  (P B : ℝ) (C : ℝ → ℂ) (p : ℝ → ℝ) (b : ℝ → Fin 5 → ℂ)
  (hCc : Continuous C) (hpc : Continuous p) (hbc : Continuous b)
  (hC : ∀ θ, ‖C θ‖ ≤ 1) (hp : ∀ θ, |p θ| ≤ P) (hB : ∀ θ, sourceSize (b θ) ≤ B)

include hCc hpc hbc hC hB in
theorem state_continuous :
    Continuous (fun θ => state ε a α β hε ha hα hβ hw (C θ) (p θ) (b θ)) :=
  physicalProfile_curve_continuous α β B hα hβ hw C p b (clockFunction ε a)
    (clockFunction_memLp ε a hε ha) hCc hpc hbc hC hB

include hCc hpc hbc hC hp hB in
theorem factor_continuous (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8) :
    Continuous (fun θ => factorOutput ε a α β hε ha hα hβ hw (C θ) (p θ) (b θ) h hb v l i) := by
  have hc := physicalProfile_curve_continuous α β B hα hβ hw C p b
    (halfClockFunction ε a) (halfClockFunction_memLp ε a hε ha) hCc hpc hbc hC hB
  have hm (u : Transverse) := (continuous_const (y := -Complex.I*(h:ℂ))).smul
    (derivative_curve_continuous α β B hα hβ hw C p b
      (dampedClockFunction ε a) (dampedClockFunction_memLp ε a hε ha) hCc hpc hbc hC hB u)
  have hs := KFCausalVariableWidthFieldContinuity.outputs_curve_continuous ε a α β h hε ha hα hβ hw hb
    P B C p b hCc hpc hbc hC hp hB
  fin_cases i
  · exact hc
  · exact hm (v 0)
  · exact hm (v 1)
  · exact hm (v 2)
  · exact hm (v 3)
  · exact hs.2.1 l
  · exact hs.2.2 l
  · exact hs.1

def meanState : Hilbert :=
  ∫ θ, state ε a α β hε ha hα hβ hw (C θ) (p θ) (b θ) ∂angleMeasure

def meanFactor (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8) : Hilbert :=
  ∫ θ, factorOutput ε a α β hε ha hα hβ hw (C θ) (p θ) (b θ) h hb v l i ∂angleMeasure

include hCc hpc hbc hC hp hB in
theorem meanFactor_graph (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8) :
    (meanState ε a α β hε ha hα hβ hw C p b,
      meanFactor ε a α β hε ha hα hβ hw h hb C p b v l i) ∈ (energyFactor ε hε h v l i).graph :=
  KFCausalEnergyFactorGraphIntegration.factor_graph ε h hε v l _ _
    (state_continuous ε a α β hε ha hα hβ hw B C p b hCc hpc hbc hC hB)
    (factor_continuous ε a α β hε ha hα hβ hw h hb P B C p b hCc hpc hbc hC hp hB v l)
    (fun θ j => factorOutput_graph ε a α β hε ha hα hβ hw (C θ) (p θ) (b θ) h hb v l j) i

#print axioms state_continuous
#print axioms factor_continuous
#print axioms meanFactor_graph
end
end UnifiedTheory.Audit.KFCausalVariableWidthSourceCurves
