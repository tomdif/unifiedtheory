/- The constructed second derivative is the actual second action of
each maximal physical transverse momentum. -/
import UnifiedTheory.Audit.KFCausalNarrowPacketSecondStates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalNarrowPacketSecondMomentumGraphs
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalNarrowFourierCoordinates (mixedCoordinates)
open KFCausalNarrowPacketSecondStates (secondState secondState_coe secondCoordinates secondState_coordinates)
open KFCausalNarrowPacketSecondDifferential (firstProfile firstProfile_eq second_derivative firstProfile_transverse_differentiable)
open KFCausalNarrowPacketMomentumGraphs (differentialState differentialState_coe momentumOutput momentum_graph)
open KFCausalPhysicalTransverseMomentum (transverseMomentum)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalTransverseTrialDerivative (derivative)
open KFCausalOrderedOperatorComposition (composition composition_graph)

variable (α β w : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 0 < w)
  (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume) (h : ℝ)

def secondOutput (j : Fin 4) : Hilbert :=
  (-Complex.I*(h:ℂ))^2 • secondState α β w hα hβ hw b P g hc hg j

theorem momentum_second_graph (j : Fin 4) :
    (momentumOutput α β w hα hβ hw b P g hc hg h j,secondOutput α β w hα hβ hw b P g hc hg h j) ∈
      (transverseMomentum h (modelDirections j)).graph := by
  let F := firstProfile α β w b P g j
  have hF : differentialState α β w hα hβ hw b P g hc hg j =ᵐ[volume] F := by
    filter_upwards [differentialState_coe α β w hα hβ hw b P g hc hg j] with x hx
    exact hx.trans (firstProfile_eq α β w b P g j x).symm
  have hS : secondState α β w hα hβ hw b P g hc hg j =ᵐ[volume] derivative (modelDirections j) F := by
    filter_upwards [secondState_coe α β w hα hβ hw b P g hc hg j] with x hx
    exact hx.trans (second_derivative α β w b P g j x).symm
  have hmF := (Lp.memLp _).ae_eq hF
  have hmS := (Lp.memLp _).ae_eq hS
  have heF : differentialState α β w hα hβ hw b P g hc hg j = hmF.toLp F :=
    Lp.ext (hF.trans hmF.coeFn_toLp.symm)
  have heS : secondState α β w hα hβ hw b P g hc hg j = hmS.toLp (derivative (modelDirections j) F) :=
    Lp.ext (hS.trans hmS.coeFn_toLp.symm)
  have hp := KFCausalTransverseMomentumDerivative.derivative_momentum_graph h F (modelDirections j) hmF hmS
    (firstProfile_transverse_differentiable α β w b P g j)
  rw [← heF,← heS] at hp
  have hs := (transverseMomentum h (modelDirections j)).graph.smul_mem (-Complex.I*(h:ℂ)) hp
  simpa only [Prod.smul_mk,smul_smul,pow_two,momentumOutput,secondOutput] using hs

theorem double_graph (j : Fin 4) :
    (KFCausalNarrowFourierPackets.state α β w hα hβ hw b P g hc hg,secondOutput α β w hα hβ hw b P g hc hg h j) ∈
      (composition (transverseMomentum h (modelDirections j)) (transverseMomentum h (modelDirections j))).graph :=
  (composition_graph _ _ _ _).mpr ⟨momentumOutput α β w hα hβ hw b P g hc hg h j,
    momentum_graph α β w hα hβ hw b P g hc hg h j,
    momentum_second_graph α β w hα hβ hw b P g hc hg h j⟩

theorem secondOutput_coordinates (j : Fin 4) :
    mixedCoordinates (secondOutput α β w hα hβ hw b P g hc hg h j) =ᵐ[volume]
      fun z => (-Complex.I*(h:ℂ))^2*secondCoordinates α β w b P g j z := by
  rw [secondOutput,map_smul]
  filter_upwards [Lp.coeFn_smul ((-Complex.I*(h:ℂ))^2)
    (mixedCoordinates (secondState α β w hα hβ hw b P g hc hg j)),
    secondState_coordinates α β w hα hβ hw b P g hc hg j] with z hz hs
  simp only [hz,Pi.smul_apply,smul_eq_mul,hs]

#print axioms momentum_second_graph
#print axioms double_graph
#print axioms secondOutput_coordinates
end
end UnifiedTheory.Audit.KFCausalNarrowPacketSecondMomentumGraphs
