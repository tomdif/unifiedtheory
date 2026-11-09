/- Bounded continuous source curves can be integrated in every natural
energy-factor graph. Matter compositions are handled through their
closed intermediate operators, not by assuming the compositions closed. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedFormOrbit
import UnifiedTheory.Audit.KFCausalProjectedKineticResponse
import UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalSourcedCurveDomain
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity
open UnifiedTheory.Audit.KFCausalClockFloorCoherentGradientContinuity (derivative_curve_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds (sourceSize)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedClockMomentum
open UnifiedTheory.Audit.KFCausalClockFloorSourcedSpectral (shiftedOutput)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedCommonDomain
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
  (neutralWidth neutralWidth_positive neutralWidth_bound clockFunction clockFunction_memLp)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorTrialClockEnergy
  (halfClockFunction halfClockFunction_memLp dampedClockFunction dampedClockFunction_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf (clockHalf_selfAdjoint)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum (clockMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorAntisymmetricGraph (clockMomentum_closed)
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse (orderedExponential_closed)
open UnifiedTheory.Audit.KFCausalPhysicalField
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition (composition_graph)
open UnifiedTheory.Audit.KFCausalProjectedKineticResponse (integral_closed_graph)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => neutralWidth_positive h hh
local notation "hw" => neutralWidth_bound h

variable (P B : ℝ) (C : ℝ → ℂ) (p : ℝ → ℝ) (b : ℝ → Fin 5 → ℂ)
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
  have hs := KFCausalClockFloorSourcedFieldContinuity.outputs_curve_continuous ε a h hε ha hh hb
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
    (meanState ε a h hε ha hh C p b,meanFactor ε a h hε ha hh hb C p b v l i) ∈
      (energyFactor ε hε h v l i).graph := by
  have hc := state_continuous ε a h hε ha hh B C p b hCc hpc hbc hC hB
  have hf := factor_continuous ε a h hε ha hh hb P B C p b hCc hpc hbc hC hp hB v l
  have ho := integral_closed_graph _ (orderedExponential_closed ε hε h) _ _ hc (hf 7)
    (fun θ => factorOutput_graph ε a α β hε ha hα hβ hw (C θ) (p θ) (b θ) h hb v l 7)
  have hl := integral_closed_graph (physicalField l) (physicalField_closed l) _ _ (hf 7) (hf 5)
    (fun θ => (physicalField l).mem_graph
      ⟨_,shiftedOutput_physicalField_domain ε a α β hε ha hα hβ hw (C θ) (p θ) (b θ) h hb l⟩)
  have hq := integral_closed_graph (fieldSquare l) (fieldSquare_selfAdjoint l).isClosed _ _ (hf 7) (hf 6)
    (fun θ => (fieldSquare l).mem_graph
      ⟨_,shiftedOutput_fieldSquare_domain ε a α β hε ha hα hβ hw (C θ) (p θ) (b θ) h hb l⟩)
  fin_cases i
  · exact integral_closed_graph _ (clockHalf_selfAdjoint ε).isClosed _ _ hc (hf 0)
      (fun θ => factorOutput_graph ε a α β hε ha hα hβ hw (C θ) (p θ) (b θ) h hb v l 0)
  · exact integral_closed_graph _ (clockMomentum_closed ε hε h (v 0)) _ _ hc (hf 1)
      (fun θ => factorOutput_graph ε a α β hε ha hα hβ hw (C θ) (p θ) (b θ) h hb v l 1)
  · exact integral_closed_graph _ (clockMomentum_closed ε hε h (v 1)) _ _ hc (hf 2)
      (fun θ => factorOutput_graph ε a α β hε ha hα hβ hw (C θ) (p θ) (b θ) h hb v l 2)
  · exact integral_closed_graph _ (clockMomentum_closed ε hε h (v 2)) _ _ hc (hf 3)
      (fun θ => factorOutput_graph ε a α β hε ha hα hβ hw (C θ) (p θ) (b θ) h hb v l 3)
  · exact integral_closed_graph _ (clockMomentum_closed ε hε h (v 3)) _ _ hc (hf 4)
      (fun θ => factorOutput_graph ε a α β hε ha hα hβ hw (C θ) (p θ) (b θ) h hb v l 4)
  · exact (composition_graph _ _ _ _).mpr ⟨_,ho,hl⟩
  · exact (composition_graph _ _ _ _).mpr ⟨_,ho,hq⟩
  · exact ho

include hb hCc hpc hbc hC hp hB in
theorem meanState_commonEnergyDomain (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    meanState ε a h hε ha hh C p b ∈ commonEnergyDomain ε hε h v l := by
  apply (commonEnergyDomain_iff ε hε h v l _).mpr
  intro i
  exact LinearPMap.mem_domain_of_mem_graph
    (meanFactor_graph ε a h hε ha hh hb P B C p b hCc hpc hbc hC hp hB v l i)

#print axioms state_continuous
#print axioms factor_continuous
#print axioms meanFactor_graph
#print axioms meanState_commonEnergyDomain
end
end UnifiedTheory.Audit.KFCausalSourcedCurveDomain
