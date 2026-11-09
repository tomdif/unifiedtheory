/- All eight actual energy factors of pure-clock momentum on an arbitrary
complex-sourced Gaussian. Half-width inputs retain the SAME amplitude.
The ordered factors use the derived T B formula, including its correction. -/
import UnifiedTheory.Audit.KFCausalSourcedMomentumOutput
import UnifiedTheory.Audit.KFCausalOriginalPureClockOutput

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalSourcedMomentumFactors
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedClockMomentum (state)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedSpectral (shiftedOutput)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedCommonDomain (linearOutput quadraticOutput)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor commonEnergyDomain commonEnergyDomain_iff)
open UnifiedTheory.Audit.KFCausalPureClockOutputMultipliers (outputMap)
open UnifiedTheory.Audit.KFCausalCoherentMomentumOutputReduction (reducedOutput)
open UnifiedTheory.Audit.KFCausalPhysicalField (physicalField)
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare (fieldSquare)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition (composition_graph)

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "S" => state ε a α β hε ha hα hβ hw C p b
local notation "Shalf" => state ε (a/2) α β hε (by positivity) hα hβ hw C p b
local notation "G" => shiftedOutput ε a α β hε ha hα hβ hw C p b h hb
local notation "Ghalf" => shiftedOutput ε (a/2) α β hε (by positivity) hα hβ hw C p b h hb

def pureOutput : Hilbert := outputMap ε a h hε ha p S Shalf

include hh in
theorem pureOutput_graph : (S,pureOutput ε a α β hε ha hα hβ hw C p b h) ∈
    (pureMomentum ε hε h).graph :=
  KFCausalOriginalPureClockOutput.profile_graph ε a hε ha C p α β hα hβ hw b h hh

def factorOutput (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8) : Hilbert :=
  let f := KFCausalClockFloorSourcedCommonDomain.factorOutput
    ε a α β hε ha hα hβ hw C p b h hb v l i
  let g := KFCausalClockFloorSourcedCommonDomain.factorOutput
    ε (a/2) α β hε (by positivity) hα hβ hw C p b h hb v l i
  if i.val < 5 then outputMap ε a h hε ha p f g
  else reducedOutput ε a h hε ha hb p f g

include hh in
theorem factorOutput_graph (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8) :
    (pureOutput ε a α β hε ha hα hβ hw C p b h,
      factorOutput ε a α β hε ha hα hβ hw C p b h hb v l i) ∈
        (energyFactor ε hε h v l i).graph := by
  have hT := KFCausalSourcedMomentumOutput.reduced_graph
    ε a α β hε ha hα hβ hw C p b h hh hb _
    (pureOutput_graph ε a α β hε ha hα hβ hw C p b h hh)
  have hL := KFCausalBoundedClockMatterGraphs.reducedOutput_field_graph ε a h hε ha hb l p
    G (linearOutput ε a α β hε ha hα hβ hw C p b h hb l)
    Ghalf (linearOutput ε (a/2) α β hε (by positivity) hα hβ hw C p b h hb l)
    ((physicalField l).mem_graph ⟨G,KFCausalClockFloorSourcedCommonDomain.shiftedOutput_physicalField_domain
      ε a α β hε ha hα hβ hw C p b h hb l⟩)
    ((physicalField l).mem_graph ⟨Ghalf,KFCausalClockFloorSourcedCommonDomain.shiftedOutput_physicalField_domain
      ε (a/2) α β hε (by positivity) hα hβ hw C p b h hb l⟩)
  have hQ := KFCausalBoundedClockMatterGraphs.reducedOutput_square_graph ε a h hε ha hb l p
    G (quadraticOutput ε a α β hε ha hα hβ hw C p b h hb l)
    Ghalf (quadraticOutput ε (a/2) α β hε (by positivity) hα hβ hw C p b h hb l)
    ((fieldSquare l).mem_graph ⟨G,KFCausalClockFloorSourcedCommonDomain.shiftedOutput_fieldSquare_domain
      ε a α β hε ha hα hβ hw C p b h hb l⟩)
    ((fieldSquare l).mem_graph ⟨Ghalf,KFCausalClockFloorSourcedCommonDomain.shiftedOutput_fieldSquare_domain
      ε (a/2) α β hε (by positivity) hα hβ hw C p b h hb l⟩)
  fin_cases i
  · exact KFCausalPureClockOutputMultipliers.outputMap_half_graph ε a h hε ha p _ _ _ _
      (KFCausalClockFloorSourcedClockMomentum.clockOutput_graph ε a α β hε ha hα hβ hw C p b)
      (KFCausalClockFloorSourcedClockMomentum.clockOutput_graph ε (a/2) α β hε (by positivity) hα hβ hw C p b)
  · exact KFCausalPureClockOutputMultipliers.outputMap_kinetic_graph ε a h hε ha hh (v 0) p _ _ _ _
      (KFCausalClockFloorSourcedClockMomentum.state_clockMomentum_graph ε a α β hε ha hα hβ hw C p b h (v 0))
      (KFCausalClockFloorSourcedClockMomentum.state_clockMomentum_graph ε (a/2) α β hε (by positivity) hα hβ hw C p b h (v 0))
  · exact KFCausalPureClockOutputMultipliers.outputMap_kinetic_graph ε a h hε ha hh (v 1) p _ _ _ _
      (KFCausalClockFloorSourcedClockMomentum.state_clockMomentum_graph ε a α β hε ha hα hβ hw C p b h (v 1))
      (KFCausalClockFloorSourcedClockMomentum.state_clockMomentum_graph ε (a/2) α β hε (by positivity) hα hβ hw C p b h (v 1))
  · exact KFCausalPureClockOutputMultipliers.outputMap_kinetic_graph ε a h hε ha hh (v 2) p _ _ _ _
      (KFCausalClockFloorSourcedClockMomentum.state_clockMomentum_graph ε a α β hε ha hα hβ hw C p b h (v 2))
      (KFCausalClockFloorSourcedClockMomentum.state_clockMomentum_graph ε (a/2) α β hε (by positivity) hα hβ hw C p b h (v 2))
  · exact KFCausalPureClockOutputMultipliers.outputMap_kinetic_graph ε a h hε ha hh (v 3) p _ _ _ _
      (KFCausalClockFloorSourcedClockMomentum.state_clockMomentum_graph ε a α β hε ha hα hβ hw C p b h (v 3))
      (KFCausalClockFloorSourcedClockMomentum.state_clockMomentum_graph ε (a/2) α β hε (by positivity) hα hβ hw C p b h (v 3))
  · exact (composition_graph _ _ _ _).mpr ⟨_,hT,hL⟩
  · exact (composition_graph _ _ _ _).mpr ⟨_,hT,hQ⟩
  · exact hT

include hh hb in
theorem pureOutput_commonEnergyDomain (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    pureOutput ε a α β hε ha hα hβ hw C p b h ∈ commonEnergyDomain ε hε h v l :=
  (commonEnergyDomain_iff ε hε h v l _).mpr (fun i => LinearPMap.mem_domain_of_mem_graph
    (factorOutput_graph ε a α β hε ha hα hβ hw C p b h hh hb v l i))

#print axioms pureOutput_graph
#print axioms factorOutput_graph
#print axioms pureOutput_commonEnergyDomain
end
end UnifiedTheory.Audit.KFCausalSourcedMomentumFactors
