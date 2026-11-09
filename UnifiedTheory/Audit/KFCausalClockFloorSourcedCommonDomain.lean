/- Every arbitrary complex-sourced Gaussian with the specified clock
factor lies in all eight natural energy-factor domains. The spectral
output is fed into the actual ordered matter operators. -/
import UnifiedTheory.Audit.KFCausalClockFloorSourcedSpectral
import UnifiedTheory.Audit.KFCausalClockFloorCoherentMatter
import UnifiedTheory.Audit.KFCausalClockFloorCommonDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorSourcedCommonDomain
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedClockMomentum
open UnifiedTheory.Audit.KFCausalClockFloorSourcedSpectral
open UnifiedTheory.Audit.KFCausalClockFloorCoherentMatter (gaussianState_fieldSquare_domain)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMatter (matterFactor)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain
open UnifiedTheory.Audit.KFCausalPhysicalField
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) (h : ℝ) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "S" => state ε a α β hε ha hα hβ hw C p b
local notation "Y" => shiftedOutput ε a α β hε ha hα hβ hw C p b h hb

theorem shiftedOutput_fieldSquare_domain (l : Transverse →L[ℝ] ℝ) : Y ∈ (fieldSquare l).domain :=
  (fieldSquare l).domain.smul_mem C
    (gaussianState_fieldSquare_domain ε a α β p b (-h/2) hε ha hα hβ hw (shift_bound ε h hb) l)

theorem shiftedOutput_physicalField_domain (l : Transverse →L[ℝ] ℝ) : Y ∈ (physicalField l).domain :=
  fieldSquare_domain_le_physicalField l
    (shiftedOutput_fieldSquare_domain ε a α β hε ha hα hβ hw C p b h hb l)

def linearOutput (l : Transverse →L[ℝ] ℝ) : Hilbert :=
  physicalField l ⟨Y,shiftedOutput_physicalField_domain ε a α β hε ha hα hβ hw C p b h hb l⟩

def quadraticOutput (l : Transverse →L[ℝ] ℝ) : Hilbert :=
  fieldSquare l ⟨Y,shiftedOutput_fieldSquare_domain ε a α β hε ha hα hβ hw C p b h hb l⟩

theorem linearOutput_graph (l : Transverse →L[ℝ] ℝ) :
    (S,linearOutput ε a α β hε ha hα hβ hw C p b h hb l) ∈
      (matterFactor ε hε h (physicalField l)).graph :=
  (composition_graph _ _ _ _).mpr ⟨_,state_ordered_graph ε a α β hε ha hα hβ hw C p b h hb,
    (physicalField l).mem_graph
      ⟨Y,shiftedOutput_physicalField_domain ε a α β hε ha hα hβ hw C p b h hb l⟩⟩

theorem quadraticOutput_graph (l : Transverse →L[ℝ] ℝ) :
    (S,quadraticOutput ε a α β hε ha hα hβ hw C p b h hb l) ∈
      (matterFactor ε hε h (fieldSquare l)).graph :=
  (composition_graph _ _ _ _).mpr ⟨_,state_ordered_graph ε a α β hε ha hα hβ hw C p b h hb,
    (fieldSquare l).mem_graph
      ⟨Y,shiftedOutput_fieldSquare_domain ε a α β hε ha hα hβ hw C p b h hb l⟩⟩

include hb in
theorem state_commonEnergyDomain (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    S ∈ commonEnergyDomain ε hε h v l := by
  apply (commonEnergyDomain_iff ε hε h v l _).mpr
  intro i
  fin_cases i
  · exact state_clockHalf_domain ε a α β hε ha hα hβ hw C p b
  · exact state_clockMomentum_domain ε a α β hε ha hα hβ hw C p b h (v 0)
  · exact state_clockMomentum_domain ε a α β hε ha hα hβ hw C p b h (v 1)
  · exact state_clockMomentum_domain ε a α β hε ha hα hβ hw C p b h (v 2)
  · exact state_clockMomentum_domain ε a α β hε ha hα hβ hw C p b h (v 3)
  · exact LinearPMap.mem_domain_of_mem_graph (linearOutput_graph ε a α β hε ha hα hβ hw C p b h hb l)
  · exact LinearPMap.mem_domain_of_mem_graph (quadraticOutput_graph ε a α β hε ha hα hβ hw C p b h hb l)
  · exact state_ordered_domain ε a α β hε ha hα hβ hw C p b h hb

def factorOutput (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) : Fin 8 → Hilbert :=
  ![clockOutput ε a α β hε ha hα hβ hw C p b,
    momentumOutput ε a α β hε ha hα hβ hw C p b h (v 0),
    momentumOutput ε a α β hε ha hα hβ hw C p b h (v 1),
    momentumOutput ε a α β hε ha hα hβ hw C p b h (v 2),
    momentumOutput ε a α β hε ha hα hβ hw C p b h (v 3),
    linearOutput ε a α β hε ha hα hβ hw C p b h hb l,
    quadraticOutput ε a α β hε ha hα hβ hw C p b h hb l,Y]

theorem factorOutput_graph (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8) :
    (S,factorOutput ε a α β hε ha hα hβ hw C p b h hb v l i) ∈ (energyFactor ε hε h v l i).graph := by
  fin_cases i
  · exact clockOutput_graph ε a α β hε ha hα hβ hw C p b
  · exact state_clockMomentum_graph ε a α β hε ha hα hβ hw C p b h (v 0)
  · exact state_clockMomentum_graph ε a α β hε ha hα hβ hw C p b h (v 1)
  · exact state_clockMomentum_graph ε a α β hε ha hα hβ hw C p b h (v 2)
  · exact state_clockMomentum_graph ε a α β hε ha hα hβ hw C p b h (v 3)
  · exact linearOutput_graph ε a α β hε ha hα hβ hw C p b h hb l
  · exact quadraticOutput_graph ε a α β hε ha hα hβ hw C p b h hb l
  · exact state_ordered_graph ε a α β hε ha hα hβ hw C p b h hb

#print axioms shiftedOutput_fieldSquare_domain
#print axioms shiftedOutput_physicalField_domain
#print axioms linearOutput_graph
#print axioms quadraticOutput_graph
#print axioms state_commonEnergyDomain
#print axioms factorOutput_graph

end
end UnifiedTheory.Audit.KFCausalClockFloorSourcedCommonDomain
