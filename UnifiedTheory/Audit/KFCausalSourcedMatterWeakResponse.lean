/- Construct the actual two matter/momentum compositions for arbitrary
sourced Gaussians. The field-weighted shear domains are derived, not
assumed. This is a fixed-state weak identity, not an evolution theorem. -/
import UnifiedTheory.Audit.KFCausalSourcedMomentumOutput
import UnifiedTheory.Audit.KFCausalCoherentWeightedShearDomains
import UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalSourcedMatterWeakResponse
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedClockMomentum (state)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedSpectral (shiftedOutput state_ordered_graph)
open UnifiedTheory.Audit.KFCausalSourcedMomentumOutput
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare (fieldSquare)
open UnifiedTheory.Audit.KFCausalPhysicalField (physicalField fieldSquare_domain_le_physicalField)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower weighted_weak_response)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockCommonDomain (clockInverse)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumCommutator (pureCorrection)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumResponse (response)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMatter (matterFactor)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition (composition_graph)
open UnifiedTheory.Audit.KFCausalCoherentMomentumOutputReduction (reducedOutput)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)

theorem fieldPower_domain_of_square (l : Transverse →L[ℝ] ℝ) (i : Fin 2)
    (f : Hilbert) (hf : f ∈ (fieldSquare l).domain) : f ∈ (fieldPower l i).domain := by
  fin_cases i
  · exact fieldSquare_domain_le_physicalField l hf
  · exact hf

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ)
  (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (l : Transverse →L[ℝ] ℝ) (i : Fin 2)
local notation "S" => state ε a α β hε ha hα hβ hw C p b
local notation "G" => shiftedOutput ε a α β hε ha hα hβ hw C p b h hb
local notation "Ghalf" => shiftedOutput ε (a/2) α β hε (by positivity) hα hβ hw C p b h hb
local notation "JG" => shearOutput ε a α β hε ha hα hβ hw C p b h hb
local notation "LG" => longitudinalOutput ε a α β hε ha hα hβ hw C p b h hb
local notation "TB" => reducedOutput ε a h hε ha hb p G Ghalf
local notation "F" => fieldPower l i
local notation "B" => pureMomentum ε hε h

theorem all_field_domains : G ∈ (F).domain ∧ TB ∈ (F).domain ∧ JG ∈ (F).domain := by
  refine ⟨fieldPower_domain_of_square l i G ?_,
    fieldPower_domain_of_square l i TB (reduced_square_domain ε a α β hε ha hα hβ hw C p b h hb l),
    fieldPower_domain_of_square l i JG ?_⟩
  · exact KFCausalClockFloorSourcedCommonDomain.shiftedOutput_fieldSquare_domain
      ε a α β hε ha hα hβ hw C p b h hb l
  · exact (fieldSquare l).domain.smul_mem C
      (KFCausalCoherentWeightedShearDomains.shearOutput_square_domain
        ε a α β p (-h/2) b hε ha hα hβ hw (shift_bound ε h hb) h l)

include hh in
theorem actual_matter_response :
    ∃ bf u v j : Hilbert,
      (S,bf) ∈ (B).graph ∧ (S,u) ∈ (matterFactor ε hε h (F)).graph ∧
      (bf,v) ∈ (matterFactor ε hε h (F)).graph ∧ (JG,j) ∈ (F).graph ∧
      (-2/h)*(inner ℂ u v).im = response ε hε h hb u j := by
  have hd := all_field_domains ε a α β hε ha hα hβ hw C p b h hb l i
  have hB := (KFCausalSourcedPureClockCommutator.pure_domains
    ε a α β hε ha hα hβ hw C p b h hh hb).1
  let bf : Hilbert := (B) ⟨S,hB⟩
  let u : Hilbert := (F) ⟨G,hd.1⟩
  let v : Hilbert := (F) ⟨TB,hd.2.1⟩
  let j : Hilbert := (F) ⟨JG,hd.2.2⟩
  have hbf : (S,bf) ∈ (B).graph := (B).mem_graph ⟨S,hB⟩
  have hu : (G,u) ∈ (F).graph := (F).mem_graph ⟨G,hd.1⟩
  have hv : (TB,v) ∈ (F).graph := (F).mem_graph ⟨TB,hd.2.1⟩
  have hj : (JG,j) ∈ (F).graph := (F).mem_graph ⟨JG,hd.2.2⟩
  refine ⟨bf,u,v,j,hbf,(composition_graph _ _ _ _).mpr
    ⟨G,state_ordered_graph ε a α β hε ha hα hβ hw C p b h hb,hu⟩,
    (composition_graph _ _ _ _).mpr
      ⟨TB,reduced_graph ε a α β hε ha hα hβ hw C p b h hh hb bf hbf,hv⟩,hj,?_⟩
  have hbg : (G,LG-clockInverse ε hε JG) ∈ (B).graph :=
    KFCausalClockFloorPureClockJointDomain.graph_decomposition ε hε h hh _ _ _
      (longitudinal_graph ε a α β hε ha hα hβ hw C p b h hh hb)
      (shear_graph ε a α β hε ha hα hβ hw C p b h hh hb)
  apply weighted_weak_response ε h hε hh hb l i G _ TB JG u v j hbg _ hu hv hj
  rw [← reduced_eq ε a α β hε ha hα hβ hw C p b h hb]
  abel

#print axioms fieldPower_domain_of_square
#print axioms all_field_domains
#print axioms actual_matter_response
end
end UnifiedTheory.Audit.KFCausalSourcedMatterWeakResponse
