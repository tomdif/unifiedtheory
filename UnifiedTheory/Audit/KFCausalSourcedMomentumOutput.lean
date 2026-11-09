/- Derive T B for arbitrary sourced Gaussians, retaining the actual
commutator. The shear terms cancel algebraically in this composition.
The resulting output has both physical field domains. -/
import UnifiedTheory.Audit.KFCausalSourcedPureClockCommutator
import UnifiedTheory.Audit.KFCausalCoherentMomentumOutputReduction
import UnifiedTheory.Audit.KFCausalBoundedClockMatterGraphs
import UnifiedTheory.Audit.KFCausalClockFloorSourcedCommonDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalSourcedMomentumOutput
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedClockMomentum (state)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedSpectral (shiftedOutput)
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum (longitudinalMomentum)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockCommonDomain (clockInverse)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumCommutator (pureCorrection shearCorrection)
open UnifiedTheory.Audit.KFCausalClockFloorOrderedMomentumCommutator (correction)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalShiftedClockMomentOperator (inverseOperator momentOperator)
open UnifiedTheory.Audit.KFCausalCoherentMomentumOutputReduction (inverseOperator_eq reducedOutput)
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare (fieldSquare)
open UnifiedTheory.Audit.KFCausalPhysicalField (physicalField fieldSquare_domain_le_physicalField)

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ)
  (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "S" => state ε a α β hε ha hα hβ hw C p b
local notation "G" => shiftedOutput ε a α β hε ha hα hβ hw C p b h hb
local notation "Ghalf" => shiftedOutput ε (a/2) α β hε (by positivity) hα hβ hw C p b h hb
local notation "Z" => inverseOperator ε (-h/2) hε (shift_bound ε h hb)
local notation "M" => momentOperator ε a (-h/2) ha

def shearOutput : Hilbert := C • KFCausalShiftedGaussianShearDomain.shearOutput
  ε a α β p (-h/2) b hε ha hα hβ hw (shift_bound ε h hb) h

def longitudinalOutput : Hilbert := C • KFCausalShiftedGaussianLongitudinalDomain.output
  ε a α β p (-h/2) b hε ha hα hβ hw (shift_bound ε h hb) h

local notation "JG" => shearOutput ε a α β hε ha hα hβ hw C p b h hb
local notation "LG" => longitudinalOutput ε a α β hε ha hα hβ hw C p b h hb
local notation "TB" => reducedOutput ε a h hε ha hb p G Ghalf

include hh in
theorem shear_graph : (G,JG) ∈ (shearMomentum h).graph :=
  (shearMomentum h).graph.smul_mem C
    (KFCausalShiftedGaussianShearDomain.gaussianState_shear_graph
      ε a α β p (-h/2) b hε ha hα hβ hw (shift_bound ε h hb) h hh)

include hh in
theorem longitudinal_graph : (G,LG) ∈ (longitudinalMomentum ε hε h).graph :=
  (longitudinalMomentum ε hε h).graph.smul_mem C
    (KFCausalShiftedGaussianLongitudinalDomain.gaussianState_graph
      ε a α β p (-h/2) b hε ha hα hβ hw (shift_bound ε h hb) h hh)

theorem longitudinal_expansion :
    LG = Z JG+(-Complex.I*(h:ℂ)) • (((p:ℂ)*Complex.I-1) • Z G-(2*(a:ℂ)) • M Ghalf) := by
  unfold longitudinalOutput
  rw [KFCausalGaussianLongitudinalOutput.output_expansion]
  unfold shearOutput shiftedOutput
  simp only [map_smul,smul_add,smul_sub,smul_smul,mul_comm,mul_left_comm,mul_assoc]

theorem reduced_eq : LG-clockInverse ε hε JG-pureCorrection ε hε h hb G JG = TB := by
  rw [longitudinal_expansion]
  unfold reducedOutput pureCorrection
  simp only [inverseOperator_eq ε h hε hb,clockInverse,shearCorrection,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.sub_apply,smul_sub]
  abel

include hh in
theorem reduced_graph (bf : Hilbert) (hB : (S,bf) ∈ (pureMomentum ε hε h).graph) :
    (bf,TB) ∈ (orderedExponential ε hε h).graph := by
  obtain ⟨bf',tb,bg,jg,hbf',ht,hbg,hjg,he⟩ :=
    KFCausalSourcedPureClockCommutator.actual_compositions ε a α β hε ha hα hβ hw C p b h hh hb
  have hbg' : (G,LG-clockInverse ε hε JG) ∈ (pureMomentum ε hε h).graph :=
    KFCausalClockFloorPureClockJointDomain.graph_decomposition ε hε h hh _ _ _
      (longitudinal_graph ε a α β hε ha hα hβ hw C p b h hh hb)
      (shear_graph ε a α β hε ha hα hβ hw C p b h hh hb)
  have eb := (pureMomentum ε hε h).mem_graph_snd_inj' hbf' hB rfl
  have eg := (pureMomentum ε hε h).mem_graph_snd_inj' hbg hbg' rfl
  have ej := (shearMomentum h).mem_graph_snd_inj' hjg
    (shear_graph ε a α β hε ha hα hβ hw C p b h hh hb) rfl
  dsimp only at eb eg ej
  rw [eg,ej] at he
  have et : tb = TB := by
    rw [← reduced_eq ε a α β hε ha hα hβ hw C p b h hb,← he]
    abel
  simpa only [eb,et] using ht

theorem reduced_square_domain (l : Transverse →L[ℝ] ℝ) : TB ∈ (fieldSquare l).domain := by
  have hg := KFCausalClockFloorSourcedCommonDomain.shiftedOutput_fieldSquare_domain
    ε a α β hε ha hα hβ hw C p b h hb l
  have hg' := KFCausalClockFloorSourcedCommonDomain.shiftedOutput_fieldSquare_domain
    ε (a/2) α β hε (by positivity) hα hβ hw C p b h hb l
  exact LinearPMap.mem_domain_of_mem_graph
    (KFCausalBoundedClockMatterGraphs.reducedOutput_square_graph ε a h hε ha hb l p _ _ _ _
      ((fieldSquare l).mem_graph ⟨G,hg⟩) ((fieldSquare l).mem_graph ⟨Ghalf,hg'⟩))

theorem reduced_field_domain (l : Transverse →L[ℝ] ℝ) : TB ∈ (physicalField l).domain :=
  fieldSquare_domain_le_physicalField l
    (reduced_square_domain ε a α β hε ha hα hβ hw C p b h hb l)

#print axioms shear_graph
#print axioms longitudinal_graph
#print axioms longitudinal_expansion
#print axioms reduced_eq
#print axioms reduced_graph
#print axioms reduced_square_domain
#print axioms reduced_field_domain
end
end UnifiedTheory.Audit.KFCausalSourcedMomentumOutput
