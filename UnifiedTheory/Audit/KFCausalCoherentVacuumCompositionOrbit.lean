/- Continuous actual B T and T B outputs for every coherent seed. The
longitudinal output expansion is proved from Gaussian representatives;
the T B graph is then obtained from the existing actual commutator. -/
import UnifiedTheory.Audit.KFCausalGaussianLongitudinalOutput
import UnifiedTheory.Audit.KFCausalCoherentVacuumWeakForce
import UnifiedTheory.Audit.KFCausalCoherentShearOrbit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCoherentVacuumCompositionOrbit
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral (shiftedOutput state_ordered_graph)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary (amplitudeConstant clockFrequency sourceCoefficients)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalShiftedClockMomentOperator
open UnifiedTheory.Audit.KFCausalCoherentShearCompositions (shiftedShearOutput shiftedOutput_shear_graph)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentShiftedOrbit (shiftedOutput_orbit_continuous)
open UnifiedTheory.Audit.KFCausalCoherentShearOrbit (shiftedShearOutput_orbit_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockCommonDomain (clockInverse)
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum (longitudinalMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumCommutator (pureCorrection shearCorrection)
open UnifiedTheory.Audit.KFCausalClockFloorOrderedMomentumCommutator (correction)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "G" => shiftedOutput ε a h hε ha hh hb
local notation "JG" => shiftedShearOutput ε a h hε ha hh hb
local notation "Z" => inverseOperator ε (-h/2) hε (shift_bound ε h hb)
local notation "B" => pureMomentum ε hε h
local notation "T" => orderedExponential ε hε h

def longitudinalOutput (k : Joint 2 4) : Hilbert := Z (JG k)+
  (-Complex.I*(h:ℂ)) • (((clockFrequency k:ℂ)*Complex.I-1) • Z (G k)-
    (2*(a:ℂ)) • shiftedMoment ε a h hε ha hh hb k)

theorem longitudinalOutput_eq (k : Joint 2 4) :
    longitudinalOutput ε a h hε ha hh hb k = amplitudeConstant h k •
      KFCausalShiftedGaussianLongitudinalDomain.output ε a (groundWidth h) (neutralWidth h)
        (clockFrequency k) (-h/2) (sourceCoefficients h k) hε ha
        (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
        (shift_bound ε h hb) h := by
  rw [KFCausalGaussianLongitudinalOutput.output_expansion]
  unfold longitudinalOutput shiftedShearOutput shiftedMoment shiftedOutput
  simp only [map_smul,smul_add,smul_sub,smul_smul,mul_comm,mul_left_comm,mul_assoc]

theorem longitudinalOutput_graph (k : Joint 2 4) :
    (G k,longitudinalOutput ε a h hε ha hh hb k) ∈ (longitudinalMomentum ε hε h).graph := by
  rw [longitudinalOutput_eq]
  exact (longitudinalMomentum ε hε h).graph.smul_mem (amplitudeConstant h k)
    (KFCausalShiftedGaussianLongitudinalDomain.gaussianState_graph ε a (groundWidth h) (neutralWidth h)
      (clockFrequency k) (-h/2) (sourceCoefficients h k) hε ha
      (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
      (shift_bound ε h hb) h hh)

theorem longitudinalOutput_orbit_continuous (k : Joint 2 4) :
    Continuous (fun θ => longitudinalOutput ε a h hε ha hh hb (parameter θ k)) := by
  unfold longitudinalOutput
  simp_rw [KFCausalClockFloorCoherentParameters.clockFrequency_parameter]
  exact ((Z).continuous.comp (shiftedShearOutput_orbit_continuous ε a h hε ha hh hb k)).add
    (((((Z).continuous.comp (shiftedOutput_orbit_continuous ε a h hε ha hh hb k)).const_smul
      ((clockFrequency k:ℂ)*Complex.I-1)).sub
        ((shiftedMoment_orbit_continuous ε a h hε ha hh hb k).const_smul (2*(a:ℂ)))).const_smul
          (-Complex.I*(h:ℂ)))

def pureOutput (k : Joint 2 4) : Hilbert :=
  longitudinalOutput ε a h hε ha hh hb k-clockInverse ε hε (JG k)

theorem pureOutput_graph (k : Joint 2 4) : (G k,pureOutput ε a h hε ha hh hb k) ∈ (B).graph :=
  KFCausalClockFloorPureClockJointDomain.graph_decomposition ε hε h hh _ _ _
    (longitudinalOutput_graph ε a h hε ha hh hb k) (shiftedOutput_shear_graph ε a h hε ha hh hb k)

theorem pureOutput_orbit_continuous (k : Joint 2 4) :
    Continuous (fun θ => pureOutput ε a h hε ha hh hb (parameter θ k)) :=
  (longitudinalOutput_orbit_continuous ε a h hε ha hh hb k).sub
    ((clockInverse ε hε).continuous.comp (shiftedShearOutput_orbit_continuous ε a h hε ha hh hb k))

def orderedMomentumOutput (k : Joint 2 4) : Hilbert :=
  pureOutput ε a h hε ha hh hb k-pureCorrection ε hε h hb (G k) (JG k)

theorem orderedMomentumOutput_orbit_continuous (k : Joint 2 4) :
    Continuous (fun θ => orderedMomentumOutput ε a h hε ha hh hb (parameter θ k)) :=
  (pureOutput_orbit_continuous ε a h hε ha hh hb k).sub
    (((correction ε hε h hb).continuous.comp (shiftedOutput_orbit_continuous ε a h hε ha hh hb k)).sub
      ((shearCorrection ε hε h hb).continuous.comp (shiftedShearOutput_orbit_continuous ε a h hε ha hh hb k)))

theorem orderedMomentumOutput_graph (k : Joint 2 4) (b : Hilbert)
    (hB : (state ε a h hε ha hh k,b) ∈ (B).graph) :
    (b,orderedMomentumOutput ε a h hε ha hh hb k) ∈ (T).graph := by
  obtain ⟨b',tb,bg,jg,hb',ht,hbg,hjg,he⟩ :=
    KFCausalClockFloorPureClockVacuumCommutator.core_compositions ε hε h hb hh _ _
      (KFCausalCoherentVacuumCommutator.state_regular ε a h hε ha hh hb k)
  have eb : b' = b := (B).mem_graph_snd_inj' hb' hB rfl
  have eg : bg = pureOutput ε a h hε ha hh hb k :=
    (B).mem_graph_snd_inj' hbg (pureOutput_graph ε a h hε ha hh hb k) rfl
  have ej : jg = JG k := (shearMomentum h).mem_graph_snd_inj' hjg
    (shiftedOutput_shear_graph ε a h hε ha hh hb k) rfl
  rw [eg,ej] at he
  have et : tb = orderedMomentumOutput ε a h hε ha hh hb k := by
    unfold orderedMomentumOutput
    rw [← he]
    abel
  simpa only [eb,et] using ht

#print axioms longitudinalOutput_eq
#print axioms longitudinalOutput_graph
#print axioms longitudinalOutput_orbit_continuous
#print axioms pureOutput_graph
#print axioms pureOutput_orbit_continuous
#print axioms orderedMomentumOutput_orbit_continuous
#print axioms orderedMomentumOutput_graph
end
end UnifiedTheory.Audit.KFCausalCoherentVacuumCompositionOrbit
