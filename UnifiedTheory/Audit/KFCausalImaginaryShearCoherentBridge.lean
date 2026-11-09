/- Identify the interpolation endpoint with the existing actual T and JT
outputs of finite coherent superpositions. The comparison is at each
charge angle; no cancellation at the other endpoint is assumed. -/
import UnifiedTheory.Audit.KFCausalImaginaryShearSuperposition
import UnifiedTheory.Audit.KFCausalCoherentShearCompositions

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalImaginaryShearCoherentBridge
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (Interval)
open UnifiedTheory.Audit.KFCausalImaginaryShearSuperposition
open UnifiedTheory.Audit.KFCausalClockShearPositiveVariation (expectation)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral (shiftedOutput state_ordered_graph)
open UnifiedTheory.Audit.KFCausalCoherentShearCompositions (shiftedShearOutput shiftedOutput_shear_graph)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary (amplitudeConstant clockFrequency sourceCoefficients)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
variable (hb : |h| ≤ 2*Real.pi*ε/3)

def coherentSeed (k : Joint 2 4) : Seed where
  a := a
  p := clockFrequency k
  α := groundWidth h
  β := neutralWidth h
  b := sourceCoefficients h k
  ha := ha
  hα := groundWidth_positive h hh
  hβ := neutralWidth_positive h hh
  hw := neutralWidth_bound h

variable {n : ℕ} (k : Fin n → Joint 2 4) (z : Fin n → ℂ)

def input (t : ℝ) : Hilbert := sumInput ε h hε hb (fun i => coherentSeed a h ha hh (k i))
  (fun i => z i*amplitudeConstant h (k i)) t
def shear (t : ℝ) : Hilbert := sumShear ε h hε hb (fun i => coherentSeed a h ha hh (k i))
  (fun i => z i*amplitudeConstant h (k i)) t

local notation "F" => input ε a h hε ha hh hb k z
local notation "J" => shear ε a h hε ha hh hb k z
local notation "R" => KFCausalClockFloorShearWeight.root ε hε h hb hh

theorem input_one : F 1 = ∑ i, z i • shiftedOutput ε a h hε ha hh hb (k i) := by
  unfold input
  rw [KFCausalImaginaryShearSuperposition.input_one]
  apply Finset.sum_congr rfl
  intro i _
  simp only [coherentSeed,shiftedOutput,smul_smul]

theorem shear_one : J 1 = ∑ i, z i • shiftedShearOutput ε a h hε ha hh hb (k i) := by
  have hg := input_graph ε h hε hb (fun i => coherentSeed a h ha hh (k i))
    (fun i => z i*amplitudeConstant h (k i)) hh ⟨1,by constructor <;> norm_num⟩
  change (F 1,J 1) ∈ (shearMomentum h).graph at hg
  have hs := graph_sum h z (fun i => shiftedOutput ε a h hε ha hh hb (k i))
    (fun i => shiftedShearOutput ε a h hε ha hh hb (k i))
    (fun i => shiftedOutput_shear_graph ε a h hε ha hh hb (k i))
  exact (shearMomentum h).mem_graph_snd_inj hg hs (input_one ε a h hε ha hh hb k z)

theorem endpoint_ordered_graph :
    (∑ i, z i • KFCausalClockFloorCoherentStates.state ε a h hε ha hh (k i),F 1) ∈
      (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h).graph := by
  rw [input_one]
  have hs := (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h).graph.sum_mem
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h).graph.smul_mem (z i)
        (state_ordered_graph ε a h hε ha hh hb (k i)))
  simpa only [Prod.smul_mk,← prod_mk_sum] using hs

theorem weighted_monotone : MonotoneOn (expectation R F J) (Icc (0:ℝ) 1) :=
  physical_weight_monotone ε h hε hb (fun i => coherentSeed a h ha hh (k i))
    (fun i => z i*amplitudeConstant h (k i)) hh

theorem weighted_endpoint_comparison : expectation R F J 0 ≤
    (inner ℂ (R (∑ i, z i • shiftedOutput ε a h hε ha hh hb (k i)))
      (R (∑ i, z i • shiftedShearOutput ε a h hε ha hh hb (k i)))).re := by
  have he := physical_weight_endpoints ε h hε hb (fun i => coherentSeed a h ha hh (k i))
    (fun i => z i*amplitudeConstant h (k i)) hh
  change expectation R F J 0 ≤ expectation R F J 1 at he
  simpa only [expectation,input_one ε a h hε ha hh hb k z,shear_one ε a h hε ha hh hb k z] using he

theorem charge_angle_comparison (θ : ℝ) :
    expectation R
      (input ε a h hε ha hh hb (fun i => KFCausalChargeModulationFlow.parameter θ (k i)) z)
      (shear ε a h hε ha hh hb (fun i => KFCausalChargeModulationFlow.parameter θ (k i)) z) 0 ≤
    (inner ℂ (R (∑ i, z i • shiftedOutput ε a h hε ha hh hb (KFCausalChargeModulationFlow.parameter θ (k i))))
      (R (∑ i, z i • shiftedShearOutput ε a h hε ha hh hb (KFCausalChargeModulationFlow.parameter θ (k i))))).re :=
  weighted_endpoint_comparison ε a h hε ha hh hb (fun i => KFCausalChargeModulationFlow.parameter θ (k i)) z

#print axioms input_one
#print axioms shear_one
#print axioms endpoint_ordered_graph
#print axioms weighted_monotone
#print axioms weighted_endpoint_comparison
#print axioms charge_angle_comparison
end
end UnifiedTheory.Audit.KFCausalImaginaryShearCoherentBridge
