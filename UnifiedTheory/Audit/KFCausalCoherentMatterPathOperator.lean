/- The constructed interpolation is a linear operator on the actual
algebraic coherent span, independent of its finite presentation. These
are algebraic operators; no Hilbert-norm bound or closed extension is inferred. -/
import UnifiedTheory.Audit.KFCausalCoherentStateBasis
import UnifiedTheory.Audit.KFCausalCoherentMatterInterpolation
import UnifiedTheory.Audit.KFCausalImaginaryShearInitialEndpoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalCoherentMatterPathOperator
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan action_coherentSpan)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state action_state)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalCoherentStateBasis (extend extend_of_representation)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary (amplitudeConstant clockFrequency sourceCoefficients)
open UnifiedTheory.Audit.KFCausalImaginaryShearCoherentBridge (coherentSeed)
open UnifiedTheory.Audit.KFCausalPolynomialImaginaryShearCurve (fieldWeight slopeWeight)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalCoherentSpanVacuumSign (finite_representation)
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (Interval)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
local notation "S" => coherentSpan ε a h hε ha hh

def rotate (θ : ℝ) : S →ₗ[ℂ] S where
  toFun f := ⟨action h hh θ f,action_coherentSpan ε a h hε ha hh θ f f.property⟩
  map_add' f g := Subtype.ext (map_add (action h hh θ) (f:Hilbert) (g:Hilbert))
  map_smul' c f := Subtype.ext (map_smul (action h hh θ) c (f:Hilbert))

theorem rotate_representation (f : S) {n : ℕ} (k : Fin n → Joint 2 4) (z : Fin n → ℂ)
    (hf : (f:Hilbert) = ∑ r, z r • state ε a h hε ha hh (k r)) (θ : ℝ) :
    (rotate ε a h hε ha hh θ f:Hilbert) = ∑ r, z r • state ε a h hε ha hh (parameter θ (k r)) := by
  change action h hh θ (f:Hilbert) = _
  rw [hf,map_sum]
  simp only [map_smul,action_state]

variable (hb : |h| ≤ 2*Real.pi*ε/3)

def input (t : ℝ) : S →ₗ[ℂ] Hilbert := extend ε a h hε ha hh (fun k => amplitudeConstant h k •
  KFCausalActualImaginaryShearCurve.input ε a (clockFrequency k) h (groundWidth h) (neutralWidth h)
    hε ha (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hb (sourceCoefficients h k) t)

def field (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (t : ℝ) : S →ₗ[ℂ] Hilbert :=
  extend ε a h hε ha hh (fun k => amplitudeConstant h k •
    KFCausalFieldShearPathGraphs.state ε h hε hb (coherentSeed a h ha hh k) (fieldWeight l i) t)
def shear (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (t : ℝ) : S →ₗ[ℂ] Hilbert :=
  extend ε a h hε ha hh (fun k => amplitudeConstant h k •
    KFCausalFieldShearPathGraphs.fieldShear ε h hε hb (coherentSeed a h ha hh k) l i t)
def derivativeField (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (t : ℝ) : S →ₗ[ℂ] Hilbert :=
  extend ε a h hε ha hh (fun k => amplitudeConstant h k •
    KFCausalFieldShearPathGraphs.state ε h hε hb (coherentSeed a h ha hh k) (slopeWeight l i) t)

theorem input_of_representation (f : S) {n : ℕ} (k : Fin n → Joint 2 4) (z : Fin n → ℂ)
    (hf : (f:Hilbert) = ∑ r, z r • state ε a h hε ha hh (k r)) (t : ℝ) :
    input ε a h hε ha hh hb t f = KFCausalImaginaryShearCoherentBridge.input ε a h hε ha hh hb k z t := by
  unfold input
  rw [extend_of_representation ε a h hε ha hh _ f k z hf]
  simp only [KFCausalImaginaryShearCoherentBridge.input,KFCausalImaginaryShearSuperposition.sumInput,
    coherentSeed,smul_smul]

theorem field_of_representation (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (f : S)
    {n : ℕ} (k : Fin n → Joint 2 4) (z : Fin n → ℂ)
    (hf : (f:Hilbert) = ∑ r, z r • state ε a h hε ha hh (k r)) (t : ℝ) :
    field ε a h hε ha hh hb l i t f = KFCausalCoherentMatterInterpolation.field ε a h hε ha hh hb l i k z t := by
  unfold field
  rw [extend_of_representation ε a h hε ha hh _ f k z hf]
  simp only [KFCausalCoherentMatterInterpolation.field,KFCausalFieldShearInterpolationEstimate.field,smul_smul]

theorem shear_of_representation (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (f : S)
    {n : ℕ} (k : Fin n → Joint 2 4) (z : Fin n → ℂ)
    (hf : (f:Hilbert) = ∑ r, z r • state ε a h hε ha hh (k r)) (t : ℝ) :
    shear ε a h hε ha hh hb l i t f = KFCausalCoherentMatterInterpolation.shear ε a h hε ha hh hb l i k z t := by
  unfold shear
  rw [extend_of_representation ε a h hε ha hh _ f k z hf]
  simp only [KFCausalCoherentMatterInterpolation.shear,KFCausalFieldShearInterpolationEstimate.shear,smul_smul]

theorem derivativeField_of_representation (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (f : S)
    {n : ℕ} (k : Fin n → Joint 2 4) (z : Fin n → ℂ)
    (hf : (f:Hilbert) = ∑ r, z r • state ε a h hε ha hh (k r)) (t : ℝ) :
    derivativeField ε a h hε ha hh hb l i t f =
      KFCausalCoherentMatterInterpolation.derivativeField ε a h hε ha hh hb l i k z t := by
  unfold derivativeField
  rw [extend_of_representation ε a h hε ha hh _ f k z hf]
  simp only [KFCausalCoherentMatterInterpolation.derivativeField,KFCausalFieldShearInterpolationEstimate.derivativeField,smul_smul]

theorem input_zero_charge (f : S) (θ : ℝ) :
    input ε a h hε ha hh hb 0 (rotate ε a h hε ha hh θ f) = action h hh θ (input ε a h hε ha hh hb 0 f) := by
  obtain ⟨n,k,z,hf⟩ := finite_representation ε a h hε ha hh f f.property
  rw [input_of_representation ε a h hε ha hh hb _ _ z
      (rotate_representation ε a h hε ha hh f k z hf θ),
    input_of_representation ε a h hε ha hh hb f k z hf]
  exact KFCausalImaginaryShearInitialEndpoint.initial_charge ε a h hε hb ha hh θ k z

theorem input_endpoint_graph (f : S) :
    ((f:Hilbert),input ε a h hε ha hh hb 1 f) ∈ (orderedExponential ε hε h).graph := by
  obtain ⟨n,k,z,hf⟩ := finite_representation ε a h hε ha hh f f.property
  rw [input_of_representation ε a h hε ha hh hb f k z hf,hf]
  exact KFCausalImaginaryShearCoherentBridge.endpoint_ordered_graph ε a h hε ha hh hb k z

theorem field_graph (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (f : S) (t : Interval) :
    (input ε a h hε ha hh hb t f,field ε a h hε ha hh hb l i t f) ∈ (fieldPower l i).graph := by
  obtain ⟨n,k,z,hf⟩ := finite_representation ε a h hε ha hh f f.property
  rw [input_of_representation ε a h hε ha hh hb f k z hf,
    field_of_representation ε a h hε ha hh hb l i f k z hf]
  exact KFCausalFieldShearInterpolationEstimate.field_graph_sum ε h hε hb l i
    (fun r => coherentSeed a h ha hh (k r)) (fun r => z r*amplitudeConstant h (k r)) t

theorem shear_graph (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (f : S) (t : Interval) :
    (field ε a h hε ha hh hb l i t f,shear ε a h hε ha hh hb l i t f) ∈ (shearMomentum h).graph := by
  obtain ⟨n,k,z,hf⟩ := finite_representation ε a h hε ha hh f f.property
  rw [field_of_representation ε a h hε ha hh hb l i f k z hf,
    shear_of_representation ε a h hε ha hh hb l i f k z hf]
  exact KFCausalFieldShearInterpolationEstimate.shear_graph_sum ε h hε hb l i
    (fun r => coherentSeed a h ha hh (k r)) (fun r => z r*amplitudeConstant h (k r)) hh t

#print axioms rotate_representation
#print axioms input_of_representation
#print axioms field_of_representation
#print axioms shear_of_representation
#print axioms derivativeField_of_representation
#print axioms input_zero_charge
#print axioms input_endpoint_graph
#print axioms field_graph
#print axioms shear_graph
end
end UnifiedTheory.Audit.KFCausalCoherentMatterPathOperator
