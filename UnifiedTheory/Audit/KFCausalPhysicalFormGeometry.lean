/- Topology and the physical embedding of the actual eight-factor
completed form spaces. Density and separability are proved here, not
supplied as limit-existence hypotheses. -/
import UnifiedTheory.Audit.KFCausalPhysicalFormTransport
import Mathlib.MeasureTheory.Measure.SeparableMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalPhysicalFormGeometry
noncomputable section
open TopologicalSpace
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalPhysicalFormTransport
open UnifiedTheory.Audit.KFCausalPhysicalFormHamiltonian (formData)

instance hilbert_secondCountable : SecondCountableTopology Hilbert := by
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  unfold Hilbert
  infer_instance

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε)
  (mass2 quartic vacuum t : ℝ)

theorem embedding_contraction (u : FormSpace ε hε hbar hh mass2 quartic vacuum t) :
    ‖embedding ε hε hbar hh mass2 quartic vacuum t u‖ ≤ ‖u‖ :=
  KFCausalClosedGraphForm.embedding_contraction (formData ε hε hbar hh mass2 quartic vacuum t) u

theorem embedding_norm_le_one : ‖embedding ε hε hbar hh mass2 quartic vacuum t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using embedding_contraction ε hε hbar hh mass2 quartic vacuum t u

theorem embedding_dense : DenseRange (embedding ε hε hbar hh mass2 quartic vacuum t) :=
  KFCausalClosedGraphForm.embedding_dense (formData ε hε hbar hh mass2 quartic vacuum t)

instance formSpace_secondCountable : SecondCountableTopology (FormSpace ε hε hbar hh mass2 quartic vacuum t) := by
  infer_instance

theorem formSpace_separable : SeparableSpace (FormSpace ε hε hbar hh mass2 quartic vacuum t) := inferInstance

#print axioms hilbert_secondCountable
#print axioms embedding_contraction
#print axioms embedding_norm_le_one
#print axioms embedding_dense
#print axioms formSpace_secondCountable
#print axioms formSpace_separable

end
end UnifiedTheory.Audit.KFCausalPhysicalFormGeometry
