/- Separability of the actual physical L2 space and completed graph form
spaces. This supplies the topology needed for sequential weak compactness. -/
import UnifiedTheory.Audit.KFCausalRegularizedFormEmbedding
import Mathlib.MeasureTheory.Measure.SeparableMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalRegularizedFormSeparable
noncomputable section
open TopologicalSpace
open UnifiedTheory.Audit.KFCausalRegularizedMomentumClosure
open UnifiedTheory.Audit.KFCausalRegularizedFormEmbedding

instance hilbert_secondCountable : SecondCountableTopology Hilbert := by
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  unfold Hilbert
  infer_instance

instance formSpace_secondCountable (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ) :
    SecondCountableTopology (FormSpace ε hε hbar coupling t) := by
  infer_instance

theorem formSpace_separable (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ) :
    SeparableSpace (FormSpace ε hε hbar coupling t) := inferInstance

#print axioms hilbert_secondCountable
#print axioms formSpace_secondCountable
#print axioms formSpace_separable

end
end UnifiedTheory.Audit.KFCausalRegularizedFormSeparable
