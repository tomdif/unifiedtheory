/- Dense physical tensor families from any nowhere-zero L2 clock weight.
Only the measure-preserving Euclidean flattening is used here. -/
import UnifiedTheory.Audit.KFCausalPhysicalTensorMomentum
import UnifiedTheory.Audit.KFCausalWeightedProductTotality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalPhysicalTensorDensity
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalClockTransverseProducts
open UnifiedTheory.Audit.KFCausalRegularizedGaussianTotality
open UnifiedTheory.Audit.KFCausalWeightedProductTotality
open UnifiedTheory.Audit.KFCausalSchwartzTransversePacket
open UnifiedTheory.Audit.KFCausalPhysicalTensorMomentum

def tensorFamily (w : ℝ → ℂ) (hw : MemLp w 2) (v : ℝ × SchwartzMap TailSpace ℂ) : Hilbert :=
  tensorState (modulate v.1 w) (unflattenSchwartz v.2) (modulate_memLp w hw v.1)

theorem tensorFamily_coordinates (w : ℝ → ℂ) (hw : MemLp w 2)
    (v : ℝ × SchwartzMap TailSpace ℂ) : euclideanPullback (tensorFamily w hw v)=euclideanFamily w hw v := by
  change euclideanPullback (tensorState (modulate v.1 w) (unflattenSchwartz v.2) (modulate_memLp w hw v.1)) =
    (product_memLp _ _ (modulate_memLp w hw v.1) (v.2.memLp 2 volume)).toLp _
  apply Lp.ext
  filter_upwards [euclideanPullback_coe (tensorState (modulate v.1 w) (unflattenSchwartz v.2) (modulate_memLp w hw v.1)),
    split_preserves_volume.quasiMeasurePreserving.ae
      (tensorState_coe (modulate v.1 w) (unflattenSchwartz v.2) (modulate_memLp w hw v.1)),
    (product_memLp _ _ (modulate_memLp w hw v.1) (v.2.memLp 2 volume)).coeFn_toLp] with x hx hf he
  rw [he]
  exact hx.trans hf

theorem dense_tensor_span (w : ℝ → ℂ) (hw : MemLp w 2) (hnw : ∀ q, w q ≠ 0) :
    (Submodule.span ℂ (Set.range (tensorFamily w hw))).topologicalClosure=⊤ := by
  let L : FrequencyHilbert →L[ℂ] Hilbert := euclideanPullback.symm
  have hd : DenseRange L := euclideanPullback.symm.surjective.denseRange
  have he := hd.topologicalClosure_map_submodule (dense_euclidean_span w hw hnw)
  have ht : (L : FrequencyHilbert → Hilbert) ∘ euclideanFamily w hw = tensorFamily w hw := by
    funext v
    apply euclideanPullback.injective
    change euclideanPullback (euclideanPullback.symm (euclideanFamily w hw v)) = _
    rw [euclideanPullback.apply_symm_apply,tensorFamily_coordinates]
  rw [Submodule.map_span,← Set.range_comp] at he
  change (Submodule.span ℂ (Set.range ((L : FrequencyHilbert → Hilbert) ∘ euclideanFamily w hw))).topologicalClosure=⊤ at he
  rw [ht] at he
  exact he

#print axioms tensorFamily_coordinates
#print axioms dense_tensor_span

end
end UnifiedTheory.Audit.KFCausalPhysicalTensorDensity
