/- Actual high-defect bridges survive a small link rotation after an
explicit threshold allowance. No event invariance is falsely assumed. -/
import UnifiedTheory.Clay.YangMills.WilsonBridgeOutputSum
import UnifiedTheory.Clay.YangMills.WilsonGroundSmallRotation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonBridgeRotationStability
noncomputable section
open Filter WilsonSlabOperator WilsonTimeSlab WilsonSymmetricLinkChange
open WilsonGroundSmallRotation WilsonBadClusterBridge WilsonBridgeOutputSum
open SpatialPlaquetteCutGeometry SpatialWilsonPlaquetteKernels
open scoped Quaternion Topology

variable (n : ℕ) [NeZero n]

omit [NeZero n] in
theorem defect_shift (e : SpatialVertex (2 * (2 * n)) × Fin 3) (q : Q)
    (p : Plaquette (2 * n)) (u : Slice (2 * (2 * n))) :
    |defect (2 * n) p (shift (2 * (2 * n)) e q u) - defect (2 * n) p u| ≤
      8 * ‖(q : ℍ) - 1‖ := by
  have h := trace_shift_bound (2 * (2 * n)) e q u p.1 p.2.val.1 p.2.val.2
  have he : defect (2 * n) p (shift (2 * (2 * n)) e q u) - defect (2 * n) p u =
      -((WilsonSingleLinkStaples.character
        (spatialHolonomy (shift (2 * (2 * n)) e q u) p.1 p.2.val.1 p.2.val.2)).re -
        (WilsonSingleLinkStaples.character (spatialHolonomy u p.1 p.2.val.1 p.2.val.2)).re) := by
    unfold defect
    ring
  rwa [he, abs_neg]

theorem event_mono (p z : Plaquette (2 * n)) (R S : ℝ) (hRS : R ≤ S) :
    event n p z S ⊆ event n p z R := by
  rintro u ⟨A,hA⟩
  exact ⟨A,fun a => by have h := hA a; linarith⟩

theorem event_shift (p z : Plaquette (2 * n)) (R r : ℝ)
    (e : SpatialVertex (2 * (2 * n)) × Fin 3) (q : Q) (hq : ‖(q : ℍ) - 1‖ ≤ r)
    (u : Slice (2 * (2 * n))) (hu : u ∈ event n p z (R + 4 * r)) :
    shift (2 * (2 * n)) e q u ∈ event n p z R := by
  obtain ⟨A,hA⟩ := hu
  refine ⟨A,?_⟩
  intro a
  have ha := hA a
  have hd := (abs_le.mp (defect_shift n e q a.val u)).1
  linarith

theorem farEvent_mono (p z : Plaquette (2 * n)) (m : ℕ) (R S : ℝ) (hRS : R ≤ S) :
    farEvent n p z m S ⊆ farEvent n p z m R := by
  unfold farEvent
  split_ifs
  · exact event_mono n p z R S hRS
  · exact Set.Subset.rfl

theorem farEvent_shift (p z : Plaquette (2 * n)) (m : ℕ) (R r : ℝ)
    (e : SpatialVertex (2 * (2 * n)) × Fin 3) (q : Q) (hq : ‖(q : ℍ) - 1‖ ≤ r)
    (u : Slice (2 * (2 * n))) (hu : u ∈ farEvent n p z m (R + 4 * r)) :
    shift (2 * (2 * n)) e q u ∈ farEvent n p z m R := by
  unfold farEvent at *
  split_ifs at *
  · exact event_shift n p z R r e q hq u hu
  · exact False.elim hu

/-- Extra room for rotations of displacement at most 1/(36 beta). -/
def bufferedThreshold (β : ℝ) : ℝ := WilsonClusterActivity.threshold β + 4 * (36 * β)⁻¹

theorem bufferedThreshold_tendsto : Tendsto bufferedThreshold atTop (𝓝 0) := by
  have h : Tendsto (fun β : ℝ => (36 * β)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 36))
  simpa only [bufferedThreshold, mul_zero, add_zero] using
    WilsonClusterActivity.threshold_tendsto.add (h.const_mul 4)

end
end UnifiedTheory.Clay.YangMills.WilsonBridgeRotationStability
