/- The actual compact transfer norm is invariant when its inhomogeneous
plaquette profile is transported through a spatial frame. -/
import UnifiedTheory.Clay.YangMills.WilsonProfileTransport
import UnifiedTheory.Clay.YangMills.KernelPartitionEquivalence

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonProfileNormTransport
noncomputable section
open SpatialPlaquetteCutGeometry WilsonPlaquetteFrames WilsonProfileTransport
open SpatialWilsonColumnTransfer SpatialWilsonCutSchwarz FiniteKernelChain
open SpatialWilsonPatchWeights

variable (n : ℕ) [NeZero n]

theorem endpoint_push (F : Frame n) (γ : Plaquette n → ℝ) (β : ℝ) (L : ℕ) :
    endpoint (WilsonSlabOperator.measure (2 * n)) (kernelMap n (push n F γ) β) L
      (boundary n (push n F γ)) (boundary n (push n F γ)) =
    endpoint (WilsonSlabOperator.measure (2 * n)) (kernelMap n γ β) L
      (boundary n γ) (boundary n γ) := by
  rw [endpoint_density, endpoint_density]
  exact partition_push n (Fin (L + 1)) F (fun _ => γ) (fun _ : Fin L => β) Fin.castSucc Fin.succ

/-- Spatial couplings may be signed here; temporal positivity only requires
beta >= 0. In particular this covers every genuine deleted profile. -/
theorem norm_push (F : Frame n) (γ : Plaquette n → ℝ) (β : ℝ) (hβ : 0 ≤ β) :
    ‖transfer n (push n F γ) β‖ = ‖transfer n γ β‖ :=
  KernelPartitionEquivalence.norm_eq (WilsonSlabOperator.measure (2 * n))
    (kernelMap n (push n F γ) β) (kernelMap n γ β)
    (transfer_positive n (push n F γ) β hβ) (transfer_positive n γ β hβ)
    (fun u v => (kernelMap_pos n (push n F γ) β u v).le)
    (fun u v => (kernelMap_pos n γ β u v).le)
    (boundary n (push n F γ)) (boundary n γ)
    (boundary_pos n (push n F γ)) (boundary_pos n γ) (endpoint_push n F γ β)

theorem norm_pushSet (F : Frame n) (S : Finset (Plaquette n)) (s β : ℝ) (hβ : 0 ≤ β) :
    ‖transfer n (omitted n (pushSet n F S) s) β‖ = ‖transfer n (omitted n S s) β‖ := by
  rw [← push_omitted]
  exact norm_push n F (omitted n S s) β hβ

theorem priced_push (F : Frame n) (γ : Plaquette n → ℝ) (β : ℝ) (hβ : 0 ≤ β) (s a : ℝ) :
    SpatialWilsonNormSchwarz.pricedNorm n (push n F γ) β s a =
      SpatialWilsonNormSchwarz.pricedNorm n γ β s a := by
  simp only [SpatialWilsonNormSchwarz.pricedNorm, norm_push n F γ β hβ, push_deficit]

end
end UnifiedTheory.Clay.YangMills.WilsonProfileNormTransport
