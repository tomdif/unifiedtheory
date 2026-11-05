/- A polynomial norm price for simultaneous deletion of an aligned spatial
patch. The k-column insertion floor yields m(beta)^k*||T_cut||<=||T_full||,
with all remaining interactions and the original full normalization retained. -/
import UnifiedTheory.Clay.YangMills.SpatialWilsonColumnTransfer
import UnifiedTheory.Clay.YangMills.SpatialWilsonPatchHistory

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SpatialWilsonPatchNorm
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSingleLinkStaples SpatialPlaquetteCutGeometry
open SpatialWilsonPatchWeights SpatialWilsonColumnTransfer KernelPartitionNorm

variable (n : ℕ) [NeZero n]

/-- The k-column history floor retains both endpoint weights and all kinetic links. -/
theorem patch_partition_floor (S : Finset (Plaquette n)) (hS : Aligned n S)
    (β : ℝ) (hβ : 0 ≤ β) (L : ℕ) :
    ((SU2GaussianMass.mass β) ^ S.card) ^ (L + 1) *
      FiniteKernelChain.endpoint (WilsonSlabOperator.measure (2 * n))
        (kernelMap n (omitted n S β) β) L (boundary n (omitted n S β))
        (boundary n (omitted n S β)) ≤
      FiniteKernelChain.endpoint (WilsonSlabOperator.measure (2 * n))
        (kernelMap n (fun _ => β) β) L (boundary n (fun _ => β))
        (boundary n (fun _ => β)) := by
  rw [endpoint_density, endpoint_density]
  have h := SpatialWilsonPatchHistory.partition_floor n (Fin (L + 1)) S hS β hβ
    (fun _ : Fin L => β) (fun _ => hβ) Fin.castSucc Fin.succ
  simpa only [Fintype.card_fin, ← pow_mul, Nat.mul_comm] using h

/-- Fixed-cutoff positive boundary constants disappear in the temporal
growth rate. The remaining price is the kth power of the exact Haar mass. -/
theorem mass_norm_lower (S : Finset (Plaquette n)) (hS : Aligned n S)
    (β : ℝ) (hβ : 0 ≤ β) :
    (SU2GaussianMass.mass β) ^ S.card * ‖transfer n (omitted n S β) β‖ ≤
      ‖WilsonSlabOperator.transfer (2 * n) β‖ := by
  let B₀ := boundary n (omitted n S β)
  let B := boundary n (fun _ => β)
  let ψ := WilsonGroundLocalComparison.ground (2 * n) β hβ
  obtain ⟨c,hc,hcB⟩ := positive_floor B₀ (boundary_pos n (omitted n S β))
  obtain ⟨d,hd,hdψ⟩ := positive_floor ψ (WilsonGroundLocalComparison.ground_pos (2 * n) β hβ)
  have hcomp (u : SpatialLinks (2 * n) Q) : B u ≤ (‖B‖ / d) * ψ u := by
    calc
      _ ≤ ‖B‖ := (le_abs_self _).trans (ContinuousMap.norm_coe_le_norm B u)
      _ = (‖B‖ / d) * d := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hdψ u) (div_nonneg (norm_nonneg _) hd.le)
  have hψ (u : SpatialLinks (2 * n) Q) :
      (∫ v, kernelMap n (fun _ => β) β (u,v) * ψ v ∂WilsonSlabOperator.measure (2 * n)) =
        ‖WilsonSlabOperator.transfer (2 * n) β‖ * ψ u := by
    simp only [constant_kernelMap]
    exact WilsonTemporalGauge.ground_raw_equation (2 * n) β hβ u
  exact norm_comparison (WilsonSlabOperator.measure (2 * n))
    (kernelMap n (omitted n S β) β) (kernelMap n (fun _ => β) β)
    (transfer_positive n _ β hβ) (fun u v => (kernelMap_pos n _ β u v).le)
    (fun u v => (kernelMap_pos n _ β u v).le) B₀ B ψ c hc hcB
    (fun u => (boundary_pos n _ u).le) ‖WilsonSlabOperator.transfer (2 * n) β‖ (‖B‖ / d)
    (norm_nonneg _) hψ hcomp ((SU2GaussianMass.mass β) ^ S.card)
    (pow_pos (SU2GaussianMass.mass_pos β) _)
    (patch_partition_floor n S hS β hβ)

/-- The k-column removal price grows as beta^(3k/2), independently of exterior
volume and temporal length. The reference norm is the original full transfer. -/
theorem polynomial_norm (S : Finset (Plaquette n)) (hS : Aligned n S)
    (β : ℝ) (hβ : 3 / 4 ≤ β) :
    ‖transfer n (omitted n S β) β‖ ≤
      (SU2GaussianMass.cap β) ^ S.card * ‖WilsonSlabOperator.transfer (2 * n) β‖ := by
  have hi := mass_norm_lower n S hS β (by linarith)
  have hc := pow_nonneg (SU2GaussianMass.cap_nonneg β (by linarith)) S.card
  have hm := one_le_pow₀ (SU2GaussianMass.mass_cap_lower β hβ) (n := S.card)
  calc
    _ ≤ (SU2GaussianMass.mass β * SU2GaussianMass.cap β) ^ S.card *
        ‖transfer n (omitted n S β) β‖ := by nlinarith [norm_nonneg (transfer n (omitted n S β) β)]
    _ = (SU2GaussianMass.cap β) ^ S.card *
        ((SU2GaussianMass.mass β) ^ S.card * ‖transfer n (omitted n S β) β‖) := by
      rw [mul_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hi hc

end
end UnifiedTheory.Clay.YangMills.SpatialWilsonPatchNorm
