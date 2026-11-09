/- A polynomial norm price for removing an actual spatial plaquette column.
Finite temporal insertion and the genuine spectral growth comparison give
m(beta)*||T_cut,raw|| <= ||T_full||. The original full ground supplies only
the upper comparison; no modified-ground reflection premise is supplied. -/
import UnifiedTheory.Clay.YangMills.SpatialWilsonColumnTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SpatialWilsonColumnNorm
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSingleLinkStaples SpatialPlaquetteCutGeometry
open SpatialWilsonInsertion SpatialWilsonColumnTransfer KernelPartitionNorm

variable (n : ℕ) [NeZero n]

/-- Fixed-cutoff positive boundary constants disappear in the temporal
growth rate. The remaining price is the exact single-plaquette Haar mass. -/
theorem mass_norm_lower (q : Plaquette n) (hq : SpatialWilsonPlaquetteKernels.Crossing n q)
    (β : ℝ) (hβ : 0 ≤ β) :
    SU2GaussianMass.mass β * ‖transfer n (omitted n q β) β‖ ≤
      ‖WilsonSlabOperator.transfer (2 * n) β‖ := by
  let B₀ := boundary n (omitted n q β)
  let B := boundary n (fun _ => β)
  let ψ := WilsonGroundLocalComparison.ground (2 * n) β hβ
  obtain ⟨c,hc,hcB⟩ := positive_floor B₀ (boundary_pos n (omitted n q β))
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
    (kernelMap n (omitted n q β) β) (kernelMap n (fun _ => β) β)
    (transfer_positive n _ β hβ) (fun u v => (kernelMap_pos n _ β u v).le)
    (fun u v => (kernelMap_pos n _ β u v).le) B₀ B ψ c hc hcB
    (fun u => (boundary_pos n _ u).le) ‖WilsonSlabOperator.transfer (2 * n) β‖ (‖B‖ / d)
    (norm_nonneg _) hψ hcomp (SU2GaussianMass.mass β) (SU2GaussianMass.mass_pos β)
    (column_partition_floor n q hq β hβ)

/-- The column removal price grows as beta^(3/2), independently of spatial
volume and temporal length. The reference norm is the original full transfer. -/
theorem polynomial_norm (q : Plaquette n) (hq : SpatialWilsonPlaquetteKernels.Crossing n q)
    (β : ℝ) (hβ : 3 / 4 ≤ β) :
    ‖transfer n (omitted n q β) β‖ ≤
      SU2GaussianMass.cap β * ‖WilsonSlabOperator.transfer (2 * n) β‖ := by
  have hi := mass_norm_lower n q hq β (by linarith)
  have hc := SU2GaussianMass.cap_nonneg β (by linarith)
  have hm := SU2GaussianMass.mass_cap_lower β hβ
  calc
    _ ≤ (SU2GaussianMass.mass β * SU2GaussianMass.cap β) *
        ‖transfer n (omitted n q β) β‖ := by nlinarith [norm_nonneg (transfer n (omitted n q β) β)]
    _ = SU2GaussianMass.cap β *
        (SU2GaussianMass.mass β * ‖transfer n (omitted n q β) β‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hi hc

end
end UnifiedTheory.Clay.YangMills.SpatialWilsonColumnNorm
