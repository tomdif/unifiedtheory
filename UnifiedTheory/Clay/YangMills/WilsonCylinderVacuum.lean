/- Actual full-endpoint Wilson boundary data converge to the constructed
vacuum at fixed spatial cutoff. Normalized two-insertion transfer pairings
then converge without substituting a vacuum boundary into the finite action. -/
import UnifiedTheory.Clay.YangMills.ContinuousBoundaryMoments
import UnifiedTheory.Clay.YangMills.WilsonBoundaryTransfer
import UnifiedTheory.Clay.YangMills.WilsonOpenSlabVacuum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonCylinderVacuum
noncomputable section
open MeasureTheory Filter WilsonSlabOperator WilsonPositiveGroundState
open WilsonSlabContraction TransferEnergySurvival ContinuousBoundaryMoments
open scoped Topology

variable (n : ℕ) [NeZero n]

/-- The genuine full-endpoint spatial boundary in the original Hilbert space. -/
def boundary (β : ℝ) : Hilbert n :=
  embed (measure n) (WilsonBoundaryTransfer.spatialBoundary n β)

def overlap (β : ℝ) (hβ : 0 ≤ β) : ℝ :=
  ∫ u, WilsonGroundLocalComparison.ground n β hβ u *
    WilsonBoundaryTransfer.spatialBoundary n β u ∂measure n

/-- Strict positivity follows from the actual positive boundary and vacuum. -/
theorem overlap_pos (β : ℝ) (hβ : 0 ≤ β) : 0 < overlap n β hβ := by
  have hp (u : Slice n) : 0 < WilsonGroundLocalComparison.ground n β hβ u *
      WilsonBoundaryTransfer.spatialBoundary n β u :=
    mul_pos (WilsonGroundLocalComparison.ground_pos n β hβ u)
      (WilsonBoundaryTransfer.spatialBoundary_pos n β u)
  have hi : Integrable (fun u => WilsonGroundLocalComparison.ground n β hβ u *
      WilsonBoundaryTransfer.spatialBoundary n β u) (measure n) :=
    ((WilsonGroundLocalComparison.ground n β hβ).continuous.mul
      (WilsonBoundaryTransfer.spatialBoundary n β).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  apply (integral_pos_iff_support_of_nonneg (fun u => (hp u).le) hi).mpr
  have hs : Function.support (fun u => WilsonGroundLocalComparison.ground n β hβ u *
      WilsonBoundaryTransfer.spatialBoundary n β u) = Set.univ := by
    ext u
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (hp u).ne'
  simp [hs]

theorem overlap_inner (β : ℝ) (hβ : 0 ≤ β) :
    inner ℂ (WilsonVacuumConvergence.vacuum n β hβ) (boundary n β) =
      (overlap n β hβ : ℂ) := by
  rw [WilsonVacuumConvergence.vacuum, boundary, embed, MeasureTheory.ContinuousMap.inner_toLp]
  simp only [complexify, ContinuousMap.coe_mk, Complex.conj_ofReal, ← Complex.ofReal_mul,
    integral_complex_ofReal, overlap]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  ring

/-- Only the already proved finite-cutoff contraction is used in this limit. -/
theorem boundary_power_tendsto (β : ℝ) (hβ : 0 ≤ β) :
    Tendsto (fun j => iterate (normalized n β) j (boundary n β)) atTop
      (nhds ((overlap n β hβ : ℂ) • WilsonVacuumConvergence.vacuum n β hβ)) := by
  simpa only [overlap_inner] using VacuumPowerConvergence.power_tendsto (normalized n β)
    (normalized_symmetric n β) (WilsonVacuumConvergence.vacuum n β hβ)
    (WilsonVacuumConvergence.vacuum_norm n β hβ)
    (WilsonVacuumConvergence.vacuum_fixed n β hβ) (ratioCap n β)
    (ratioCap_nonneg n β hβ) (ratioCap_lt_one n β)
    (WilsonVacuumConvergence.vacuum_contraction n β hβ) (boundary n β)

/-- A scalar normalization of the actual full-endpoint boundary message. -/
def scaledMessage (β : ℝ) (j : ℕ) : C(Slice n, ℝ) :=
  (‖transfer n β‖⁻¹) ^ j •
    WilsonBoundaryTransfer.message n β (WilsonBoundaryTransfer.spatialBoundary n β) j

theorem scaledMessage_embedding (β : ℝ) (j : ℕ) :
    embed (measure n) (scaledMessage n β j) =
      iterate (normalized n β) j (boundary n β) := by
  rw [scaledMessage, embed_smul]
  unfold embed
  rw [WilsonBoundaryTransfer.message_embedding, normalized,
    WilsonOpenSlabVacuum.iterate_real_smul, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

/-- The fixed-separation two-insertion transfer ratio has the actual vacuum limit.
Identification with interior observables of a longer raw cylinder additionally
uses its finite three-segment integration identity. -/
theorem two_insertion_pairing_tendsto (β : ℝ) (hβ : 0 ≤ β)
    (F G : C(Slice n, ℝ)) (k : ℕ) :
    Tendsto (fun j =>
      (inner ℂ (embed (measure n) (F * scaledMessage n β j))
        (iterate (normalized n β) k (embed (measure n) (G * scaledMessage n β j)))).re /
      (inner ℂ (embed (measure n) (scaledMessage n β j))
        (iterate (normalized n β) k (embed (measure n) (scaledMessage n β j)))).re) atTop
      (nhds ((inner ℂ (embed (measure n) (F * WilsonGroundLocalComparison.ground n β hβ))
        (iterate (normalized n β) k
          (embed (measure n) (G * WilsonGroundLocalComparison.ground n β hβ)))).re)) := by
  apply normalized_pairing_tendsto (measure n) (normalized n β)
    (WilsonGroundLocalComparison.ground n β hβ)
    (WilsonVacuumConvergence.vacuum_norm n β hβ)
    (WilsonVacuumConvergence.vacuum_fixed n β hβ)
    (scaledMessage n β) (overlap n β hβ) (overlap_pos n β hβ)
  simpa only [scaledMessage_embedding] using boundary_power_tendsto n β hβ


/-- Exact scalar bookkeeping for the original transfer clock and endpoint integrals. -/
theorem pairing_scaling (β c : ℝ) (F G : C(Slice n, ℝ)) (k : ℕ) :
    (inner ℂ (embed (measure n) (c • F))
      (iterate (normalized n β) k (embed (measure n) (c • G)))).re =
        (c^2 * (‖transfer n β‖⁻¹)^k) *
          WilsonBoundaryTransfer.endpointIntegral n β k F G := by
  rw [embed_smul, embed_smul, normalized, WilsonOpenSlabVacuum.iterate_real_smul,
    ContinuousBoundaryMoments.iterate_smul, RCLike.real_smul_eq_coe_smul (K := ℂ),
    inner_smul_left, inner_smul_right, inner_smul_right,
    WilsonBoundaryTransfer.endpointIntegral_matrix]
  change (starRingEnd ℂ (c : ℂ) *
    (((((‖transfer n β‖⁻¹)^k : ℝ) : ℂ)) *
      ((c : ℂ) * inner ℂ (embed (measure n) F)
        (iterate (transfer n β) k (embed (measure n) G))))).re = _
  simp only [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, embed, pow_two]
  ring

/-- Both transfer normalization and boundary-message normalization cancel from
the actual finite endpoint-integral quotient. -/
theorem pairing_quotient_eq (β : ℝ) (hβ : 0 ≤ β)
    (F G : C(Slice n, ℝ)) (j k : ℕ) :
    let B := WilsonBoundaryTransfer.message n β (WilsonBoundaryTransfer.spatialBoundary n β) j
    (inner ℂ (embed (measure n) (F * scaledMessage n β j))
        (iterate (normalized n β) k (embed (measure n) (G * scaledMessage n β j)))).re /
      (inner ℂ (embed (measure n) (scaledMessage n β j))
        (iterate (normalized n β) k (embed (measure n) (scaledMessage n β j)))).re =
      WilsonBoundaryTransfer.endpointIntegral n β k (F * B) (G * B) /
        WilsonBoundaryTransfer.endpointIntegral n β k B B := by
  dsimp only
  have he (H : C(Slice n, ℝ)) : H * scaledMessage n β j =
      (‖transfer n β‖⁻¹)^j • (H * WilsonBoundaryTransfer.message n β
        (WilsonBoundaryTransfer.spatialBoundary n β) j) := by
    rw [scaledMessage, mul_smul_comm]
  rw [he F, he G, pairing_scaling, scaledMessage, pairing_scaling]
  have hp : 0 < ((‖transfer n β‖⁻¹)^j)^2 * (‖transfer n β‖⁻¹)^k := by
    have hT := (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1
    positivity
  exact mul_div_mul_left _ _ hp.ne'

/-- The literal finite-chain integral quotient with propagated actual full-endpoint
boundaries has the normalized original-transfer vacuum limit. -/
theorem endpoint_quotient_tendsto (β : ℝ) (hβ : 0 ≤ β)
    (F G : C(Slice n, ℝ)) (k : ℕ) :
    Tendsto (fun j =>
      let B := WilsonBoundaryTransfer.message n β (WilsonBoundaryTransfer.spatialBoundary n β) j
      WilsonBoundaryTransfer.endpointIntegral n β k (F * B) (G * B) /
        WilsonBoundaryTransfer.endpointIntegral n β k B B) atTop
      (nhds ((inner ℂ (embed (measure n) (F * WilsonGroundLocalComparison.ground n β hβ))
        (iterate (normalized n β) k
          (embed (measure n) (G * WilsonGroundLocalComparison.ground n β hβ)))).re)) := by
  have h := two_insertion_pairing_tendsto n β hβ F G k
  simpa only [pairing_quotient_eq n β hβ F G] using h

end
end UnifiedTheory.Clay.YangMills.WilsonCylinderVacuum
