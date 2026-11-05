/- The distant mixed-ground sum is the limit of literal finite-boundary
Wilson response sums. A bound uniform in cylinder depth passes to the true
ground without a cutoff-uniform vacuum-convergence rate. The required
depth-uniform response estimate is not proved here. -/
import UnifiedTheory.Clay.YangMills.WilsonBoundaryPointwise
import UnifiedTheory.Clay.YangMills.WilsonGramNearFar

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonBoundaryMixedLimit
noncomputable section
open MeasureTheory Filter WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonBoundaryPointwise WilsonCylinderVacuum WilsonSymmetricLinkChange
open WilsonMixedGroundResponse WilsonSpatialGramNeighborhood WilsonGramNearFar
open scoped Topology

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

/-- The finite output partition after removing the input spatial weight.
Its boundary is the actual finite message, with no ground amplitude. -/
def boundaryPartition (β : ℝ) (j : ℕ) (u : Slice n) : ℝ :=
  ∫ v, kineticWeight WilsonSingleLinkStaples.character β 2 u v *
    spatialWeight WilsonSingleLinkStaples.character β 2 v * boundaryMessage n β j v ∂measure n

theorem boundaryMessage_partition (β : ℝ) (j : ℕ) (u : Slice n) :
    boundaryMessage n β (j+1) u =
      spatialWeight WilsonSingleLinkStaples.character β 2 u * boundaryPartition n β j u := by
  rw [boundaryMessage_raw_succ, boundaryPartition, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with v
  unfold WilsonTemporalGauge.rawKernel
  ring

/-- Four actual finite boundary messages; no vacuum boundary is inserted. -/
def boundaryRatio (β : ℝ) (j : ℕ) (e d : SpatialVertex n × Fin 3)
    (q r : Q) (u : Slice n) : ℝ :=
  boundaryMessage n β (j+1) u*boundaryMessage n β (j+1) (shift n e q (shift n d r u)) /
    (boundaryMessage n β (j+1) (shift n e q u)*boundaryMessage n β (j+1) (shift n d r u))-1

/-- Away from shared plaquettes, the bare spatial factors cancel exactly. -/
theorem boundaryRatio_partition (β : ℝ) (j : ℕ) (e d : SpatialVertex n × Fin 3)
    (q r : Q) (hed : e ≠ d)
    (hd : Disjoint (WilsonSlabLocalComparison.affected n e.1 e.2)
      (WilsonSlabLocalComparison.affected n d.1 d.2)) (u : Slice n) :
    boundaryRatio n β j e d q r u =
      boundaryPartition n β j u * boundaryPartition n β j (shift n e q (shift n d r u)) /
        (boundaryPartition n β j (shift n e q u)*boundaryPartition n β j (shift n d r u))-1 := by
  simp only [boundaryRatio, boundaryMessage_partition]
  have hs := spatialWeight_cross n β e d q r hed hd u
  have hw (z : Slice n) : spatialWeight WilsonSingleLinkStaples.character β 2 z ≠ 0 :=
    (Real.exp_pos _).ne'
  congr 1
  rw [show spatialWeight WilsonSingleLinkStaples.character β 2 u * boundaryPartition n β j u *
      (spatialWeight WilsonSingleLinkStaples.character β 2 (shift n e q (shift n d r u)) *
        boundaryPartition n β j (shift n e q (shift n d r u))) =
      (spatialWeight WilsonSingleLinkStaples.character β 2 u *
        spatialWeight WilsonSingleLinkStaples.character β 2 (shift n e q (shift n d r u))) *
      (boundaryPartition n β j u * boundaryPartition n β j (shift n e q (shift n d r u))) by ring,
    show spatialWeight WilsonSingleLinkStaples.character β 2 (shift n e q u) *
      boundaryPartition n β j (shift n e q u) *
      (spatialWeight WilsonSingleLinkStaples.character β 2 (shift n d r u) *
        boundaryPartition n β j (shift n d r u)) =
      (spatialWeight WilsonSingleLinkStaples.character β 2 (shift n e q u) *
        spatialWeight WilsonSingleLinkStaples.character β 2 (shift n d r u)) *
      (boundaryPartition n β j (shift n e q u)*boundaryPartition n β j (shift n d r u)) by ring,
    hs, mul_div_mul_left _ _ (mul_ne_zero (hw u) (hw _))]

theorem boundaryRatio_scaled (β : ℝ) (hβ : 0 ≤ β) (j : ℕ)
    (e d : SpatialVertex n × Fin 3) (q r : Q) (u : Slice n) :
    boundaryRatio n β j e d q r u =
      scaledMessage n β (j+1) u*scaledMessage n β (j+1) (shift n e q (shift n d r u)) /
        (scaledMessage n β (j+1) (shift n e q u)*scaledMessage n β (j+1) (shift n d r u))-1 := by
  let c := (‖transfer n β‖⁻¹)^(j+1)
  have hc : c ≠ 0 := pow_ne_zero _ (inv_ne_zero
    (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1.ne')
  have he (a b x y : ℝ) : (c*a*(c*y))/((c*b)*(c*x)) = (a*y)/(b*x) := by
    rw [show c*a*(c*y) = (c*c)*(a*y) by ring,
      show c*b*(c*x) = (c*c)*(b*x) by ring,
      mul_div_mul_left _ _ (mul_ne_zero hc hc)]
  simp only [boundaryRatio, scaledMessage, ContinuousMap.smul_apply, smul_eq_mul]
  exact congrArg (fun x : ℝ => x-1) (he _ _ _ _).symm

/-- Only the finite-cutoff positive overlap and ground value enter division. -/
theorem boundaryRatio_tendsto (β : ℝ) (hβ : 0 ≤ β)
    (e d : SpatialVertex n × Fin 3) (q r : Q) (u : Slice n) :
    Tendsto (fun j => boundaryRatio n β j e d q r u) atTop
      (nhds (ground n β hβ u*ground n β hβ (shift n e q (shift n d r u)) /
        (ground n β hβ (shift n e q u)*ground n β hβ (shift n d r u))-1)) := by
  have hc := (overlap_pos n β hβ).ne'
  have h := ((scaledMessage_pointwise_tendsto n β hβ u).mul
    (scaledMessage_pointwise_tendsto n β hβ (shift n e q (shift n d r u)))).div
    ((scaledMessage_pointwise_tendsto n β hβ (shift n e q u)).mul
      (scaledMessage_pointwise_tendsto n β hβ (shift n d r u)))
    (mul_ne_zero (mul_ne_zero hc (ground_pos n β hβ _).ne')
      (mul_ne_zero hc (ground_pos n β hβ _).ne'))
  have hs := h.sub_const 1
  have he :
      (overlap n β hβ*ground n β hβ u)*
          (overlap n β hβ*ground n β hβ (shift n e q (shift n d r u))) /
        ((overlap n β hβ*ground n β hβ (shift n e q u))*
          (overlap n β hβ*ground n β hβ (shift n d r u))) =
      ground n β hβ u*ground n β hβ (shift n e q (shift n d r u)) /
        (ground n β hβ (shift n e q u)*ground n β hβ (shift n d r u)) := by
    field_simp [hc, (ground_pos n β hβ (shift n e q u)).ne',
      (ground_pos n β hβ (shift n d r u)).ne']
  rw [he] at hs
  convert hs using 1
  ext j
  exact boundaryRatio_scaled n β hβ j e d q r u

def boundaryFar (β : ℝ) (j : ℕ) (rotations : SpatialVertex n × Fin 3 → Q)
    (u : Slice n) (e : SpatialVertex n × Fin 3) : ℝ :=
  ∑ d ∈ Finset.univ \ near n e, |boundaryRatio n β j e d (rotations e) (rotations d) u|

/-- The true distant-ground sum, not a different limiting covariance. -/
theorem boundaryFar_tendsto (β : ℝ) (hβ : 0 ≤ β)
    (rotations : SpatialVertex n × Fin 3 → Q) (u : Slice n) (e : SpatialVertex n × Fin 3) :
    Tendsto (fun j => boundaryFar n β j rotations u e) atTop
      (nhds (farCost n β hβ rotations u e)) := by
  unfold boundaryFar farCost
  apply tendsto_finset_sum
  intro d hd
  have hdn := (Finset.mem_sdiff.mp hd).2
  have h := boundaryRatio_tendsto n β hβ e d (rotations e) (rotations d) u
  rw [← gram_ground_ratio n β hβ e d (rotations e) (rotations d)
      (far_ne n e d hdn) (far_disjoint n e d hdn), add_sub_cancel_right,
    gram_ground_log n β hβ e d (rotations e) (rotations d)
      (far_ne n e d hdn) (far_disjoint n e d hdn)] at h
  exact h.abs

/-- No interchange of spatial and temporal limits is made. The constant
passes through each fixed-cutoff limit unchanged. -/
theorem far_bound_of_boundary (β : ℝ) (hβ : 0 ≤ β)
    (rotations : SpatialVertex n × Fin 3 → Q) (u : Slice n) (e : SpatialVertex n × Fin 3)
    (R : ℝ) (hboundary : ∀ j, boundaryFar n β j rotations u e ≤ R) :
    farCost n β hβ rotations u e ≤ R :=
  le_of_tendsto (boundaryFar_tendsto n β hβ rotations u e) (Eventually.of_forall hboundary)

theorem energy_le_loss_of_boundary (β : ℝ) (hβ : 0 ≤ β)
    (rotations : SpatialVertex n × Fin 3 → Q) (D R : ℝ) (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hcap : ∀ d, WilsonVarianceResponse.coefficient β (rotations d) ≤ D)
    (hboundary : ∀ j u e, boundaryFar n β j rotations u e ≤ R) (f : C(Slice n, ℝ)) :
    WilsonCollectiveGram.energy n β hβ id rotations (fun _ => 1)
      (WilsonPhysicalVariance.step n β hβ f) ≤
        (16*D+R)*WilsonPhysicalVariance.loss n β hβ f :=
  energy_le_loss_of_far n β hβ rotations D R hD hR hcap
    (fun u e => far_bound_of_boundary n β hβ rotations u e R (fun j => hboundary j u e)) f

end
end UnifiedTheory.Clay.YangMills.WilsonBoundaryMixedLimit
