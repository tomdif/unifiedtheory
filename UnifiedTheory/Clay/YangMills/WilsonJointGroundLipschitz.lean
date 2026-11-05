/- A joint first-difference bound for the actual ground logarithm.
Exact plaquette incidence gives the total-displacement constant six. -/
import UnifiedTheory.Clay.YangMills.WilsonMiddleEntropy

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonJointGroundLipschitz
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonJointRotation WilsonVarianceProfile WilsonVarianceProfileCost WilsonTemporalInfluence
open WilsonVarianceResponse
open scoped Quaternion

variable (n : ℕ) [NeZero n]

theorem linear_incidence (q : Slice n) :
    (∑ x : SpatialVertex n, ∑ p : SpatialPlane,
      (displacement n q (x,p.1.1) + displacement n q (spatialStep n x p.1.1,p.1.2) +
        displacement n q (spatialStep n x p.1.2,p.1.1) + displacement n q (x,p.1.2))) =
      4*length n q := by
  rw [Finset.sum_comm]
  have he (p : SpatialPlane) :
      (∑ x : SpatialVertex n, (displacement n q (x,p.1.1) +
        displacement n q (spatialStep n x p.1.1,p.1.2) +
        displacement n q (spatialStep n x p.1.2,p.1.1) + displacement n q (x,p.1.2))) =
        2*∑ x : SpatialVertex n, (displacement n q (x,p.1.1)+displacement n q (x,p.1.2)) := by
    simp only [Finset.sum_add_distrib]
    rw [step_sum n (fun x => displacement n q (x,p.1.2)),
      step_sum n (fun x => displacement n q (x,p.1.1))]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hp (x : SpatialVertex n) := plane_sum (fun i => displacement n q (x,i))
  simp_rw [hp]
  rw [← Finset.mul_sum]
  unfold length
  rw [Fintype.sum_prod_type]
  ring

/-- This counts word occurrences exactly, including small periodic lattices. -/
theorem potential_difference (q u : Slice n) :
    |potential WilsonSingleLinkStaples.character 2 (q*u)-
      potential WilsonSingleLinkStaples.character 2 u| ≤ 8*length n q := by
  let D := fun (x : SpatialVertex n) (p : SpatialPlane) =>
    displacement n q (x,p.1.1)+displacement n q (spatialStep n x p.1.1,p.1.2)+
      displacement n q (spatialStep n x p.1.2,p.1.1)+displacement n q (x,p.1.2)
  have h (x : SpatialVertex n) (p : SpatialPlane) :
      |(2-(WilsonSingleLinkStaples.character (spatialHolonomy (q*u) x p.1.1 p.1.2)).re)-
        (2-(WilsonSingleLinkStaples.character (spatialHolonomy u x p.1.1 p.1.2)).re)| ≤
        2*D x p := by
    have ht := WilsonPlaquetteTransport.character_difference
      (spatialHolonomy (q*u) x p.1.1 p.1.2) (spatialHolonomy u x p.1.1 p.1.2)
    have hd := (holonomy_variation n q u x p.1.1 p.1.2).1
    unfold WilsonPlaquetteTransport.chord at ht
    dsimp only [D]
    have he : (2-(WilsonSingleLinkStaples.character
        (spatialHolonomy (q*u) x p.1.1 p.1.2)).re)-
        (2-(WilsonSingleLinkStaples.character (spatialHolonomy u x p.1.1 p.1.2)).re) =
        -((WilsonSingleLinkStaples.character (spatialHolonomy (q*u) x p.1.1 p.1.2)).re-
          (WilsonSingleLinkStaples.character (spatialHolonomy u x p.1.1 p.1.2)).re) := by ring
    rw [he, abs_neg]
    linarith
  unfold potential
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ x : SpatialVertex n, |(∑ p : SpatialPlane,
        (2-(WilsonSingleLinkStaples.character (spatialHolonomy (q*u) x p.1.1 p.1.2)).re))-
        ∑ p : SpatialPlane,
          (2-(WilsonSingleLinkStaples.character (spatialHolonomy u x p.1.1 p.1.2)).re)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x : SpatialVertex n, ∑ p : SpatialPlane, 2*D x p := by
      apply Finset.sum_le_sum
      intro x _
      rw [← Finset.sum_sub_distrib]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun p _ => h x p))
    _ = 8*length n q := by
      simp_rw [← Finset.mul_sum]
      have hi : (∑ x, ∑ p, D x p) = 4*length n q := linear_incidence n q
      rw [hi]
      ring

theorem spatial_comparison (β : ℝ) (hβ : 0 ≤ β) (q u : Slice n) :
    spatialWeight WilsonSingleLinkStaples.character β 2 (q*u) ≤
      Real.exp (4*β*length n q)*spatialWeight WilsonSingleLinkStaples.character β 2 u := by
  have h := mul_le_mul_of_nonneg_left (abs_le.mp (potential_difference n q u)).1 hβ
  unfold spatialWeight
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem ground_comparison (β : ℝ) (hβ : 0 ≤ β) (q u : Slice n) :
    ground n β hβ (q*u) ≤ Real.exp (6*β*length n q)*ground n β hβ u := by
  have hw := spatial_comparison n β hβ q u
  have hz := rowPartition_geometric n β hβ (q*u) u
  rw [rotation_cost] at hz
  have hp := mul_le_mul hw hz (rowPartition_pos n β hβ (q*u)).le
    (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  have he : (Real.exp (4*β*length n q)*spatialWeight WilsonSingleLinkStaples.character β 2 u)*
      (Real.exp (2*β*length n q)*rowPartition n β hβ u) =
      Real.exp (6*β*length n q)*
        (spatialWeight WilsonSingleLinkStaples.character β 2 u*rowPartition n β hβ u) := by
    rw [show 6*β*length n q = 4*β*length n q+2*β*length n q by ring, Real.exp_add]
    ring
  rw [he, rowPartition_ground, rowPartition_ground] at hp
  have ht := (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1
  nlinarith

/-- The actual joint log-ground increment is bounded without a global density-ratio constant. -/
theorem log_gain_bound (β : ℝ) (hβ : 0 ≤ β) (q u : Slice n) :
    |WilsonJointEntropy.logGain n β hβ q u| ≤ 6*β*length n q := by
  have hp := Real.log_le_log (ground_pos n β hβ (q*u)) (ground_comparison n β hβ q u)
  rw [Real.log_mul (Real.exp_pos _).ne' (ground_pos n β hβ u).ne', Real.log_exp] at hp
  have hm := ground_comparison n β hβ q⁻¹ (q*u)
  rw [inv_mul_cancel_left, length_inv] at hm
  have hh := Real.log_le_log (ground_pos n β hβ u) hm
  rw [Real.log_mul (Real.exp_pos _).ne' (ground_pos n β hβ (q*u)).ne', Real.log_exp] at hh
  unfold WilsonJointEntropy.logGain
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end
end UnifiedTheory.Clay.YangMills.WilsonJointGroundLipschitz
