/- Beyond shared spatial plaquettes, the actual off-diagonal likelihood
Gram entry is exactly a mixed ratio of the constructed ground amplitude.
Locality of the bare action does not set this ground response to zero. -/
import UnifiedTheory.Clay.YangMills.WilsonRowGram

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonMixedGroundResponse
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonTemporalInfluence WilsonSymmetricLinkChange WilsonSlabLocalComparison WilsonRowGram

variable (n : ℕ) [NeZero n]

omit [NeZero n] in
theorem shift_commute (e d : SpatialVertex n × Fin 3) (q r : Q) (hed : e ≠ d)
    (u : Slice n) : shift n e q (shift n d r u) = shift n d r (shift n e q u) := by
  funext j
  by_cases he : j = e
  · subst j
    rw [shift_at, shift_away n d r u e hed, shift_away n d r _ e hed, shift_at]
  · by_cases hd : j = d
    · subst j
      rw [shift_away n e q _ d hed.symm, shift_at, shift_at, shift_away n e q u d hed.symm]
    · simp only [shift_away n e q _ j he, shift_away n d r _ j hd]

/-- If the affected plaquette sets are disjoint, the bare spatial mixed difference vanishes. -/
theorem potential_cross (e d : SpatialVertex n × Fin 3) (q r : Q) (hed : e ≠ d)
    (hd : Disjoint (affected n e.1 e.2) (affected n d.1 d.2)) (u : Slice n) :
    potential WilsonSingleLinkStaples.character 2 (shift n e q (shift n d r u)) +
      potential WilsonSingleLinkStaples.character 2 u =
        potential WilsonSingleLinkStaples.character 2 (shift n e q u) +
          potential WilsonSingleLinkStaples.character 2 (shift n d r u) := by
  unfold potential
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  have unchanged (a : SpatialVertex n × Fin 3) (t : Q) (z : Slice n)
      (hp : (x,p) ∉ affected n a.1 a.2) :
      spatialHolonomy (shift n a t z) x p.1.1 p.1.2 = spatialHolonomy z x p.1.1 p.1.2 :=
    holonomy_unchanged n Q a.1 a.2 (x,p) hp _ _
      (fun j hj => shift_away n a t z j hj)
  by_cases he : (x,p) ∈ affected n e.1 e.2
  · have hp : (x,p) ∉ affected n d.1 d.2 :=
      fun h => Finset.disjoint_left.mp hd he h
    rw [shift_commute n e d q r hed, unchanged d r (shift n e q u) hp, unchanged d r u hp]
  · rw [unchanged e q (shift n d r u) he, unchanged e q u he]
    ring

theorem spatialWeight_cross (β : ℝ) (e d : SpatialVertex n × Fin 3) (q r : Q)
    (hed : e ≠ d) (hd : Disjoint (affected n e.1 e.2) (affected n d.1 d.2)) (u : Slice n) :
    spatialWeight WilsonSingleLinkStaples.character β 2 (shift n e q u) *
      spatialWeight WilsonSingleLinkStaples.character β 2 (shift n d r u) =
        spatialWeight WilsonSingleLinkStaples.character β 2 u *
          spatialWeight WilsonSingleLinkStaples.character β 2 (shift n e q (shift n d r u)) := by
  have h := potential_cross n e d q r hed hd u
  unfold spatialWeight
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [← mul_add, ← mul_add, ← h]
  ring

theorem partition_as_ground (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    rowPartition n β hβ u = ‖transfer n β‖*ground n β hβ u /
      spatialWeight WilsonSingleLinkStaples.character β 2 u := by
  apply (eq_div_iff (Real.exp_pos _).ne').mpr
  rw [mul_comm]
  exact rowPartition_ground n β hβ u

/-- An exact identity for the original interacting ground, without a decay hypothesis. -/
theorem gram_ground_ratio (β : ℝ) (hβ : 0 ≤ β) (e d : SpatialVertex n × Fin 3)
    (q r : Q) (hed : e ≠ d)
    (hd : Disjoint (affected n e.1 e.2) (affected n d.1 d.2)) (u : Slice n) :
    gram n β hβ e d q r u + 1 =
      (ground n β hβ u * ground n β hβ (shift n e q (shift n d r u))) /
        (ground n β hβ (shift n e q u) * ground n β hβ (shift n d r u)) := by
  rw [gram_mixed_partition n β hβ e d q r hed]
  have hs := spatialWeight_cross n β e d q r hed hd u
  have htop := (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1.ne'
  have hw (z : Slice n) : spatialWeight WilsonSingleLinkStaples.character β 2 z ≠ 0 :=
    (Real.exp_pos _).ne'
  calc
    _ = ((ground n β hβ u * ground n β hβ (shift n e q (shift n d r u))) /
        (ground n β hβ (shift n e q u) * ground n β hβ (shift n d r u))) *
      ((spatialWeight WilsonSingleLinkStaples.character β 2 (shift n e q u) *
        spatialWeight WilsonSingleLinkStaples.character β 2 (shift n d r u)) /
      (spatialWeight WilsonSingleLinkStaples.character β 2 u *
        spatialWeight WilsonSingleLinkStaples.character β 2 (shift n e q (shift n d r u)))) := by
      simp only [partition_as_ground]
      field_simp [htop, (ground_pos n β hβ (shift n e q u)).ne',
        (ground_pos n β hβ (shift n d r u)).ne', (Real.exp_pos _).ne']
    _ = _ := by rw [hs, div_self (mul_ne_zero (hw u) (hw _)), mul_one]

def groundMixedLog (β : ℝ) (hβ : 0 ≤ β) (e d : SpatialVertex n × Fin 3)
    (q r : Q) (u : Slice n) : ℝ :=
  Real.log (ground n β hβ u) + Real.log (ground n β hβ (shift n e q (shift n d r u))) -
    Real.log (ground n β hβ (shift n e q u)) - Real.log (ground n β hβ (shift n d r u))

theorem gram_ground_log (β : ℝ) (hβ : 0 ≤ β) (e d : SpatialVertex n × Fin 3)
    (q r : Q) (hed : e ≠ d)
    (hd : Disjoint (affected n e.1 e.2) (affected n d.1 d.2)) (u : Slice n) :
    gram n β hβ e d q r u = Real.exp (groundMixedLog n β hβ e d q r u)-1 := by
  have he : Real.exp (groundMixedLog n β hβ e d q r u) =
      (ground n β hβ u * ground n β hβ (shift n e q (shift n d r u))) /
        (ground n β hβ (shift n e q u) * ground n β hβ (shift n d r u)) := by
    unfold groundMixedLog
    rw [Real.exp_sub, Real.exp_sub, Real.exp_add]
    simp only [Real.exp_log (ground_pos n β hβ _)]
    ring
  rw [he, ← gram_ground_ratio n β hβ e d q r hed hd]
  ring

end
end UnifiedTheory.Clay.YangMills.WilsonMixedGroundResponse
