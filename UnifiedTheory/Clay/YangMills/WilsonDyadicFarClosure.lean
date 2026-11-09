/- A precise polynomial-decay target for the distant mixed-ground sum.
The torus counting, source integration, nonlinear ratio, and boundary limit
are proved. The displayed decay of actual tilted covariances remains an
analytic hypothesis; neither it nor global coercivity is asserted here. -/
import UnifiedTheory.Clay.YangMills.SpatialDyadicSummation
import UnifiedTheory.Clay.YangMills.WilsonBoundaryDecayBudget

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonDyadicFarClosure
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonBoundaryConnected WilsonBoundaryMixedLimit
open WilsonBoundaryDecayBudget WilsonSpatialGramNeighborhood
open WilsonPhysicalVariance WilsonVarianceResponse WilsonDissipationIteration

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

def logEntry (β : ℝ) (j : ℕ) (rotations : Slice n) (u : Slice n)
    (e d : SpatialVertex n × Fin 3) : ℝ :=
  if d ∈ near n e then 0 else |mixedLog n β j e d (rotations e) (rotations d) u|

theorem logEntry_nonneg (β : ℝ) (j : ℕ) (rotations : Slice n) (u : Slice n)
    (e d : SpatialVertex n × Fin 3) : 0 ≤ logEntry n β j rotations u e d := by
  unfold logEntry
  split
  · exact le_rfl
  · exact abs_nonneg _

theorem logEntry_sum (β : ℝ) (j : ℕ) (rotations : Slice n) (u : Slice n)
    (e : SpatialVertex n × Fin 3) :
    (∑ d, logEntry n β j rotations u e d) =
      ∑ d ∈ Finset.univ \ near n e, |mixedLog n β j e d (rotations e) (rotations d) u| := by
  simp only [logEntry, Finset.sum_ite, Finset.sum_const_zero, zero_add]
  congr 1
  ext d
  simp

/-- This bound includes every distant entry, not just bad bridges or selected clusters. -/
theorem boundaryFar_of_log_decay (β : ℝ) (j : ℕ) (rotations : Slice n)
    (u : Slice n) (e : SpatialVertex n × Fin 3) (M C : ℝ) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hlocal : ∀ d, d ∉ near n e →
      |mixedLog n β j e d (rotations e) (rotations d) u| ≤ M)
    (hdecay : ∀ k d, d ∉ near n e → d ∉ SpatialDyadicSummation.ball n (2 ^ k) e →
      |mixedLog n β j e d (rotations e) (rotations d) u| ≤ C * (1 / 16 : ℝ) ^ k) :
    boundaryFar n β j rotations u e ≤ Real.exp M * (81 * M + 750 * C) := by
  have hs := SpatialDyadicSummation.sum_bound n (logEntry n β j rotations u e) M C hM hC e
    (fun d _ => by
      unfold logEntry
      split
      · exact hM
      · exact hlocal d ‹_›)
    (fun k d hd => by
      unfold logEntry
      split
      · positivity
      · exact hdecay k d ‹_› hd)
  rw [logEntry_sum] at hs
  calc
    _ ≤ ∑ d ∈ Finset.univ \ near n e,
        Real.exp M * |mixedLog n β j e d (rotations e) (rotations d) u| := by
      apply Finset.sum_le_sum
      intro d hd
      have hdn := (Finset.mem_sdiff.mp hd).2
      exact boundaryRatio_bound n β j e d _ _ (far_ne n e d hdn)
        (far_disjoint n e d hdn) u M (hlocal d hdn)
    _ = Real.exp M *
        ∑ d ∈ Finset.univ \ near n e, |mixedLog n β j e d (rotations e) (rotations d) u| :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (Real.exp_pos M).le

/-- Only the stated connected-covariance decay remains conditional here.
The all-distance logarithmic cap four follows from the actual action. -/
theorem boundaryFar_of_connected_decay (β : ℝ) (hβ : 0 ≤ β) (j : ℕ)
    (rotations : Slice n) (hscale : ∀ d, β * ‖(rotations d : Quaternion ℝ) - 1‖ ≤ 1)
    (u : Slice n) (e : SpatialVertex n × Fin 3) (C : ℝ) (hC : 0 ≤ C)
    (hdecay : ∀ k d, d ∉ near n e → d ∉ SpatialDyadicSummation.ball n (2 ^ k) e →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |connected n β j e d (rotations e) (rotations d) u s t| ≤
          C * (1 / 16 : ℝ) ^ k) :
    boundaryFar n β j rotations u e ≤ Real.exp 4 * (324 + 750 * C) := by
  rw [show (324 : ℝ) = 81 * 4 by norm_num]
  apply boundaryFar_of_log_decay n β j rotations u e 4 C (by norm_num) hC
  · intro d hd
    exact mixedLog_scaled n β hβ j e d _ _ (far_ne n e d hd) u (hscale e) (hscale d)
  · intro k d hd hball
    exact mixedLog_of_connected n β j e d _ _ (far_ne n e d hd) u _ (hdecay k d hd hball)

/-- Uniformity in finite boundary depth suffices to pass to the constructed
ground. No uniform boundary-convergence rate is being used. -/
theorem groundFar_of_connected_decay (β : ℝ) (hβ : 0 ≤ β)
    (rotations : Slice n) (hscale : ∀ d, β * ‖(rotations d : Quaternion ℝ) - 1‖ ≤ 1)
    (u : Slice n) (e : SpatialVertex n × Fin 3) (C : ℝ) (hC : 0 ≤ C)
    (hdecay : ∀ j k d, d ∉ near n e → d ∉ SpatialDyadicSummation.ball n (2 ^ k) e →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |connected n β j e d (rotations e) (rotations d) u s t| ≤
          C * (1 / 16 : ℝ) ^ k) :
    WilsonGramNearFar.farCost n β hβ rotations u e ≤ Real.exp 4 * (324 + 750 * C) :=
  far_bound_of_boundary n β hβ rotations u e _ (fun j =>
    boundaryFar_of_connected_decay n β hβ j rotations hscale u e C hC (hdecay j))

/-- A complete original-transfer upper estimate, conditional on the displayed
polynomial decay. It supplies no independent lower coercivity estimate. -/
theorem energy_le_loss_of_connected_decay (β : ℝ) (hβ : 0 ≤ β)
    (rotations : Slice n) (hscale : ∀ d, β * ‖(rotations d : Quaternion ℝ) - 1‖ ≤ 1)
    (C : ℝ) (hC : 0 ≤ C)
    (hdecay : ∀ u e j k d, d ∉ near n e → d ∉ SpatialDyadicSummation.ball n (2 ^ k) e →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |connected n β j e d (rotations e) (rotations d) u s t| ≤
          C * (1 / 16 : ℝ) ^ k)
    (f : C(Slice n, ℝ)) :
    WilsonCollectiveGram.energy n β hβ id rotations (fun _ => 1) (step n β hβ f) ≤
      (16 * (Real.exp 4 - 1) ^ 2 + Real.exp 4 * (324 + 750 * C)) * loss n β hβ f :=
  WilsonGramNearFar.energy_le_loss_of_far n β hβ rotations _ _ (sq_nonneg _) (by positivity)
    (fun d => coefficient_scaled β hβ (rotations d) (hscale d))
    (fun u e => groundFar_of_connected_decay n β hβ rotations hscale u e C hC (hdecay u e)) f

end
end UnifiedTheory.Clay.YangMills.WilsonDyadicFarClosure
