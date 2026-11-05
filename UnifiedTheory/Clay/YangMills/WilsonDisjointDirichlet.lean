/-
Disjoint-support cross-Dirichlet cancellation for the actual Wilson random
color update. Product conditional measures give the factorization; actual
stationarity, reversibility and idempotence supply the pairing identity.
No covariance-decay or mixing estimate is assumed.
-/
import UnifiedTheory.Clay.YangMills.CoordinateSupport
import UnifiedTheory.Clay.YangMills.WilsonParallelContraction

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonDisjointDirichlet
noncomputable section
open MeasureTheory WilsonIndependentBlocks WilsonCoordinateInfluence
open WilsonParallelContraction WilsonParallelColors CompactGibbsBlockUpdate

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (Link n) := Classical.decEq _
local instance coordinateProbability (β : ℝ) (a : Link n) (U : State n) :
    IsProbabilityMeasure (coordinateLaw n β U a) := coordinateLaw_probability n β U a

/-- Disjointly supported observables factor under every actual independent Wilson block update. -/
theorem blockAverage_mul_of_disjoint (β : ℝ) (B : Finset (Link n))
    (hB : Independent n B) (S T : Finset (Link n)) (hST : Disjoint S T)
    (F G : C(State n, ℝ)) (hF : DependsOn (F : State n → ℝ) (S : Set (Link n)))
    (hG : DependsOn (G : State n → ℝ) (T : Set (Link n))) :
    blockAverage SU2HaarTilt.haar (WilsonParallelKernel.stateAction n β) B (F * G) =
      blockAverage SU2HaarTilt.haar (WilsonParallelKernel.stateAction n β) B F *
        blockAverage SU2HaarTilt.haar (WilsonParallelKernel.stateAction n β) B G := by
  ext U
  simp only [ContinuousMap.mul_apply]
  rw [WilsonParallelKernel.blockAverage_eq_parallelAverage n β U B hB (F * G),
    WilsonParallelKernel.blockAverage_eq_parallelAverage n β U B hB F,
    WilsonParallelKernel.blockAverage_eq_parallelAverage n β U B hB G]
  exact CoordinateSupport.integral_mul_of_disjoint
    (ParallelOscillation.updateMarginal (fun a V => coordinateLaw n β V a) B U)
    S T hST F G F.continuous G.continuous hF hG

/-- Projection and stationarity turn the conditional product identity into a pairing identity. -/
theorem block_pairing_of_disjoint (β : ℝ) (B : Finset (Link n))
    (hB : Independent n B) (S T : Finset (Link n)) (hST : Disjoint S T)
    (F G : C(State n, ℝ)) (hF : DependsOn (F : State n → ℝ) (S : Set (Link n)))
    (hG : DependsOn (G : State n → ℝ) (T : Set (Link n))) :
    (∫ U, F U * blockAverage SU2HaarTilt.haar
      (WilsonParallelKernel.stateAction n β) B G U ∂law n β) =
        ∫ U, F U * G U ∂law n β := by
  have hs := blockAverage_stationary SU2HaarTilt.haar
    (WilsonParallelKernel.stateAction n β) B (F * G)
  rw [blockAverage_mul_of_disjoint n β B hB S T hST F G hF hG] at hs
  have hr := blockAverage_reversible SU2HaarTilt.haar
    (WilsonParallelKernel.stateAction n β) B F
    (blockAverage SU2HaarTilt.haar (WilsonParallelKernel.stateAction n β) B G)
  rw [blockAverage_idempotent] at hr
  exact hr.trans hs

/-- A random color update has zero cross-energy between disjointly supported tests. -/
theorem update_pairing_of_disjoint (β : ℝ) (heven : 2 ∣ n)
    (S T : Finset (Link n)) (hST : Disjoint S T)
    (F G : C(State n, ℝ)) (hF : DependsOn (F : State n → ℝ) (S : Set (Link n)))
    (hG : DependsOn (G : State n → ℝ) (T : Set (Link n))) :
    (∫ U, F U * update n β heven G U ∂law n β) =
      ∫ U, F U * G U ∂law n β := by
  have he (U : State n) : F U * update n β heven G U =
      (1 / 8 : ℝ) * ∑ c : Color, F U *
        blockAverage SU2HaarTilt.haar (WilsonParallelKernel.stateAction n β)
          (colorBlock n heven c) G U := by
    rw [update_apply, ← mul_assoc, mul_comm (F U) (1 / 8), mul_assoc, Finset.mul_sum]
  simp_rw [he]
  rw [integral_const_mul]
  have hi (c : Color) : Integrable (fun U : State n => F U *
      blockAverage SU2HaarTilt.haar (WilsonParallelKernel.stateAction n β)
        (colorBlock n heven c) G U) (law n β) :=
    (F.continuous.mul (blockAverage SU2HaarTilt.haar (WilsonParallelKernel.stateAction n β)
      (colorBlock n heven c) G).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  rw [integral_finset_sum Finset.univ (fun c _ => hi c)]
  simp_rw [block_pairing_of_disjoint n β _ (colorBlock_independent n heven _) S T hST F G hF hG]
  simp only [Finset.sum_const, Finset.card_univ, color_card, nsmul_eq_mul]
  ring

/-- The requested exact cross-Dirichlet cancellation in the original Wilson law. -/
theorem cross_dirichlet_zero (β : ℝ) (heven : 2 ∣ n)
    (S T : Finset (Link n)) (hST : Disjoint S T)
    (F G : C(State n, ℝ)) (hF : DependsOn (F : State n → ℝ) (S : Set (Link n)))
    (hG : DependsOn (G : State n → ℝ) (T : Set (Link n))) :
    (∫ U, F U * (G U - update n β heven G U) ∂law n β) = 0 := by
  have hi : Integrable (fun U : State n => F U * G U) (law n β) :=
    (F.continuous.mul G.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hj : Integrable (fun U : State n => F U * update n β heven G U) (law n β) :=
    (F.continuous.mul (update n β heven G).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp_rw [mul_sub]
  rw [integral_sub hi hj, update_pairing_of_disjoint n β heven S T hST F G hF hG, sub_self]

/-- Reversibility moves the exact cancellation to the first observable for telescoping. -/
theorem disjoint_pairing_eq_update (β : ℝ) (heven : 2 ∣ n)
    (S T : Finset (Link n)) (hST : Disjoint S T)
    (F G : C(State n, ℝ)) (hF : DependsOn (F : State n → ℝ) (S : Set (Link n)))
    (hG : DependsOn (G : State n → ℝ) (T : Set (Link n))) :
    (∫ U, F U * G U ∂law n β) =
      ∫ U, update n β heven F U * G U ∂law n β := by
  rw [← update_reversible]
  exact (update_pairing_of_disjoint n β heven S T hST F G hF hG).symm

end
end UnifiedTheory.Clay.YangMills.WilsonDisjointDirichlet
