/- Volume-independent continuous-observable Poincare and color-variance
factorization for the actual strong-coupling Wilson resampling law. These
are auxiliary heat-bath estimates, not a physical transfer mass gap. -/
import UnifiedTheory.Clay.YangMills.WilsonParallelContraction
import UnifiedTheory.Clay.YangMills.ContinuousUpdateGap
import UnifiedTheory.Clay.YangMills.WilsonCoordinateLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonParallelPoincare
noncomputable section
open MeasureTheory WilsonParallelContraction WilsonIndependentBlocks
open WilsonCoordinateInfluence WilsonParallelColors CompactGibbsBlockUpdate

variable (n : ℕ) [NeZero n] [Fact (1 < n)]
local instance linkDecidableEq : DecidableEq (Link n) := Classical.decEq _

omit [Fact (1 < n)] in
theorem iterate_eq (β : ℝ) (heven : 2 ∣ n) (F : C(State n, ℝ)) (k : ℕ) :
    ContinuousUpdateGap.iterate (update n β heven) k F =
      ParallelOscillation.updateIterate (update n β heven) k F := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [ContinuousUpdateGap.iterate, ParallelOscillation.updateIterate, ih]

/-- Observable-dependent correlation prefactors disappear from the actual
one-step quadratic estimate. No variance inequality is supplied as a premise. -/
theorem centered_dirichlet_gap (β : ℝ) (hβ : 0 ≤ β) (heven : 2 ∣ n)
    (F : C(State n, ℝ)) (hmean : (∫ U, F U ∂law n β) = 0) :
    (1 - rate β) * (∫ U, F U ^ 2 ∂law n β) ≤
      ∫ U, F U * (F U - update n β heven F U) ∂law n β := by
  apply ContinuousUpdateGap.dirichlet_gap (law n β) (update n β heven)
    (update_reversible n β heven) F (rate β)
    (2 * Fintype.card (Link n) * ‖F‖ ^ 2) (rate_nonneg β hβ)
  intro k
  simpa only [ContinuousUpdateGap.pairing, iterate_eq] using
    centered_moment_bound n β hβ heven F hmean k

def colorResidual (β : ℝ) (heven : 2 ∣ n) (F : C(State n, ℝ)) (c : Color) : ℝ :=
  ∫ U, (F U - blockAverage SU2HaarTilt.haar (WilsonParallelKernel.stateAction n β)
    (colorBlock n heven c) F U)^2 ∂law n β

omit [Fact (1 < n)] in
/-- The auxiliary Dirichlet form is exactly the mean of the eight actual
conditional-averaging residuals, with its update clock retained. -/
theorem update_dirichlet_eq_residuals (β : ℝ) (heven : 2 ∣ n) (F : C(State n, ℝ)) :
    (∫ U, F U * (F U - update n β heven F U) ∂law n β) =
      (1 / 8 : ℝ) * ∑ c : Color, colorResidual n β heven F c := by
  have he (U : State n) : F U * (F U - update n β heven F U) =
      (1 / 8 : ℝ) * ∑ c : Color,
        F U * (F U - blockAverage SU2HaarTilt.haar (WilsonParallelKernel.stateAction n β)
          (colorBlock n heven c) F U) := by
    rw [update_apply]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, color_card,
      nsmul_eq_mul, ← Finset.mul_sum]
    ring
  simp_rw [he]
  rw [integral_const_mul]
  congr 1
  have hi (c : Color) : Integrable (fun U => F U *
      (F U - blockAverage SU2HaarTilt.haar (WilsonParallelKernel.stateAction n β)
        (colorBlock n heven c) F U)) (law n β) :=
    (F.continuous.mul (F.continuous.sub
      (blockAverage SU2HaarTilt.haar (WilsonParallelKernel.stateAction n β)
        (colorBlock n heven c) F).continuous)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  rw [integral_finset_sum Finset.univ (fun c _ => hi c)]
  apply Finset.sum_congr rfl
  intro c _
  exact block_dirichlet_eq_residual SU2HaarTilt.haar (WilsonParallelKernel.stateAction n β)
    (colorBlock n heven c) F

theorem centered_factorization (β : ℝ) (hβ : 0 ≤ β) (heven : 2 ∣ n)
    (F : C(State n, ℝ)) (hmean : (∫ U, F U ∂law n β) = 0) :
    (1 - 36 * β) * (∫ U, F U ^ 2 ∂law n β) ≤
      ∑ c : Color, colorResidual n β heven F c := by
  have h := centered_dirichlet_gap n β hβ heven F hmean
  rw [update_dirichlet_eq_residuals, rate] at h
  nlinarith

def centered (β : ℝ) (F : C(State n, ℝ)) : C(State n, ℝ) :=
  F - ContinuousMap.const _ (∫ U, F U ∂law n β)

omit [Fact (1 < n)] in
theorem centered_mean (β : ℝ) (F : C(State n, ℝ)) :
    (∫ U, centered n β F U ∂law n β) = 0 := by
  simp only [centered, ContinuousMap.sub_apply, ContinuousMap.const_apply]
  rw [integral_sub (F.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)) (integrable_const _)]
  simp

omit [Fact (1 < n)] in
theorem centered_residual (β : ℝ) (heven : 2 ∣ n) (F : C(State n, ℝ)) (c : Color) :
    colorResidual n β heven (centered n β F) c = colorResidual n β heven F c := by
  unfold colorResidual centered
  rw [blockAverage_sub, blockAverage_const]
  apply integral_congr_ae
  filter_upwards [] with U
  simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply]
  ring

/-- Actual Wilson variance factorization across the eight simultaneous
conditional blocks, with a constant independent of the lattice volume. -/
theorem variance_factorization (β : ℝ) (hβ : 0 ≤ β) (hsmall : β < 1 / 36)
    (heven : 2 ∣ n) (F : C(State n, ℝ)) :
    (∫ U, (F U - ∫ V, F V ∂law n β)^2 ∂law n β) ≤
      (∑ c : Color, colorResidual n β heven F c) / (1 - 36 * β) := by
  have h := centered_factorization n β hβ heven (centered n β F) (centered_mean n β F)
  simp_rw [centered_residual] at h
  change (1 - 36 * β) *
    (∫ U, (F U - ∫ V, F V ∂law n β)^2 ∂law n β) ≤ _ at h
  apply (le_div_iff₀ (by linarith : 0 < 1 - 36 * β)).mpr
  simpa only [mul_comm] using h


/-- Pullback through the proved actual Wilson coordinate equivalence. -/
def pullback (F : C(RegulatedGauge.Configuration (PeriodicLattice4.Vertex n) Q, ℝ)) :
    C(State n, ℝ) :=
  F.comp ⟨WilsonCoordinateLaw.configEquiv n, WilsonCoordinateLaw.configEquiv_continuous n⟩

/-- The variance on the left is explicitly under the original Wilson law,
not a substitute product law. The right-hand blocks are its actual resamplings. -/
theorem original_wilson_variance_factorization (β : ℝ) (hβ : 0 ≤ β)
    (hsmall : β < 1 / 36) (heven : 2 ∣ n)
    (F : C(RegulatedGauge.Configuration (PeriodicLattice4.Vertex n) Q, ℝ)) :
    (∫ U, (F U - ∫ V, F V ∂PeriodicLattice4.wilsonLaw n Q
        WilsonSingleLinkStaples.character β 2)^2
      ∂PeriodicLattice4.wilsonLaw n Q WilsonSingleLinkStaples.character β 2) ≤
      (∑ c : Color, colorResidual n β heven (pullback n F) c) / (1 - 36 * β) := by
  have hm : (∫ U, pullback n F U ∂law n β) =
      ∫ U, F U ∂PeriodicLattice4.wilsonLaw n Q WilsonSingleLinkStaples.character β 2 :=
    (WilsonCoordinateLaw.wilson_preserving n β).integral_comp
      (WilsonCoordinateLaw.configEquiv n).measurableEmbedding F
  have hv := (WilsonCoordinateLaw.wilson_preserving n β).integral_comp
    (WilsonCoordinateLaw.configEquiv n).measurableEmbedding
    (fun U => (F U - ∫ V, F V ∂PeriodicLattice4.wilsonLaw n Q
      WilsonSingleLinkStaples.character β 2)^2)
  have h := variance_factorization n β hβ hsmall heven (pullback n F)
  rw [hm] at h
  exact hv ▸ h

end
end UnifiedTheory.Clay.YangMills.WilsonParallelPoincare
