/- Exact extensive conditional noise under the original interacting Wilson law.
Eight independent color classes yield a lower bound on full source variance,
without a coupling-smallness or global mixing hypothesis. -/
import UnifiedTheory.Clay.YangMills.SU2RetainedCovariance
import UnifiedTheory.Clay.YangMills.WilsonParallelPoincare

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonIndependentVariance
noncomputable section
open MeasureTheory PeriodicLattice4 WilsonIndependentBlocks
open CompactGibbsBlockUpdate

section Variance
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem covariance_sub_const (F : X → ℝ) (hF : Continuous F) (c : ℝ) :
    GibbsCrossCovariance.covariance μ (fun x => F x - c) (fun x => F x - c) =
      GibbsCrossCovariance.covariance μ F F := by
  unfold GibbsCrossCovariance.covariance
  rw [GibbsCrossCovariance.centered_product μ F F hF hF c c]
  rw [integral_sub (hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (integrable_const c)]
  simp only [integral_const, probReal_univ, one_smul]
  ring

/-- Any identity subtraction leaves at least the connected variance. -/
theorem covariance_le_square_shift (F : X → ℝ) (hF : Continuous F) (c : ℝ) :
    GibbsCrossCovariance.covariance μ F F ≤ ∫ x, (F x - c)^2 ∂μ := by
  have h := GibbsCrossCovariance.centered_product μ F F hF hF c c
  simp only [← pow_two] at h
  unfold GibbsCrossCovariance.covariance
  simp only [← pow_two]
  nlinarith [sq_nonneg ((∫ x, F x ∂μ) - c)]

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] in
theorem source_covariance_zero (A F : X → ℝ) :
    CompactGibbsSource.covariance μ A F F F 0 =
      GibbsCrossCovariance.covariance (CompactGibbsContinuity.law μ A) F F := by
  have he : CompactGibbsSource.action A F 0 = A := by
    funext x
    simp [CompactGibbsSource.action]
  simp only [CompactGibbsSource.covariance, CompactGibbsSource.expectation, he,
    GibbsCrossCovariance.covariance]
end Variance

abbrev Q := SU2QuaternionEquivalence.UnitQuaternion
abbrev State (n : ℕ) := Link n → Q
variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (Link n) := Classical.decEq _
local instance edgeDecidableEq : DecidableEq (RegulatedGauge.Edge (Vertex n)) := Classical.decEq _

/-- The actual full plaquette source in positive-link coordinates. -/
def sourceMap (f : PlaquetteIndex n → ℝ) : C(State n, ℝ) :=
  ⟨fun U => WilsonBlockIntegration.source n Q WilsonSingleLinkStaples.character 2 f
    (WilsonCoordinateInfluence.toConfiguration n U),
    (WilsonBlockIntegration.source_continuous n Q WilsonSingleLinkStaples.character
      WilsonSingleLinkStaples.character_continuous 2 f).comp
      (continuous_pi (fun e => continuous_apply (edgeCoord n e)))⟩

/-- Each selected Hessian summand is exactly the original one-link conditional variance. -/
theorem local_covariance (β : ℝ) (f : PlaquetteIndex n → ℝ) (U : State n)
    (S : Finset (Link n)) (a : Link n) :
    CompactGibbsSource.covariance SU2HaarTilt.haar
      (WilsonBlockIntegration.localAction n Q WilsonSingleLinkStaples.character β 2
        (WilsonCoordinateInfluence.toConfiguration n U) S a)
      (WilsonBlockIntegration.localSource n Q WilsonSingleLinkStaples.character 2 f
        (WilsonCoordinateInfluence.toConfiguration n U) S a)
      (WilsonBlockIntegration.localSource n Q WilsonSingleLinkStaples.character 2 f
        (WilsonCoordinateInfluence.toConfiguration n U) S a)
      (WilsonBlockIntegration.localSource n Q WilsonSingleLinkStaples.character 2 f
        (WilsonCoordinateInfluence.toConfiguration n U) S a) 0 =
      if a ∈ S then SU2AnnealedVariance.originalVariance n a.1 a.2 β f
        (WilsonCoordinateInfluence.toConfiguration n U) else 0 := by
  rw [source_covariance_zero, WilsonParallelKernel.localAction_law]
  by_cases ha : a ∈ S
  · rw [if_pos ha, if_pos ha]
    let ν := WilsonCoordinateInfluence.coordinateLaw n β U a
    letI : IsProbabilityMeasure ν := WilsonCoordinateInfluence.coordinateLaw_probability n β U a
    let r := SU2StarEnergy.exterior n a.1 a.2 (WilsonCoordinateInfluence.toConfiguration n U)
    let H : Q → ℝ := fun q => SU2WilsonConditionalSource.splitSource n a.1 a.2 f (r, q)
    have hH : Continuous H :=
      (SU2WilsonConditionalSource.splitSource_continuous n a.1 a.2 f).comp
        (continuous_const.prodMk continuous_id)
    have he : WilsonBlockIntegration.localSource n Q WilsonSingleLinkStaples.character 2 f
        (WilsonCoordinateInfluence.toConfiguration n U) S a =
      fun q => H q - sourceMap n f U := by
      funext q
      unfold WilsonBlockIntegration.localSource
      rw [if_pos ha]
      dsimp only [H, SU2WilsonConditionalSource.splitSource, r]
      rw [WilsonParallelKernel.assemble_exterior_update]
      rfl
    rw [he, covariance_sub_const ν H hH]
    rw [GibbsCrossCovariance.covariance_eq_centered ν H H hH hH]
    change (∫ q, (H q - ∫ z, H z ∂ν) * (H q - ∫ z, H z ∂ν) ∂ν) = _
    have hm : SU2WilsonConditionalSource.conditionalSource n a.1 a.2 β f r =
        ∫ q, H q ∂ν :=
      SU2WilsonConditionalSource.conditionalSource_eq_integral n a.1 a.2 β f r
    rw [← hm]
    simp only [← pow_two]
    rfl
  · rw [if_neg ha, if_neg ha]
    simp only [WilsonBlockIntegration.localSource, if_neg ha,
      GibbsCrossCovariance.covariance, mul_zero, integral_zero, sub_zero]

/-- A conditional block covariance is computed using the genuine full-fiber action. -/
theorem block_covariance_sum (β : ℝ) (f : PlaquetteIndex n → ℝ) (U : State n)
    (S : Finset (Link n)) (hS : Independent n S) :
    blockAverage SU2HaarTilt.haar (WilsonParallelKernel.stateAction n β) S
        (sourceMap n f * sourceMap n f) U -
      (blockAverage SU2HaarTilt.haar (WilsonParallelKernel.stateAction n β) S
        (sourceMap n f) U)^2 =
      ∑ a ∈ S, SU2AnnealedVariance.originalVariance n a.1 a.2 β f
        (WilsonCoordinateInfluence.toConfiguration n U) := by
  have h := WilsonBlockIntegration.fiber_covariance_eq_sum n Q
    WilsonSingleLinkStaples.character WilsonSingleLinkStaples.character_continuous β 2 f
    (WilsonCoordinateInfluence.toConfiguration n U) S hS 0
  rw [source_covariance_zero] at h
  simp_rw [local_covariance n β f U S] at h
  simp only [Finset.sum_ite_mem, Finset.univ_inter] at h
  rw [CompactGibbsBlockFiber.blockAverage_full_fiber,
    CompactGibbsBlockFiber.blockAverage_full_fiber]
  change (∫ W, (sourceMap n f (WilsonParallelKernel.overwrite n U S W)) *
      (sourceMap n f (WilsonParallelKernel.overwrite n U S W))
      ∂CompactGibbsContinuity.law (Measure.pi (fun _ : Link n => SU2HaarTilt.haar))
        (fun W => WilsonParallelKernel.stateAction n β
          (WilsonParallelKernel.overwrite n U S W))) -
    (∫ W, sourceMap n f (WilsonParallelKernel.overwrite n U S W)
      ∂CompactGibbsContinuity.law (Measure.pi (fun _ : Link n => SU2HaarTilt.haar))
        (fun W => WilsonParallelKernel.stateAction n β
          (WilsonParallelKernel.overwrite n U S W)))^2 = _
  simp only [sourceMap, ContinuousMap.coe_mk, WilsonParallelKernel.stateAction,
    WilsonParallelKernel.toConfiguration_overwrite]
  simpa only [GibbsCrossCovariance.covariance, pow_two] using h


/-- An actual conditional block can discard no more than the full variance.
This is total variance under the constructed law, with no tensorization hypothesis. -/
theorem block_variance_mean_le (β : ℝ) (S : Finset (Link n)) (F : C(State n, ℝ)) :
    (∫ U, blockAverage SU2HaarTilt.haar (WilsonParallelKernel.stateAction n β) S (F * F) U -
        (blockAverage SU2HaarTilt.haar (WilsonParallelKernel.stateAction n β) S F U)^2
      ∂WilsonParallelContraction.law n β) ≤
      GibbsCrossCovariance.covariance (WilsonParallelContraction.law n β) F F := by
  let A := WilsonParallelKernel.stateAction n β
  let ν := WilsonParallelContraction.law n β
  let H := blockAverage SU2HaarTilt.haar A S F
  let m := ∫ U, F U ∂ν
  have hm : (∫ U, H U ∂ν) = m := blockAverage_stationary SU2HaarTilt.haar A S F
  have hsq : m^2 ≤ ∫ U, (H U)^2 ∂ν := by
    have h := GibbsCrossCovariance.centered_product ν H H H.continuous H.continuous m m
    rw [hm] at h
    have hp : 0 ≤ ∫ U, (H U - m) * (H U - m) ∂ν :=
      integral_nonneg (fun U => mul_self_nonneg (H U - m))
    simp only [← pow_two] at h hp
    nlinarith
  have hiH : Integrable (fun U => (H U)^2) ν :=
    (H.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiQ : Integrable (fun U => blockAverage SU2HaarTilt.haar A S (F * F) U) ν :=
    (blockAverage SU2HaarTilt.haar A S (F * F)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ U, blockAverage SU2HaarTilt.haar A S (F * F) U - (H U)^2 ∂ν) ≤ _
  have hstat : (∫ U, blockAverage SU2HaarTilt.haar A S (F * F) U ∂ν) =
      ∫ U, (F * F) U ∂ν := blockAverage_stationary SU2HaarTilt.haar A S (F * F)
  rw [integral_sub hiQ hiH, hstat]
  change (∫ U, F U * F U ∂ν) - (∫ U, (H U)^2 ∂ν) ≤
    (∫ U, F U * F U ∂ν) - m * m
  nlinarith

/-- Sum of true one-link conditional variances for an independent block is
bounded by the source variance under the original Wilson law. -/
theorem independent_variance_sum (β : ℝ) (f : PlaquetteIndex n → ℝ)
    (S : Finset (Link n)) (hS : Independent n S) :
    (∑ a ∈ S, ∫ U, SU2AnnealedVariance.originalVariance n a.1 a.2 β f U
      ∂wilsonLaw n Q WilsonSingleLinkStaples.character β 2) ≤
      GibbsCrossCovariance.covariance (wilsonLaw n Q WilsonSingleLinkStaples.character β 2)
        (WilsonBlockIntegration.source n Q WilsonSingleLinkStaples.character 2 f)
        (WilsonBlockIntegration.source n Q WilsonSingleLinkStaples.character 2 f) := by
  have h := block_variance_mean_le n β S (sourceMap n f)
  simp_rw [block_covariance_sum n β f _ S hS] at h
  have hi (a : Link n) : Integrable (fun U => SU2AnnealedVariance.originalVariance
      n a.1 a.2 β f (WilsonCoordinateInfluence.toConfiguration n U))
      (WilsonParallelContraction.law n β) :=
    ((SU2AnnealedVariance.originalVariance_continuous n a.1 a.2 β f).comp
      (continuous_pi (fun e => continuous_apply (edgeCoord n e)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_finset_sum S (fun a _ => hi a)] at h
  simp_rw [show ∀ a : Link n, (∫ U, SU2AnnealedVariance.originalVariance n a.1 a.2 β f
      (WilsonCoordinateInfluence.toConfiguration n U) ∂WilsonParallelContraction.law n β) =
      ∫ U, SU2AnnealedVariance.originalVariance n a.1 a.2 β f U
        ∂wilsonLaw n Q WilsonSingleLinkStaples.character β 2 from
    fun a => WilsonCoordinateLaw.coordinate_integral n β _] at h
  convert h using 1
  unfold GibbsCrossCovariance.covariance
  change _ = (∫ U, (WilsonBlockIntegration.source n Q WilsonSingleLinkStaples.character 2 f
      (WilsonCoordinateInfluence.toConfiguration n U)) *
      (WilsonBlockIntegration.source n Q WilsonSingleLinkStaples.character 2 f
      (WilsonCoordinateInfluence.toConfiguration n U)) ∂WilsonParallelContraction.law n β) -
    (∫ U, WilsonBlockIntegration.source n Q WilsonSingleLinkStaples.character 2 f
      (WilsonCoordinateInfluence.toConfiguration n U) ∂WilsonParallelContraction.law n β) *
    (∫ U, WilsonBlockIntegration.source n Q WilsonSingleLinkStaples.character 2 f
      (WilsonCoordinateInfluence.toConfiguration n U) ∂WilsonParallelContraction.law n β)
  unfold WilsonParallelContraction.law
  rw [WilsonCoordinateLaw.coordinate_integral n β
    (fun U => WilsonBlockIntegration.source n Q WilsonSingleLinkStaples.character 2 f U *
      WilsonBlockIntegration.source n Q WilsonSingleLinkStaples.character 2 f U),
    WilsonCoordinateLaw.coordinate_integral n β
      (WilsonBlockIntegration.source n Q WilsonSingleLinkStaples.character 2 f)]

/-- All eight independent colors aggregate the actual conditional noise.
There is no small-coupling restriction and no factor growing with volume. -/
theorem all_link_variance_sum (β : ℝ) (f : PlaquetteIndex n → ℝ) (heven : 2 ∣ n) :
    (∑ a : Link n, ∫ U, SU2AnnealedVariance.originalVariance n a.1 a.2 β f U
      ∂wilsonLaw n Q WilsonSingleLinkStaples.character β 2) ≤
      8 * GibbsCrossCovariance.covariance
        (wilsonLaw n Q WilsonSingleLinkStaples.character β 2)
        (WilsonBlockIntegration.source n Q WilsonSingleLinkStaples.character 2 f)
        (WilsonBlockIntegration.source n Q WilsonSingleLinkStaples.character 2 f) := by
  classical
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset WilsonParallelColors.Color))
    (fun c _ => independent_variance_sum n β f
      (WilsonParallelColors.colorBlock n heven c)
      (WilsonParallelColors.colorBlock_independent n heven c))
  rw [Finset.sum_const, Finset.card_univ, WilsonParallelColors.color_card, nsmul_eq_mul] at h
  convert h using 1
  simp only [WilsonParallelColors.colorBlock, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp


/-- Actual extensive conditional noise survives any scalar renormalization
and any identity counterterm. No centering or small-coupling premise is imposed. -/
theorem renormalized_second_moment_lower (β Z c : ℝ) (f : PlaquetteIndex n → ℝ)
    (heven : 2 ∣ n) :
    Z^2 * (∑ a : Link n, ∫ U, SU2AnnealedVariance.originalVariance n a.1 a.2 β f U
      ∂wilsonLaw n Q WilsonSingleLinkStaples.character β 2) ≤
      8 * ∫ U, (Z * WilsonBlockIntegration.source n Q
        WilsonSingleLinkStaples.character 2 f U - c)^2
        ∂wilsonLaw n Q WilsonSingleLinkStaples.character β 2 := by
  let ν := wilsonLaw n Q WilsonSingleLinkStaples.character β 2
  let F := WilsonBlockIntegration.source n Q WilsonSingleLinkStaples.character 2 f
  letI : IsProbabilityMeasure ν := wilsonLaw_probability n Q WilsonSingleLinkStaples.character
    WilsonSingleLinkStaples.character_continuous β 2
  have hF : Continuous F := WilsonBlockIntegration.source_continuous n Q
    WilsonSingleLinkStaples.character WilsonSingleLinkStaples.character_continuous 2 f
  have h := mul_le_mul_of_nonneg_left (all_link_variance_sum n β f heven) (sq_nonneg Z)
  have hu := covariance_le_square_shift ν (fun U => Z * F U) (continuous_const.mul hF) c
  have hs : GibbsCrossCovariance.covariance ν (fun U => Z * F U) (fun U => Z * F U) =
      Z^2 * GibbsCrossCovariance.covariance ν F F := by
    rw [GibbsCrossCovariance.covariance_scale]
    ring
  rw [hs] at hu
  change Z^2 * (∑ a : Link n, ∫ U, SU2AnnealedVariance.originalVariance n a.1 a.2 β f U
    ∂ν) ≤ 8 * ∫ U, (Z * F U - c)^2 ∂ν
  change Z^2 * (∑ a : Link n, ∫ U, SU2AnnealedVariance.originalVariance n a.1 a.2 β f U
    ∂ν) ≤ Z^2 * (8 * GibbsCrossCovariance.covariance ν F F) at h
  nlinarith

end
end UnifiedTheory.Clay.YangMills.WilsonIndependentVariance
