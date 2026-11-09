/- Stabilized actual Wilson interactions and their genuine integration towers.
The positive star remainder is retained; the negative part is removed at a
uniform cost 27/(32*beta) per corrected link. This one initial perturbation is
not amplified by arbitrary later exact integrations. No new corrections at
later stages, extensive physical-scale limit or continuum mass gap is proved. -/
import UnifiedTheory.Clay.YangMills.SU2StableStarRemainder
import UnifiedTheory.Clay.YangMills.GibbsOrderedPerturbation
import UnifiedTheory.Clay.YangMills.WilsonStarApproximationProbability
import UnifiedTheory.Clay.YangMills.WilsonFactorTower

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonStabilizedIntegration
noncomputable section
open MeasureTheory Filter RegulatedGauge PeriodicLattice4 WilsonSingleLinkStaples
open WilsonUniformVariance WilsonIndependentBlocks SU2StarEnergy SU2StableStarRemainder
open GibbsCoordinateTower GibbsOrderedPerturbation WilsonFactorTower
open scoped Quaternion Topology

variable (n : ℕ) [NeZero n] [Fact (1 < n)]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

def penaltySum (S : Finset (Link n)) (β : ℝ) (U : Configuration (Vertex n) Q) : ℝ :=
  ∑ e ∈ S, penalty β (stapleField n e.1 e.2 U)

omit [Fact (1 < n)] in
theorem penaltySum_continuous (S : Finset (Link n)) (β : ℝ) :
    Continuous (penaltySum n S β) := by
  unfold penaltySum
  exact continuous_finset_sum S (fun e _ =>
    (penalty_continuous β).comp (stapleField_continuous n e.1 e.2))

def budget (S : Finset (Link n)) (β : ℝ) : ℝ := S.card * (27 / (32 * β))

omit [NeZero n] in
theorem penaltySum_bounds (S : Finset (Link n)) (β : ℝ) (hβ : 3 / 2 ≤ β)
    (U : Configuration (Vertex n) Q) : penaltySum n S β U ∈ Set.Icc 0 (budget n S β) := by
  constructor
  · exact Finset.sum_nonneg (fun e _ =>
      (penalty_bounds β hβ _ (stapleField_norm_le_six n e.1 e.2 U)).1)
  · have h := Finset.sum_le_sum (s := S) (fun e _ =>
      (penalty_bounds β hβ _ (stapleField_norm_le_six n e.1 e.2 U)).2)
    simpa only [Finset.sum_const, nsmul_eq_mul] using h

/-- This is the original full Wilson action with the displayed local penalty. -/
def stabilizedAction (S : Finset (Link n)) (β : ℝ) : C(Configuration (Vertex n) Q, ℝ) :=
  ⟨fun U => initialAction n β U + penaltySum n S β U,
    (initialAction n β).continuous.add (penaltySum_continuous n S β)⟩

omit [Fact (1 < n)] in
theorem action_difference (S : Finset (Link n)) (β : ℝ) (U : Configuration (Vertex n) Q) :
    stabilizedAction n S β U - initialAction n β U = penaltySum n S β U := by
  change initialAction n β U + penaltySum n S β U - initialAction n β U = _
  ring

/-- A boundary penalty passes through the literal one-link integral exactly. -/
theorem one_link_effectiveAction (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (r : Exterior n Q x μ) :
    GibbsMarginalTower.effectiveAction SU2HaarTilt.haar
      (fun z : Exterior n Q x μ × Q => SU2WilsonConditionalSource.splitAction n x μ β z +
        penalty β (exteriorStaple n x μ z.1)) r =
      β * exteriorSourceConstant n x μ r (fun _ => 1) +
        stabilizedPotential β (exteriorStaple n x μ r) := by
  have hf : GibbsMarginalTower.fiberMass SU2HaarTilt.haar
      (fun z : Exterior n Q x μ × Q => SU2WilsonConditionalSource.splitAction n x μ β z +
        penalty β (exteriorStaple n x μ z.1)) r =
      Real.exp (-penalty β (exteriorStaple n x μ r)) *
        GibbsMarginalTower.fiberMass SU2HaarTilt.haar
          (SU2WilsonConditionalSource.splitAction n x μ β) r := by
    unfold GibbsMarginalTower.fiberMass
    simp_rw [neg_add, Real.exp_add]
    rw [integral_mul_const]
    ring
  rw [GibbsMarginalTower.effectiveAction, hf,
    Real.log_mul (Real.exp_ne_zero _)
      (GibbsMarginalTower.fiberMass_positive SU2HaarTilt.haar _
        (SU2WilsonConditionalSource.splitAction_continuous n x μ β) r).ne', Real.log_exp]
  have he := SU2InducedAction.wilson_effectiveAction n x μ β r
  unfold GibbsMarginalTower.effectiveAction at he
  have hs := stabilized_difference β (exteriorStaple n x μ r)
  linarith

omit [Fact (1 < n)] in
/-- The modified split action is the singleton corrected full Wilson action. -/
theorem singleton_split (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (z : Exterior n Q x μ × Q) :
    stabilizedAction n {(x, μ)} β
        (SingleCoordinateProduct.assemble (selectedLink n x μ) z) =
      SU2WilsonConditionalSource.splitAction n x μ β z +
        penalty β (exteriorStaple n x μ z.1) := by
  have he : exterior n x μ (SingleCoordinateProduct.assemble (selectedLink n x μ) z) = z.1 := by
    exact SU2WilsonMarginalTransport.exteriorProjection_assemble n x μ z
  change initialAction n β (SingleCoordinateProduct.assemble (selectedLink n x μ) z) + _ = _
  simp only [penaltySum, Finset.sum_singleton, stapleField, he]
  rfl

/-- Every actual later effective action stays within the same initial budget. -/
theorem iterated_action_bounds (S : Finset (Link n)) (β : ℝ) (hβ : 3 / 2 ≤ β)
    (T : ℕ → Finset (Edge (Vertex n))) (k : ℕ) (U : Configuration (Vertex n) Q) :
    action (compactHaar Q) T (stabilizedAction n S β) k U -
      action (compactHaar Q) T (initialAction n β) k U ∈ Set.Icc 0 (budget n S β) :=
  action_bounds (compactHaar Q) T _ _ _
    (fun V => by rw [action_difference]; exact penaltySum_bounds n S β hβ V) k U

/-- Normalized density ratios remain bounded at every depth, even at rare configurations. -/
theorem iterated_density_bounds (S : Finset (Link n)) (β : ℝ) (hβ : 3 / 2 ≤ β)
    (T : ℕ → Finset (Edge (Vertex n))) (k : ℕ) (U : Configuration (Vertex n) Q) :
    Real.exp (-budget n S β) ≤
      normalizedWeight (Measure.pi (fun _ : Edge (Vertex n) => compactHaar Q))
          (action (compactHaar Q) T (stabilizedAction n S β) k) U /
        normalizedWeight (Measure.pi (fun _ : Edge (Vertex n) => compactHaar Q))
          (action (compactHaar Q) T (initialAction n β) k) U ∧
    normalizedWeight (Measure.pi (fun _ : Edge (Vertex n) => compactHaar Q))
        (action (compactHaar Q) T (stabilizedAction n S β) k) U /
      normalizedWeight (Measure.pi (fun _ : Edge (Vertex n) => compactHaar Q))
        (action (compactHaar Q) T (initialAction n β) k) U ≤ Real.exp (budget n S β) :=
  stage_density_ratio_bounds (compactHaar Q) T _ _ _
    (fun V => by rw [action_difference]; exact penaltySum_bounds n S β hβ V) k U

/-- Uniform bounded-observable control with no integration-depth factor. -/
theorem iterated_expectation_bound (S : Finset (Link n)) (β : ℝ) (hβ : 3 / 2 ≤ β)
    (T : ℕ → Finset (Edge (Vertex n))) (k : ℕ)
    (F : C(Configuration (Vertex n) Q, ℝ)) (M : ℝ) (hM : 0 ≤ M)
    (hF : ∀ U, |F U| ≤ M) :
    |(∫ U, F U ∂law (compactHaar Q) T (stabilizedAction n S β) k) -
      (∫ U, F U ∂law (compactHaar Q) T (initialAction n β) k)| ≤ M * budget n S β / 2 :=
  stage_expectation_difference (compactHaar Q) T _ _ F _ M
    (by unfold budget; positivity) hM
    (fun V => by rw [action_difference]; exact penaltySum_bounds n S β hβ V) hF k

omit n [NeZero n] [Fact (1 < n)] in
/-- Cutoff, selected links, integration depth and tests may all vary. Only
the explicitly displayed number-of-corrections / beta budget must vanish. -/
theorem iterated_expectation_tendsto {ι : Type*} {l : Filter ι}
    (N : ι → ℕ) [∀ i, NeZero (N i)] [∀ i, Fact (1 < N i)]
    (β : ι → ℝ) (hβ : Tendsto β l atTop)
    (S : (i : ι) → Finset (Link (N i)))
    (hsize : Tendsto (fun i => (S i).card / β i) l (𝓝 (0 : ℝ)))
    (T : (i : ι) → ℕ → Finset (Edge (Vertex (N i)))) (depth : ι → ℕ)
    (F : (i : ι) → C(Configuration (Vertex (N i)) Q, ℝ))
    (M : ℝ) (hM : 0 ≤ M) (hF : ∀ i U, |F i U| ≤ M) :
    Tendsto (fun i =>
      |(∫ U, F i U ∂law (compactHaar Q) (T i)
          (stabilizedAction (N i) (S i) (β i)) (depth i)) -
        (∫ U, F i U ∂law (compactHaar Q) (T i)
          (initialAction (N i) (β i)) (depth i))|) l (𝓝 0) := by
  have hb : Tendsto (fun i => M * budget (N i) (S i) (β i) / 2) l (𝓝 0) := by
    convert hsize.const_mul (M * 27 / 64) using 1
    · ext i
      unfold budget
      ring
    · simp only [mul_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
  · exact Eventually.of_forall (fun _ => abs_nonneg _)
  · filter_upwards [hβ.eventually_ge_atTop (3 / 2)] with i hi
    exact iterated_expectation_bound (N i) (S i) (β i) hi (T i) (depth i) (F i) M hM (hF i)

end
end UnifiedTheory.Clay.YangMills.WilsonStabilizedIntegration
