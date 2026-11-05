/- Quantitative high-coefficient endpoints for the actual proposed rescaled
Wilson reflected correlation. The normalization Z is fixed independently of
beta. This supplies the small endpoint in a tuning argument, not a positive
endpoint, physical running, or a nonzero continuum limit. -/
import UnifiedTheory.Clay.YangMills.ReflectedGridRate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.ProposedCouplingTail
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4 WilsonCrossingKernel
open CellReflectionCovariance ReflectedWilsonRenormalization ReflectedGridRate
open WilsonGridCouplingRate
open scoped Topology

variable (d : Type*) [Fintype d] [Nonempty d] [DecidableEq d]
  (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (N : ℕ) [NeZero N]

def signal (L a : ℝ) (plane : Plane) (ρ : G →* Matrix.unitaryGroup d ℂ)
    (Z : ℂ) (f : CorrelationTest 1) (beta : ℝ) : ℝ :=
  L ^ 8 * ‖Z‖ ^ 2 *
    (proposedCurvatureForm G N a plane (realPartCharacter G (unitaryCharacter ρ))
      (unitaryCharacter ρ) beta (Fintype.card d) (Fintype.card d) f f).re

def boundConstant (L : ℝ) (Z : ℂ) (f : CorrelationTest 1) : ℝ :=
  L ^ 8 * ‖Z‖ ^ 2 * rateConstant d *
    BoundedKernelDistribution.l1Seminorm volume f *
    BoundedKernelDistribution.l1Seminorm volume f

theorem boundConstant_nonneg (L : ℝ) (Z : ℂ) (f : CorrelationTest 1) :
    0 ≤ boundConstant d L Z f := by
  unfold boundConstant
  exact mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (by positivity) (sq_nonneg _)) (rateConstant_nonneg d))
    (apply_nonneg _ _)) (apply_nonneg _ _)

theorem signal_grid_bound (L a : ℝ) (ha : 0 < a) (plane : Plane)
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (Z : ℂ) (f : CorrelationTest 1) (K : ℕ) (hK : 0 < K)
    (beta : ℝ) (hbeta : betaThreshold d K ≤ beta) :
    |signal d G N L a plane ρ Z f beta| ≤
      boundConstant d L Z f / (a ^ 8 * (K : ℝ) ^ 2) := by
  have h := proposedCurvatureForm_grid_bound d G N a ha plane ρ hρ K hK
    beta hbeta (Fintype.card d) f f
  have hp : 0 ≤ L ^ 8 * ‖Z‖ ^ 2 := by positivity
  unfold signal
  rw [abs_mul, abs_of_nonneg hp]
  calc
    _ ≤ L ^ 8 * ‖Z‖ ^ 2 *
        ‖proposedCurvatureForm G N a plane (realPartCharacter G (unitaryCharacter ρ))
          (unitaryCharacter ρ) beta (Fintype.card d) (Fintype.card d) f f‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hp
    _ ≤ L ^ 8 * ‖Z‖ ^ 2 *
        (rateConstant d * BoundedKernelDistribution.l1Seminorm volume f *
          BoundedKernelDistribution.l1Seminorm volume f / (a ^ 8 * (K : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left h hp
    _ = _ := by unfold boundConstant; ring

/-- A genuine tail estimate at each fixed regulator, derived from the
explicit Haar/grid bound. No positive signal is presumed. -/
theorem signal_tendsto_zero (L a : ℝ) (ha : 0 < a) (plane : Plane)
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (Z : ℂ) (f : CorrelationTest 1) :
    Tendsto (signal d G N L a plane ρ Z f) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  obtain ⟨K, hK⟩ := exists_nat_gt (max 1 (boundConstant d L Z f / (a ^ 8 * eps)))
  have hk1 : (1 : ℝ) < K := (le_max_left _ _).trans_lt hK
  have hk : 0 < K := Nat.cast_pos.mp (lt_trans zero_lt_one hk1)
  have hc : boundConstant d L Z f / (a ^ 8 * eps) < (K : ℝ) ^ 2 := by
    have hh := (le_max_right _ _).trans_lt hK
    nlinarith
  have he : boundConstant d L Z f / (a ^ 8 * (K : ℝ) ^ 2) < eps := by
    have ha8 : 0 < a ^ 8 := pow_pos ha 8
    have hk2 : 0 < (K : ℝ) ^ 2 := sq_pos_of_pos (Nat.cast_pos.mpr hk)
    have hh := (div_lt_iff₀ (mul_pos ha8 heps)).mp hc
    apply (div_lt_iff₀ (mul_pos ha8 hk2)).mpr
    nlinarith
  refine ⟨betaThreshold d K, ?_⟩
  intro beta hbeta
  simpa only [Real.dist_eq, sub_zero] using
    (signal_grid_bound d G N L a ha plane ρ hρ Z f K hk beta hbeta).trans_lt he

/-- Every starting coefficient has a larger actual small-signal endpoint.
Thus only the opposite, positive endpoint remains in the proposed tuning
bracket. Z may depend on the cutoff, but is fixed while beta is tuned. -/
theorem exists_small_endpoint (L a : ℝ) (ha : 0 < a) (plane : Plane)
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (Z : ℂ) (f : CorrelationTest 1) (start eps : ℝ) (heps : 0 < eps) :
    ∃ beta, start < beta ∧ |signal d G N L a plane ρ Z f beta| < eps := by
  obtain ⟨b, hb⟩ := Metric.tendsto_atTop.mp
    (signal_tendsto_zero d G N L a ha plane ρ hρ Z f) eps heps
  refine ⟨max b (start + 1), ?_, ?_⟩
  · exact (lt_add_one start).trans_le (le_max_right _ _)
  · simpa only [Real.dist_eq, sub_zero] using hb _ (le_max_left _ _)

end
end UnifiedTheory.Clay.YangMills.ProposedCouplingTail
