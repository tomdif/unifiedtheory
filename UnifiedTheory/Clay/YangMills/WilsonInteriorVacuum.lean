/- Actual interior correlations of the raw full Wilson time cylinder converge
to original-transfer vacuum matrix elements at fixed spatial cutoff. -/
import UnifiedTheory.Clay.YangMills.WilsonCylinderGluing
import UnifiedTheory.Clay.YangMills.WilsonCylinderVacuum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonInteriorVacuum
noncomputable section
open MeasureTheory Filter WilsonSlabOperator WilsonFiniteCylinder WilsonCylinderGluing
open WilsonSlabContraction ContinuousBoundaryMoments TransferEnergySurvival
open scoped Topology

variable (n : ℕ) [NeZero n]

/-- Two actual interior observations with j slices of padding on either side. -/
def correlation (β : ℝ) (j k : ℕ) (F G : C(Slice n, ℝ)) : ℝ :=
  ∫ z : Slices n Q (j + k + j) × TemporalLinks n Q (j + k + j),
    F (z.1 (mark (j + k) j)) * G (z.1 (secondMark j k j))
    ∂WilsonFiniteCylinder.law WilsonSingleLinkStaples.character β 2 (j + k + j)

def vacuumCorrelation (β : ℝ) (hβ : 0 ≤ β) (k : ℕ) (F G : C(Slice n, ℝ)) : ℝ :=
  (inner ℂ (embed (measure n) (F * WilsonGroundLocalComparison.ground n β hβ))
    (iterate (normalized n β) k
      (embed (measure n) (G * WilsonGroundLocalComparison.ground n β hβ)))).re

/-- Finite raw-cylinder integration, scalar cancellation and the actual
positive-boundary limit are now joined; no vacuum boundary is inserted. -/
theorem correlation_tendsto (β : ℝ) (hβ : 0 ≤ β)
    (F G : C(Slice n, ℝ)) (k : ℕ) :
    Tendsto (fun j => correlation n β j k F G) atTop
      (nhds (vacuumCorrelation n β hβ k F G)) := by
  have h := WilsonCylinderVacuum.endpoint_quotient_tendsto n β hβ F G k
  simpa only [correlation, cylinder_interior_expectation, mul_comm,
    vacuumCorrelation] using h


def groundMean (β : ℝ) (hβ : 0 ≤ β) (F : C(Slice n, ℝ)) : ℝ :=
  ∫ u, (WilsonGroundLocalComparison.ground n β hβ u)^2 * F u ∂measure n

theorem vacuumCorrelation_one_right (β : ℝ) (hβ : 0 ≤ β)
    (k : ℕ) (F : C(Slice n, ℝ)) :
    vacuumCorrelation n β hβ k F 1 = groundMean n β hβ F := by
  have hf : normalized n β (embed (measure n) (WilsonGroundLocalComparison.ground n β hβ)) =
      embed (measure n) (WilsonGroundLocalComparison.ground n β hβ) :=
    WilsonVacuumConvergence.vacuum_fixed n β hβ
  unfold vacuumCorrelation
  rw [one_mul, ContinuousBoundaryMoments.iterate_fixed (measure n) (normalized n β) _
    hf k]
  rw [embed, embed, MeasureTheory.ContinuousMap.inner_toLp]
  simp only [WilsonPositiveGroundState.complexify, ContinuousMap.coe_mk,
    ContinuousMap.mul_apply, Complex.conj_ofReal, ← Complex.ofReal_mul,
    integral_complex_ofReal, Complex.ofReal_re, groundMean]
  apply integral_congr_ae
  filter_upwards [] with u
  ring

theorem vacuumCorrelation_one_left (β : ℝ) (hβ : 0 ≤ β)
    (k : ℕ) (G : C(Slice n, ℝ)) :
    vacuumCorrelation n β hβ k 1 G = groundMean n β hβ G := by
  have hf : normalized n β (embed (measure n) (WilsonGroundLocalComparison.ground n β hβ)) =
      embed (measure n) (WilsonGroundLocalComparison.ground n β hβ) :=
    WilsonVacuumConvergence.vacuum_fixed n β hβ
  unfold vacuumCorrelation
  rw [one_mul, ← iterate_symmetric (normalized n β) (normalized_symmetric n β),
    ContinuousBoundaryMoments.iterate_fixed (measure n) (normalized n β) _
      hf k]
  rw [embed, embed, MeasureTheory.ContinuousMap.inner_toLp]
  simp only [WilsonPositiveGroundState.complexify, ContinuousMap.coe_mk,
    ContinuousMap.mul_apply, Complex.conj_ofReal, ← Complex.ofReal_mul,
    integral_complex_ofReal, Complex.ofReal_re, groundMean]
  apply integral_congr_ae
  filter_upwards [] with u
  ring

/-- The actual centered cylinder covariance, with its own finite-cylinder means. -/
def covariance (β : ℝ) (j k : ℕ) (F G : C(Slice n, ℝ)) : ℝ :=
  correlation n β j k F G - correlation n β j k F 1 * correlation n β j k 1 G

/-- Connected correlations pass to the vacuum along the same raw cylinders. -/
theorem covariance_tendsto (β : ℝ) (hβ : 0 ≤ β)
    (F G : C(Slice n, ℝ)) (k : ℕ) :
    Tendsto (fun j => covariance n β j k F G) atTop
      (nhds (vacuumCorrelation n β hβ k F G -
        groundMean n β hβ F * groundMean n β hβ G)) := by
  have h := (correlation_tendsto n β hβ F G k).sub
    ((correlation_tendsto n β hβ F 1 k).mul (correlation_tendsto n β hβ 1 G k))
  simpa only [vacuumCorrelation_one_right, vacuumCorrelation_one_left] using h

end
end UnifiedTheory.Clay.YangMills.WilsonInteriorVacuum
