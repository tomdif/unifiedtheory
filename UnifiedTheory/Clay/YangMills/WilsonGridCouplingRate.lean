/- A concrete quantitative Wilson-coefficient prescription from the proved
grid mass and matrix-square estimates. It produces inverse-square grid decay.
It is not identified with a physical Yang--Mills running coupling. -/
import UnifiedTheory.Clay.YangMills.QuantitativeWilsonConcentration

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonGridCouplingRate
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonCrossingKernel
open UnitaryHaarNeighborhood QuantitativeWilsonConcentration WilsonAverageDefect
open BareDefectHierarchy ContinuumControl

variable (d : Type*) [Fintype d]

def betaThreshold (K : ℕ) : ℝ :=
  (((8*(Fintype.card d)^2+2 : ℕ) : ℝ)*Real.log ((2*K+1 : ℕ) : ℝ)) /
    (6*squaredTolerance d K)

theorem betaThreshold_nonneg (K : ℕ) : 0 ≤ betaThreshold d K := by
  apply div_nonneg
  · apply mul_nonneg (Nat.cast_nonneg _)
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 2*K+1 by omega)
  · exact mul_nonneg (by norm_num) (squaredTolerance_nonneg d K)

theorem errorRatio_antitone (K : ℕ) {beta gamma : ℝ} (h : beta ≤ gamma) :
    errorRatio d K gamma ≤ errorRatio d K beta := by
  unfold errorRatio
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.exp_le_exp.mpr
  have he := squaredTolerance_nonneg d K
  nlinarith

variable [Nonempty d]

theorem squaredTolerance_pos (K : ℕ) (hK : 0 < K) : 0 < squaredTolerance d K := by
  rw [squaredTolerance_formula]
  have hd : 0 < (Fintype.card d : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hk : 0 < (K : ℝ) := Nat.cast_pos.mpr hK
  positivity

/-- The error ratio is exactly an inverse square at this explicit coupling. -/
theorem errorRatio_at_threshold (K : ℕ) (hK : 0 < K) :
    errorRatio d K (betaThreshold d K) = 1/((2*K+1 : ℕ) : ℝ)^2 := by
  have heps := (squaredTolerance_pos d K hK).ne'
  have hbase : 0 < ((2*K+1 : ℕ) : ℝ) := by positivity
  have he : -6*betaThreshold d K*squaredTolerance d K =
      -((8*(Fintype.card d)^2+2 : ℕ) : ℝ)*Real.log ((2*K+1 : ℕ) : ℝ) := by
    unfold betaThreshold
    field_simp
    <;> ring
  rw [errorRatio_explicit, he, neg_mul, Real.exp_neg, Real.exp_nat_mul,
    Real.exp_log hbase, pow_add]
  field_simp

theorem errorRatio_le_inverse_square (K : ℕ) (hK : 0 < K) (beta : ℝ)
    (hbeta : betaThreshold d K ≤ beta) :
    errorRatio d K beta ≤ 1/((2*K+1 : ℕ) : ℝ)^2 :=
  (errorRatio_antitone d K hbeta).trans_eq (errorRatio_at_threshold d K hK)

theorem errorRatio_le_one (K : ℕ) (hK : 0 < K) (beta : ℝ)
    (hbeta : betaThreshold d K ≤ beta) : errorRatio d K beta ≤ 1 := by
  apply (errorRatio_le_inverse_square d K hK beta hbeta).trans
  have hbase : 1 ≤ ((2*K+1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 2*K+1 by omega)
  apply (div_le_one (by positivity)).mpr
  nlinarith

variable [DecidableEq d]
  (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem average_inverse_square_bound (N : ℕ) [NeZero N]
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (K : ℕ) (hK : 0 < K) (beta : ℝ) (hbeta : betaThreshold d K ≤ beta) :
    (∫ U, averageDefect N G ρ U
      ∂wilsonLaw N G (unitaryCharacter ρ) beta (Fintype.card d)) ≤
      2*squaredTolerance d K + 2*(Fintype.card d : ℝ)/((2*K+1 : ℕ) : ℝ)^2 := by
  apply (average_bound G N ρ hρ K hK beta
    ((betaThreshold_nonneg d K).trans hbeta) (errorRatio_le_one d K hK beta hbeta)).trans
  have hr := errorRatio_le_inverse_square d K hK beta hbeta
  have hd : 0 ≤ 2*(Fintype.card d : ℝ) := by positivity
  have hh := mul_le_mul_of_nonneg_left hr hd
  simpa only [mul_one_div] using add_le_add_right hh (2*squaredTolerance d K)

/-- This bounds actual fixed Schwartz correlations, not pointwise variance. -/
theorem hierarchy_inverse_square_bound (N : ℕ) [NeZero N] (a : ℝ) (plane : Plane)
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (K : ℕ) (hK : 0 < K) (beta : ℝ) (hbeta : betaThreshold d K ≤ beta)
    (m : ℕ) (f : CorrelationTest m) :
    ‖(unitaryHierarchy N a plane ρ hρ beta).correlation m f -
      (Fintype.card d : ℂ)^m * ∫ x, f x‖ ≤
      (Fintype.card d : ℝ)^(m-1) * ((m : ℝ) *
        (6*(2*squaredTolerance d K + 2*(Fintype.card d : ℝ)/((2*K+1 : ℕ) : ℝ)^2))) *
        BoundedKernelDistribution.l1Seminorm volume f := by
  apply (hierarchy_difference_average N a plane ρ hρ beta m f).trans
  have hb := average_inverse_square_bound d G N ρ hρ K hK beta hbeta
  gcongr

end
end UnifiedTheory.Clay.YangMills.WilsonGridCouplingRate
