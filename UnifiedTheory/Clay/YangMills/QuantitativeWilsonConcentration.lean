/- Explicit dimension-dependent concentration for the actual Wilson law.
Both the low-energy tolerance and Haar mass are proved functions of the grid
size. The resulting fixed-Schwartz estimate is not a renormalized limit. -/
import UnifiedTheory.Clay.YangMills.UnitaryHaarNeighborhood
import UnifiedTheory.Clay.YangMills.WilsonIdentityNeighborhood
import UnifiedTheory.Clay.YangMills.BareDefectHierarchy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.QuantitativeWilsonConcentration
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonCrossingKernel
open UnitaryCharacterObservables WilsonAverageDefect WilsonIdentityNeighborhood
open UnitaryHaarNeighborhood GibbsLowEnergyConcentration BareDefectHierarchy ContinuumControl
open scoped NNReal

variable (d : Type*) [Fintype d]

def errorRatio (K : ℕ) (beta : ℝ) : ℝ :=
  Real.exp (-6*beta*squaredTolerance d K)/(massLower d K)^4

theorem errorRatio_explicit (K : ℕ) (beta : ℝ) :
    errorRatio d K beta = Real.exp (-6*beta*squaredTolerance d K) *
      ((2*K+1 : ℕ) : ℝ)^(8*(Fintype.card d)^2) := by
  unfold errorRatio massLower
  rw [div_pow, one_pow, div_div_eq_mul_div, div_one, ← pow_mul]
  congr 2
  omega

variable {d} [DecidableEq d]
  (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- No neighborhood mass or defect bound is assumed: both come from the
actual representation grid and exact matrix-square identity. -/
theorem average_bound (N : ℕ) [NeZero N]
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (K : ℕ) (hK : 0 < K) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hr : errorRatio d K beta ≤ 1) :
    (∫ U, averageDefect N G ρ U
      ∂wilsonLaw N G (unitaryCharacter ρ) beta (Fintype.card d)) ≤
      2*squaredTolerance d K + 2*(Fintype.card d : ℝ)*errorRatio d K beta := by
  rw [law_eq_average_weight N G ρ hρ beta]
  apply volume_uniform_expectation_bound (referenceMeasure G (Vertex N))
    (averageDefect N G ρ) (average_continuous N G ρ hρ) beta hbeta
    (squaredTolerance d K) (squaredTolerance_nonneg d K)
    (2*(Fintype.card d : ℝ)) (by positivity) (average_le N G ρ)
    (massLower d K) (massLower_pos d K) (Fintype.card (Vertex N)) Fintype.card_pos
    (goodEvent N G (nearIdentity ρ K))
    (goodEvent_measurable N G _ (nearIdentity_measurable ρ hρ K))
  · rw [goodEvent_mass]
    exact pow_le_pow_left₀ (massLower_pos d K).le (nearIdentity_mass_lower ρ hρ K hK) _
  · intro U hU
    exact goodEvent_small N G ρ (nearIdentity ρ K) (squaredTolerance d K)
      (fun a ha b hb c hc e he => four_link_defect_squared_bound ρ K a b c e ha hb hc he) U hU
  · exact hr

/-- A direct quantitative estimate for every actual multi-point fixed smear,
with constants independent of lattice spacing and volume. -/
theorem hierarchy_bound (N : ℕ) [NeZero N] (a : ℝ) (plane : Plane)
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (K : ℕ) (hK : 0 < K) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hr : errorRatio d K beta ≤ 1) (m : ℕ) (f : CorrelationTest m) :
    ‖(unitaryHierarchy N a plane ρ hρ beta).correlation m f -
      (Fintype.card d : ℂ)^m * ∫ x, f x‖ ≤
      (Fintype.card d : ℝ)^(m-1) * ((m : ℝ) *
        (6*(2*squaredTolerance d K + 2*(Fintype.card d : ℝ)*errorRatio d K beta))) *
        BoundedKernelDistribution.l1Seminorm volume f := by
  apply (hierarchy_difference_average N a plane ρ hρ beta m f).trans
  have hb := average_bound G N ρ hρ K hK beta hbeta hr
  gcongr

end
end UnifiedTheory.Clay.YangMills.QuantitativeWilsonConcentration
