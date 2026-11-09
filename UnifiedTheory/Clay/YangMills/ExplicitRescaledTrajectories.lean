/- Explicit sufficient coupling choices for actual rescaled fixed-test
reflected forms on refining, expanding lattices. The balanced choice gives
only an upper bound; a faster choice forces a zero limit. Neither trajectory
is identified with physical Yang--Mills running or nontrivial curvature fields. -/
import UnifiedTheory.Clay.YangMills.ReflectedGridRate
import UnifiedTheory.Clay.YangMills.ExplicitLatticeScales

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.ExplicitRescaledTrajectories
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4 WilsonCrossingKernel
open CellReflectionCovariance ReflectedWilsonRenormalization ReflectedGridRate
open ExplicitLatticeScales WilsonGridCouplingRate
open scoped Topology

def balancedGrid (k : ℕ) : ℕ := (k+1)^4

def rapidGrid (k : ℕ) : ℕ := (k+1)^5

theorem balanced_factor (k : ℕ) : spacing k ^ 8 * (balancedGrid k : ℝ)^2 = 1 := by
  unfold spacing balancedGrid
  push_cast
  have h : (k : ℝ)+1 ≠ 0 := by positivity
  field_simp
  <;> ring

theorem rapid_factor (k : ℕ) : spacing k ^ 8 * (rapidGrid k : ℝ)^2 = ((k : ℝ)+1)^2 := by
  unfold spacing rapidGrid
  push_cast
  have h : (k : ℝ)+1 ≠ 0 := by positivity
  field_simp
  <;> ring

variable (d : Type*) [Fintype d] [Nonempty d] [DecidableEq d]
  (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- A proved uniform upper bound for the proposed normalization on one
explicit actual Wilson trajectory. No positive lower bound is concluded. -/
theorem balanced_uniform_bound (plane : Plane)
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (f g : CorrelationTest 1) (k : ℕ) :
    ‖proposedCurvatureForm G (2*halfPeriod k) (spacing k) plane
      (realPartCharacter G (unitaryCharacter ρ)) (unitaryCharacter ρ)
      (betaThreshold d (balancedGrid k)) (Fintype.card d) (Fintype.card d) f g‖ ≤
      rateConstant d * BoundedKernelDistribution.l1Seminorm volume f *
        BoundedKernelDistribution.l1Seminorm volume g := by
  exact proposed_uniform_bound d G (2*halfPeriod k) (spacing k) (spacing_pos k) plane
    ρ hρ (balancedGrid k) (by unfold balancedGrid; positivity) _ le_rfl
    (by rw [balanced_factor]) (Fintype.card d) f g

/-- Overly fast action coefficients force even the proposed rescaled
connected form to zero on the actual refining and expanding lattice family. -/
theorem rapid_reflected_tendsto_zero (plane : Plane)
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (f g : CorrelationTest 1) :
    Tendsto (fun k => proposedCurvatureForm G (2*halfPeriod k) (spacing k) plane
      (realPartCharacter G (unitaryCharacter ρ)) (unitaryCharacter ρ)
      (betaThreshold d (rapidGrid k)) (Fintype.card d) (Fintype.card d) f g)
      atTop (𝓝 0) := by
  let C := rateConstant d * BoundedKernelDistribution.l1Seminorm volume f *
    BoundedKernelDistribution.l1Seminorm volume g
  apply squeeze_zero_norm (a := fun k : ℕ => C / ((k : ℝ)+1)^2)
  · intro k
    have h := proposedCurvatureForm_grid_bound d G (2*halfPeriod k) (spacing k)
      (spacing_pos k) plane ρ hρ (rapidGrid k) (by unfold rapidGrid; positivity)
      _ le_rfl (Fintype.card d) f g
    rw [rapid_factor] at h
    exact h
  · simpa [spacing, div_pow, div_eq_mul_inv] using
      (spacing_to_zero.pow 2).const_mul C

end
end UnifiedTheory.Clay.YangMills.ExplicitRescaledTrajectories
