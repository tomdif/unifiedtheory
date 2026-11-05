/- An explicit simultaneous fine-mesh and infinite-volume lattice sequence.
This supplies geometric scales only, not a renormalized Yang--Mills trajectory. -/
import UnifiedTheory.Clay.YangMills.PositiveCellSupport
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.ExplicitLatticeScales
noncomputable section
open Filter ContinuumControl
open scoped Topology

def halfPeriod (k : ℕ) : ℕ := (k + 1) ^ 2
def spacing (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

instance halfPeriod_ne_zero (k : ℕ) : NeZero (halfPeriod k) :=
  ⟨pow_ne_zero _ (Nat.succ_ne_zero k)⟩

theorem spacing_pos (k : ℕ) : 0 < spacing k := by
  unfold spacing
  positivity

theorem half_extent (k : ℕ) : (halfPeriod k : ℝ) * spacing k = (k : ℝ) + 1 := by
  unfold halfPeriod spacing
  push_cast
  have h : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp

theorem spacing_to_zero : Tendsto spacing atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem half_extent_to_infinity :
    Tendsto (fun k => (halfPeriod k : ℝ) * spacing k) atTop atTop := by
  simp_rw [half_extent]
  exact Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

def scales : RegulatorScales where
  spacing := spacing
  radius k := (halfPeriod k : ℝ) * spacing k
  spacing_pos := spacing_pos
  radius_pos k := by rw [half_extent]; positivity
  ultraviolet_limit := spacing_to_zero
  infinite_volume := half_extent_to_infinity

theorem fixed_test_eventually_supported (plane : PeriodicLattice4.Plane)
    (m : ℕ) (f : CorrelationTest m) (R : ℝ)
    (hf : ∀ x, f x ≠ 0 → ∀ j, 0 ≤ PeriodicCellSampling.point m j x 0 ∧
      PeriodicCellSampling.point m j x 0 ≤ R) :
    ∀ᶠ k in atTop, ClosedHalfSmearing.Supported (halfPeriod k) (spacing k) plane m f :=
  PositiveCellSupport.eventually_supported halfPeriod spacing spacing_pos
    half_extent_to_infinity plane m f R hf

end
end UnifiedTheory.Clay.YangMills.ExplicitLatticeScales
