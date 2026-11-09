/- Full smeared dimension-four Wilson moments diverge at logarithmic coupling.
The test is fixed, smooth and compactly supported. The period is arbitrary;
every deterministic identity subtraction is allowed. This does not assert a
no-go theorem for contact-renormalized or separated-point Schwinger functions. -/
import UnifiedTheory.Clay.YangMills.ExpandingLogarithmicPath
import UnifiedTheory.Clay.YangMills.LogarithmicUltravioletGrowth
import UnifiedTheory.Clay.YangMills.WilsonSupportedWeightLower

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonLogarithmicMomentObstruction
noncomputable section
open MeasureTheory Filter PeriodicLattice4 WilsonSmoothSourceObstruction
open scoped Topology

/-- The genuine fixed-test second moment under the original Wilson law. -/
def moment (N : ℕ → ℕ) [∀ k, NeZero (N k)] (a β c : ℕ → ℝ) (plane : Plane) (k : ℕ) : ℝ :=
  secondMoment (N k) (β k) ((a k)^4)⁻¹ (c k)
    (WilsonPhysicalCellWeights.weight (N k) (a k) plane WilsonCellWeightLower.witnessTest)

variable (N : ℕ → ℕ) [∀ k, NeZero (N k)] [∀ k, Fact (1 < N k)]

/-- The actual compact-support lower bound is eventually valid on any shrinking mesh. -/
theorem eventual_lower (a β c : ℕ → ℝ) (plane : Plane) (heven : ∀ k, 2 ∣ N k)
    (ha : ∀ᶠ k in atTop, 0 < a k) (ha0 : Tendsto a atTop (𝓝 0))
    (hβ : Tendsto β atTop atTop) :
    ∀ᶠ k in atTop, ((a k)^4)⁻¹ / (768 * 9^4 * (β k)^2) ≤ moment N a β c plane k := by
  have he := (WilsonEnergyDensity.energyEnvelope_tendsto.comp hβ).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 72))
  have ha1 := ha0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [ha, ha1, hβ.eventually_ge_atTop 5, he] with k hak ha1k hk he
  exact WilsonSupportedWeightLower.classical_compact_witness_lower
    (N k) (β k) (a k) (c k) plane (heven k) hk he.le hak ha1k.le

/-- Every weak-coupling selection inside a logarithmic upper bracket has
unbounded ordinary second moments, uniformly with respect to lattice volume. -/
theorem moment_tendsto (a β c : ℕ → ℝ) (plane : Plane) (heven : ∀ k, 2 ∣ N k)
    (b : ℝ) (hb : 0 < b) (ha : ∀ᶠ k in atTop, 0 < a k)
    (ha0 : Tendsto a atTop (𝓝 0)) (hβ : Tendsto β atTop atTop)
    (hupper : ∀ᶠ k in atTop, β k ≤ b * Real.log (a k)⁻¹) :
    Tendsto (moment N a β c plane) atTop atTop := by
  have hp : ∀ᶠ k in atTop, 0 < β k := hβ.eventually_gt_atTop 0
  have h := (LogarithmicUltravioletGrowth.inverse_fourth_div_square_tendsto
    atTop a β b hb ha ha0 hp hupper).const_mul_atTop
      (show (0 : ℝ) < 1 / (768 * 9^4) by norm_num)
  have hl : Tendsto (fun k => ((a k)^4)⁻¹ / (768 * 9^4 * (β k)^2)) atTop atTop := by
    convert h using 1
    funext k
    ring
  exact tendsto_atTop_mono' atTop (eventual_lower N a β c plane heven ha ha0 hβ) hl

/-- No identity counterterm can make the second moment of this fixed test uniformly bounded. -/
theorem no_uniform_second_moment (a β c : ℕ → ℝ) (plane : Plane)
    (heven : ∀ k, 2 ∣ N k) (b : ℝ) (hb : 0 < b)
    (ha : ∀ᶠ k in atTop, 0 < a k) (ha0 : Tendsto a atTop (𝓝 0))
    (hβ : Tendsto β atTop atTop)
    (hupper : ∀ᶠ k in atTop, β k ≤ b * Real.log (a k)⁻¹) :
    ¬ ∃ C : ℝ, ∀ k, moment N a β c plane k ≤ C := by
  rintro ⟨C, hC⟩
  have h := (moment_tendsto N a β c plane heven b hb ha ha0 hβ hupper).eventually_gt_atTop C
  obtain ⟨k, hk⟩ := h.exists
  exact (not_lt_of_ge (hC k)) hk

omit [∀ k, NeZero (N k)] [∀ k, Fact (1 < N k)] in
/-- A fully explicit shrinking-mesh, expanding-volume example, with exact logarithmic coupling. -/
theorem explicit_path_moment_tendsto (plane : Plane) (c : ℕ → ℝ) (b : ℝ) (hb : 0 < b) :
    Tendsto (moment ExpandingLogarithmicPath.period ExpandingLogarithmicPath.spacing
      (ExpandingLogarithmicPath.coupling b) c plane) atTop atTop := by
  apply moment_tendsto ExpandingLogarithmicPath.period ExpandingLogarithmicPath.spacing
    (ExpandingLogarithmicPath.coupling b) c plane ExpandingLogarithmicPath.period_even b hb
    (Eventually.of_forall ExpandingLogarithmicPath.spacing_pos)
    ExpandingLogarithmicPath.spacing_tendsto (ExpandingLogarithmicPath.coupling_tendsto b hb)
  exact Eventually.of_forall (fun k => (ExpandingLogarithmicPath.coupling_log_spacing b k).le)

end
end UnifiedTheory.Clay.YangMills.WilsonLogarithmicMomentObstruction
