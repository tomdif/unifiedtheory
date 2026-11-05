/- An explicit polynomially expanding regulator path on which the actual removed
Wilson noise admits full-Schwartz contact subtraction. Both the local error and
all periodic-image tails are proved to vanish, without a compact-support premise. -/
import UnifiedTheory.Clay.YangMills.WilsonSchwartzContactBound
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSchwartzContactPath
noncomputable section
open MeasureTheory Filter RegulatedGauge LocalFields PeriodicLattice4
open WilsonIndependentBlocks WilsonInfluenceGeometry
open WilsonCompactContactSubtraction WilsonSchwartzContactBound
open scoped Topology

local instance pairVolumeHaar :
    (volume : Measure (Spacetime × Spacetime)).IsAddHaarMeasure := by
  change (volume.prod volume : Measure (Spacetime × Spacetime)).IsAddHaarMeasure
  infer_instance

def radius (k : ℕ) : ℝ := (k : ℝ) + 1
def spacing (k : ℕ) : ℝ := 1 / radius k ^ 8
def period (k : ℕ) : ℕ := 4 * (k + 1) ^ 9
def coupling (b : ℝ) (k : ℕ) : ℝ := 8 * b * Real.log (radius k)

theorem radius_pos (k : ℕ) : 0 < radius k := by unfold radius; positivity
theorem spacing_pos (k : ℕ) : 0 < spacing k :=
  one_div_pos.mpr (pow_pos (radius_pos k) 8)

theorem period_gt_one (k : ℕ) : 1 < period k := by
  have h : 1 ≤ (k + 1) ^ 9 := Nat.one_le_pow 9 (k + 1) (by omega)
  unfold period
  omega

instance periodNeZero (k : ℕ) : NeZero (period k) := ⟨by have := period_gt_one k; omega⟩
instance periodFact (k : ℕ) : Fact (1 < period k) := ⟨period_gt_one k⟩

theorem period_even (k : ℕ) : 2 ∣ period k := by unfold period; omega

theorem radius_tendsto : Tendsto radius atTop atTop :=
  tendsto_atTop_mono (fun k => by dsimp [radius]; linarith) tendsto_natCast_atTop_atTop

theorem spacing_tendsto : Tendsto spacing atTop (𝓝 0) := by
  have h := ((tendsto_pow_atTop (α := ℝ) (by norm_num : (8 : ℕ) ≠ 0)).comp
    radius_tendsto).inv_tendsto_atTop
  convert h using 1
  funext k
  simp [spacing]

theorem physical_size (k : ℕ) : (period k : ℝ) * spacing k = 4 * radius k := by
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  simp only [period, spacing, radius, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
    Nat.cast_add, Nat.cast_one]
  field_simp

theorem physical_size_tendsto :
    Tendsto (fun k => (period k : ℝ) * spacing k) atTop atTop := by
  simp_rw [physical_size]
  exact radius_tendsto.const_mul_atTop (by norm_num)

/-- This admissible geometry also permits every positive logarithmic coupling slope. -/
theorem coupling_log_spacing (b : ℝ) (k : ℕ) :
    coupling b k = b * Real.log (spacing k)⁻¹ := by
  unfold coupling spacing
  rw [one_div, inv_inv, Real.log_pow]
  ring

theorem coupling_tendsto (b : ℝ) (hb : 0 < b) : Tendsto (coupling b) atTop atTop :=
  (Real.tendsto_log_atTop.comp radius_tendsto).const_mul_atTop (by positivity)

/-- The no-wrap inequality holds with strict room for the actual four-spacing stencil. -/
theorem no_wrap (k : ℕ) (hk : 1 ≤ k) :
    2 * radius k + 2 * spacing k < (period k : ℝ) * spacing k := by
  rw [physical_size]
  have hr : 1 < radius k := by unfold radius; exact_mod_cast (show 1 < k + 1 by omega)
  have hs : spacing k ≤ 1 := by
    unfold spacing
    exact (div_le_one (pow_pos (radius_pos k) 8)).mpr (one_le_pow₀ hr.le)
  nlinarith

theorem local_factor (k : ℕ) : spacing k * radius k ^ 4 = (radius k ^ 4)⁻¹ := by
  have hk : radius k ≠ 0 := (radius_pos k).ne'
  unfold spacing
  field_simp

theorem tail_factor (k : ℕ) : (spacing k ^ 8 * radius k ^ 72)⁻¹ = (radius k ^ 8)⁻¹ := by
  have hk : radius k ≠ 0 := (radius_pos k).ne'
  unfold spacing
  field_simp

theorem local_factor_tendsto :
    Tendsto (fun k => spacing k * radius k ^ 4) atTop (𝓝 0) := by
  simp_rw [local_factor]
  exact ((tendsto_pow_atTop (α := ℝ) (by norm_num : (4 : ℕ) ≠ 0)).comp
    radius_tendsto).inv_tendsto_atTop

theorem tail_factor_tendsto :
    Tendsto (fun k => (spacing k ^ 8 * radius k ^ 72)⁻¹) atTop (𝓝 0) := by
  simp_rw [tail_factor]
  exact ((tendsto_pow_atTop (α := ℝ) (by norm_num : (8 : ℕ) ≠ 0)).comp
    radius_tendsto).inv_tendsto_atTop

local instance edgeDecidableEq (k : ℕ) : DecidableEq (Edge (Vertex (period k))) :=
  Classical.decEq _
local instance linkDecidableEq (k : ℕ) : DecidableEq (Link (period k)) := Classical.decEq _

/-- An explicit full-Schwartz estimate with all periodic-image contributions included. -/
theorem error_bound (β : ℕ → ℝ)
    (S : (k : ℕ) → Finset (Edge (Vertex (period k))))
    (hS : ∀ k, Independent (period k) ((S k).image (edgeCoord (period k))))
    (plane plane' : Plane) (f : SchwartzMap (Spacetime × Spacetime) ℂ)
    (k : ℕ) (hk : 1 ≤ k) :
    ‖pairing (period k) (β k) (spacing k) (S k) plane plane' f -
      contact4 (period k) (β k) (spacing k) (radius k) (S k) plane plane' f‖ ≤
      ((WilsonNoiseTubeMass.massConstant 1 * 4 ^ 5 / 24) *
        SchwartzMap.seminorm ℝ 0 5 f) / radius k ^ 4 +
          (16 * SchwartzWeightedTail.weightedMoment volume 72 f) / radius k ^ 8 := by
  have h := schwartz_subtraction_bound_scaled (period k) (β k) (spacing k) (radius k)
    (S k) (hS k) plane plane' f 72 (spacing_pos k) (radius_pos k) (no_wrap k hk)
  simpa only [local_factor, tail_factor, div_eq_mul_inv] using h

/-- The literal sampled actual removed covariance converges after its explicit order-four
contact subtraction on every Schwartz test, with no restriction on the coupling sequence. -/
theorem subtraction_tendsto (β : ℕ → ℝ)
    (S : (k : ℕ) → Finset (Edge (Vertex (period k))))
    (hS : ∀ k, Independent (period k) ((S k).image (edgeCoord (period k))))
    (plane plane' : Plane) (f : SchwartzMap (Spacetime × Spacetime) ℂ) :
    Tendsto (fun k => pairing (period k) (β k) (spacing k) (S k) plane plane' f -
      contact4 (period k) (β k) (spacing k) (radius k) (S k) plane plane' f)
      atTop (𝓝 0) :=
  subtraction_tendsto_of_growth atTop period β spacing radius S hS plane plane' f 72
    (Eventually.of_forall spacing_pos) (Eventually.of_forall radius_pos)
    (eventually_atTop.2 ⟨1, no_wrap⟩) local_factor_tendsto tail_factor_tendsto

end
end UnifiedTheory.Clay.YangMills.WilsonSchwartzContactPath
