/- An explicit regulator path pays exponential support growth over an unbounded
number of contact subtractions. Every physical stage radius still shrinks to zero.
This is an analytic path for kernels with proved stage hypotheses, not a
construction of the remaining interacting field. -/
import UnifiedTheory.Clay.YangMills.GrowingStageContact

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.GrowingStageContactPath
noncomputable section
open MeasureTheory Filter LocalFields GrowingStageContact
open scoped Topology

def radius (k : ℕ) : ℝ := 2 ^ k
def spacing (k : ℕ) : ℝ := (radius k ^ 16)⁻¹
def period (k : ℕ) : ℕ := 16 * (2 ^ k) ^ 17

theorem period_gt_one (k : ℕ) : 1 < period k := by
  have h : 1 ≤ (2 ^ k) ^ 17 := Nat.one_le_pow 17 (2 ^ k) Nat.one_le_two_pow
  unfold period
  omega

theorem period_even (k : ℕ) : 2 ∣ period k := by
  unfold period
  omega

theorem radius_pos (k : ℕ) : 0 < radius k := by unfold radius; positivity

theorem radius_ge_one (k : ℕ) : 1 ≤ radius k := by
  exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)

theorem spacing_pos (k : ℕ) : 0 < spacing k := by
  exact inv_pos.mpr (pow_pos (radius_pos k) 16)

theorem radius_succ (k : ℕ) : radius (k + 1) = 2 * radius k := by
  simp [radius, pow_succ, mul_comm]

theorem radius_mono {j k : ℕ} (hjk : j ≤ k) : radius j ≤ radius k :=
  pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hjk

theorem radius_tendsto : Tendsto radius atTop atTop :=
  tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)

theorem spacing_tendsto : Tendsto spacing atTop (𝓝 0) :=
  ((tendsto_pow_atTop (α := ℝ) (by norm_num : (16 : ℕ) ≠ 0)).comp
    radius_tendsto).inv_tendsto_atTop

theorem physical_size (k : ℕ) : (period k : ℝ) * spacing k = 16 * radius k := by
  have hr := (radius_pos k).ne'
  simp only [period, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  change 16 * radius k ^ 17 * (radius k ^ 16)⁻¹ = _
  field_simp

theorem physical_size_tendsto :
    Tendsto (fun k => (period k : ℝ) * spacing k) atTop atTop := by
  simp_rw [physical_size]
  exact radius_tendsto.const_mul_atTop (by norm_num)

/-- A single geometric sum pays all ninth-power stage-radius costs. -/
theorem radius_sum_nine (k : ℕ) :
    (∑ j ∈ Finset.range k, radius j ^ 9) ≤ radius k ^ 9 := by
  induction k with
  | zero => simp [radius]
  | succ k ih =>
    rw [Finset.sum_range_succ, radius_succ]
    have hp : 0 ≤ radius k ^ 9 := (pow_pos (radius_pos k) 9).le
    calc
      _ ≤ 2 * radius k ^ 9 := by linarith
      _ ≤ (2 * radius k) ^ 9 := by nlinarith [hp]

/-- The largest permitted stencil fits in the physical box with uniform room. -/
theorem no_wrap (k j : ℕ) (hjk : j ≤ k) :
    2 * radius k + (4 * radius j + 1) * spacing k < (period k : ℝ) * spacing k := by
  rw [physical_size]
  have hr := radius_ge_one k
  have hj := radius_mono hjk
  have hs : spacing k ≤ 1 := by
    unfold spacing
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hr)
  have hsp := (spacing_pos k).le
  have hjp := (radius_pos j).le
  have hmul := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 4 * radius j + 1)
  nlinarith

theorem local_factor_bound (k : ℕ) :
    spacing k * radius k ^ 4 * (∑ j ∈ Finset.range k, radius j ^ 9) ≤
      (radius k ^ 3)⁻¹ := by
  have hr := (radius_pos k).ne'
  calc
    _ ≤ spacing k * radius k ^ 4 * radius k ^ 9 :=
      mul_le_mul_of_nonneg_left (radius_sum_nine k)
        (mul_nonneg (spacing_pos k).le (pow_nonneg (radius_pos k).le 4))
    _ = _ := by unfold spacing; field_simp

theorem tail_factor (k : ℕ) :
    (spacing k ^ 8 * radius k ^ 144)⁻¹ = (radius k ^ 16)⁻¹ := by
  have hr := (radius_pos k).ne'
  unfold spacing
  field_simp

theorem stage_count_bound (k : ℕ) : (k : ℝ) ≤ radius k := by
  change (k : ℝ) ≤ (2 : ℝ) ^ k
  exact_mod_cast (show k < 2 ^ k from Nat.lt_two_pow_self).le

theorem tail_factor_bound (k : ℕ) :
    (k : ℝ) * (spacing k ^ 8 * radius k ^ 144)⁻¹ ≤ (radius k ^ 15)⁻¹ := by
  rw [tail_factor]
  have hr := (radius_pos k).ne'
  calc
    _ ≤ radius k * (radius k ^ 16)⁻¹ :=
      mul_le_mul_of_nonneg_right (stage_count_bound k) (by positivity)
    _ = _ := by field_simp

theorem local_factor_tendsto :
    Tendsto (fun k => spacing k * radius k ^ 4 *
      ∑ j ∈ Finset.range k, radius j ^ 9) atTop (𝓝 0) := by
  apply squeeze_zero (fun k => mul_nonneg
    (mul_nonneg (spacing_pos k).le (pow_nonneg (radius_pos k).le 4))
    (Finset.sum_nonneg (fun j _ => pow_nonneg (radius_pos j).le 9))) local_factor_bound
  exact ((tendsto_pow_atTop (α := ℝ) (by norm_num : (3 : ℕ) ≠ 0)).comp
    radius_tendsto).inv_tendsto_atTop

theorem tail_factor_tendsto :
    Tendsto (fun k : ℕ => (k : ℝ) * (spacing k ^ 8 * radius k ^ 144)⁻¹) atTop (𝓝 0) := by
  apply squeeze_zero (fun k => by positivity) tail_factor_bound
  exact ((tendsto_pow_atTop (α := ℝ) (by norm_num : (15 : ℕ) ≠ 0)).comp
    radius_tendsto).inv_tendsto_atTop

/-- A fixed radius prefactor three also fits, covering the already proved ten-spacing stage. -/
theorem scaled_no_wrap (k j : ℕ) (hjk : j ≤ k) :
    2 * radius k + (4 * (3 * radius j) + 1) * spacing k <
      (period k : ℝ) * spacing k := by
  rw [physical_size]
  have hr := radius_ge_one k
  have hj := radius_mono hjk
  have hjp := (radius_pos j).le
  have hs : spacing k ≤ 1 := by
    unfold spacing
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hr)
  have hmul := mul_le_mul_of_nonneg_left hs
    (by positivity : 0 ≤ 4 * (3 * radius j) + 1)
  nlinarith

/-- Even the largest stage remains ultraviolet on this explicit path. -/
theorem largest_stencil_factor (k : ℕ) :
    12 * radius k * spacing k = 12 * (radius k ^ 15)⁻¹ := by
  have hr := (radius_pos k).ne'
  unfold spacing
  field_simp

theorem largest_stencil_tendsto :
    Tendsto (fun k => 12 * radius k * spacing k) atTop (𝓝 0) := by
  simp_rw [largest_stencil_factor]
  have h := ((tendsto_pow_atTop (α := ℝ) (by norm_num : (15 : ℕ) ≠ 0)).comp
    radius_tendsto).inv_tendsto_atTop
  simpa only [mul_zero] using h.const_mul 12

/-- The stage count tends to infinity while the complete accumulated contact error vanishes.
The stagewise kernel hypotheses still need actual repeated-elimination proofs. -/
theorem accumulated_tendsto
    (K : ℕ → ℕ → Spacetime × Spacetime → ℝ)
    (hK : ∀ k, ∀ j < k, Measurable (K k j))
    (hbound : ∀ k, ∀ j < k, ∀ z, |K k j z| ≤ 4 / spacing k ^ 8)
    (hlocal : ∀ k, ∀ j < k, ∀ z, ‖z.1‖ ≤ radius k → ‖z.2‖ ≤ radius k →
      (4 * radius j) * spacing k < ‖z.1 - z.2‖ → K k j z = 0)
    (F : SchwartzMap (Spacetime × Spacetime) ℂ) :
    Tendsto (fun k => remainder k (K k) (spacing k) (radius k) radius F) atTop (𝓝 0) :=
  remainder_tendsto_of_growth atTop id K spacing radius (fun _ => radius) hK F 144
    (Eventually.of_forall spacing_pos) (Eventually.of_forall radius_pos)
    (Eventually.of_forall (fun _ j _ => (radius_pos j).le))
    (Eventually.of_forall hbound) (Eventually.of_forall hlocal)
    local_factor_tendsto tail_factor_tendsto


/-- Multiplying every stage radius by three changes only the fixed local constant,
so the growing-stage estimate also covers this larger concrete stencil schedule. -/
theorem scaled_accumulated_tendsto
    (K : ℕ → ℕ → Spacetime × Spacetime → ℝ)
    (hK : ∀ k, ∀ j < k, Measurable (K k j))
    (hbound : ∀ k, ∀ j < k, ∀ z, |K k j z| ≤ 4 / spacing k ^ 8)
    (hlocal : ∀ k, ∀ j < k, ∀ z, ‖z.1‖ ≤ radius k → ‖z.2‖ ≤ radius k →
      (4 * (3 * radius j)) * spacing k < ‖z.1 - z.2‖ → K k j z = 0)
    (F : SchwartzMap (Spacetime × Spacetime) ℂ) :
    Tendsto (fun k => remainder k (K k) (spacing k) (radius k)
      (fun j => 3 * radius j) F) atTop (𝓝 0) := by
  apply remainder_tendsto_of_growth atTop id K spacing radius
    (fun _ j => 3 * radius j) hK F 144
    (Eventually.of_forall spacing_pos) (Eventually.of_forall radius_pos)
    (Eventually.of_forall (fun _ j _ => mul_nonneg (by norm_num) (radius_pos j).le))
    (Eventually.of_forall hbound) (Eventually.of_forall hlocal) ?_ tail_factor_tendsto
  have h := local_factor_tendsto.const_mul ((3 : ℝ) ^ 9)
  simp only [mul_zero] at h
  convert h using 1
  funext k
  simp only [id_eq, mul_pow, ← Finset.mul_sum]
  ring

end
end UnifiedTheory.Clay.YangMills.GrowingStageContactPath
