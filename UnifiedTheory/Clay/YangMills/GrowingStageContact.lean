/- Accumulation of proved finite-range Schwartz contact errors over a growing
number of stages. Kernel measurability, amplitude and support must be established
for each actual induced stage; this analytic theorem does not assume Wilson closure. -/
import UnifiedTheory.Clay.YangMills.FiniteRangeSchwartzContact

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.GrowingStageContact
noncomputable section
open MeasureTheory Filter LocalFields FiniteRangeSchwartzContact
open scoped Topology

local instance pairVolumeHaar :
    (volume : Measure (Spacetime × Spacetime)).IsAddHaarMeasure := by
  change (volume.prod volume).IsAddHaarMeasure
  infer_instance

/-- The stage-independent local constant; the ninth power contains all radius growth. -/
def localConstant : ℝ := mass 4 1 1 * 4 ^ 5 / 24

theorem localConstant_nonneg : 0 ≤ localConstant := by
  unfold localConstant mass
  positivity

theorem local_constant_scaling (c : ℝ) :
    mass 4 c 1 * (4 * c) ^ 5 / 24 = localConstant * c ^ 9 := by
  unfold localConstant mass
  ring

/-- The sum uses each stage's own constructed Taylor contact. -/
def remainder (J : ℕ) (K : ℕ → Spacetime × Spacetime → ℝ) (a R : ℝ)
    (c : ℕ → ℝ) (F : SchwartzMap (Spacetime × Spacetime) ℂ) : ℂ :=
  ∑ j ∈ Finset.range J,
    ((∫ z, (K j z : ℂ) * F z) - contact (K j) a R (c j) F)

/-- Both stage-count and support-radius losses are explicit, including every global tail. -/
theorem remainder_bound (J : ℕ) (K : ℕ → Spacetime × Spacetime → ℝ)
    (hK : ∀ j < J, Measurable (K j)) (a R : ℝ) (ha : 0 < a) (hR : 0 < R)
    (c : ℕ → ℝ) (hc : ∀ j < J, 0 ≤ c j)
    (hbound : ∀ j < J, ∀ z, |K j z| ≤ 4 / a ^ 8)
    (hlocal : ∀ j < J, ∀ z, ‖z.1‖ ≤ R → ‖z.2‖ ≤ R →
      (4 * c j) * a < ‖z.1 - z.2‖ → K j z = 0)
    (F : SchwartzMap (Spacetime × Spacetime) ℂ) (m : ℕ) :
    ‖remainder J K a R c F‖ ≤
      (localConstant * SchwartzMap.seminorm ℝ 0 5 F) *
        (a * R ^ 4 * ∑ j ∈ Finset.range J, c j ^ 9) +
      (4 * SchwartzWeightedTail.weightedMoment volume m F) *
        ((J : ℝ) * (a ^ 8 * R ^ m)⁻¹) := by
  calc
    _ ≤ ∑ j ∈ Finset.range J,
        ‖(∫ z, (K j z : ℂ) * F z) - contact (K j) a R (c j) F‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range J,
        (((mass 4 (c j) 1 * (4 * c j) ^ 5 / 24) * SchwartzMap.seminorm ℝ 0 5 F) *
          (a * R ^ 4) +
        (4 * SchwartzWeightedTail.weightedMoment volume m F) * (a ^ 8 * R ^ m)⁻¹) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj := Finset.mem_range.mp hj
      exact subtraction_bound_scaled (K j) (hK j hj) a R (c j) 4 ha hR (hc j hj)
        (by norm_num) (hbound j hj) (hlocal j hj) F m
    _ = _ := by
      simp_rw [local_constant_scaling]
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

/-- Arbitrary stage counts and radius schedules are allowed once their two explicit
accumulated growth factors vanish. No convergence of the retained field is asserted. -/
theorem remainder_tendsto_of_growth {ι : Type*} (l : Filter ι)
    (J : ι → ℕ) (K : ι → ℕ → Spacetime × Spacetime → ℝ)
    (a R : ι → ℝ) (c : ι → ℕ → ℝ)
    (hK : ∀ k, ∀ j < J k, Measurable (K k j))
    (F : SchwartzMap (Spacetime × Spacetime) ℂ) (m : ℕ)
    (ha : ∀ᶠ k in l, 0 < a k) (hR : ∀ᶠ k in l, 0 < R k)
    (hc : ∀ᶠ k in l, ∀ j < J k, 0 ≤ c k j)
    (hbound : ∀ᶠ k in l, ∀ j < J k, ∀ z, |K k j z| ≤ 4 / a k ^ 8)
    (hlocal : ∀ᶠ k in l, ∀ j < J k, ∀ z, ‖z.1‖ ≤ R k → ‖z.2‖ ≤ R k →
      (4 * c k j) * a k < ‖z.1 - z.2‖ → K k j z = 0)
    (hsmall : Tendsto (fun k => a k * R k ^ 4 *
      ∑ j ∈ Finset.range (J k), c k j ^ 9) l (𝓝 0))
    (htail : Tendsto (fun k => (J k : ℝ) * (a k ^ 8 * R k ^ m)⁻¹) l (𝓝 0)) :
    Tendsto (fun k => remainder (J k) (K k) (a k) (R k) (c k) F) l (𝓝 0) := by
  have hb : ∀ᶠ k in l, ‖remainder (J k) (K k) (a k) (R k) (c k) F‖ ≤
      (localConstant * SchwartzMap.seminorm ℝ 0 5 F) *
        (a k * R k ^ 4 * ∑ j ∈ Finset.range (J k), c k j ^ 9) +
      (4 * SchwartzWeightedTail.weightedMoment volume m F) *
        ((J k : ℝ) * (a k ^ 8 * R k ^ m)⁻¹) := by
    filter_upwards [ha, hR, hc, hbound, hlocal] with k hak hRk hck hbk hlk
    exact remainder_bound (J k) (K k) (hK k) (a k) (R k) hak hRk (c k) hck hbk hlk F m
  apply squeeze_zero_norm' hb
  simpa only [mul_zero, zero_add] using
    (hsmall.const_mul (localConstant * SchwartzMap.seminorm ℝ 0 5 F)).add
      (htail.const_mul (4 * SchwartzWeightedTail.weightedMoment volume m F))

end
end UnifiedTheory.Clay.YangMills.GrowingStageContact
