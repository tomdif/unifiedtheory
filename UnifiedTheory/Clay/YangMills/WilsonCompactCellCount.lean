/- A fixed compact physical support occupies only O(a^-4) sampled plaquettes.
The residue map may identify integer cells; it can only decrease the count.
No relation between lattice period and physical support is required. -/
import UnifiedTheory.Clay.YangMills.WilsonPhysicalCellWeights
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonCompactCellCount
noncomputable section
open MeasureTheory LocalFields PeriodicLattice4

/-- An integer box large enough for every cell meeting the radius-two ball. -/
def radius (a : ℝ) : ℕ := Nat.ceil (2 / a) + 1

def interval (a : ℝ) : Finset ℤ := Finset.Icc (-(radius a : ℤ)) (radius a : ℤ)

def cube (a : ℝ) : Finset (Fin 4 → ℤ) := Fintype.piFinset (fun _ => interval a)

/-- All possible plaquette residues sampled from that integer box. -/
def cells (n : ℕ) (a : ℝ) (plane : Plane) : Finset (PlaquetteIndex n) := by
  classical
  exact (cube a).image (fun z => ((fun μ => (z μ : ZMod n)), plane))

theorem interval_card (a : ℝ) : (interval a).card = 2 * radius a + 1 := by
  rw [interval, Int.card_Icc]
  omega

theorem cube_card (a : ℝ) : (cube a).card = (2 * radius a + 1) ^ 4 := by
  simp [cube, Fintype.card_piFinset, interval_card]

theorem cells_card (n : ℕ) (a : ℝ) (plane : Plane) :
    (cells n a plane).card ≤ (2 * radius a + 1) ^ 4 := by
  classical
  exact Finset.card_image_le.trans (le_of_eq (cube_card a))

/-- Quantitative occupied-cell count independent of the torus period. -/
theorem cells_card_bound (n : ℕ) (a : ℝ) (plane : Plane)
    (ha : 0 < a) (ha1 : a ≤ 1) :
    ((cells n a plane).card : ℝ) ≤ (9 / a) ^ 4 := by
  have hr : (radius a : ℝ) < 2 / a + 2 := by
    have h := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 2 / a)
    simp only [radius, Nat.cast_add, Nat.cast_one]
    linarith
  have hr' : ((2 * radius a + 1 : ℕ) : ℝ) ≤ 9 / a := by
    push_cast
    have hi : (1 : ℝ) ≤ 1 / a := (le_div_iff₀ ha).mpr (by simpa using ha1)
    simp only [div_eq_mul_inv] at hr hi ⊢
    linarith
  calc
    _ ≤ ((2 * radius a + 1 : ℕ) : ℝ) ^ 4 := by
      exact_mod_cast cells_card n a plane
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hr' 4

/-- The actual floor sampling of a point in the ball lies in the integer box. -/
theorem sample_mem (n : ℕ) (a : ℝ) (plane : Plane) (ha : 0 < a)
    (x : Spacetime) (hx : ‖x‖ ≤ 2) :
    PeriodicCellSampling.sample n a plane x ∈ cells n a plane := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨fun μ => Int.floor (x μ / a), ?_, rfl⟩
  apply Fintype.mem_piFinset.mpr
  intro μ
  have hc : |x μ| ≤ 2 := by
    exact (PiLp.norm_apply_le x μ).trans hx
  have hlow : -(2 / a) ≤ x μ / a := by
    rw [← neg_div]
    exact div_le_div_of_nonneg_right (abs_le.mp hc).1 ha.le
  have hupp : x μ / a ≤ 2 / a :=
    div_le_div_of_nonneg_right (abs_le.mp hc).2 ha.le
  have hceil := Nat.le_ceil (2 / a)
  have hfl := Int.floor_le (x μ / a)
  have hfl' := Int.lt_floor_add_one (x μ / a)
  have hlo : -((radius a : ℕ) : ℝ) ≤ (Int.floor (x μ / a) : ℝ) := by
    simp only [radius, Nat.cast_add, Nat.cast_one]
    linarith
  have hhi : (Int.floor (x μ / a) : ℝ) ≤ ((radius a : ℕ) : ℝ) := by
    simp only [radius, Nat.cast_add, Nat.cast_one]
    linarith
  apply Finset.mem_Icc.mpr
  constructor
  · exact_mod_cast hlo
  · exact_mod_cast hhi

variable (n : ℕ)

/-- Every nonzero actual physical cell weight is contained in this finite residue set. -/
theorem weight_supported (a : ℝ) (plane : Plane) (ha : 0 < a)
    (f : TestFunction) (hf : ∀ x, f x ≠ 0 → ‖x‖ ≤ 2)
    (p : PlaquetteIndex n) (hp : p ∉ cells n a plane) :
    WilsonPhysicalCellWeights.weight n a plane f p = 0 := by
  have he : FiniteCellSmearing.cellFunction (PeriodicCellSampling.sample n a plane) p f = 0 := by
    funext x
    unfold FiniteCellSmearing.cellFunction
    split_ifs with hs
    · by_contra h
      have hm := sample_mem n a plane ha x (hf x h)
      rw [hs] at hm
      exact hp hm
    · rfl
  unfold WilsonPhysicalCellWeights.weight FiniteCellSmearing.coefficient
  rw [he]
  simp

end
end UnifiedTheory.Clay.YangMills.WilsonCompactCellCount
