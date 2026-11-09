/- A finite measurable coordinate grid for an actual unitary representation.
Equal bins give an explicit entrywise error, with a dimension-only bin count.
This supplies a quantitative Haar neighborhood argument without assuming one. -/
import UnifiedTheory.Clay.YangMills.UnitaryHolonomyDefect
import Mathlib.MeasureTheory.Function.Floor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.UnitaryCoordinateGrid
noncomputable section
open MeasureTheory UnitaryCharacterObservables

variable {d : Type*} [Fintype d] [DecidableEq d]

def coordinate (A : Matrix.unitaryGroup d ℂ) (p : (d × d) × Bool) : ℝ :=
  if p.2 then (A p.1.1 p.1.2).re else (A p.1.1 p.1.2).im

theorem coordinate_abs_le (A : Matrix.unitaryGroup d ℂ) (p : (d × d) × Bool) :
    |coordinate A p| ≤ 1 := by
  unfold coordinate
  split
  · exact (Complex.abs_re_le_norm _).trans (unitary_entry_bound A _ _)
  · exact (Complex.abs_im_le_norm _).trans (unitary_entry_bound A _ _)

def bin (K : ℕ) (r : ℝ) (hr : r ≤ 1) : Fin (2*K+1) :=
  ⟨⌊(K : ℝ)*(r+1)⌋₊, Nat.lt_succ_iff.mpr (Nat.floor_le_of_le (by
    push_cast
    nlinarith [show (0 : ℝ) ≤ (K : ℝ) from Nat.cast_nonneg K]))⟩

theorem bin_same (K : ℕ) (hK : 0 < K) (r s : ℝ)
    (hr : |r| ≤ 1) (hs : |s| ≤ 1)
    (he : bin K r (le_of_abs_le hr) = bin K s (le_of_abs_le hs)) :
    |r-s| ≤ 1/(K : ℝ) := by
  have hk : 0 < (K : ℝ) := Nat.cast_pos.mpr hK
  have he' : ⌊(K : ℝ)*(r+1)⌋₊ = ⌊(K : ℝ)*(s+1)⌋₊ := congrArg Fin.val he
  have hr0 : 0 ≤ (K : ℝ)*(r+1) := mul_nonneg hk.le (by linarith [(abs_le.mp hr).1])
  have hs0 : 0 ≤ (K : ℝ)*(s+1) := mul_nonneg hk.le (by linarith [(abs_le.mp hs).1])
  have hrlo := Nat.floor_le hr0
  have hrhi := Nat.lt_floor_add_one ((K : ℝ)*(r+1))
  have hslo := Nat.floor_le hs0
  have hshi := Nat.lt_floor_add_one ((K : ℝ)*(s+1))
  rw [he'] at hrlo hrhi
  rw [abs_le]
  constructor
  · apply (neg_le_iff_add_nonneg).mpr
    have hdiv : (1 : ℝ)/(K : ℝ)*(K : ℝ) = 1 := div_mul_cancel₀ _ hk.ne'
    nlinarith
  · apply (le_div_iff₀ hk).mpr
    nlinarith

def grid (K : ℕ) (A : Matrix.unitaryGroup d ℂ) : ((d × d) × Bool) → Fin (2*K+1) :=
  fun p => bin K (coordinate A p) (le_of_abs_le (coordinate_abs_le A p))

theorem grid_card (K : ℕ) :
    Fintype.card (((d × d) × Bool) → Fin (2*K+1)) =
      (2*K+1) ^ (2 * (Fintype.card d)^2) := by
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod, Fintype.card_bool]
  congr 1
  ring

theorem grid_same_entry (K : ℕ) (hK : 0 < K) (A B : Matrix.unitaryGroup d ℂ)
    (he : grid K A = grid K B) (i j : d) : ‖A i j - B i j‖ ≤ 2/(K : ℝ) := by
  have hre := bin_same K hK _ _ (coordinate_abs_le A ((i,j),true))
    (coordinate_abs_le B ((i,j),true)) (congrFun he ((i,j),true))
  have him := bin_same K hK _ _ (coordinate_abs_le A ((i,j),false))
    (coordinate_abs_le B ((i,j),false)) (congrFun he ((i,j),false))
  simp only [coordinate, Bool.false_eq_true, ↓reduceIte] at hre him
  have hn := Complex.norm_le_abs_re_add_abs_im (A i j - B i j)
  simp only [Complex.sub_re, Complex.sub_im] at hn
  calc
    ‖A i j - B i j‖ ≤ 1/(K : ℝ) + 1/(K : ℝ) := hn.trans (add_le_add hre him)
    _ = _ := by ring

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]

theorem coordinate_continuous (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (p : (d × d) × Bool) : Continuous (fun g => coordinate (ρ g) p) := by
  have hc : Continuous (fun g => (ρ g : Matrix d d ℂ) p.1.1 p.1.2) :=
    (continuous_apply _).comp ((continuous_apply _).comp (continuous_subtype_val.comp hρ))
  unfold coordinate
  split
  · exact Complex.continuous_re.comp hc
  · exact Complex.continuous_im.comp hc

theorem grid_measurable (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ) (K : ℕ) :
    Measurable (fun g => grid K (ρ g)) := by
  apply measurable_pi_lambda
  intro p
  have he : MeasurableEmbedding (Fin.val : Fin (2*K+1) → ℕ) :=
    ⟨Fin.val_injective, measurable_of_finite _, fun _ _ => Set.to_countable _ |>.measurableSet⟩
  apply he.measurable_comp_iff.mp
  exact ((measurable_const.mul ((coordinate_continuous ρ hρ p).measurable.add
    measurable_const)).nat_floor)

end
end UnifiedTheory.Clay.YangMills.UnitaryCoordinateGrid
