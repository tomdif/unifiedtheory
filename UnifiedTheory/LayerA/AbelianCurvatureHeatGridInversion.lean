/- Normalized Fourier inversion with the actual centered grid frequencies. -/
import UnifiedTheory.LayerA.AbelianCurvatureHeatGridLimit
import Mathlib.Data.ZMod.ValMinAbs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerA.AbelianCurvatureHeatGridInversion
noncomputable section
open UnifiedTheory.LayerA.AbelianCurvatureHeat
open UnifiedTheory.LayerA.AbelianCurvatureHeatFourier
open UnifiedTheory.LayerA.AbelianCurvatureHeatContinuum
open UnifiedTheory.LayerA.AbelianCurvatureHeatGridLimit

section FiniteInversion
variable {V : Type*} [AddCommGroup V] [Fintype V]

def normalizedCoefficient (f : V → ℂ) (χ : AddChar V ℂ) : ℂ :=
  (∑ p, f p * χ (-p)) / (Fintype.card V : ℂ)

theorem normalized_fourier_inversion (f : V → ℂ) (q : V) :
    ∑ χ : AddChar V ℂ, normalizedCoefficient f χ * χ q = f q := by
  classical
  have hc : (Fintype.card V : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hd (p : V) : (∑ χ : AddChar V ℂ, χ (-p) * χ q) =
      if p = q then (Fintype.card V : ℂ) else 0 := by
    simp_rw [← AddChar.map_add_eq_mul]
    rw [AddChar.sum_apply_eq_ite]
    simp only [neg_add_eq_zero, eq_comm]
  calc
    _ = (∑ p, f p * ∑ χ : AddChar V ℂ, χ (-p) * χ q) / (Fintype.card V : ℂ) := by
      simp only [normalizedCoefficient, div_mul_eq_mul_div, Finset.sum_mul,
        ← Finset.sum_div, Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro χ _
      ring
    _ = f q := by simp [hd, hc]
end FiniteInversion

variable (n : ℕ) [NeZero n]

/-- The negative endpoint convention agrees with the half-open frequency window. -/
def centered (a : ZMod n) : ℤ := -(-a).valMinAbs

theorem centered_cast (a : ZMod n) : ((centered n a : ℤ) : ZMod n) = a := by
  simp [centered]

theorem centered_bounds (a : ZMod n) :
    -(1 / 2 : ℝ) ≤ (1 / (n : ℝ)) * centered n a ∧
      (1 / (n : ℝ)) * centered n a < 1 / 2 := by
  have h := (-a).valMinAbs_mem_Ioc
  have h1 : -(n : ℝ) < ((-a).valMinAbs : ℝ) * 2 := by exact_mod_cast h.1
  have h2 : ((-a).valMinAbs : ℝ) * 2 ≤ (n : ℝ) := by exact_mod_cast h.2
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr (NeZero.pos n)
  unfold centered
  push_cast
  rw [show (1 / (n : ℝ)) * -((-a).valMinAbs : ℝ) =
    -((-a).valMinAbs : ℝ) / (n : ℝ) by ring]
  constructor
  · apply (le_div_iff₀ hn).mpr
    linarith
  · apply (div_lt_iff₀ hn).mpr
    linarith

theorem centered_unique (a : ZMod n) (j : ℤ)
    (hc : (j : ZMod n) = a)
    (hj : -(1 / 2 : ℝ) ≤ (1 / (n : ℝ)) * j ∧ (1 / (n : ℝ)) * j < 1 / 2) :
    centered n a = j := by
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr (NeZero.pos n)
  have h1 := mul_le_mul_of_nonneg_left hj.1 hn.le
  have h2 := mul_lt_mul_of_pos_left hj.2 hn
  have he : (n : ℝ) * (1 / (n : ℝ) * j) = j := by field_simp
  rw [he] at h1 h2
  have hs : (-a).valMinAbs = -j := (ZMod.valMinAbs_spec _ _).mpr ⟨by simp [hc], by
    constructor
    · exact_mod_cast (show -(n : ℝ) < -(j : ℝ) * 2 by linarith)
    · exact_mod_cast (show -(j : ℝ) * 2 ≤ (n : ℝ) by linarith)⟩
  simp [centered, hs]

def frequencyEquiv : {k // k ∈ gridFrequencies n} ≃ Grid n where
  toFun k := ((k.val.1 : ZMod n), (k.val.2 : ZMod n))
  invFun p := ⟨(centered n p.1, centered n p.2),
    (mem_gridFrequencies n _).mpr ⟨centered_bounds n p.1, centered_bounds n p.2⟩⟩
  left_inv k := by
    apply Subtype.ext
    apply Prod.ext
    · exact centered_unique n _ _ rfl ((mem_gridFrequencies n k).mp k.property).1
    · exact centered_unique n _ _ rfl ((mem_gridFrequencies n k).mp k.property).2
  right_inv p := by simp [centered_cast]

def gridDualMap (p : Grid n) : AddChar (Grid n) ℂ :=
  gridCharacter n (centered n p.1, centered n p.2)

theorem gridDualMap_bijective : Function.Bijective (gridDualMap n) := by
  apply (Fintype.bijective_iff_injective_and_card (gridDualMap n)).mpr
  constructor
  · intro p q h
    have hx := congrArg (fun χ : AddChar (Grid n) ℂ => χ (1, 0)) h
    have hy := congrArg (fun χ : AddChar (Grid n) ℂ => χ (0, 1)) h
    simp only [gridDualMap, gridCharacter, AddChar.coe_mk, mul_one, mul_zero,
      add_zero, zero_add, centered_cast] at hx hy
    exact Prod.ext (ZMod.injective_stdAddChar hx) (ZMod.injective_stdAddChar hy)
  · exact (AddChar.card_eq (α := Grid n)).symm

def frequencyCharacterEquiv : {k // k ∈ gridFrequencies n} ≃ AddChar (Grid n) ℂ :=
  (frequencyEquiv n).trans (Equiv.ofBijective (gridDualMap n) (gridDualMap_bijective n))

theorem frequencyCharacterEquiv_apply (k : {k // k ∈ gridFrequencies n}) :
    frequencyCharacterEquiv n k = gridCharacter n k := by
  change gridCharacter n (centered n (k.val.1 : ZMod n), centered n (k.val.2 : ZMod n)) = _
  rw [centered_unique n _ _ rfl ((mem_gridFrequencies n k).mp k.property).1,
    centered_unique n _ _ rfl ((mem_gridFrequencies n k).mp k.property).2]

theorem grid_fourier_inversion (f : Grid n → ℂ) (p : Grid n) :
    ∑ k ∈ gridFrequencies n, normalizedCoefficient f (gridCharacter n k) * gridCharacter n k p =
      f p := by
  classical
  rw [← Finset.sum_attach]
  rw [← normalized_fourier_inversion f p]
  simpa only [Finset.attach_eq_univ, frequencyCharacterEquiv_apply] using
    Equiv.sum_comp (frequencyCharacterEquiv n) (fun χ => normalizedCoefficient f χ * χ p)

end
end UnifiedTheory.LayerA.AbelianCurvatureHeatGridInversion
