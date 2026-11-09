/-
Cell-integral Fourier coefficients for the actual lower-left grid sampling.
The coefficient bounds and consistency are proved from integrability, rather
than supplied as assumptions to the Fourier convergence theorem.
-/
import UnifiedTheory.LayerA.AbelianCurvatureHeatGridLimit
import UnifiedTheory.LayerA.AbelianCurvatureHeatGridInversion
import UnifiedTheory.LayerA.AbelianCurvatureHeatPDE
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerA.AbelianCurvatureHeatCellAverage
noncomputable section
open UnifiedTheory.LayerA.AbelianCurvatureHeat
open UnifiedTheory.LayerA.AbelianCurvatureHeatFourier
open UnifiedTheory.LayerA.AbelianCurvatureHeatContinuum
open UnifiedTheory.LayerA.AbelianCurvatureHeatGridLimit
open UnifiedTheory.LayerA.AbelianCurvatureHeatGridInversion
open MeasureTheory Filter Set
open scoped Topology

def unitSquare : Set (ℝ × ℝ) := Ico 0 1 ×ˢ Ico 0 1
def squareMeasure : Measure (ℝ × ℝ) := volume.restrict unitSquare

def snapCoordinate (n : ℕ) (x : ℝ) : ℝ :=
  (⌊((n : ℝ) + 1) * x⌋ : ℝ) / ((n : ℝ) + 1)

def snap (n : ℕ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (snapCoordinate n z.1, snapCoordinate n z.2)

theorem snapCoordinate_error (n : ℕ) (x : ℝ) :
    |snapCoordinate n x - x| ≤ 1 / ((n : ℝ) + 1) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hl := Int.floor_le (((n : ℝ) + 1) * x)
  have hu := Int.lt_floor_add_one (((n : ℝ) + 1) * x)
  have he : snapCoordinate n x - x =
      ((⌊((n : ℝ) + 1) * x⌋ : ℝ) - ((n : ℝ) + 1) * x) / ((n : ℝ) + 1) := by
    unfold snapCoordinate
    field_simp
  rw [he, abs_div, abs_of_pos hn]
  apply div_le_div_of_nonneg_right _ hn.le
  apply abs_le.mpr
  constructor <;> linarith

theorem snapCoordinate_tendsto (x : ℝ) :
    Tendsto (fun n => snapCoordinate n x) atTop (𝓝 x) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have he := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (gt_mem_nhds hε)
  filter_upwards [he] with n hn
  rw [Real.dist_eq]
  exact (snapCoordinate_error n x).trans_lt hn

theorem snap_tendsto (z : ℝ × ℝ) : Tendsto (fun n => snap n z) atTop (𝓝 z) :=
  by simpa only [← nhds_prod_eq] using
    (snapCoordinate_tendsto z.1).prodMk (snapCoordinate_tendsto z.2)

theorem measurable_snap (n : ℕ) : Measurable (snap n) := by
  unfold snap snapCoordinate
  fun_prop

theorem continuous_planeWave (k : ℤ × ℤ) : Continuous (planeWave k) := by
  unfold planeWave
  fun_prop

def continuumCoefficient (μ : Measure (ℝ × ℝ)) (f : ℝ × ℝ → ℂ) (k : ℤ × ℤ) : ℂ :=
  ∫ z, f z * planeWave (-k) z ∂μ

def cellCoefficient (μ : Measure (ℝ × ℝ)) (f : ℝ × ℝ → ℂ) (n : ℕ) (k : ℤ × ℤ) : ℂ :=
  ∫ z, f z * planeWave (-k) (snap n z) ∂μ

theorem continuumCoefficient_bound (μ : Measure (ℝ × ℝ)) (f : ℝ × ℝ → ℂ) (k : ℤ × ℤ) :
    ‖continuumCoefficient μ f k‖ ≤ ∫ z, ‖f z‖ ∂μ := by
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by simp only [norm_mul, planeWave_norm, mul_one])

theorem cellCoefficient_bound (μ : Measure (ℝ × ℝ)) (f : ℝ × ℝ → ℂ)
    (n : ℕ) (k : ℤ × ℤ) : ‖cellCoefficient μ f n k‖ ≤ ∫ z, ‖f z‖ ∂μ := by
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by simp only [norm_mul, planeWave_norm, mul_one])

/-- Modewise consistency for any integrable datum, including discontinuous data. -/
theorem cellCoefficient_tendsto (μ : Measure (ℝ × ℝ)) (f : ℝ × ℝ → ℂ)
    (hf : Integrable f μ) (k : ℤ × ℤ) :
    Tendsto (fun n => cellCoefficient μ f n k) atTop (𝓝 (continuumCoefficient μ f k)) := by
  apply tendsto_integral_of_dominated_convergence (fun z => ‖f z‖)
  · intro n
    exact hf.aestronglyMeasurable.mul
      (((continuous_planeWave (-k)).measurable.comp (measurable_snap n)).aestronglyMeasurable)
  · exact hf.norm
  · intro n
    exact Eventually.of_forall (fun z => by rw [norm_mul, planeWave_norm, mul_one])
  · exact Eventually.of_forall (fun z => tendsto_const_nhds.mul
      ((continuous_planeWave (-k)).continuousAt.tendsto.comp (snap_tendsto z)))

def cellIndex (n : ℕ) (z : ℝ × ℝ) : Grid (n + 1) :=
  ((⌊((n : ℝ)+1)*z.1⌋ : ZMod (n + 1)), (⌊((n : ℝ)+1)*z.2⌋ : ZMod (n + 1)))

def cell (n : ℕ) (p : Grid (n + 1)) : Set (ℝ × ℝ) := {z | cellIndex n z = p}

theorem measurableSet_cell (n : ℕ) (p : Grid (n + 1)) : MeasurableSet (cell n p) := by
  have hi : Measurable (fun z : ℝ × ℝ => (⌊((n : ℝ)+1)*z.1⌋, ⌊((n : ℝ)+1)*z.2⌋)) := by
    fun_prop
  exact (Set.to_countable {j : ℤ × ℤ | ((j.1 : ZMod (n + 1)), (j.2 : ZMod (n + 1))) = p}).measurableSet.preimage hi

theorem planeWave_snap (n : ℕ) (k : ℤ × ℤ) (z : ℝ × ℝ) :
    planeWave k (snap n z) = gridCharacter (n + 1) k (cellIndex n z) := by
  simpa [snap, snapCoordinate, cellIndex] using
    planeWave_integer_grid (n + 1) k (⌊((n : ℝ)+1)*z.1⌋, ⌊((n : ℝ)+1)*z.2⌋)

/-- The coefficient is exactly the finite sum of cell integrals times grid characters. -/
theorem cellCoefficient_eq_sum (μ : Measure (ℝ × ℝ)) (f : ℝ × ℝ → ℂ)
    (hf : Integrable f μ) (n : ℕ) (k : ℤ × ℤ) :
    cellCoefficient μ f n k = ∑ p : Grid (n + 1),
      (∫ z in cell n p, f z ∂μ) * gridCharacter (n + 1) (-k) p := by
  classical
  have he (z : ℝ × ℝ) : f z * planeWave (-k) (snap n z) =
      ∑ p : Grid (n + 1), (cell n p).indicator f z * gridCharacter (n + 1) (-k) p := by
    rw [Finset.sum_eq_single (cellIndex n z)]
    · simp [cell, planeWave_snap]
    · intro p _ hp
      simp [cell, hp.symm]
    · simp
  simp only [cellCoefficient, he]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro p _
    rw [integral_mul_const, integral_indicator (measurableSet_cell n p)]
  · intro p _
    exact (hf.indicator (measurableSet_cell n p)).mul_const _

def cellAverage (μ : Measure (ℝ × ℝ)) (f : ℝ × ℝ → ℂ) (n : ℕ) (p : Grid (n + 1)) : ℂ :=
  ((n : ℂ) + 1)^2 * ∫ z in cell n p, f z ∂μ

theorem gridCharacter_neg_frequency (N : ℕ) [NeZero N] (k : ℤ × ℤ) (p : Grid N) :
    gridCharacter N k (-p) = gridCharacter N (-k) p := by
  change ZMod.stdAddChar ((k.1 : ZMod N) * (-p.1) + (k.2 : ZMod N) * (-p.2)) =
    ZMod.stdAddChar (((-k.1 : ℤ) : ZMod N) * p.1 + ((-k.2 : ℤ) : ZMod N) * p.2)
  congr 1
  push_cast
  ring

theorem cellCoefficient_eq_normalized (μ : Measure (ℝ × ℝ)) (f : ℝ × ℝ → ℂ)
    (hf : Integrable f μ) (n : ℕ) (k : ℤ × ℤ) :
    cellCoefficient μ f n k = normalizedCoefficient (cellAverage μ f n)
      (gridCharacter (n + 1) k) := by
  have hcard : (Fintype.card (Grid (n + 1)) : ℂ) = ((n : ℂ)+1)^2 := by
    simp [Grid, Fintype.card_prod, ZMod.card, pow_two]
  have hN : ((n : ℂ)+1)^2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast Nat.succ_ne_zero n)
  rw [cellCoefficient_eq_sum μ f hf, normalizedCoefficient, hcard]
  simp only [cellAverage, gridCharacter_neg_frequency, mul_assoc, ← Finset.mul_sum]
  field_simp

theorem reconstructedData_cellAverage (μ : Measure (ℝ × ℝ)) (f : ℝ × ℝ → ℂ)
    (hf : Integrable f μ) (n : ℕ) (p : Grid (n + 1)) :
    reconstructedData (n + 1) (cellCoefficient μ f n) p = (cellAverage μ f n p).re := by
  have h := congrArg Complex.re (grid_fourier_inversion (n + 1) (cellAverage μ f n) p)
  simpa only [reconstructedData, cellCoefficient_eq_normalized μ f hf n, Complex.re_sum] using h

/-- The original coefficient hypotheses have been discharged from cell integration.
With squareMeasure, the input is the normalized cell average on the unit square. -/
theorem gridHeat_cellAverage_limit (μ : Measure (ℝ × ℝ)) (f : ℝ × ℝ → ℂ)
    (hf : Integrable f μ) (t : ℝ) (ht : 0 < t) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ p : Grid (n + 1),
      |gridHeat (n + 1) t (fun q => (cellAverage μ f n q).re) p -
        (continuumSeries (continuumCoefficient μ f) t (gridPosition (n + 1) p)).re| < ε := by
  have h := gridHeat_reconstruction_limit (cellCoefficient μ f) (continuumCoefficient μ f)
    (∫ z, ‖f z‖ ∂μ) t (cellCoefficient_bound μ f) (continuumCoefficient_bound μ f) ht
    (cellCoefficient_tendsto μ f hf)
  have hd (n : ℕ) : reconstructedData (n + 1) (cellCoefficient μ f n) =
      (fun p => (cellAverage μ f n p).re) := funext (reconstructedData_cellAverage μ f hf n)
  simpa only [hd] using h

/-- The limiting real field of this same cell-average construction solves the heat equation. -/
theorem cellAverage_limit_heat_equation (μ : Measure (ℝ × ℝ)) (f : ℝ × ℝ → ℂ)
    (t : ℝ) (ht : 0 < t) (x y : ℝ) :
    let u := UnifiedTheory.LayerA.AbelianCurvatureHeatPDE.realHeat (continuumCoefficient μ f)
    deriv (fun s => u s (x, y)) t =
      deriv (fun a => deriv (fun b => u t (b, y)) a) x +
      deriv (fun a => deriv (fun b => u t (x, b)) a) y := by
  exact UnifiedTheory.LayerA.AbelianCurvatureHeatPDE.real_heat_equation
    (continuumCoefficient μ f) (∫ z, ‖f z‖ ∂μ) (continuumCoefficient_bound μ f) t ht x y

def cellRectangle (n : ℕ) (p : Grid (n + 1)) : Set (ℝ × ℝ) :=
  Ico ((p.1.val : ℝ) / ((n : ℝ)+1)) (((p.1.val : ℝ)+1) / ((n : ℝ)+1)) ×ˢ
    Ico ((p.2.val : ℝ) / ((n : ℝ)+1)) (((p.2.val : ℝ)+1) / ((n : ℝ)+1))

theorem coordinate_cell_iff (n : ℕ) (a : ZMod (n + 1)) (x : ℝ) :
    (x ∈ Ico (0 : ℝ) 1 ∧ (⌊((n : ℝ)+1)*x⌋ : ZMod (n + 1)) = a) ↔
      x ∈ Ico ((a.val : ℝ)/((n : ℝ)+1)) (((a.val : ℝ)+1)/((n : ℝ)+1)) := by
  have hn : 0 < (n : ℝ)+1 := by positivity
  constructor
  · rintro ⟨hx, ha⟩
    have hf0 : 0 ≤ ⌊((n : ℝ)+1)*x⌋ := Int.floor_nonneg.mpr (mul_nonneg hn.le hx.1)
    have hfN : ⌊((n : ℝ)+1)*x⌋ < (n + 1 : ℕ) := by
      apply Int.floor_lt.mpr
      push_cast
      nlinarith [mul_lt_mul_of_pos_left hx.2 hn]
    have hv : ((⌊((n : ℝ)+1)*x⌋ : ZMod (n + 1)).val : ℤ) = ⌊((n : ℝ)+1)*x⌋ := by
      rw [ZMod.val_intCast, Int.emod_eq_of_lt hf0 hfN]
    rw [ha] at hv
    have hb := Int.floor_eq_iff.mp hv.symm
    constructor
    · apply (div_le_iff₀ hn).mpr
      simpa [mul_comm] using hb.1
    · apply (lt_div_iff₀ hn).mpr
      simpa [mul_comm] using hb.2
  · intro hx
    have hlow := (div_le_iff₀ hn).mp hx.1
    have hhigh := (lt_div_iff₀ hn).mp hx.2
    have hf : ⌊((n : ℝ)+1)*x⌋ = (a.val : ℤ) := Int.floor_eq_iff.mpr
      ⟨by simpa [mul_comm] using hlow, by simpa [mul_comm] using hhigh⟩
    constructor
    · constructor
      · exact (div_nonneg (Nat.cast_nonneg _) hn.le).trans hx.1
      · have ha : (a.val : ℝ)+1 ≤ (n : ℝ)+1 := by exact_mod_cast a.val_lt
        nlinarith
    · rw [hf]
      simp

/-- Inside the unit square the modular cells are exactly the usual half-open rectangles. -/
theorem cell_inter_square (n : ℕ) (p : Grid (n + 1)) :
    unitSquare ∩ cell n p = cellRectangle n p := by
  ext z
  simp only [unitSquare, cell, cellIndex, cellRectangle, mem_inter_iff,
    mem_prod, mem_setOf_eq, Prod.mk.injEq]
  rw [← coordinate_cell_iff, ← coordinate_cell_iff]
  simp only [Prod.ext_iff, Prod.fst, Prod.snd]
  tauto

theorem squareMeasure_cell (n : ℕ) (p : Grid (n + 1)) :
    squareMeasure (cell n p) = ENNReal.ofReal (1 / ((n : ℝ)+1)^2) := by
  rw [squareMeasure, Measure.restrict_apply (measurableSet_cell n p), inter_comm,
    cell_inter_square, cellRectangle, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_Ico, Real.volume_Ico]
  have hx : ((p.1.val : ℝ)+1) / ((n : ℝ)+1) - (p.1.val : ℝ) / ((n : ℝ)+1) =
      1 / ((n : ℝ)+1) := by ring
  have hy : ((p.2.val : ℝ)+1) / ((n : ℝ)+1) - (p.2.val : ℝ) / ((n : ℝ)+1) =
      1 / ((n : ℝ)+1) := by ring
  rw [hx, hy, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [← pow_two, div_pow, one_pow]

theorem squareMeasure_univ : squareMeasure univ = 1 := by
  simp [squareMeasure, unitSquare, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico]

local instance : IsProbabilityMeasure squareMeasure := ⟨squareMeasure_univ⟩

def realCellAverage (f : ℝ × ℝ → ℝ) (n : ℕ) (p : Grid (n + 1)) : ℝ :=
  ((n : ℝ)+1)^2 * ∫ z in cell n p, f z ∂squareMeasure

theorem realCellAverage_eq_complex (f : ℝ × ℝ → ℝ) (n : ℕ) (p : Grid (n + 1)) :
    realCellAverage f n p = (cellAverage squareMeasure (fun z => (f z : ℂ)) n p).re := by
  unfold realCellAverage cellAverage
  rw [integral_complex_ofReal]
  have he : (n : ℂ)+1 = (((n : ℝ)+1 : ℝ) : ℂ) := by push_cast; rfl
  rw [he, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- The original bounded measurable real datum supplies all coefficient hypotheses.
The initial grid values are the exact normalized cell integrals, and the conclusion
is uniform over grid nodes at every fixed strictly positive time. -/
theorem bounded_cellAverage_limit (f : ℝ × ℝ → ℝ) (M : ℝ)
    (hf : AEStronglyMeasurable f squareMeasure)
    (hbound : ∀ᵐ z ∂squareMeasure, |f z| ≤ M) (t : ℝ) (ht : 0 < t) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ p : Grid (n + 1),
      |gridHeat (n + 1) t (realCellAverage f n) p -
        (continuumSeries (continuumCoefficient squareMeasure (fun z => (f z : ℂ)))
          t (gridPosition (n + 1) p)).re| < ε := by
  have hi : Integrable f squareMeasure := (integrable_const M).mono' hf
    (by simpa only [Real.norm_eq_abs] using hbound)
  have h := gridHeat_cellAverage_limit squareMeasure (fun z => (f z : ℂ)) hi.ofReal t ht
  simpa only [← realCellAverage_eq_complex] using h

end
end UnifiedTheory.LayerA.AbelianCurvatureHeatCellAverage
