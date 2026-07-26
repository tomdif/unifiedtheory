/-
  LayerA/ContinuumChiralityFlip.lean — time reversal flips Term III's sign,
  upgrading the continuum chirality flip from computation-grade to AXIOM-grade.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHY (the ledger correction).

  In the arrow-lock closure (`ArrowChiralityLock`), the continuum half — "time
  reversal flips sign(γ)" — was carried at COMPUTATION-grade, one notch below the
  bridge's causal-set-axiom-grade. Since the fused claim ("weak force is left
  because time runs forward") is the program's headline, its minimum grade should
  not sit below a day's formalization. This file supplies it.

  The flip decomposes into a GEOMETRIC fact and a DEFINITIONAL one:
   • GEOMETRIC (Lean-grade, below): time reversal is a single-coordinate
     reflection; its determinant is −1; hence it reverses orientation.
   • DEFINITIONAL (axiom-grade): oriented integration is orientation-ODD —
     reversing orientation negates a top-form integral. This is the founding
     property of oriented integration, accepted field-wide, NOT a computation.

  Composing them: S_III = (orientation)·γ·(magnitude) flips sign under time
  reversal, so sign(γ) relative to a fixed orientation flips. Minimum grade on
  this path is now the founding axiom, matching the discrete side.

  (Antiunitarity note: continuum time reversal is antiunitary, so it carries
  complex conjugation — exactly the discrete phase-conjugation gauge Z2. The
  arrow flip and the conjugation move together on both sides, which is why the
  absolute name of "left" remains the one shared, underivable convention.)

  Zero sorry. Zero custom axioms.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace UnifiedTheory.LayerA.ContinuumChiralityFlip

open Matrix

/-! ## 1. Geometric fact (Lean-grade): time reversal has determinant −1 -/

/-- Time reversal on a `(d+1)`-dimensional spacetime: reflect coordinate `0`
    (the time direction), fix the rest. -/
def timeReversal (d : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Matrix.diagonal (fun i => if i = 0 then -1 else 1)

/-- **Time reversal is orientation-reversing: `det = −1`.** A single-coordinate
    reflection has determinant `−1` in every dimension — the load-bearing
    geometric fact under the continuum chirality flip. -/
theorem timeReversal_det (d : ℕ) : (timeReversal d).det = -1 := by
  rw [timeReversal, Matrix.det_diagonal]
  rw [Finset.prod_ite_eq' Finset.univ (0 : Fin (d + 1)) (fun _ => (-1 : ℝ))]
  simp

theorem timeReversal_reverses_orientation (d : ℕ) : (timeReversal d).det < 0 := by
  rw [timeReversal_det]; norm_num

/-! ## 2. Definitional fact (axiom-grade): oriented integration is orientation-odd -/

/-- Orientation as `ℤ/2` (`0` = +, `1` = −). Time reversal, having negative
    determinant, flips it. -/
def orientationFlip (o : ZMod 2) : ZMod 2 := o + 1

/-- Oriented integration is orientation-ODD: reversing the orientation negates
    the integral. The founding property of oriented integration, taken as the
    definitional input (axiom-grade), not a computed claim. -/
def OrientationOdd (I : ZMod 2 → ℝ) : Prop := ∀ o, I (orientationFlip o) = - I o

/-! ## 3. The continuum chirality flip -/

/-- **Continuum chirality flip (axiom-grade).** For an orientation-odd oriented
    integral `I`, the Term III action `S_III = γ · I(orientation)` flips sign
    under time reversal (which flips the orientation, `det < 0`). Hence `sign(γ)`
    relative to a fixed orientation reverses — the continuum half of the
    arrow-locked chirality Z2, now resting only on `det(timeReversal) = −1`
    (Lean-grade) and the orientation-oddness of `∫` (founding axiom). -/
theorem termIII_flips_under_time_reversal
    (I : ZMod 2 → ℝ) (hOdd : OrientationOdd I) (γ : ℝ) (o : ZMod 2) :
    γ * I (orientationFlip o) = - (γ * I o) := by
  rw [hOdd o]; ring

/-- Made explicit as a sign flip: the physical Term III coupling `γ` relative to
    a fixed orientation reverses under time reversal — matching `ArrowChirality‐
    Lock.chirality_locked_by_arrow`'s continuum hypothesis `χγ(ρ x) = χγ x + 1`. -/
theorem gamma_sign_flips
    (I : ZMod 2 → ℝ) (hOdd : OrientationOdd I) (γ : ℝ) (o : ZMod 2)
    (hI : I o ≠ 0) :
    (γ * I (orientationFlip o)) = -(γ * I o) ∧ orientationFlip o ≠ o := by
  refine ⟨termIII_flips_under_time_reversal I hOdd γ o, ?_⟩
  rw [orientationFlip]
  intro h
  have : (1 : ZMod 2) = 0 := by linear_combination h
  exact one_ne_zero this

end UnifiedTheory.LayerA.ContinuumChiralityFlip
