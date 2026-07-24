/-
  Audit/KFCausalCSpecMonodromy.lean   (arc file 5/6)

  MONODROMY: TWO UNFILLED CYCLES OBSTRUCT A GLOBAL SHEET LABELING

  The two unfilled cycles carry the adjacent transpositions (0 1) and (1 2).  A
  GLOBAL sheet labeling would be a direction assignment invariant under every
  holonomy — in particular under both transpositions.  We prove that the only
  such invariant zero-sum field is zero: the two transpositions alone force any
  invariant direction field to be constant, and a constant zero-sum field
  vanishes.  Hence there is no nontrivial global labeling; the local system is
  genuinely twisted.

  (The two adjacent transpositions generate all of S3, so the full holonomy image
  is S3; but only the two of them are needed to kill the global section, which is
  what we prove.)

  Zero sorry. Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalCSpecIntrinsicDescent

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecMonodromy

open scoped BigOperators
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile

/-- A zero-sum direction field (a section of the standard `S3`-representation). -/
def IsZeroSum (x : Direction → ℝ) : Prop := ∑ i, x i = 0

/-- **No global labeling.** A zero-sum direction field invariant under the two
adjacent transpositions `(0 1)` and `(1 2)` must be identically zero. -/
theorem no_global_section (x : Direction → ℝ)
    (h01 : x ∘ Equiv.swap 0 1 = x)
    (h12 : x ∘ Equiv.swap 1 2 = x)
    (hsum : IsZeroSum x) :
    x = 0 := by
  -- invariance under swap 0 1 gives x 0 = x 1
  have e01 : x 0 = x 1 := by
    have := congrFun h01 0
    simpa [Function.comp, Equiv.swap_apply_left] using this.symm
  -- invariance under swap 1 2 gives x 1 = x 2
  have e12 : x 1 = x 2 := by
    have := congrFun h12 1
    simpa [Function.comp, Equiv.swap_apply_left] using this.symm
  have h3 : x 0 + x 1 + x 2 = 0 := by
    simpa [IsZeroSum, Fin.sum_univ_three] using hsum
  have hx0 : x 0 = 0 := by
    rw [← e01, ← e01.trans e12] at h3; linarith
  have hx1 : x 1 = 0 := e01 ▸ hx0
  have hx2 : x 2 = 0 := (e01.trans e12) ▸ hx0
  funext k
  fin_cases k
  · simpa using hx0
  · simpa using hx1
  · simpa using hx2

/-- **The obstruction is intrinsic to unfilled cycles.** Equivalently: any
direction field that descends to a global section is forced to be the zero field
whenever the holonomy contains the two adjacent transpositions.  So a nonzero
global sheet labeling cannot exist. -/
theorem global_section_forces_trivial (x : Direction → ℝ)
    (h01 : x ∘ Equiv.swap 0 1 = x) (h12 : x ∘ Equiv.swap 1 2 = x)
    (hsum : IsZeroSum x) (hne : x ≠ 0) : False :=
  hne (no_global_section x h01 h12 hsum)

#print axioms no_global_section

end UnifiedTheory.Audit.KFCausalCSpecMonodromy
