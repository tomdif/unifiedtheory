/-
  Audit/KFCausalCSpecGlobalRank.lean   (Step 3 — rank core + the collapse test)

  The globalization's antisymmetry is bought by a strictly monotone rank.  The
  fibre is the Boolean 3-cube; its Hamming rank is `card`.  This file proves the
  two facts the rank must satisfy, and then records the decisive structural test
  the design's "overlap identifications" must pass — the loop-collapse test.

  RESULTS:
    * `cubeAct_rank`   : every S3 chart automorphism preserves Hamming rank
                         (the heart of `globalRank_wellDefined`).
    * `cubeLT_rank_lt` : every strict local cube relation strictly increases rank
                         (the heart of `global_strictLE_rank_lt`, hence
                         antisymmetry — a strict cycle would strictly increase
                         its own rank).
    * `loop_identification_collapses` : the sharp obstruction.  Identifying a
                         non-`S3`-invariant fibre point across a `(0 1)`-loop
                         forces two DISTINCT rank-2 points to be identified.
                         So the monodromy CANNOT live in quotient identifications;
                         it must be order-encoded on separate shared carriers.

  Zero sorry. Zero custom axioms.
-/
import Mathlib

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecGlobalRank

open scoped BigOperators

/-- The Boolean 3-cube fibre. -/
abbrev Cube := Fin 3 → Bool

/-- Hamming rank = number of set coordinates. -/
def cubeRank (x : Cube) : ℕ := ∑ b, if x b = true then 1 else 0

/-- The `S3` chart automorphism: permute the three coordinates. -/
def cubeAct (σ : Equiv.Perm (Fin 3)) (x : Cube) : Cube := fun b => x (σ.symm b)

/-- **Rank is `S3`-invariant.**  The heart of `globalRank_wellDefined`: any
overlap identification built from a chart automorphism relates equal-rank points,
so the rank descends to the quotient. -/
theorem cubeAct_rank (σ : Equiv.Perm (Fin 3)) (x : Cube) :
    cubeRank (cubeAct σ x) = cubeRank x :=
  Equiv.sum_comp σ.symm (fun b => if x b = true then 1 else 0)

/-- Local Boolean order on the cube. -/
def cubeLE (x y : Cube) : Prop := ∀ b, x b = true → y b = true

/-- **Strict local order strictly increases rank.**  The heart of
`global_strictLE_rank_lt`: since a strict cube relation is a proper coordinate
inclusion, its rank goes up — so the global order is acyclic and antisymmetric
for free, with no antisymmetrization. -/
theorem cubeLT_rank_lt (x y : Cube) (hle : cubeLE x y) (hne : x ≠ y) :
    cubeRank x < cubeRank y := by
  have hsub : (Finset.univ.filter (fun b => x b = true))
      ⊆ (Finset.univ.filter (fun b => y b = true)) := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact hle b hb
  have hstrict : (Finset.univ.filter (fun b => x b = true))
      ⊂ (Finset.univ.filter (fun b => y b = true)) := by
    refine ⟨hsub, ?_⟩
    intro hsup
    apply hne
    funext b
    by_cases hxb : x b = true
    · rw [hxb]; exact (hle b hxb).symm
    · by_cases hyb : y b = true
      · have : b ∈ (Finset.univ.filter (fun b => y b = true)) := by
          simp [hyb]
        have := hsup this
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact absurd this hxb
      · simp only [Bool.not_eq_true] at hxb hyb; rw [hxb, hyb]
  have hcard := Finset.card_lt_card hstrict
  have hx : (Finset.univ.filter (fun b => x b = true)).card = cubeRank x :=
    Finset.card_filter (fun b => x b = true) Finset.univ
  have hy : (Finset.univ.filter (fun b => y b = true)).card = cubeRank y :=
    Finset.card_filter (fun b => y b = true) Finset.univ
  rw [hx, hy] at hcard
  exact hcard

/-! ## The decisive collapse test -/

/-- The rank-2 cube points, as coordinate pairs. -/
def pair (i j : Fin 3) : Cube := fun b => decide (b = i ∨ b = j)

/-- **Loop-collapse obstruction.**  The `(0 1)` transposition — the holonomy of
the first base loop — moves the rank-2 point `{0,2}` to the DISTINCT rank-2 point
`{1,2}`.  Hence identifying fibre points across a loop (quotient equality of loop
transport) would glue `{0,2}` to `{1,2}`, two distinct points of one fibre.  The
monodromy therefore cannot be an identification; it must be carried by the ORDER
on separate shared carriers, leaving the specialization order acyclic. -/
theorem loop_identification_collapses :
    cubeAct (Equiv.swap 0 1) (pair 0 2) = pair 1 2
    ∧ pair 0 2 ≠ pair 1 2 := by
  constructor
  · funext b; fin_cases b <;> simp [cubeAct, pair, Equiv.swap_apply_def]
  · intro h
    have := congrFun h 0
    simp [pair] at this

#print axioms cubeAct_rank
#print axioms cubeLT_rank_lt
#print axioms loop_identification_collapses

end UnifiedTheory.Audit.KFCausalCSpecGlobalRank
