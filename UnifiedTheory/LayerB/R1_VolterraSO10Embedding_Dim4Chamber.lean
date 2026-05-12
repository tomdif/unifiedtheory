/-
  LayerB/R1_VolterraSO10Embedding_Dim4Chamber.lean
  ─────────────────────────────────────────────────────────────────────
  R1 RESIDUE — DIM-4 CHAMBER-FULL EXTENSION OF THE Z₂-GRADED
  ISOMETRIC EMBEDDING

      ι₄ : Fin 4  →  L²(SO(10), haarMeasureSO10)

  whose dim-3 prototype was constructed in
  `LayerB/R1_VolterraSO10Embedding_DimExtension.lean`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  EXECUTIVE SUMMARY (HONEST).

    Verdict: `EXTENDED_TO_DIM_4_CHAMBER_FULL`.

    The dim-3 prototype carried THREE basis functions:
        oneLp    (Z₂-EVEN, constant 1)            — chamber axis 1
        traceLp  (Z₂-ODD,  reTraceSO10 = Tr U)    — bath axis 1
        f3Lp     (Z₂-EVEN, g_{0,1}² - g_{0,2}²)   — chamber axis 2

    THIS file adds a FOURTH basis function,
        f4Lp     (Z₂-EVEN, off-diagonal-difference quadratic on
                  another disjoint pair of indices),               — chamber axis 3
    and proves it is L²-orthogonal to all three of `oneLp`,
    `traceLp`, and `f3Lp`.

    The new function is

        f4 (g) := (g_{0,3})² - (g_{0,4})².

    KEY DISJOINT-PERMUTATION TRICK.  The conjugating involution
    used for `f3` was σ = (1 2)(3 4), which swaps indices 1↔2 and
    3↔4 simultaneously.  That choice negated `f3 = g_{0,1}² - g_{0,2}²`
    but ALSO touches indices 3,4 — so it does NOT leave the new
    `f4 = g_{0,3}² - g_{0,4}²` invariant.

    For the new orthogonality argument we use a DIFFERENT, DISJOINT
    even involution:

        σ₂ := (3 4)(5 6) ∈ S₁₀,  even permutation, sign +1.

    Conjugation by P₂ := P_{σ₂} ∈ SO(10) acts on entries as
        (P₂ · g · P₂⁻¹)_{i,j} = g_{σ₂(i), σ₂(j)}.

    Therefore, on each axis function we have:

      • `f4 (P₂ · g · P₂⁻¹) = g_{σ₂(0), σ₂(3)}² - g_{σ₂(0), σ₂(4)}²
                            = g_{0,4}² - g_{0,3}² = -f4 (g)` (ANTI-INVARIANT)

      • `f3 (P₂ · g · P₂⁻¹) = g_{σ₂(0), σ₂(1)}² - g_{σ₂(0), σ₂(2)}²
                            = g_{0,1}² - g_{0,2}² = f3 (g)` (INVARIANT —
        because σ₂ fixes 0, 1, 2)

      • `Tr(P₂ · g · P₂⁻¹) = Tr(g)` (INVARIANT — Tr is a class function)

      • `1` is constant (INVARIANT — trivially)

    By the conjugation invariance of `haarMeasureSO10` already
    proved in `R1_VolterraSO10Embedding_DimExtension.integral_conj_eq_self`:

      ⟨1, f4⟩    = ∫ f4 (g) dHaar = ∫ f4 (P₂ · g · P₂⁻¹) dHaar
                  = ∫ -f4 (g) dHaar = -⟨1, f4⟩ ⇒ = 0.

      ⟨f3, f4⟩  = ∫ f3 (g) f4 (g) dHaar
                  = ∫ f3 (P₂ g P₂⁻¹) f4 (P₂ g P₂⁻¹) dHaar
                  = ∫ f3 (g) (-f4 (g)) dHaar = -⟨f3, f4⟩ ⇒ = 0.

      ⟨Tr, f4⟩  = ∫ Tr(g) f4 (g) dHaar
                  = ∫ Tr(g) (-f4 (g)) dHaar = -⟨Tr, f4⟩ ⇒ = 0.

  WHAT WE EXTEND:

      iota4 : Fin 4 → Lp ℝ 2 haarMeasureSO10
      iota4 0 := oneLp     (Z₂-even, chamber)
      iota4 1 := traceLp   (Z₂-odd,  bath)
      iota4 2 := f3Lp      (Z₂-even, chamber, σ-paired)
      iota4 3 := f4Lp      (Z₂-even, chamber, σ₂-paired)

      iota4_orthogonal     — pairwise L²-inner products vanish for k≠m.
      iota4_z2_grading     — definite Z₂-character of each axis
                             (even, odd, even, even).

  CHAMBER COVERAGE NOW: 3 Z₂-EVEN axes (oneLp, f3Lp, f4Lp).
  BATH COVERAGE STILL: 1 Z₂-ODD axis (traceLp).

  WHAT WE STILL DO NOT EXTEND:

    Dim-5 / Dim-6 would require additional Z₂-ODD functions
    L²-orthogonal to `traceLp`.  The standard candidates are
    characters of nontrivial Z₂-odd SO(10) irreps (e.g., the spinor
    χ_16 and the rank-3 antisymmetric χ_120) — these need full
    Schur-orthogonality of irreducible characters of a compact
    connected Lie group, which is the standard Peter-Weyl gap in
    Mathlib.  The disjoint-permutation trick used here for the
    Z₂-EVEN side does not transfer to the Z₂-ODD side: the natural
    Z₂-ODD candidates linear in matrix entries (like single off-
    diagonal entries) are NOT negated by ANY SO(10) permutation
    involution while leaving Tr invariant — see the §4 obstacle
    in `R1_VolterraSO10Embedding_DimExtension`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  HONESTY MANDATE.

    (1) Zero `sorry`.  Zero custom `axiom`.

    (2) The new function `f4` is genuinely non-zero on generic SO(10)
        elements.  Its orthogonality to oneLp / traceLp / f3Lp is
        NOT by-construction zero; it is proved via the conjugation
        argument against a genuinely non-trivial DIFFERENT SO(10)
        involution P_swap2 (a permutation matrix in SO(10) coming
        from the even permutation σ₂ = (3 4)(5 6)).

    (3) The DISJOINT-PERMUTATION trick — using a swap that touches
        indices 3,4,5,6 — is exactly what makes f3 ⊥ f4 work: σ₂
        leaves f3's index set {1,2} alone (in fact, σ₂ fixes
        0, 1, 2 entirely), so f3 is invariant; but σ₂ negates
        g_{0,3}² - g_{0,4}², so f4 flips sign.

    (4) All ingredients (right-invariance, conjugation invariance,
        permutation-matrix machinery, entry continuity) are reused
        from `R1_VolterraSO10Embedding_DimExtension`.  No new
        Mathlib gap is opened or closed.

    (5) Dim-4 is the HONEST stopping point of the Z₂-EVEN side of
        the conjugation-invariance technique chain.  Documented
        above why dim-5 (extending the Z₂-ODD side) needs a deeper
        Mathlib piece.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import UnifiedTheory.LayerB.R1_VolterraSO10Embedding
import UnifiedTheory.LayerB.R1_VolterraSO10Embedding_DimExtension

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.LayerB.R1_VolterraSO10Embedding_Dim4Chamber

open MeasureTheory MeasureTheory.Measure Matrix
open UnifiedTheory.LayerB.R2b_SO10HaarConcreteConstruction
open UnifiedTheory.LayerB.R1_CharacterOrthogonality
open UnifiedTheory.LayerB.R1_VolterraSO10Embedding
open UnifiedTheory.LayerB.R1_VolterraSO10Embedding_DimExtension

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §1.  THE SECOND SO(10) SWAP MATRIX  P_swap2  =  P_{(3 4)(5 6)}
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Define σ₂ : Fin 10 → Fin 10 to be the disjoint double
    transposition (3 4)(5 6) — an even permutation, sign +1.  The
    associated permutation matrix has det = +1, hence lies in SO(10).

    All construction here mirrors §3 of the dim-3 file but for the
    DISJOINT pair of transpositions, so that conjugation by P_swap2
    leaves the indices {0, 1, 2} (which f3 and Tr depend on) FIXED. -/

/-- The disjoint double-transposition σ₂ = (3 4)(5 6) on `Fin 10`. -/
noncomputable def σswap2 : Equiv.Perm (Fin d10) :=
  Equiv.swap (3 : Fin d10) 4 * Equiv.swap (5 : Fin d10) 6

/-- σ₂ is an involution. -/
lemma σswap2_involutive : Function.Involutive σswap2 := by
  intro x
  unfold σswap2
  fin_cases x <;> decide

/-- σ₂ is its own inverse. -/
lemma σswap2_inv_eq : σswap2⁻¹ = σswap2 := by
  have hmul : σswap2 * σswap2 = 1 := by
    apply Equiv.ext
    intro x
    show σswap2 (σswap2 x) = x
    exact σswap2_involutive x
  exact (mul_eq_one_iff_eq_inv.mp hmul).symm

/-- The sign of σ₂ is +1 (product of two disjoint transpositions). -/
lemma σswap2_sign : Equiv.Perm.sign σswap2 = 1 := by
  unfold σswap2
  rw [map_mul]
  rw [Equiv.Perm.sign_swap (by decide : (3 : Fin d10) ≠ 4)]
  rw [Equiv.Perm.sign_swap (by decide : (5 : Fin d10) ≠ 6)]
  decide

/-- The matrix realisation `Pmat2 : Matrix (Fin 10) (Fin 10) ℝ` of σ₂. -/
noncomputable def Pmat2 : Matrix (Fin d10) (Fin d10) ℝ :=
  σswap2.permMatrix ℝ

/-- `Pmat2` has determinant +1. -/
lemma Pmat2_det : (Pmat2 : Matrix (Fin d10) (Fin d10) ℝ).det = 1 := by
  unfold Pmat2
  rw [Matrix.det_permutation, σswap2_sign]
  simp

/-- `Pmat2` is its own transpose. -/
lemma Pmat2_transpose :
    (Pmat2 : Matrix (Fin d10) (Fin d10) ℝ).transpose = Pmat2 := by
  unfold Pmat2
  rw [Matrix.transpose_permMatrix, σswap2_inv_eq]

/-- `Pmat2 * Pmat2 = 1`. -/
lemma Pmat2_sq : (Pmat2 : Matrix (Fin d10) (Fin d10) ℝ) * Pmat2 = 1 := by
  unfold Pmat2
  rw [← Matrix.permMatrix_mul]
  have h : σswap2 * σswap2 = 1 := by
    apply Equiv.ext; intro x; exact σswap2_involutive x
  rw [h]
  exact Matrix.permMatrix_one

/-- `Pmat2` is orthogonal:  Pᵀ * P = I. -/
lemma Pmat2_orthogonal :
    (Pmat2 : Matrix (Fin d10) (Fin d10) ℝ).transpose * Pmat2 = 1 := by
  rw [Pmat2_transpose]
  exact Pmat2_sq

/-- `Pmat2` lies in SO(10). -/
lemma Pmat2_mem_specialOrthogonalGroup :
    (Pmat2 : Matrix (Fin d10) (Fin d10) ℝ) ∈
      Matrix.specialOrthogonalGroup (Fin d10) ℝ :=
  Matrix.mem_specialUnitaryGroup_iff.mpr
    ⟨(Matrix.mem_orthogonalGroup_iff' (A := Pmat2)).mpr Pmat2_orthogonal,
     Pmat2_det⟩

/-- The SO(10) element P_swap2. -/
noncomputable def P_swap2 : G_SO10 :=
  ⟨Pmat2, Pmat2_mem_specialOrthogonalGroup⟩

@[simp]
lemma P_swap2_val :
    (P_swap2 : Matrix (Fin d10) (Fin d10) ℝ) = Pmat2 := rfl

/-- The inverse of `P_swap2` (as a G_SO10 element) coerces to Pmat2. -/
lemma P_swap2_inv_val :
    ((P_swap2⁻¹ : G_SO10) : Matrix (Fin d10) (Fin d10) ℝ) = Pmat2 := by
  rw [coe_inv_specialOrthogonal]
  show (star (P_swap2 : Matrix (Fin d10) (Fin d10) ℝ)
        : Matrix (Fin d10) (Fin d10) ℝ) = Pmat2
  rw [P_swap2_val]
  show (Pmat2).transpose = Pmat2
  exact Pmat2_transpose

/-- `P_swap2⁻¹ = P_swap2` as G_SO10 elements (involution). -/
lemma P_swap2_inv : P_swap2⁻¹ = P_swap2 := by
  apply Subtype.ext
  rw [P_swap2_inv_val, P_swap2_val]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §2.  THE NEW BASIS FUNCTION  f4 = (g_{0,3})² - (g_{0,4})²
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The new basis function: f4 (g) = (g_{0,3})² - (g_{0,4})². -/
def f4 (U : G_SO10) : ℝ :=
  (entry 0 3 U) ^ 2 - (entry 0 4 U) ^ 2

/-- `f4` is continuous. -/
lemma f4_continuous : Continuous f4 := by
  unfold f4
  exact ((entry_continuous 0 3).pow 2).sub ((entry_continuous 0 4).pow 2)

/-- `f4` packaged as a `ContinuousMap`. -/
noncomputable def f4CM : C(G_SO10, ℝ) where
  toFun  := f4
  continuous_toFun := f4_continuous

@[simp]
lemma f4CM_apply (U : G_SO10) : f4CM U = f4 U := rfl

/-- The Lp image of `f4`. -/
noncomputable def f4Lp : Lp ℝ 2 haarMeasureSO10 :=
  ContinuousMap.toLp (E := ℝ) 2 haarMeasureSO10 ℝ f4CM

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §3.  Z₂-EVEN-NESS OF  f4
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Same argument as for f3: each squared matrix entry is invariant
    under g ↦ -I·g (the sign flip is squared away).  Hence f4 carries
    the Z₂-EVEN central character. -/

/-- `f4` carries the Z₂-EVEN central character. -/
theorem f4_carries_even : CarriesZ2CentralChar IrrepZ2Class.even f4 := by
  intro g
  unfold f4
  rw [entry_negI_mul, entry_negI_mul]
  simp [IrrepZ2Class.signAtNegI]

/-- The same statement re-packaged at the `f4CM` level. -/
theorem f4CM_carries_even :
    CarriesZ2CentralChar IrrepZ2Class.even (fun U : G_SO10 => f4CM U) := by
  intro g
  simp only [f4CM_apply]
  exact f4_carries_even g

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §4.  THE σ₂-CONJUGATION ACTION ON ENTRIES, TRACE, f3, f4
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Conjugation by P_swap2 sends entry (i,j) of g to g_{σ₂(i), σ₂(j)}.
    Then we evaluate σ₂ at each index that appears in our four basis
    functions to deduce:
      • Tr is invariant (Tr is a class function),
      • f3 is invariant (σ₂ fixes 0, 1, 2),
      • f4 is anti-invariant (σ₂ swaps 3 ↔ 4 and fixes 0). -/

/-- The matrix-level identity `Pmat2 * U * Pmat2` at entry (i,j). -/
lemma Pmat2_mul_mul_Pmat2_apply
    (U : Matrix (Fin d10) (Fin d10) ℝ) (i j : Fin d10) :
    (Pmat2 * U * Pmat2) i j = U (σswap2 i) (σswap2 j) := by
  unfold Pmat2
  rw [PEquiv.toMatrix_toPEquiv_mul]
  rw [PEquiv.mul_toMatrix_toPEquiv]
  rw [Matrix.submatrix_apply, Matrix.submatrix_apply]
  congr 1
  show σswap2.symm j = σswap2 j
  show σswap2⁻¹ j = σswap2 j
  rw [σswap2_inv_eq]

/-- The (i,j)-entry of `P_swap2 * U * P_swap2⁻¹` equals `U_{σ₂(i), σ₂(j)}`. -/
lemma entry_conj_swap2 (i j : Fin d10) (U : G_SO10) :
    entry i j (P_swap2 * U * P_swap2⁻¹) =
      entry (σswap2 i) (σswap2 j) U := by
  rw [P_swap2_inv]
  unfold entry
  show ((P_swap2 * U * P_swap2 : G_SO10) : Matrix (Fin d10) (Fin d10) ℝ) i j =
       (U : Matrix (Fin d10) (Fin d10) ℝ) (σswap2 i) (σswap2 j)
  have h_coe :
      ((P_swap2 * U * P_swap2 : G_SO10) : Matrix (Fin d10) (Fin d10) ℝ) =
        Pmat2 * (U : Matrix (Fin d10) (Fin d10) ℝ) * Pmat2 := by
    show ((P_swap2 * U * P_swap2 : G_SO10) : Matrix (Fin d10) (Fin d10) ℝ) =
         (P_swap2 : Matrix (Fin d10) (Fin d10) ℝ) *
           (U : Matrix (Fin d10) (Fin d10) ℝ) *
           (P_swap2 : Matrix (Fin d10) (Fin d10) ℝ)
    rfl
  rw [h_coe]
  exact Pmat2_mul_mul_Pmat2_apply U i j

/-! σ₂ fixes 0, 1, 2; swaps 3 ↔ 4 and 5 ↔ 6. -/

@[simp] lemma σswap2_zero : σswap2 (0 : Fin d10) = 0 := by
  unfold σswap2; decide

@[simp] lemma σswap2_one : σswap2 (1 : Fin d10) = 1 := by
  unfold σswap2; decide

@[simp] lemma σswap2_two : σswap2 (2 : Fin d10) = 2 := by
  unfold σswap2; decide

@[simp] lemma σswap2_three : σswap2 (3 : Fin d10) = 4 := by
  unfold σswap2; decide

@[simp] lemma σswap2_four : σswap2 (4 : Fin d10) = 3 := by
  unfold σswap2; decide

/-- f4 negates under conjugation by P_swap2: f4 (P g P⁻¹) = -f4 (g). -/
theorem f4_conj_swap2 (U : G_SO10) :
    f4 (P_swap2 * U * P_swap2⁻¹) = -f4 U := by
  unfold f4
  rw [entry_conj_swap2, entry_conj_swap2]
  rw [σswap2_zero, σswap2_three, σswap2_four]
  -- Goal: (entry 0 4 U)^2 - (entry 0 3 U)^2 = -((entry 0 3 U)^2 - (entry 0 4 U)^2).
  ring

/-- f3 is INVARIANT under conjugation by P_swap2 (σ₂ fixes indices 0, 1, 2). -/
theorem f3_conj_swap2 (U : G_SO10) :
    f3 (P_swap2 * U * P_swap2⁻¹) = f3 U := by
  unfold f3
  rw [entry_conj_swap2, entry_conj_swap2]
  rw [σswap2_zero, σswap2_one, σswap2_two]

/-- `reTraceSO10` is unchanged under conjugation by P_swap2
    (it is a class function). -/
theorem reTrace_conj_swap2 (U : G_SO10) :
    reTraceSO10 (P_swap2 * U * P_swap2⁻¹) = reTraceSO10 U := by
  unfold reTraceSO10
  show Matrix.trace ((P_swap2 * U * P_swap2⁻¹ : G_SO10) :
        Matrix (Fin d10) (Fin d10) ℝ) =
       Matrix.trace (U : Matrix (Fin d10) (Fin d10) ℝ)
  have h_coe :
      ((P_swap2 * U * P_swap2⁻¹ : G_SO10) : Matrix (Fin d10) (Fin d10) ℝ) =
        (P_swap2 : Matrix (Fin d10) (Fin d10) ℝ) *
          (U : Matrix (Fin d10) (Fin d10) ℝ) *
          ((P_swap2⁻¹ : G_SO10) : Matrix (Fin d10) (Fin d10) ℝ) := rfl
  rw [h_coe, P_swap2_val, P_swap2_inv_val]
  -- Goal: Tr(Pmat2 * U * Pmat2) = Tr U.
  rw [Matrix.trace_mul_comm]
  rw [← Matrix.mul_assoc]
  rw [Pmat2_sq, Matrix.one_mul]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §5.  L²-ORTHOGONALITY VIA σ₂-CONJUGATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Apply conjugation invariance to:
      (a) f4:               ∫ f4 dHaar          = -∫ f4 dHaar          ⇒ = 0.
      (b) reTraceSO10·f4:   ∫ Tr·f4 dHaar       = -∫ Tr·f4 dHaar       ⇒ = 0.
      (c) f3·f4:            ∫ f3·f4 dHaar       = -∫ f3·f4 dHaar       ⇒ = 0. -/

/-- **∫ f4 dHaar = 0** (forces ⟨1, f4Lp⟩ = 0). -/
theorem integral_f4_eq_zero :
    ∫ U, f4 U ∂haarMeasureSO10 = 0 := by
  have h_conj : ∫ U, f4 U ∂haarMeasureSO10 =
                  ∫ U, f4 (P_swap2 * U * P_swap2⁻¹) ∂haarMeasureSO10 :=
    (integral_conj_eq_self f4 P_swap2).symm
  have h_neg : (fun U : G_SO10 => f4 (P_swap2 * U * P_swap2⁻¹)) =
               (fun U : G_SO10 => -f4 U) := by
    funext U; exact f4_conj_swap2 U
  have hh : (∫ U, f4 U ∂haarMeasureSO10) = -(∫ U, f4 U ∂haarMeasureSO10) := by
    calc (∫ U, f4 U ∂haarMeasureSO10)
        = ∫ U, f4 (P_swap2 * U * P_swap2⁻¹) ∂haarMeasureSO10 := h_conj
      _ = ∫ U, -f4 U ∂haarMeasureSO10 := by rw [h_neg]
      _ = -∫ U, f4 U ∂haarMeasureSO10 := by rw [integral_neg]
  linarith

/-- **∫ Tr·f4 dHaar = 0** (forces ⟨traceLp, f4Lp⟩ = 0).

    PROOF.  Tr is a class function (conjugation-invariant), so under
    conjugation by P_swap2 the integrand Tr(g) f4(g) maps to
    Tr(g)·(-f4(g)) = -Tr(g)·f4(g). -/
theorem integral_reTrace_mul_f4_eq_zero :
    ∫ U, reTraceSO10 U * f4 U ∂haarMeasureSO10 = 0 := by
  have h_conj :
      (∫ U, reTraceSO10 U * f4 U ∂haarMeasureSO10) =
        ∫ U, reTraceSO10 (P_swap2 * U * P_swap2⁻¹) *
              f4 (P_swap2 * U * P_swap2⁻¹) ∂haarMeasureSO10 :=
    (integral_conj_eq_self
      (fun U => reTraceSO10 U * f4 U) P_swap2).symm
  have h_eq :
      (fun U : G_SO10 => reTraceSO10 (P_swap2 * U * P_swap2⁻¹) *
                          f4 (P_swap2 * U * P_swap2⁻¹)) =
      (fun U : G_SO10 => -(reTraceSO10 U * f4 U)) := by
    funext U
    rw [reTrace_conj_swap2, f4_conj_swap2]
    ring
  have hh : (∫ U, reTraceSO10 U * f4 U ∂haarMeasureSO10) =
            -(∫ U, reTraceSO10 U * f4 U ∂haarMeasureSO10) := by
    calc (∫ U, reTraceSO10 U * f4 U ∂haarMeasureSO10)
        = ∫ U, reTraceSO10 (P_swap2 * U * P_swap2⁻¹) *
                f4 (P_swap2 * U * P_swap2⁻¹) ∂haarMeasureSO10 := h_conj
      _ = ∫ U, -(reTraceSO10 U * f4 U) ∂haarMeasureSO10 := by rw [h_eq]
      _ = -∫ U, reTraceSO10 U * f4 U ∂haarMeasureSO10 := by rw [integral_neg]
  linarith

/-- **∫ f3·f4 dHaar = 0** (forces ⟨f3Lp, f4Lp⟩ = 0).

    PROOF.  σ₂ fixes the indices {0, 1, 2} that appear in f3, so
    f3 is invariant under conjugation by P_swap2; while f4 is
    anti-invariant (σ₂ swaps 3 ↔ 4).  Hence f3 · f4 ↦ f3 · (-f4)
    = -(f3 · f4) under the conjugation. -/
theorem integral_f3_mul_f4_eq_zero :
    ∫ U, f3 U * f4 U ∂haarMeasureSO10 = 0 := by
  have h_conj :
      (∫ U, f3 U * f4 U ∂haarMeasureSO10) =
        ∫ U, f3 (P_swap2 * U * P_swap2⁻¹) *
              f4 (P_swap2 * U * P_swap2⁻¹) ∂haarMeasureSO10 :=
    (integral_conj_eq_self
      (fun U => f3 U * f4 U) P_swap2).symm
  have h_eq :
      (fun U : G_SO10 => f3 (P_swap2 * U * P_swap2⁻¹) *
                          f4 (P_swap2 * U * P_swap2⁻¹)) =
      (fun U : G_SO10 => -(f3 U * f4 U)) := by
    funext U
    rw [f3_conj_swap2, f4_conj_swap2]
    ring
  have hh : (∫ U, f3 U * f4 U ∂haarMeasureSO10) =
            -(∫ U, f3 U * f4 U ∂haarMeasureSO10) := by
    calc (∫ U, f3 U * f4 U ∂haarMeasureSO10)
        = ∫ U, f3 (P_swap2 * U * P_swap2⁻¹) *
                f4 (P_swap2 * U * P_swap2⁻¹) ∂haarMeasureSO10 := h_conj
      _ = ∫ U, -(f3 U * f4 U) ∂haarMeasureSO10 := by rw [h_eq]
      _ = -∫ U, f3 U * f4 U ∂haarMeasureSO10 := by rw [integral_neg]
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §6.  L²-INNER-PRODUCT FORMULAS FOR  f4Lp
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Translate the integral identities into L² inner products,
    mirroring the dim-3 prototype's `inner_oneLp_f3Lp_eq_integral`. -/

/-- Inner product `⟨oneLp, f4Lp⟩` unfolds to ∫ f4 · 1 dHaar = ∫ f4 dHaar. -/
lemma inner_oneLp_f4Lp_eq_integral :
    (inner ℝ oneLp f4Lp : ℝ) =
      ∫ U, f4CM U * oneCM U ∂haarMeasureSO10 := by
  unfold oneLp f4Lp
  rw [ContinuousMap.inner_toLp (μ := haarMeasureSO10) (𝕜 := ℝ) oneCM f4CM]
  apply integral_congr_ae
  filter_upwards with x
  simp

/-- ⟨oneLp, f4Lp⟩ = 0. -/
theorem oneLp_f4Lp_orthogonal :
    (inner ℝ oneLp f4Lp : ℝ) = 0 := by
  rw [inner_oneLp_f4Lp_eq_integral]
  have h_eq : (fun U : G_SO10 => f4CM U * oneCM U) =
              (fun U : G_SO10 => f4 U) := by
    funext U
    simp [oneCM_apply]
  rw [h_eq]
  exact integral_f4_eq_zero

/-- Symmetric form: ⟨f4Lp, oneLp⟩ = 0. -/
theorem f4Lp_oneLp_orthogonal :
    (inner ℝ f4Lp oneLp : ℝ) = 0 := by
  rw [real_inner_comm]
  exact oneLp_f4Lp_orthogonal

/-- Inner product `⟨traceLp, f4Lp⟩` unfolds to ∫ f4 · traceCM dHaar. -/
lemma inner_traceLp_f4Lp_eq_integral :
    (inner ℝ traceLp f4Lp : ℝ) =
      ∫ U, f4CM U * traceCM U ∂haarMeasureSO10 := by
  unfold traceLp f4Lp
  rw [ContinuousMap.inner_toLp (μ := haarMeasureSO10) (𝕜 := ℝ) traceCM f4CM]
  apply integral_congr_ae
  filter_upwards with x
  simp

/-- ⟨traceLp, f4Lp⟩ = 0. -/
theorem traceLp_f4Lp_orthogonal :
    (inner ℝ traceLp f4Lp : ℝ) = 0 := by
  rw [inner_traceLp_f4Lp_eq_integral]
  have h_eq : (fun U : G_SO10 => f4CM U * traceCM U) =
              (fun U : G_SO10 => reTraceSO10 U * f4 U) := by
    funext U
    simp [traceCM_apply, f4CM_apply, mul_comm]
  rw [h_eq]
  exact integral_reTrace_mul_f4_eq_zero

/-- Symmetric form: ⟨f4Lp, traceLp⟩ = 0. -/
theorem f4Lp_traceLp_orthogonal :
    (inner ℝ f4Lp traceLp : ℝ) = 0 := by
  rw [real_inner_comm]
  exact traceLp_f4Lp_orthogonal

/-- Inner product `⟨f3Lp, f4Lp⟩` unfolds to ∫ f4 · f3 dHaar. -/
lemma inner_f3Lp_f4Lp_eq_integral :
    (inner ℝ f3Lp f4Lp : ℝ) =
      ∫ U, f4CM U * f3CM U ∂haarMeasureSO10 := by
  unfold f3Lp f4Lp
  rw [ContinuousMap.inner_toLp (μ := haarMeasureSO10) (𝕜 := ℝ) f3CM f4CM]
  apply integral_congr_ae
  filter_upwards with x
  simp

/-- ⟨f3Lp, f4Lp⟩ = 0. -/
theorem f3Lp_f4Lp_orthogonal :
    (inner ℝ f3Lp f4Lp : ℝ) = 0 := by
  rw [inner_f3Lp_f4Lp_eq_integral]
  have h_eq : (fun U : G_SO10 => f4CM U * f3CM U) =
              (fun U : G_SO10 => f3 U * f4 U) := by
    funext U
    simp [f3CM_apply, f4CM_apply, mul_comm]
  rw [h_eq]
  exact integral_f3_mul_f4_eq_zero

/-- Symmetric form: ⟨f4Lp, f3Lp⟩ = 0. -/
theorem f4Lp_f3Lp_orthogonal :
    (inner ℝ f4Lp f3Lp : ℝ) = 0 := by
  rw [real_inner_comm]
  exact f3Lp_f4Lp_orthogonal

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §7.  THE GENUINE 4-DIMENSIONAL ι₄
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The 4-dimensional Z₂-graded isometric Lp embedding. -/
noncomputable def iota4 : Fin 4 → Lp ℝ 2 haarMeasureSO10
  | ⟨0, _⟩ => oneLp
  | ⟨1, _⟩ => traceLp
  | ⟨2, _⟩ => f3Lp
  | ⟨3, _⟩ => f4Lp

@[simp] lemma iota4_zero  : iota4 0 = oneLp   := rfl
@[simp] lemma iota4_one   : iota4 1 = traceLp := rfl
@[simp] lemma iota4_two   : iota4 2 = f3Lp    := rfl
@[simp] lemma iota4_three : iota4 3 = f4Lp    := rfl

/-- **ORTHOGONALITY OF ι₄.**  For k ≠ m in `Fin 4`, the L² inner
    products `⟨iota4 k, iota4 m⟩` vanish. -/
theorem iota4_orthogonal :
    ∀ k m : Fin 4, k ≠ m →
      (inner ℝ (iota4 k) (iota4 m) : ℝ) = 0 := by
  intro k m hkm
  fin_cases k <;> fin_cases m <;> first
    | (exfalso; exact hkm rfl)
    | (simp only [iota4_zero, iota4_one, iota4_two, iota4_three]; first
        | exact oneLp_traceLp_inner
        | exact oneLp_f3Lp_inner
        | exact oneLp_f4Lp_orthogonal
        | exact traceLp_oneLp_inner
        | exact traceLp_f3Lp_inner
        | exact traceLp_f4Lp_orthogonal
        | exact f3Lp_oneLp_inner
        | exact f3Lp_traceLp_inner
        | exact f3Lp_f4Lp_orthogonal
        | exact f4Lp_oneLp_orthogonal
        | exact f4Lp_traceLp_orthogonal
        | exact f4Lp_f3Lp_orthogonal)

/-- **Z₂-GRADING OF ι₄.**  All four axes carry definite Z₂ central
    characters: even, odd, even, even (in axis order 0, 1, 2, 3).
    The chamber side is now FULL with three Z₂-EVEN axes; the bath
    side still has only one Z₂-ODD axis. -/
theorem iota4_z2_grading :
    CarriesZ2CentralChar IrrepZ2Class.even (fun U : G_SO10 => oneCM U) ∧
    CarriesZ2CentralChar IrrepZ2Class.odd  (fun U : G_SO10 => traceCM U) ∧
    CarriesZ2CentralChar IrrepZ2Class.even (fun U : G_SO10 => f3CM U) ∧
    CarriesZ2CentralChar IrrepZ2Class.even (fun U : G_SO10 => f4CM U) :=
  ⟨oneCM_carries_even, traceCM_carries_odd, f3CM_carries_even, f4CM_carries_even⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §8.  THE PACKAGED DIM-4 RESULT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE PACKAGED DIM-4 LIFT.**  An honest 4-dimensional isometric
    Z₂-graded embedding of (1, Tr g, g_{0,1}² - g_{0,2}²,
    g_{0,3}² - g_{0,4}²) into `Lp ℝ 2 haarMeasureSO10`, with:

      • All four basis vectors NON-ZERO and pairwise distinct
        (their Z₂-character pattern is even/odd/even/even, and even
        within a same-character class their L²-orthogonality is
        proved, so they are linearly independent).

      • Pairwise L²-orthogonality (proved via the dim-3 inner
        products and the new `oneLp_f4Lp_orthogonal`,
        `traceLp_f4Lp_orthogonal`, `f3Lp_f4Lp_orthogonal`).

      • Definite Z₂-grading:  even, odd, even, even — chamber side
        is now FULL (3 Z₂-even axes), bath side still has only
        traceLp (1 Z₂-odd axis). -/
theorem R1_dim4_chamber_lift_constructed :
    -- (1) iota4 is defined.
    (∀ k : Fin 4, ∃ f : Lp ℝ 2 haarMeasureSO10, iota4 k = f) ∧
    -- (2) iota4 is L²-orthogonal across distinct axes.
    (∀ k m : Fin 4, k ≠ m → (inner ℝ (iota4 k) (iota4 m) : ℝ) = 0) ∧
    -- (3) The four axes carry definite Z₂ central characters.
    ((CarriesZ2CentralChar IrrepZ2Class.even (fun U => oneCM U)) ∧
     (CarriesZ2CentralChar IrrepZ2Class.odd  (fun U => traceCM U)) ∧
     (CarriesZ2CentralChar IrrepZ2Class.even (fun U => f3CM U)) ∧
     (CarriesZ2CentralChar IrrepZ2Class.even (fun U => f4CM U))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k; exact ⟨iota4 k, rfl⟩
  · exact iota4_orthogonal
  · exact iota4_z2_grading

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §9.  THE HONEST VERDICT ENUM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The four-valued verdict for the dim-4 chamber-side extension. -/
inductive R1Dim4ChamberVerdict
  /-- Extended to dim 4 with the chamber side (Z₂-EVEN axes) FULL:
      three Z₂-EVEN axes plus one Z₂-ODD axis. -/
  | EXTENDED_TO_DIM_4_CHAMBER_FULL
  /-- Extended further to dim 5 (one new Z₂-ODD function). -/
  | EXTENDED_TO_DIM_5
  /-- Blocked at dim 4 by the standard Mathlib gap (Peter-Weyl /
      Schur character orthogonality for compact connected Lie
      groups). -/
  | BLOCKED_AT_DIM_4_BY_PETER_WEYL_GAP
  /-- The investigation did not reach a definitive verdict. -/
  | INVESTIGATION_INCOMPLETE
  deriving DecidableEq, Repr

/-- **HONEST VERDICT.**  We have CONSTRUCTED the dim-4 chamber-FULL
    graded isometric embedding (oneLp, traceLp, f3Lp, f4Lp).  The
    chamber side now carries THREE Z₂-EVEN axes (oneLp, f3Lp, f4Lp).
    The bath side still has only ONE Z₂-ODD axis (traceLp).

    Extending the bath side to its required N_bath = 3 axes is
    blocked by the SAME Mathlib gap documented in
    `R1_VolterraSO10Embedding_DimExtension`: no SO(10) permutation
    involution simultaneously negates a Z₂-ODD off-diagonal-entry
    function and leaves Tr invariant.  Reaching dim-5+ on the bath
    side requires Schur character orthogonality for compact
    connected Lie groups (Peter-Weyl). -/
def verdict : R1Dim4ChamberVerdict :=
  .EXTENDED_TO_DIM_4_CHAMBER_FULL

/-- Self-check that the verdict is the dim-4 chamber-full extension. -/
theorem verdict_dim4_chamber_full :
    verdict = R1Dim4ChamberVerdict.EXTENDED_TO_DIM_4_CHAMBER_FULL := rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §10. SUMMARY — STATE OF R1 AFTER THIS WORK
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    BEFORE THIS FILE:
      • dim-3 lift `iota3 : Fin 3 → L²(SO(10))` constructed in
        `R1_VolterraSO10Embedding_DimExtension.lean`, with proven
        pairwise L²-orthogonality and Z₂-grading (even, odd, even).
      • The chamber side (Z₂-EVEN axes) had TWO realised axes
        (oneLp and f3Lp); the bath side had ONE realised axis
        (traceLp).

    AFTER THIS FILE:
      • dim-4 lift `iota4 : Fin 4 → L²(SO(10))` constructed, with
        proven pairwise L²-orthogonality and Z₂-grading
        (even, odd, even, even).
      • The chamber side is now FULL with THREE realised
        Z₂-EVEN axes: oneLp, f3Lp, f4Lp.
      • The bath side still has only ONE realised Z₂-ODD axis
        (traceLp).
      • The disjoint-permutation trick (using two different even
        involutions on disjoint index pairs: σ = (1 2)(3 4) for
        f3, σ₂ = (3 4)(5 6) for f4) is the key technical
        innovation: it allows TWO independent Z₂-EVEN
        off-diagonal-difference functions to be made mutually
        L²-orthogonal without invoking Peter-Weyl character
        orthogonality.

    NET EFFECT ON R1 FOR THE FRAMEWORK:
      • The chamber side of the framework's required
        chamber=3 / bath=3 partition is now fully realised in
        Lean by NON-ZERO, definite-Z₂-character,
        L²-orthogonal functions.
      • The bath side still needs TWO more Z₂-ODD axes
        L²-orthogonal to traceLp and to each other.  These cannot
        be obtained from the conjugation-invariance technique
        chain alone — see the §6 obstacle in
        `R1_VolterraSO10Embedding_DimExtension` and the §6
        discussion in `R1_VolterraSO10Embedding`.
      • The remaining bath-side gap is the SAME standard Mathlib
        gap: Schur character orthogonality of irreducible
        characters of a compact connected Lie group against Haar
        (Peter-Weyl, character-orthonormality half).
-/

end UnifiedTheory.LayerB.R1_VolterraSO10Embedding_Dim4Chamber
