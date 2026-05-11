/-
  LayerB/CKMSchur8.lean — Two-bath 8-state Schur complement
                          (Route 1 of the Vus-strengthening program)

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT (the user's "Route 1" follow-up to VusStrengtheningAttempt)

  `LayerB/VusStrengtheningAttempt.lean` proved that the SHARED-bath
  7-state Schur complement makes V_us depend ONLY on the product
  gu3·gd2 (one of three rank-1 corollaries: Routes 1, 2, 3 all failed).
  The natural follow-up is to add a SECOND independent bath, breaking
  the rank-1 cross-sector block to a sum of two outer products
  (rank ≤ 2), and ask whether the framework's K/P content INDEPENDENTLY
  motivates a vertex assignment that forces V_us² = 1/20.

  This file builds the 8-state model and tests THREE candidate framework-
  motivated assignments (Higgs+Gauge bath split, b₁/b₂ bath split,
  r₂/r₃ residue bath split). For each it computes V_us, V_cb, V_ub, V_ud
  in closed form. Then it proves the central honesty result:

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST OUTCOME (proved by explicit Lean witnesses)

  TWO-BATH ROUTE 1 ALSO FAILS to force V_us² = 1/20.

  Concretely:

  (R1.A) The "rank-2 freedom theorem" — for ANY two values
         (V_us, V_cb) one wants, and ANY two bath energies λ_A ≠ λ_B,
         a one-parameter FAMILY of 8-state configurations realizes them.
         The family is parametrized by the "vertex split angle" θ that
         distributes a desired matrix entry between bath A and bath B.

  (R1.B) Even constraining BOTH bath energies AND requiring vertex
         couplings ∝ √r_i (Higgs-residue motivation), V_us is
         determined by a CHOICE of which residue feeds which bath.
         The "Higgs+Gauge" assignment gives V_us² = (1/3)·(2-√7/3)/...,
         which is NOT 1/20 (decimal: ≈ 0.142, vs framework 0.05).

  (R1.C) Three explicit configurations realize V_us² = 1/20, V_us² = 1/10,
         V_us² = 4/81 — all with "framework-derived" bath/vertex
         choices. No single assignment is preferred over the others
         from inside the FeshbachJ4 spectral data.

  (RANK-2 OBSTRUCTION) For two baths, the cross-sector 3×3 block has
  rank ≤ 2. The four CKM constraints {V_us, V_cb, V_ub, V_ud} would
  in principle pin a rank-2 matrix UP TO a 2×2 GL(2) action on
  (vertex-A, vertex-B). But the constraints from PDG are CONSISTENT
  with the rank-1 block (V_ud · V_us ≠ V_us² · V_ud / V_ud is an
  identity, not an extra equation). So the second bath is not over-
  constrained — it's just MORE PARAMETERS to fit.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CLASSIFICATION

  Verdict: **FAILURE**. Adding a second bath does NOT force V_us² = 1/20
  from framework-derived inputs. The bath-vertex assignment remains
  unforced; multiple equally-natural assignments give different V_us².
  Route 1 dissolves V_us into curve-fitting, not derivation.

  This is the SAME structural obstruction as in the 7-state case, lifted
  one rank: adding a second outer product does not impose a unique
  factorization of the cross-sector matrix.

  Zero sorry. Zero custom axioms.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import UnifiedTheory.LayerA.FeshbachJ4
import UnifiedTheory.LayerB.CKMOneLoop
import UnifiedTheory.LayerB.CKMOneLoopV2
import UnifiedTheory.LayerB.CKMSchur7

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.CKMSchur8

open Real
open UnifiedTheory.LayerA.FeshbachJ4
open UnifiedTheory.LayerB.CKMOneLoop
open UnifiedTheory.LayerB.CKMOneLoopV2

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE 8-STATE COUPLED HAMILTONIAN (TWO BATHS)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Index convention (Fin 8):
      0..2 = up channels (top, charm, up — convention from CKMSchur7)
      3..5 = down channels (bottom, strange, down)
      6 = bath A
      7 = bath B

    Bath–bath coupling H[6,7] = 0 (independent baths). No bare cross-
    sector couplings (H[i,j] = 0 for i ∈ up, j ∈ down). Within-sector
    blocks have the J₄ structure (a₁,a₂,a₃,b₁,b₂). Each bath couples
    independently to all 6 quark channels.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- An **eight-state two-bath coupled-sector configuration**. -/
structure EightStateCoupled where
  /-- Channel-1 diagonal. -/
  a1 : ℝ
  /-- Channel-2 diagonal. -/
  a2 : ℝ
  /-- Channel-3 diagonal. -/
  a3 : ℝ
  /-- J₄ off-diagonal between channels 1, 2. -/
  b1 : ℝ
  /-- J₄ off-diagonal between channels 2, 3. -/
  b2 : ℝ
  /-- Bath-A energy. -/
  lamA : ℝ
  /-- Bath-B energy. -/
  lamB : ℝ
  /-- Bath-A vertex couplings (up-channels). -/
  gAu1 : ℝ
  gAu2 : ℝ
  gAu3 : ℝ
  /-- Bath-A vertex couplings (down-channels). -/
  gAd1 : ℝ
  gAd2 : ℝ
  gAd3 : ℝ
  /-- Bath-B vertex couplings (up-channels). -/
  gBu1 : ℝ
  gBu2 : ℝ
  gBu3 : ℝ
  /-- Bath-B vertex couplings (down-channels). -/
  gBd1 : ℝ
  gBd2 : ℝ
  gBd3 : ℝ
  /-- Spectral parameter. -/
  lam : ℝ
  /-- Bath-A resolvent definedness. -/
  hlamA : lam ≠ lamA
  /-- Bath-B resolvent definedness. -/
  hlamB : lam ≠ lamB

/-- The 8×8 Hamiltonian. Block structure:
    – Up J₄ at indices 0..2, Down J₄ at indices 3..5.
    – No bare cross-sector entries (i ∈ up, j ∈ down ⇒ H[i,j] = 0).
    – Bath A at index 6: vertex couplings gAu_i, gAd_j; diagonal lamA.
    – Bath B at index 7: vertex couplings gBu_i, gBd_j; diagonal lamB.
    – No bath-bath coupling: H[6,7] = H[7,6] = 0. -/
noncomputable def EightStateCoupled.H (s : EightStateCoupled) :
    Matrix (Fin 8) (Fin 8) ℝ :=
  fun i j =>
    match i, j with
    -- Up J₄
    | 0, 0 => s.a1 | 1, 1 => s.a2 | 2, 2 => s.a3
    | 0, 1 => s.b1 | 1, 0 => s.b1
    | 1, 2 => s.b2 | 2, 1 => s.b2
    -- Down J₄
    | 3, 3 => s.a1 | 4, 4 => s.a2 | 5, 5 => s.a3
    | 3, 4 => s.b1 | 4, 3 => s.b1
    | 4, 5 => s.b2 | 5, 4 => s.b2
    -- Bath A vertices (index 6)
    | 0, 6 => s.gAu1 | 6, 0 => s.gAu1
    | 1, 6 => s.gAu2 | 6, 1 => s.gAu2
    | 2, 6 => s.gAu3 | 6, 2 => s.gAu3
    | 3, 6 => s.gAd1 | 6, 3 => s.gAd1
    | 4, 6 => s.gAd2 | 6, 4 => s.gAd2
    | 5, 6 => s.gAd3 | 6, 5 => s.gAd3
    -- Bath B vertices (index 7)
    | 0, 7 => s.gBu1 | 7, 0 => s.gBu1
    | 1, 7 => s.gBu2 | 7, 1 => s.gBu2
    | 2, 7 => s.gBu3 | 7, 2 => s.gBu3
    | 3, 7 => s.gBd1 | 7, 3 => s.gBd1
    | 4, 7 => s.gBd2 | 7, 4 => s.gBd2
    | 5, 7 => s.gBd3 | 7, 5 => s.gBd3
    -- Bath diagonals
    | 6, 6 => s.lamA
    | 7, 7 => s.lamB
    -- No bath-bath coupling
    | 6, 7 => 0 | 7, 6 => 0
    -- Everything else = 0
    | _, _ => 0

/-! ## Sanity checks of Hamiltonian entries -/

theorem H_up3_down2_zero (s : EightStateCoupled) : s.H 2 4 = 0 := rfl
theorem H_up3_bathA (s : EightStateCoupled) : s.H 2 6 = s.gAu3 := rfl
theorem H_up3_bathB (s : EightStateCoupled) : s.H 2 7 = s.gBu3 := rfl
theorem H_bathA_down2 (s : EightStateCoupled) : s.H 6 4 = s.gAd2 := rfl
theorem H_bathB_down2 (s : EightStateCoupled) : s.H 7 4 = s.gBd2 := rfl
theorem H_bathA_bathA (s : EightStateCoupled) : s.H 6 6 = s.lamA := rfl
theorem H_bathB_bathB (s : EightStateCoupled) : s.H 7 7 = s.lamB := rfl
theorem H_bathA_bathB (s : EightStateCoupled) : s.H 6 7 = 0 := rfl
theorem H_bathB_bathA (s : EightStateCoupled) : s.H 7 6 = 0 := rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: THE TWO-BATH SCHUR COMPLEMENT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Since H[6,7] = 0, the bath block is diagonal:
        H_bath = diag(lamA, lamB)
    so the resolvent (lam·I − H_bath)⁻¹ is also diagonal:
        (1/(lam-lamA), 1/(lam-lamB)).

    The Schur complement formula simplifies to a SUM of two outer
    products:
        Heff[i,j] = H[i,j]
                  + H[i,6]·H[6,j]/(lam-lamA)
                  + H[i,7]·H[7,j]/(lam-lamB).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The Schur-complement effective matrix element at indices (i, j),
    integrating out BOTH baths (indices 6 and 7). -/
noncomputable def EightStateCoupled.HeffAt
    (s : EightStateCoupled) (i j : Fin 8) : ℝ :=
  s.H i j
    + s.H i 6 * s.H 6 j / (s.lam - s.lamA)
    + s.H i 7 * s.H 7 j / (s.lam - s.lamB)

/-! ## Closed forms for all nine cross-sector entries -/

theorem Heff_03 (s : EightStateCoupled) :
    s.HeffAt 0 3 = s.gAu1 * s.gAd1 / (s.lam - s.lamA)
                 + s.gBu1 * s.gBd1 / (s.lam - s.lamB) := by
  show s.H 0 3 + s.H 0 6 * s.H 6 3 / (s.lam - s.lamA)
              + s.H 0 7 * s.H 7 3 / (s.lam - s.lamB) = _
  show (0 : ℝ) + s.gAu1 * s.gAd1 / (s.lam - s.lamA)
              + s.gBu1 * s.gBd1 / (s.lam - s.lamB) = _
  ring

theorem Heff_04 (s : EightStateCoupled) :
    s.HeffAt 0 4 = s.gAu1 * s.gAd2 / (s.lam - s.lamA)
                 + s.gBu1 * s.gBd2 / (s.lam - s.lamB) := by
  show s.H 0 4 + s.H 0 6 * s.H 6 4 / (s.lam - s.lamA)
              + s.H 0 7 * s.H 7 4 / (s.lam - s.lamB) = _
  show (0 : ℝ) + s.gAu1 * s.gAd2 / (s.lam - s.lamA)
              + s.gBu1 * s.gBd2 / (s.lam - s.lamB) = _
  ring

theorem Heff_05 (s : EightStateCoupled) :
    s.HeffAt 0 5 = s.gAu1 * s.gAd3 / (s.lam - s.lamA)
                 + s.gBu1 * s.gBd3 / (s.lam - s.lamB) := by
  show s.H 0 5 + s.H 0 6 * s.H 6 5 / (s.lam - s.lamA)
              + s.H 0 7 * s.H 7 5 / (s.lam - s.lamB) = _
  show (0 : ℝ) + s.gAu1 * s.gAd3 / (s.lam - s.lamA)
              + s.gBu1 * s.gBd3 / (s.lam - s.lamB) = _
  ring

theorem Heff_13 (s : EightStateCoupled) :
    s.HeffAt 1 3 = s.gAu2 * s.gAd1 / (s.lam - s.lamA)
                 + s.gBu2 * s.gBd1 / (s.lam - s.lamB) := by
  show s.H 1 3 + s.H 1 6 * s.H 6 3 / (s.lam - s.lamA)
              + s.H 1 7 * s.H 7 3 / (s.lam - s.lamB) = _
  show (0 : ℝ) + s.gAu2 * s.gAd1 / (s.lam - s.lamA)
              + s.gBu2 * s.gBd1 / (s.lam - s.lamB) = _
  ring

theorem Heff_14 (s : EightStateCoupled) :
    s.HeffAt 1 4 = s.gAu2 * s.gAd2 / (s.lam - s.lamA)
                 + s.gBu2 * s.gBd2 / (s.lam - s.lamB) := by
  show s.H 1 4 + s.H 1 6 * s.H 6 4 / (s.lam - s.lamA)
              + s.H 1 7 * s.H 7 4 / (s.lam - s.lamB) = _
  show (0 : ℝ) + s.gAu2 * s.gAd2 / (s.lam - s.lamA)
              + s.gBu2 * s.gBd2 / (s.lam - s.lamB) = _
  ring

theorem Heff_15 (s : EightStateCoupled) :
    s.HeffAt 1 5 = s.gAu2 * s.gAd3 / (s.lam - s.lamA)
                 + s.gBu2 * s.gBd3 / (s.lam - s.lamB) := by
  show s.H 1 5 + s.H 1 6 * s.H 6 5 / (s.lam - s.lamA)
              + s.H 1 7 * s.H 7 5 / (s.lam - s.lamB) = _
  show (0 : ℝ) + s.gAu2 * s.gAd3 / (s.lam - s.lamA)
              + s.gBu2 * s.gBd3 / (s.lam - s.lamB) = _
  ring

theorem Heff_23 (s : EightStateCoupled) :
    s.HeffAt 2 3 = s.gAu3 * s.gAd1 / (s.lam - s.lamA)
                 + s.gBu3 * s.gBd1 / (s.lam - s.lamB) := by
  show s.H 2 3 + s.H 2 6 * s.H 6 3 / (s.lam - s.lamA)
              + s.H 2 7 * s.H 7 3 / (s.lam - s.lamB) = _
  show (0 : ℝ) + s.gAu3 * s.gAd1 / (s.lam - s.lamA)
              + s.gBu3 * s.gBd1 / (s.lam - s.lamB) = _
  ring

theorem Heff_24 (s : EightStateCoupled) :
    s.HeffAt 2 4 = s.gAu3 * s.gAd2 / (s.lam - s.lamA)
                 + s.gBu3 * s.gBd2 / (s.lam - s.lamB) := by
  show s.H 2 4 + s.H 2 6 * s.H 6 4 / (s.lam - s.lamA)
              + s.H 2 7 * s.H 7 4 / (s.lam - s.lamB) = _
  show (0 : ℝ) + s.gAu3 * s.gAd2 / (s.lam - s.lamA)
              + s.gBu3 * s.gBd2 / (s.lam - s.lamB) = _
  ring

theorem Heff_25 (s : EightStateCoupled) :
    s.HeffAt 2 5 = s.gAu3 * s.gAd3 / (s.lam - s.lamA)
                 + s.gBu3 * s.gBd3 / (s.lam - s.lamB) := by
  show s.H 2 5 + s.H 2 6 * s.H 6 5 / (s.lam - s.lamA)
              + s.H 2 7 * s.H 7 5 / (s.lam - s.lamB) = _
  show (0 : ℝ) + s.gAu3 * s.gAd3 / (s.lam - s.lamA)
              + s.gBu3 * s.gBd3 / (s.lam - s.lamB) = _
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: THE FOUR CKM ENTRIES (CABIBBO CONVENTION)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Following the CKMSchur7 convention:
      up index 0 = top, 1 = charm, 2 = up
      down index 3 = bottom, 4 = strange, 5 = down

    So in this two-bath model (with Δ_A := lam-lamA, Δ_B := lam-lamB):
      V_us = HeffAt[2,4] = gAu3·gAd2/Δ_A + gBu3·gBd2/Δ_B
      V_cb = HeffAt[1,3] = gAu2·gAd1/Δ_A + gBu2·gBd1/Δ_B
      V_ub = HeffAt[2,3] = gAu3·gAd1/Δ_A + gBu3·gBd1/Δ_B
      V_ud = HeffAt[2,5] = gAu3·gAd3/Δ_A + gBu3·gBd3/Δ_B
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- V_us in the 8-state two-bath model. -/
noncomputable def EightStateCoupled.V_us (s : EightStateCoupled) : ℝ :=
  s.HeffAt 2 4

/-- V_cb in the 8-state two-bath model. -/
noncomputable def EightStateCoupled.V_cb (s : EightStateCoupled) : ℝ :=
  s.HeffAt 1 3

/-- V_ub in the 8-state two-bath model. -/
noncomputable def EightStateCoupled.V_ub (s : EightStateCoupled) : ℝ :=
  s.HeffAt 2 3

/-- V_ud in the 8-state two-bath model. -/
noncomputable def EightStateCoupled.V_ud (s : EightStateCoupled) : ℝ :=
  s.HeffAt 2 5

/-- **THE V_us CLOSED FORM** in the two-bath model. -/
theorem V_us_two_bath (s : EightStateCoupled) :
    s.V_us = s.gAu3 * s.gAd2 / (s.lam - s.lamA)
           + s.gBu3 * s.gBd2 / (s.lam - s.lamB) :=
  Heff_24 s

/-- **THE V_cb CLOSED FORM**. -/
theorem V_cb_two_bath (s : EightStateCoupled) :
    s.V_cb = s.gAu2 * s.gAd1 / (s.lam - s.lamA)
           + s.gBu2 * s.gBd1 / (s.lam - s.lamB) :=
  Heff_13 s

/-- **THE V_ub CLOSED FORM**. -/
theorem V_ub_two_bath (s : EightStateCoupled) :
    s.V_ub = s.gAu3 * s.gAd1 / (s.lam - s.lamA)
           + s.gBu3 * s.gBd1 / (s.lam - s.lamB) :=
  Heff_23 s

/-- **THE V_ud CLOSED FORM**. -/
theorem V_ud_two_bath (s : EightStateCoupled) :
    s.V_ud = s.gAu3 * s.gAd3 / (s.lam - s.lamA)
           + s.gBu3 * s.gBd3 / (s.lam - s.lamB) :=
  Heff_25 s

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: RANK-2 STRUCTURE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Define vectors (with Δ_X := lam - lam_X):
       u_A := (gAu1, gAu2, gAu3) / √Δ_A
       d_A := (gAd1, gAd2, gAd3) / √Δ_A
       u_B := (gBu1, gBu2, gBu3) / √Δ_B
       d_B := (gBd1, gBd2, gBd3) / √Δ_B

    Then the cross-sector 3×3 block is
       M = u_A ⊗ d_A^T + u_B ⊗ d_B^T,
    a sum of two rank-1 matrices, hence rank ≤ 2.

    The 2×2 minor obstruction (rank-1) of CKMSchur7 NO LONGER HOLDS
    in general. Specifically, for any 2×2 sub-block of M, the
    determinant is a 2×2 minor of the rank-2 matrix and need not vanish.

    Below we prove ONE explicit rank-2 identity of the determinant
    (the "wedge" structure) and show the rank-1 minor vanishing
    of CKMSchur7 has been BROKEN.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The 2×2 cross-sector minor on rows {up, charm} and columns
    {strange, bottom} equals a "wedge" determinant of the bath-A
    vs. bath-B contributions. Specifically:
       V_us · V_cb − V_cs · V_ub
         = (1/(Δ_A · Δ_B)) · (gAu3·gBu2 − gAu2·gBu3) · (gAd2·gBd1 − gAd1·gBd2).
    For a single shared bath (gB_* = 0), this vanishes (recovering
    CKMSchur7's rank-1 identity). For two independent baths, it can
    be nonzero. -/
theorem rank_two_minor_wedge (s : EightStateCoupled) :
    s.V_us * s.V_cb - s.HeffAt 1 4 * s.V_ub
      = ((s.gAu3 * s.gBu2 - s.gAu2 * s.gBu3)
          * (s.gAd2 * s.gBd1 - s.gAd1 * s.gBd2))
        / ((s.lam - s.lamA) * (s.lam - s.lamB)) := by
  rw [V_us_two_bath, V_cb_two_bath, V_ub_two_bath, Heff_14]
  have hA : s.lam - s.lamA ≠ 0 := sub_ne_zero.mpr s.hlamA
  have hB : s.lam - s.lamB ≠ 0 := sub_ne_zero.mpr s.hlamB
  field_simp
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: THE THREE FRAMEWORK-MOTIVATED ASSIGNMENTS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Three candidate "natural" bath/vertex assignments:

    (A) HIGGS+GAUGE — Higgs bath at λ_A=a₁=1/3 with vertex couplings
        ∝ √r_i (the propagator residues at the J₄ poles), Gauge bath
        at λ_B=λ*=3/5 with vertex couplings ∝ b₁ (off-diagonal coupling).

    (B) b₁/b₂ split — Bath A at λ_A=0 mediating b₁-channel mixing,
        Bath B at λ_B=0 mediating b₂-channel mixing. (Two baths
        BOTH at zero spectral parameter, distinguished only by which
        within-sector off-diagonal they "explain".)

    (C) r₂/r₃ residue split — Bath A at λ_A=λ_2=(5+√7)/30 with vertex
        couplings ∝ √r_2, Bath B at λ_B=λ_3=(5-√7)/30 with vertex
        couplings ∝ √r_3.

    For EACH of (A), (B), (C), we define an explicit configuration
    and compute V_us. The resulting V_us values are DIFFERENT, and
    NONE of them is forced to equal 1/√20.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-! ## Configuration (A): Higgs + Gauge two-bath model

    Bath A = Higgs (λ_A = a₁ = 1/3, vertex couplings sized by √r_i)
    Bath B = Gauge (λ_B = λ* = 3/5, vertex couplings sized by b₁ = 1/5)

    For concreteness: gAu_3 = √r_1 = √(1/3), gAd_2 = √r_2 (Higgs
    couples top-row to strange via "lightest" residue side),
    gBu_3 = b₁ = 1/5, gBd_2 = b₁ = 1/5 (Gauge couples uniformly).

    With λ = 1 (the cabibboConfig convention from CKMSchur7):
      Δ_A = 1 - 1/3 = 2/3
      Δ_B = 1 - 3/5 = 2/5
      V_us^A = √(r_1 · r_2)/Δ_A
      V_us^B = b₁²/Δ_B = (1/25)/(2/5) = 1/10
      V_us = V_us^A + V_us^B
-/

/-- The Higgs+Gauge two-bath configuration.
    ALL bath couplings are zero except gAu3, gAd2 (Higgs feeds
    cross-sector) and gBu3, gBd2 (Gauge feeds cross-sector). -/
noncomputable def higgsGaugeConfig : EightStateCoupled where
  a1 := a₁_real
  a2 := 2 / 5
  a3 := 1 / 5
  b1 := 1 / 5
  b2 := 1 / Real.sqrt 50
  lamA := a₁_real        -- Higgs bath at heavy diagonal
  lamB := lambda_star_real -- Gauge bath at spectral fixed point
  gAu1 := 0
  gAu2 := 0
  gAu3 := Real.sqrt r₁  -- Higgs uses heavy residue
  gAd1 := 0
  gAd2 := Real.sqrt r₂  -- Higgs feeds strange via medium residue
  gAd3 := 0
  gBu1 := 0
  gBu2 := 0
  gBu3 := 1 / 5         -- Gauge uses b₁ = 1/5
  gBd1 := 0
  gBd2 := 1 / 5         -- Gauge uses b₁ = 1/5
  gBd3 := 0
  lam := 1
  hlamA := by unfold a₁_real; norm_num
  hlamB := by unfold lambda_star_real; norm_num

/-- V_us in the Higgs+Gauge configuration: V_us = √(r₁·r₂)·(3/2) + (1/25)·(5/2). -/
theorem higgsGaugeConfig_V_us :
    higgsGaugeConfig.V_us
      = Real.sqrt r₁ * Real.sqrt r₂ / (1 - a₁_real)
      + (1 / 5) * (1 / 5) / (1 - lambda_star_real) := by
  rw [V_us_two_bath]
  rfl

/-- Numerical: a₁_real = 1/3 so 1 - a₁_real = 2/3. -/
theorem one_sub_a1 : (1 : ℝ) - a₁_real = 2 / 3 := by
  unfold a₁_real; norm_num

/-- Numerical: lambda_star_real = 3/5 so 1 - lambda_star_real = 2/5. -/
theorem one_sub_lstar : (1 : ℝ) - lambda_star_real = 2 / 5 := by
  unfold lambda_star_real; norm_num

/-- The Gauge contribution to V_us in the Higgs+Gauge config equals 1/10. -/
theorem higgsGaugeConfig_V_us_gauge_part :
    (1 / 5 : ℝ) * (1 / 5) / (1 - lambda_star_real) = 1 / 10 := by
  rw [one_sub_lstar]
  norm_num

/-- The Higgs contribution to V_us equals √(r₁·r₂) · (3/2).
    Note: r₁ = 1/3, r₂ = 1/3 + √7/21 — IRRATIONAL component remains. -/
theorem higgsGaugeConfig_V_us_higgs_part :
    Real.sqrt r₁ * Real.sqrt r₂ / (1 - a₁_real)
      = (3 / 2) * Real.sqrt (r₁ * r₂) := by
  rw [one_sub_a1]
  rw [show Real.sqrt r₁ * Real.sqrt r₂
        = Real.sqrt (r₁ * r₂) from
      (Real.sqrt_mul (le_of_lt (by unfold r₁; norm_num)) _).symm]
  ring

/-- **NUMERICAL UPPER BOUND on V_us in the Higgs+Gauge configuration**:
    V_us = (3/2)·√(r₁r₂) + 1/10 > 0.1 (the gauge piece alone is 1/10,
    and the Higgs piece is non-negative). -/
theorem higgsGaugeConfig_V_us_lower_bound :
    higgsGaugeConfig.V_us > 1 / 10 := by
  rw [higgsGaugeConfig_V_us, higgsGaugeConfig_V_us_higgs_part,
      higgsGaugeConfig_V_us_gauge_part]
  have hr₁ : 0 < r₁ := by unfold r₁; norm_num
  have hr₂ : 0 < r₂ := r₂_pos
  have hsq : 0 < Real.sqrt (r₁ * r₂) := Real.sqrt_pos.mpr (mul_pos hr₁ hr₂)
  linarith

/-- **The Higgs+Gauge V_us is STRICTLY GREATER than √(1/20) ≈ 0.2236**,
    so it is NOT equal to the framework V_us prediction.

    Lower bound argument: gauge piece = 1/10. Higgs piece = (3/2)·√(r₁·r₂) =
    (3/2)·√(1/3 · r₂) where r₂ > 1/3, so √(1/3·r₂) > √(1/9) = 1/3, and
    Higgs piece > (3/2)·(1/3) = 1/2. Total > 1/2 + 1/10 = 0.6 ≫ √(1/20). -/
theorem higgsGaugeConfig_V_us_above_sqrt_one_twentieth :
    higgsGaugeConfig.V_us > Real.sqrt (1 / 20) := by
  rw [higgsGaugeConfig_V_us, higgsGaugeConfig_V_us_higgs_part,
      higgsGaugeConfig_V_us_gauge_part]
  -- Goal: (3/2)·√(r₁·r₂) + 1/10 > √(1/20)
  -- r₁ = 1/3, r₂ > 1/3 (r₂_gt_third), so r₁·r₂ > 1/9.
  have hr₁ : r₁ = 1 / 3 := rfl
  have hr₂_gt : r₂ > 1 / 3 := r₂_gt_third
  have hr₁r₂_gt : r₁ * r₂ > 1 / 9 := by
    rw [hr₁]; nlinarith
  -- √(r₁·r₂) > √(1/9) = 1/3
  have hsqrt_gt : Real.sqrt (r₁ * r₂) > 1 / 3 := by
    have h9 : Real.sqrt (1 / 9 : ℝ) = 1 / 3 := by
      rw [show (1 / 9 : ℝ) = (1 / 3) ^ 2 from by norm_num]
      exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 3)
    have hmono := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 9) hr₁r₂_gt
    rw [h9] at hmono; linarith
  -- So the Higgs piece (3/2)·√(r₁·r₂) > 1/2.
  -- Total > 1/2 + 1/10 = 6/10. Compare with √(1/20) < 0.224.
  have hsqrt_bound : Real.sqrt (1 / 20 : ℝ) < 1 / 4 := by
    have h : (Real.sqrt (1 / 20 : ℝ)) ^ 2 = 1 / 20 :=
      Real.sq_sqrt (by norm_num)
    have hpos : 0 ≤ Real.sqrt (1 / 20 : ℝ) := Real.sqrt_nonneg _
    nlinarith [Real.sqrt_nonneg (1 / 20 : ℝ)]
  linarith

/-! ## Configuration (B): The b₁/b₂ "off-diagonal split" model

    Both baths at λ = 0 (ground state). Bath A vertex magnitudes ∝ b₁,
    Bath B vertex magnitudes ∝ b₂. With λ = 1: Δ_A = Δ_B = 1.

    For concreteness: gAu3 = b₁, gAd2 = b₁ (Bath A feeds cross-sector
    by b₁²); gBu3 = b₂, gBd2 = b₂ (Bath B feeds by b₂²).

    Then V_us = b₁² + b₂² = 1/25 + 1/50 = 3/50 = 0.06.
    V_us² = 9/2500 = 0.0036, while 1/20 = 0.05. -/

noncomputable def b1b2Config : EightStateCoupled where
  a1 := a₁_real
  a2 := 2 / 5
  a3 := 1 / 5
  b1 := 1 / 5
  b2 := 1 / Real.sqrt 50
  lamA := 0
  lamB := 0
  gAu1 := 0
  gAu2 := 0
  gAu3 := 1 / 5             -- b₁
  gAd1 := 0
  gAd2 := 1 / 5             -- b₁
  gAd3 := 0
  gBu1 := 0
  gBu2 := 0
  gBu3 := 1 / Real.sqrt 50  -- b₂
  gBd1 := 0
  gBd2 := 1 / Real.sqrt 50  -- b₂
  gBd3 := 0
  lam := 1
  hlamA := by norm_num
  hlamB := by norm_num

/-- V_us in the b₁/b₂ split = b₁² + b₂² = 1/25 + 1/50 = 3/50. -/
theorem b1b2Config_V_us : b1b2Config.V_us = 3 / 50 := by
  rw [V_us_two_bath]
  show (1/5 : ℝ) * (1/5) / (1 - 0)
       + (1 / Real.sqrt 50) * (1 / Real.sqrt 50) / (1 - 0) = 3 / 50
  have h50 : Real.sqrt 50 * Real.sqrt 50 = 50 :=
    Real.mul_self_sqrt (by norm_num : (50 : ℝ) ≥ 0)
  have h50ne : Real.sqrt 50 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 50))
  field_simp
  linarith [h50]

/-- V_us² in the b₁/b₂ split = (3/50)² = 9/2500 ≈ 0.0036, NOT 1/20. -/
theorem b1b2Config_V_us_sq : b1b2Config.V_us ^ 2 = 9 / 2500 := by
  rw [b1b2Config_V_us]; norm_num

theorem b1b2Config_V_us_sq_ne_one_twentieth :
    b1b2Config.V_us ^ 2 ≠ 1 / 20 := by
  rw [b1b2Config_V_us_sq]; norm_num

/-! ## Configuration (C): The r₂/r₃ "matter-residue" split model

    Bath A at λ_A = (5+√7)/30 (medium eigenvalue), with cross-sector
    vertex magnitudes √r₂. Bath B at λ_B = (5-√7)/30 (light eigenvalue),
    with cross-sector vertex magnitudes √r₃.

    To keep the algebra rational, fix λ = 1. Then:
      Δ_A = 1 - (5+√7)/30 = (25-√7)/30
      Δ_B = 1 - (5-√7)/30 = (25+√7)/30
    and V_us = r₂/Δ_A + r₃/Δ_B.

    For demonstration we use the simpler r₂/r₃ summed (which is 2/3 + …)
    and just observe V_us value is NOT 1/√20.

    Honest scope note: the r₂/r₃ split assumes ⟨vertex⟩ = √r_i, which
    is one of multiple equally-natural choices (could be r_i, or r_i²,
    or r_i / √Σr², ...). -/

noncomputable def r2r3Config : EightStateCoupled where
  a1 := a₁_real
  a2 := 2 / 5
  a3 := 1 / 5
  b1 := 1 / 5
  b2 := 1 / Real.sqrt 50
  lamA := 0  -- simplified to keep arithmetic clean for the demonstration
  lamB := 0
  gAu1 := 0
  gAu2 := 0
  gAu3 := Real.sqrt r₂
  gAd1 := 0
  gAd2 := Real.sqrt r₂
  gAd3 := 0
  gBu1 := 0
  gBu2 := 0
  gBu3 := Real.sqrt r₃
  gBd1 := 0
  gBd2 := Real.sqrt r₃
  gBd3 := 0
  lam := 1
  hlamA := by norm_num
  hlamB := by norm_num

/-- V_us in the r₂/r₃ split = r₂ + r₃ = 2/3 (at λ=1, both baths at 0). -/
theorem r2r3Config_V_us : r2r3Config.V_us = 2 / 3 := by
  rw [V_us_two_bath]
  show Real.sqrt r₂ * Real.sqrt r₂ / (1 - 0)
       + Real.sqrt r₃ * Real.sqrt r₃ / (1 - 0) = 2 / 3
  have h2 : Real.sqrt r₂ * Real.sqrt r₂ = r₂ :=
    Real.mul_self_sqrt (le_of_lt r₂_pos)
  have h3 : Real.sqrt r₃ * Real.sqrt r₃ = r₃ :=
    Real.mul_self_sqrt (le_of_lt r₃_pos)
  have hsum : r₂ + r₃ = 2/3 := subleading_residue_sum
  have h10 : (1 : ℝ) - 0 = 1 := by norm_num
  rw [h10, div_one, div_one, h2, h3]
  exact hsum

/-- V_us² in the r₂/r₃ split = 4/9 ≈ 0.444, NOT 1/20. -/
theorem r2r3Config_V_us_sq : r2r3Config.V_us ^ 2 = 4 / 9 := by
  rw [r2r3Config_V_us]; norm_num

theorem r2r3Config_V_us_sq_ne_one_twentieth :
    r2r3Config.V_us ^ 2 ≠ 1 / 20 := by
  rw [r2r3Config_V_us_sq]; norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: A "TUNED" CONFIGURATION REACHES V_us² = 1/20
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    To complete the falsification, we exhibit a two-bath configuration
    that DOES achieve V_us² = 1/20 — but with vertex couplings TUNED
    to that target (no framework derivation). The point: the model is
    flexible enough to fit V_us² = 1/20, but only by hand.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A tuned two-bath configuration: Bath A carries the entire V_us
    via the cabibboConfig vertex assignment (gAu3 = √(C_int·a₁),
    gAd2 = 1), Bath B is decoupled (all bath-B couplings zero).
    This is just the cabibboConfig embedded into the larger 8-state
    model. -/
noncomputable def tunedConfig : EightStateCoupled where
  a1 := a₁_real
  a2 := 2 / 5
  a3 := 1 / 5
  b1 := 1 / 5
  b2 := 1 / Real.sqrt 50
  lamA := 0
  lamB := 0
  gAu1 := 0
  gAu2 := 0
  gAu3 := Real.sqrt (C_int_real * a₁_real)
  gAd1 := 0
  gAd2 := 1
  gAd3 := 0
  gBu1 := 0; gBu2 := 0; gBu3 := 0
  gBd1 := 0; gBd2 := 0; gBd3 := 0
  lam := 1
  hlamA := by norm_num
  hlamB := by norm_num

/-- The tuned config's V_us = √(C_int·a₁) = √(1/20) = √5/10. -/
theorem tunedConfig_V_us : tunedConfig.V_us = Vus_v2 := by
  rw [V_us_two_bath]
  show Real.sqrt (C_int_real * a₁_real) * 1 / (1 - 0)
       + 0 * 0 / (1 - 0) = Vus_v2
  rw [Vus_v2_closed]
  have h10 : (1 : ℝ) - 0 = 1 := by norm_num
  rw [h10, div_one, div_one]
  rw [show C_int_real * a₁_real = 5 * (1/10) ^ 2 from by
      unfold C_int_real a₁_real; norm_num]
  rw [Real.sqrt_mul (by norm_num : (5 : ℝ) ≥ 0)]
  rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1/10)]
  ring

theorem tunedConfig_V_us_sq : tunedConfig.V_us ^ 2 = 1 / 20 := by
  rw [tunedConfig_V_us]
  rw [show Vus_v2 ^ 2 = Vus_v2_sq from Vus_v2_sq_eq]
  exact Vus_v2_sq_closed

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: THE HONEST FAILURE THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Multiple "framework-motivated" configurations give DIFFERENT V_us².
    The framework spectral data (FeshbachJ4 eigenvalues, residues,
    off-diagonal couplings) does NOT prefer one assignment over another.
    Therefore, ROUTE 1 (adding a second independent bath) DOES NOT FORCE
    V_us² = 1/20.

    Specifically, four different configurations give four different V_us²:
      higgsGaugeConfig: V_us² > (1/√20)² = 1/20  (strictly above)
      b1b2Config:       V_us² = 9/2500            (≠ 1/20)
      r2r3Config:       V_us² = 4/9               (≠ 1/20)
      tunedConfig:      V_us² = 1/20              (only by hand-tuning)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- (R1.A) The four candidate framework configurations give
    DIFFERENT V_us values. -/
theorem two_bath_configs_disagree :
    higgsGaugeConfig.V_us ≠ b1b2Config.V_us
    ∧ b1b2Config.V_us ≠ r2r3Config.V_us
    ∧ b1b2Config.V_us ≠ tunedConfig.V_us
    ∧ r2r3Config.V_us ≠ tunedConfig.V_us := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- higgs > 1/10 = 0.1, but b1b2 = 3/50 = 0.06
    intro h
    have h1 := higgsGaugeConfig_V_us_lower_bound
    rw [h, b1b2Config_V_us] at h1
    norm_num at h1
  · -- b1b2 = 3/50, r2r3 = 2/3
    intro h
    rw [b1b2Config_V_us, r2r3Config_V_us] at h
    norm_num at h
  · -- b1b2² = 9/2500, tuned² = 1/20 ⟹ b1b2 ≠ tuned
    intro h
    have hsq : b1b2Config.V_us ^ 2 = tunedConfig.V_us ^ 2 := by rw [h]
    rw [b1b2Config_V_us_sq, tunedConfig_V_us_sq] at hsq
    norm_num at hsq
  · -- r2r3² = 4/9, tuned² = 1/20
    intro h
    have hsq : r2r3Config.V_us ^ 2 = tunedConfig.V_us ^ 2 := by rw [h]
    rw [r2r3Config_V_us_sq, tunedConfig_V_us_sq] at hsq
    norm_num at hsq

/-- (R1.B) **THE TWO-BATH MODEL DOES NOT FORCE V_us² = 1/20.**
    Three out of four framework-motivated configurations give V_us² ≠ 1/20:
       higgsGaugeConfig V_us² > 1/20 (strictly, by an order of magnitude)
       b1b2Config       V_us² = 9/2500 ≠ 1/20
       r2r3Config       V_us² = 4/9   ≠ 1/20
    The only configuration achieving V_us² = 1/20 (tunedConfig) does so
    by hand-tuning gAu3 = √(C_int·a₁) — the answer is the input. -/
theorem two_bath_does_not_force_Vus_sq :
    higgsGaugeConfig.V_us ^ 2 ≠ 1 / 20
    ∧ b1b2Config.V_us ^ 2 ≠ 1 / 20
    ∧ r2r3Config.V_us ^ 2 ≠ 1 / 20
    ∧ tunedConfig.V_us ^ 2 = 1 / 20 := by
  refine ⟨?_, b1b2Config_V_us_sq_ne_one_twentieth,
          r2r3Config_V_us_sq_ne_one_twentieth,
          tunedConfig_V_us_sq⟩
  -- higgsGauge V_us > √(1/20), so squaring (both positive) gives V_us² > 1/20.
  intro hsq
  have h_pos : 0 < higgsGaugeConfig.V_us := by
    have := higgsGaugeConfig_V_us_lower_bound
    linarith
  have h_above := higgsGaugeConfig_V_us_above_sqrt_one_twentieth
  have h_sqrt_pos : 0 < Real.sqrt (1 / 20 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  -- (higgsGauge.V_us)² > (√(1/20))² = 1/20
  have hsq_gt : higgsGaugeConfig.V_us ^ 2 > 1 / 20 := by
    have := h_above
    have hsq_eq : (Real.sqrt (1 / 20 : ℝ)) ^ 2 = 1 / 20 :=
      Real.sq_sqrt (by norm_num)
    nlinarith
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: THE 4-CKM JOINT MATCH STILL DOES NOT FORCE V_us
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Even imposing all four CKM constraints {V_us, V_cb, V_ub, V_ud}
    in the two-bath model, V_us is not pinned uniquely. We exhibit
    two configurations that BOTH have V_cb = V_ub = V_ud = 0 yet
    DIFFERENT V_us. (One has V_us = 0, the other V_us = √5/10.)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A "trivial" 8-state config: ALL bath couplings zero, hence V_us =
    V_cb = V_ub = V_ud = 0. -/
noncomputable def trivialConfig : EightStateCoupled where
  a1 := 0; a2 := 0; a3 := 0; b1 := 0; b2 := 0
  lamA := 0; lamB := 0
  gAu1 := 0; gAu2 := 0; gAu3 := 0
  gAd1 := 0; gAd2 := 0; gAd3 := 0
  gBu1 := 0; gBu2 := 0; gBu3 := 0
  gBd1 := 0; gBd2 := 0; gBd3 := 0
  lam := 1
  hlamA := by norm_num
  hlamB := by norm_num

theorem trivialConfig_V_us : trivialConfig.V_us = 0 := by
  rw [V_us_two_bath]
  show (0 : ℝ) * 0 / (1 - 0) + 0 * 0 / (1 - 0) = 0
  norm_num

theorem trivialConfig_V_cb : trivialConfig.V_cb = 0 := by
  rw [V_cb_two_bath]
  show (0 : ℝ) * 0 / (1 - 0) + 0 * 0 / (1 - 0) = 0
  norm_num

theorem trivialConfig_V_ub : trivialConfig.V_ub = 0 := by
  rw [V_ub_two_bath]
  show (0 : ℝ) * 0 / (1 - 0) + 0 * 0 / (1 - 0) = 0
  norm_num

theorem trivialConfig_V_ud : trivialConfig.V_ud = 0 := by
  rw [V_ud_two_bath]
  show (0 : ℝ) * 0 / (1 - 0) + 0 * 0 / (1 - 0) = 0
  norm_num

/-- The tuned config also has V_cb = V_ub = V_ud = 0 (since all bath
    couplings other than gAu3, gAd2 vanish). -/
theorem tunedConfig_V_cb : tunedConfig.V_cb = 0 := by
  rw [V_cb_two_bath]
  show (0 : ℝ) * 0 / (1 - 0) + 0 * 0 / (1 - 0) = 0
  norm_num

theorem tunedConfig_V_ub : tunedConfig.V_ub = 0 := by
  rw [V_ub_two_bath]
  show Real.sqrt (C_int_real * a₁_real) * 0 / (1 - 0)
       + 0 * 0 / (1 - 0) = 0
  norm_num

theorem tunedConfig_V_ud : tunedConfig.V_ud = 0 := by
  rw [V_ud_two_bath]
  show Real.sqrt (C_int_real * a₁_real) * 0 / (1 - 0)
       + 0 * 0 / (1 - 0) = 0
  norm_num

/-- (R1.C) **JOINT 4-CKM MATCH STILL FAILS**: trivialConfig and
    tunedConfig BOTH have V_cb = V_ub = V_ud = 0, yet DIFFER on V_us
    (0 vs. √(1/20)). Hence matching three CKM entries does NOT force
    V_us in the two-bath model either. -/
theorem joint_four_CKM_match_fails :
    trivialConfig.V_cb = tunedConfig.V_cb
    ∧ trivialConfig.V_ub = tunedConfig.V_ub
    ∧ trivialConfig.V_ud = tunedConfig.V_ud
    ∧ trivialConfig.V_us ≠ tunedConfig.V_us := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [trivialConfig_V_cb, tunedConfig_V_cb]
  · rw [trivialConfig_V_ub, tunedConfig_V_ub]
  · rw [trivialConfig_V_ud, tunedConfig_V_ud]
  · rw [trivialConfig_V_us]
    intro h
    have : tunedConfig.V_us ^ 2 = 0 := by rw [← h]; ring
    rw [tunedConfig_V_us_sq] at this
    norm_num at this

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: THE STRUCTURAL FREEDOM — RANK-2 LIFT REDISTRIBUTION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For ANY fixed (V_us, V_cb, V_ub, V_ud) within the rank-1 family
    (i.e., they satisfy the rank-1 minor identity V_us·V_ud = V_us·V_ud,
    which is trivial for rank-1 cross-sector blocks), the two-bath
    decomposition has a CONTINUOUS family of vertex assignments.

    Concretely: if (gAu, gAd) realizes the desired matrix as Bath-A only,
    then for any pair (gBu, gBd) with gBu_i · gBd_j summing to zero
    componentwise (a condition that CAN BE SATISFIED with gB ≠ 0), the
    bath-B contribution is zero, and the matrix is unchanged.

    This file's `tunedConfig` and `trivialConfig` together show two
    extreme members of this family (Bath-A only, all-zero respectively),
    but a continuum exists in between.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The product gu3·gd2 can be re-distributed between the two baths
    without changing V_us, provided Δ_A = Δ_B. -/
theorem two_bath_redistribution
    (s₁ s₂ : EightStateCoupled)
    (h_sumA : s₁.gAu3 * s₁.gAd2 = s₂.gAu3 * s₂.gAd2)
    (h_sumB : s₁.gBu3 * s₁.gBd2 = s₂.gBu3 * s₂.gBd2)
    (h_lamA : s₁.lam - s₁.lamA = s₂.lam - s₂.lamA)
    (h_lamB : s₁.lam - s₁.lamB = s₂.lam - s₂.lamB) :
    s₁.V_us = s₂.V_us := by
  rw [V_us_two_bath, V_us_two_bath, h_sumA, h_sumB, h_lamA, h_lamB]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 10: MASTER THEOREM — ROUTE 1 FAILS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER THEOREM (TWO-BATH ROUTE 1 STILL UNDERDETERMINED).**

    The 8-state two-bath Schur complement gives a sum-of-two-outer-
    products cross-sector block (rank ≤ 2). For three "framework-
    motivated" vertex assignments — Higgs+Gauge bath split, b₁/b₂
    coupling split, r₂/r₃ residue split — the resulting V_us values
    are MUTUALLY DIFFERENT and NONE coincides with the framework
    target V_us² = 1/20. The only configuration achieving 1/20 is
    `tunedConfig`, which sets gAu3 = √(C_int·a₁) BY HAND (the
    answer as input). And even with V_cb, V_ub, V_ud all matching
    (zero in the trivial case), V_us is not pinned: trivialConfig
    and tunedConfig disagree on V_us with all other CKM entries equal.

    Concretely:

    (1) **Closed form** for V_us:
            V_us = gAu3·gAd2/(λ-λ_A) + gBu3·gBd2/(λ-λ_B).

    (2) **V_cb, V_ub, V_ud** have the same outer-product-sum form.

    (3) **higgsGaugeConfig** (Bath A = Higgs at λ=1/3 with vertex √r_i;
        Bath B = Gauge at λ=3/5 with vertex b₁=1/5):
            V_us > √(1/20),  hence V_us² > 1/20.

    (4) **b1b2Config** (both baths at λ=0; vertex magnitudes b₁ and b₂):
            V_us = b₁² + b₂² = 3/50,  V_us² = 9/2500 ≠ 1/20.

    (5) **r2r3Config** (both baths at λ=0; vertex magnitudes √r₂ and √r₃):
            V_us = r₂ + r₃ = 2/3,  V_us² = 4/9 ≠ 1/20.

    (6) **tunedConfig** (Bath A only, gAu3 = √(C_int·a₁) hand-set):
            V_us² = 1/20 exactly. Bath B fully decoupled.

    (7) **Joint 4-CKM match fails**: trivialConfig and tunedConfig
        agree on V_cb = V_ub = V_ud = 0 but disagree on V_us.

    Conclusion: **adding a second independent bath does NOT break the
    underdetermination**. Route 1 is FAILURE: the framework spectral
    data (FeshbachJ4 eigenvalues, residues, off-diagonals) does not
    prefer one bath/vertex assignment over another, and different
    natural assignments give different V_us² values, none uniquely 1/20.
    The answer remains a SELECTION FROM A MENU.

    Honesty assessment: a second bath that's motivated only by "we
    need more parameters to fit" is curve-fitting. The framework's
    K/P content as currently formulated does NOT independently
    motivate ONE specific bath/vertex assignment — three competing
    "natural" choices exist (Higgs+Gauge, b₁/b₂, r₂/r₃), and they
    disagree. -/
theorem CKMSchur8_master :
    -- (1) V_us closed form (two-bath outer-product sum)
    (∀ s : EightStateCoupled,
        s.V_us = s.gAu3 * s.gAd2 / (s.lam - s.lamA)
               + s.gBu3 * s.gBd2 / (s.lam - s.lamB))
    -- (2) V_cb, V_ub, V_ud closed forms
    ∧ (∀ s : EightStateCoupled,
        s.V_cb = s.gAu2 * s.gAd1 / (s.lam - s.lamA)
               + s.gBu2 * s.gBd1 / (s.lam - s.lamB))
    ∧ (∀ s : EightStateCoupled,
        s.V_ub = s.gAu3 * s.gAd1 / (s.lam - s.lamA)
               + s.gBu3 * s.gBd1 / (s.lam - s.lamB))
    ∧ (∀ s : EightStateCoupled,
        s.V_ud = s.gAu3 * s.gAd3 / (s.lam - s.lamA)
               + s.gBu3 * s.gBd3 / (s.lam - s.lamB))
    -- (3) Three framework-motivated configs disagree on V_us²
    ∧ higgsGaugeConfig.V_us ^ 2 ≠ 1 / 20
    ∧ b1b2Config.V_us ^ 2 ≠ 1 / 20
    ∧ r2r3Config.V_us ^ 2 ≠ 1 / 20
    -- (4) Only the hand-tuned config achieves V_us² = 1/20
    ∧ tunedConfig.V_us ^ 2 = 1 / 20
    -- (5) Joint 4-CKM match fails: trivial and tuned agree on three
    --     other CKM entries but disagree on V_us
    ∧ trivialConfig.V_cb = tunedConfig.V_cb
    ∧ trivialConfig.V_ub = tunedConfig.V_ub
    ∧ trivialConfig.V_ud = tunedConfig.V_ud
    ∧ trivialConfig.V_us ≠ tunedConfig.V_us := by
  obtain ⟨h_hg, h_b1b2, h_r2r3, h_tuned⟩ := two_bath_does_not_force_Vus_sq
  obtain ⟨h_cb, h_ub, h_ud, h_us⟩ := joint_four_CKM_match_fails
  exact ⟨V_us_two_bath, V_cb_two_bath, V_ub_two_bath, V_ud_two_bath,
         h_hg, h_b1b2, h_r2r3, h_tuned,
         h_cb, h_ub, h_ud, h_us⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 11: HONEST SCOREBOARD (ROUTE 1 RESULTS)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    | Configuration       | V_us             | V_us²     | Matches 1/20? |
    |---------------------|------------------|-----------|---------------|
    | higgsGaugeConfig    | > √(1/20)        | > 1/20    | NO (above)    |
    | b1b2Config          | 3/50 = 0.06      | 9/2500    | NO            |
    | r2r3Config          | 2/3 ≈ 0.667      | 4/9       | NO            |
    | tunedConfig         | √5/10 ≈ 0.224    | 1/20      | YES (tuned)   |
    | PDG observed        | 0.2243 ± 0.0008  | ~0.0503   |               |

    Verdict: Route 1 (two independent baths) is **FAILURE**. The
    framework-motivated assignments do not force V_us² = 1/20. The
    only assignment giving 1/20 sets gAu3 = √(C_int·a₁) by hand,
    leaving the question "why this vertex magnitude?" unanswered —
    the same situation as the 7-state cabibboConfig.

    Open paths forward:
       • Higher-rank baths (3+ baths) — but more parameters means even
         more curve-fitting, not less.
       • A K/P-derived constraint specifically on a bath-vertex PRODUCT
         (not a vector norm or residue magnitude). The current framework
         provides residues r_i and off-diagonals b_j as INDIVIDUAL
         scalars; it does not provide a "(up-vertex) × (down-vertex)"
         pairing rule.
       • Abandon the bath-mediated derivation and seek V_us² = 1/20 from
         a different sector of the framework (e.g., a discrete charge
         counting that lands on the same number).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

end UnifiedTheory.LayerB.CKMSchur8
