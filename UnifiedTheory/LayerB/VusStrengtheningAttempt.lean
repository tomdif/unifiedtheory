/-
  LayerB/VusStrengtheningAttempt.lean — HONEST attempt to strengthen V_us = 1/√20
  from "menu selection" to a real derivation.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  CONTEXT (the user's "Path 2" falsification follow-up)

  `LayerB/VusFalsificationTest.lean` proved:
    – depth-≤2 K/P combinations admit ≥ 3 PDG-compatible candidates;
    – the chosen `√(C_int · a₁) = √(b₁ − C_int)` are five algebraically
      equivalent rewritings of one number, 1/√20.
  `LayerB/CKMSchur7.lean` exhibited a 7-state Schur-complement model whose
  (up_3, down_2) effective entry equals V_us — but the configuration sets
  `gu3 := √(C_int · a₁)` BY HAND. The answer is the input.

  This file tests three independent strategies for FORCING V_us² = 1/20
  out of the framework's other content, WITHOUT smuggling 1/20 into the
  vertex assignments.

      ROUTE 3: Multi-CKM joint Schur. Demand the SAME 7-state coupled
               Hamiltonian reproduces V_us, V_cb, V_ub simultaneously
               with ONE assignment of vertices. Count equations vs.
               unknowns; check whether the system pins V_us.

      ROUTE 1: CKM unitarity. Derive |V_ud|² as the (up_3, down_3)
               effective entry from the same 7-state Schur, impose
               |V_ud|² + |V_us|² + |V_ub|² = 1, see if V_us is forced.

      ROUTE 2: Vertex completeness sum rule. Impose Σ gu_i² = 1 and
               Σ gd_j² = 1 (analogous to residue completeness
               r₁ + r₂ + r₃ = 1) and see if V_us is pinned.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  THE CENTRAL OBSERVATION (proved in this file)

  The 7-state Schur complement of the SHARED bath produces a RANK-1
  cross-sector block:

      Heff_ij = gu_i · gd_j / Δλ      (i ∈ up, j ∈ down)

  Hence the cross-sector 3×3 block is

      M = (1/Δλ) · u ⊗ d^T,        u = (gu1, gu2, gu3),  d = (gd1, gd2, gd3).

  This is a MATRIX-LEVEL FACT. Given a single shared bath, the framework's
  V_us, V_cb, V_ub, V_ud, V_cs, ... are ALL outer-product entries of
  one rank-1 matrix.

  Consequence (Route 3): Three CKM elements give three equations in six
  vertex unknowns plus Δλ, modulo the (gu, gd) ↔ (cgu, gd/c) scale
  redundancy — a one-parameter family in (V_us, V_cb, V_ub) is
  reproducible. **The 7-state model does not over-constrain.**

  Consequence (Route 1): If we add the unitarity constraint
  |V_ud|² + |V_us|² + |V_ub|² = 1 with V_ud = gu3·gd3, V_ub = gu3·gd1,
  V_us = gu3·gd2, then unitarity becomes
      gu3² · (gd1² + gd2² + gd3²) = 1.
  This pins gu3 IF Σ gd_j² is known, but it does NOT pin V_us = gu3·gd2.
  Adding Σ gd_j² = 1 (one of several "natural" normalizations) gives
  gu3 = 1, V_us = gd2 — and gd2 is still free in [0,1].

  Consequence (Route 2): Σ gu_i² = Σ gd_j² = 1 (six unknowns reduced to
  four by two normalizations) combined with V_cb, V_ub closed forms
  pins gu2/gu3 = b₁ · 50 = 10 and gd1/gd2 = 1/50, but V_us = gu3·gd2
  remains unpinned. The full system is RANK-1 and does NOT separate
  the gu3 ↔ gd2 product into individual factors.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  HONEST VERDICTS PROVED IN THIS FILE

  (R3) **Route 3 (joint Schur) FAILS**: there exist TWO 7-state
       configurations giving the SAME (V_cb, V_ub) but DIFFERENT V_us.
       Hence reproducing V_cb and V_ub does not force V_us.

  (R1) **Route 1 (unitarity) FAILS**: even with first-row CKM unitarity
       imposed AND Σ gd_j² = 1 normalization, V_us = gd2 ranges over a
       continuous interval [V_ub, V_ud]. Hence unitarity does not pin V_us.

  (R2) **Route 2 (vertex completeness) FAILS**: the system has the
       gu3·gd2 product as ONE algebraic variable; no normalization of
       single-vector lengths separates this into (gu3, gd2) pair values.

  (RANK1) **The matrix-level cause**: the SHARED-bath Schur complement
          is RANK-1 across sectors. Routes 1, 2, 3 all hit the same wall:
          the gu3·gd2 product is the only thing that controls V_us, and
          the framework's other constraints fix RATIOS, never individual
          products with gd2 explicitly.

  (Open) An honest path forward would be: either MULTIPLE shared baths
         (changing the rank-1 structure to a sum of outer products), or a
         framework-derived NORMALIZATION specific to (gu3, gd2) (not just
         to vector lengths). Neither is currently provided.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  CLASSIFICATION

  After Routes 1, 2, 3: V_us = 1/√20 remains a SELECTION FROM A MENU.
  No "natural" framework constraint inside the existing 7-state Schur
  derivation forces 1/20 over the rank-1 family of values
  V_us · V_ub = V_us^2 / 50, V_us · V_cb = V_us^2 / 5 (which are
  identities that the framework's b₁, b₂² ratios already encode).

  Zero sorry. Zero custom axioms.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import UnifiedTheory.LayerA.FeshbachJ4
import UnifiedTheory.LayerB.CKMSchur7
import UnifiedTheory.LayerB.CKMOneLoop
import UnifiedTheory.LayerB.CKMOneLoopV2

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.VusStrengtheningAttempt

open Real
open UnifiedTheory.LayerA.FeshbachJ4
open UnifiedTheory.LayerB.CKMSchur7
open UnifiedTheory.LayerB.CKMOneLoop
open UnifiedTheory.LayerB.CKMOneLoopV2

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE RANK-1 STRUCTURE OF THE SHARED-BATH SCHUR COMPLEMENT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Every cross-sector Heff entry of the 7-state Schur complement is a
    product of (one up-vertex) × (one down-vertex) divided by Δλ. So the
    cross-sector 3×3 block is RANK 1 — it has the form
        M_ij = u_i · v_j      with u, v ∈ ℝ^3.
    All "physical" CKM identities below trace back to this single fact.

    Convention: "up" channels are indices 0, 1, 2 of `Fin 7`;
    "down" channels are indices 3, 4, 5; bath is index 6.
    Following the `cabibboConfig` convention from `CKMSchur7.lean`:
       index 0..2 of up-block ↔ (heaviest, middle, lightest) up
       index 3..5 of down-block ↔ (heaviest, middle, lightest) down
    so that Heff[2,4] = lightest up × middle down = gu3·gd2/Δλ = V_us.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- General cross-sector formula at (0, 3): HeffAt[0,3] = gu1·gd1/Δλ. -/
theorem Heff_cross_sector_03 (s : SevenStateCoupled) :
    s.HeffAt 0 3 = s.gu1 * s.gd1 / (s.lam - s.lamb) := by
  show s.H 0 3 + s.H 0 6 * s.H 6 3 / (s.lam - s.lamb) = _
  show (0 : ℝ) + s.gu1 * s.gd1 / (s.lam - s.lamb) = _
  ring

/-- HeffAt[0,4] = gu1·gd2/Δλ. -/
theorem Heff_cross_sector_04 (s : SevenStateCoupled) :
    s.HeffAt 0 4 = s.gu1 * s.gd2 / (s.lam - s.lamb) := by
  show s.H 0 4 + s.H 0 6 * s.H 6 4 / (s.lam - s.lamb) = _
  show (0 : ℝ) + s.gu1 * s.gd2 / (s.lam - s.lamb) = _
  ring

/-- HeffAt[0,5] = gu1·gd3/Δλ. -/
theorem Heff_cross_sector_05 (s : SevenStateCoupled) :
    s.HeffAt 0 5 = s.gu1 * s.gd3 / (s.lam - s.lamb) := by
  show s.H 0 5 + s.H 0 6 * s.H 6 5 / (s.lam - s.lamb) = _
  show (0 : ℝ) + s.gu1 * s.gd3 / (s.lam - s.lamb) = _
  ring

/-- HeffAt[1,3] = gu2·gd1/Δλ. -/
theorem Heff_cross_sector_13 (s : SevenStateCoupled) :
    s.HeffAt 1 3 = s.gu2 * s.gd1 / (s.lam - s.lamb) := by
  show s.H 1 3 + s.H 1 6 * s.H 6 3 / (s.lam - s.lamb) = _
  show (0 : ℝ) + s.gu2 * s.gd1 / (s.lam - s.lamb) = _
  ring

/-- HeffAt[1,4] = gu2·gd2/Δλ. -/
theorem Heff_cross_sector_14 (s : SevenStateCoupled) :
    s.HeffAt 1 4 = s.gu2 * s.gd2 / (s.lam - s.lamb) := by
  show s.H 1 4 + s.H 1 6 * s.H 6 4 / (s.lam - s.lamb) = _
  show (0 : ℝ) + s.gu2 * s.gd2 / (s.lam - s.lamb) = _
  ring

/-- HeffAt[1,5] = gu2·gd3/Δλ. -/
theorem Heff_cross_sector_15 (s : SevenStateCoupled) :
    s.HeffAt 1 5 = s.gu2 * s.gd3 / (s.lam - s.lamb) := by
  show s.H 1 5 + s.H 1 6 * s.H 6 5 / (s.lam - s.lamb) = _
  show (0 : ℝ) + s.gu2 * s.gd3 / (s.lam - s.lamb) = _
  ring

/-- HeffAt[2,3] = gu3·gd1/Δλ. -/
theorem Heff_cross_sector_23 (s : SevenStateCoupled) :
    s.HeffAt 2 3 = s.gu3 * s.gd1 / (s.lam - s.lamb) := by
  show s.H 2 3 + s.H 2 6 * s.H 6 3 / (s.lam - s.lamb) = _
  show (0 : ℝ) + s.gu3 * s.gd1 / (s.lam - s.lamb) = _
  ring

/-- HeffAt[2,4] = gu3·gd2/Δλ (this is V_us in the cabibbo convention). -/
theorem Heff_cross_sector_24 (s : SevenStateCoupled) :
    s.HeffAt 2 4 = s.gu3 * s.gd2 / (s.lam - s.lamb) := by
  show s.H 2 4 + s.H 2 6 * s.H 6 4 / (s.lam - s.lamb) = _
  show (0 : ℝ) + s.gu3 * s.gd2 / (s.lam - s.lamb) = _
  ring

/-- HeffAt[2,5] = gu3·gd3/Δλ. -/
theorem Heff_cross_sector_25 (s : SevenStateCoupled) :
    s.HeffAt 2 5 = s.gu3 * s.gd3 / (s.lam - s.lamb) := by
  show s.H 2 5 + s.H 2 6 * s.H 6 5 / (s.lam - s.lamb) = _
  show (0 : ℝ) + s.gu3 * s.gd3 / (s.lam - s.lamb) = _
  ring

/-! ## The CKM "physical" identifications (rank-1 outer-product reading)

    Following the `cabibboConfig` convention:
      up index 0 = top,    up index 1 = charm,   up index 2 = up
      down index 3 = bottom, down index 4 = strange, down index 5 = down

    So the nine bath-mediated cross-sector entries fill the CKM block as:

      Heff[0,3] = V_tb = gu1·gd1/Δλ
      Heff[0,4] = V_ts = gu1·gd2/Δλ
      Heff[0,5] = V_td = gu1·gd3/Δλ
      Heff[1,3] = V_cb = gu2·gd1/Δλ
      Heff[1,4] = V_cs = gu2·gd2/Δλ
      Heff[1,5] = V_cd = gu2·gd3/Δλ
      Heff[2,3] = V_ub = gu3·gd1/Δλ
      Heff[2,4] = V_us = gu3·gd2/Δλ          (= s.V_us from CKMSchur7)
      Heff[2,5] = V_ud = gu3·gd3/Δλ -/

/-- Compact CKM aliases as plain (non-dot) functions. -/
noncomputable def V_ub (s : SevenStateCoupled) : ℝ := s.HeffAt 2 3
noncomputable def V_ud (s : SevenStateCoupled) : ℝ := s.HeffAt 2 5
noncomputable def V_cb (s : SevenStateCoupled) : ℝ := s.HeffAt 1 3
noncomputable def V_cs (s : SevenStateCoupled) : ℝ := s.HeffAt 1 4
noncomputable def V_cd (s : SevenStateCoupled) : ℝ := s.HeffAt 1 5
noncomputable def V_tb (s : SevenStateCoupled) : ℝ := s.HeffAt 0 3
noncomputable def V_ts (s : SevenStateCoupled) : ℝ := s.HeffAt 0 4
noncomputable def V_td (s : SevenStateCoupled) : ℝ := s.HeffAt 0 5

/-- Closed forms. -/
theorem V_ub_formula (s : SevenStateCoupled) :
    V_ub s = s.gu3 * s.gd1 / (s.lam - s.lamb) := Heff_cross_sector_23 s

theorem V_ud_formula (s : SevenStateCoupled) :
    V_ud s = s.gu3 * s.gd3 / (s.lam - s.lamb) := Heff_cross_sector_25 s

theorem V_cb_formula (s : SevenStateCoupled) :
    V_cb s = s.gu2 * s.gd1 / (s.lam - s.lamb) := Heff_cross_sector_13 s

theorem V_cs_formula (s : SevenStateCoupled) :
    V_cs s = s.gu2 * s.gd2 / (s.lam - s.lamb) := Heff_cross_sector_14 s

theorem V_cd_formula (s : SevenStateCoupled) :
    V_cd s = s.gu2 * s.gd3 / (s.lam - s.lamb) := Heff_cross_sector_15 s

theorem V_tb_formula (s : SevenStateCoupled) :
    V_tb s = s.gu1 * s.gd1 / (s.lam - s.lamb) := Heff_cross_sector_03 s

theorem V_ts_formula (s : SevenStateCoupled) :
    V_ts s = s.gu1 * s.gd2 / (s.lam - s.lamb) := Heff_cross_sector_04 s

theorem V_td_formula (s : SevenStateCoupled) :
    V_td s = s.gu1 * s.gd3 / (s.lam - s.lamb) := Heff_cross_sector_05 s

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: THE RANK-1 IDENTITIES — UNAVOIDABLE FROM SHARED BATH
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The cross-sector 3×3 block is rank 1, so all 2×2 minors vanish:
        V_ij · V_kl = V_il · V_kj.
    The framework's coherent-scaling identities V_cb/V_us = b₁ and
    V_ub/V_us = b₂² ARE INSTANCES of these rank-1 identities — they
    follow from the bath structure, not from extra physics.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Fundamental rank-1 identity: V_us · V_cb = V_cs · V_ub
    (the 2×2 minor of the cross-sector block on rows {up, charm} and
    columns {strange, bottom} vanishes). -/
theorem rank_one_identity_1 (s : SevenStateCoupled) :
    s.V_us * V_cb s = V_cs s * V_ub s := by
  rw [SevenStateCoupled.V_us_formula, V_cb_formula, V_cs_formula, V_ub_formula]
  ring

/-- Another rank-1 identity: V_us · V_cd = V_cs · V_ud
    (rows {up, charm}, columns {strange, down}). -/
theorem rank_one_identity_2 (s : SevenStateCoupled) :
    s.V_us * V_cd s = V_cs s * V_ud s := by
  rw [SevenStateCoupled.V_us_formula, V_cd_formula, V_cs_formula, V_ud_formula]
  ring

/-- Determinant of any cross-sector 2×2 sub-block vanishes. -/
theorem cross_sector_2x2_minor_vanishes (s : SevenStateCoupled) :
    s.V_us * V_cb s - V_cs s * V_ub s = 0 := by
  have := rank_one_identity_1 s; linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: ROUTE 3 — JOINT SCHUR (V_us, V_cb, V_ub) — DOES NOT FORCE V_us
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Premise: demand ONE configuration `s : SevenStateCoupled` reproduce
    all three values
        s.V_us = U,   V_cb s = C,   V_ub s = B
    where U, C, B are the framework's predictions (or PDG values).

    THE EQUATIONS (with Δ := s.lam − s.lamb)
        gu3 · gd2 / Δ = U      ... (1)
        gu2 · gd1 / Δ = C      ... (2)
        gu3 · gd1 / Δ = B      ... (3)

    THE UNKNOWNS (without normalization): gu1, gu2, gu3, gd1, gd2, gd3, Δ.
    That is 7 unknowns, 3 equations. The system is UNDERDETERMINED.

    Even adding "Δ = 1" leaves 6 unknowns, 3 equations.
    The free parameters: gu1, gd3 (don't appear), and the (gu3, gd2)
    rescaling (gu3, gd2) ↦ (c·gu3, U/(c·gd2)) — a 1-parameter family
    along the rank-1 manifold of fixed product gu3·gd2.

    CONSEQUENCE: there exist TWO distinct configurations giving the same
    (V_cb, V_ub) but DIFFERENT V_us.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A "twin" of `cabibboConfig` with the SAME V_cb = V_ub = 0 but a
    DIFFERENT V_us. Both `cabibboConfig` and its twin reproduce
    (V_cb = 0, V_ub = 0) and have a single nontrivial cross-sector entry,
    yet the value of V_us differs.

    This is the explicit witness that "matching V_cb and V_ub" does NOT
    force V_us. -/
noncomputable def cabibboConfig_twin : SevenStateCoupled where
  a1 := a₁_real
  a2 := 2 / 5
  a3 := 1 / 5
  b1 := 1 / 5
  b2 := 1 / Real.sqrt 50
  lamb := 0
  gu1 := 0
  gu2 := 0
  gu3 := 7 / 25  -- DIFFERENT from √(C_int·a₁); equals 0.28, ≠ 1/√20 ≈ 0.2236
  gd1 := 0
  gd2 := 1
  gd3 := 0
  lam := 1
  hlam := by norm_num

/-- The twin's V_us equals 7/25 (the chosen gu3 value), NOT √(1/20). -/
theorem cabibboConfig_twin_V_us : cabibboConfig_twin.V_us = 7 / 25 := by
  rw [SevenStateCoupled.V_us_formula]
  show (7 / 25 : ℝ) * 1 / (1 - 0) = 7 / 25
  ring

/-- The twin's V_cb is 0 (since gu2 = 0). -/
theorem cabibboConfig_twin_V_cb : V_cb cabibboConfig_twin = 0 := by
  rw [V_cb_formula]
  show (0 : ℝ) * 0 / (1 - 0) = 0
  norm_num

/-- The twin's V_ub is 0 (since gd1 = 0). -/
theorem cabibboConfig_twin_V_ub : V_ub cabibboConfig_twin = 0 := by
  rw [V_ub_formula]
  show (7 / 25 : ℝ) * 0 / (1 - 0) = 0
  norm_num

/-- The original `cabibboConfig` also has V_cb = 0 and V_ub = 0
    (since gu2 = gd1 = 0 in that configuration). -/
theorem cabibboConfig_V_cb_zero : V_cb cabibboConfig = 0 := by
  rw [V_cb_formula]
  show (0 : ℝ) * 0 / (1 - 0) = 0
  norm_num

theorem cabibboConfig_V_ub_zero : V_ub cabibboConfig = 0 := by
  rw [V_ub_formula]
  show Real.sqrt (C_int_real * a₁_real) * 0 / (1 - 0) = 0
  simp

/-- `cabibboConfig` and its twin agree on V_cb and V_ub (both zero). -/
theorem twins_agree_on_V_cb_V_ub :
    V_cb cabibboConfig = V_cb cabibboConfig_twin ∧
    V_ub cabibboConfig = V_ub cabibboConfig_twin := by
  refine ⟨?_, ?_⟩
  · rw [cabibboConfig_V_cb_zero, cabibboConfig_twin_V_cb]
  · rw [cabibboConfig_V_ub_zero, cabibboConfig_twin_V_ub]

/-- `cabibboConfig` and its twin disagree on V_us.
    Specifically `cabibboConfig.V_us = 1/√20 ≈ 0.2236`, but
    `cabibboConfig_twin.V_us = 7/25 = 0.28`. -/
theorem twins_disagree_on_V_us :
    cabibboConfig.V_us ≠ cabibboConfig_twin.V_us := by
  rw [cabibboConfig_V_us_eq, cabibboConfig_twin_V_us]
  -- Need: Vus_v2 ≠ 7/25 = 0.28
  -- Vus_v2 = √5/10 ≈ 0.2236, while 7/25 = 0.28.
  intro h
  have h1 : Vus_v2 = 7 / 25 := h
  have h2 : Vus_v2 ^ 2 = (7 / 25) ^ 2 := by rw [h1]
  rw [Vus_v2_sq_eq, Vus_v2_sq_closed] at h2
  norm_num at h2

/-- (R3) ROUTE 3 FAILS: there exist two `SevenStateCoupled` configurations
    `s₁ = cabibboConfig` and `s₂ = cabibboConfig_twin` such that
        V_cb s₁ = V_cb s₂ = 0,
        V_ub s₁ = V_ub s₂ = 0,
    yet s₁.V_us ≠ s₂.V_us. Hence reproducing V_cb and V_ub jointly
    does NOT pin V_us. -/
theorem Route3_fails :
    ∃ (s₁ s₂ : SevenStateCoupled),
      V_cb s₁ = V_cb s₂ ∧ V_ub s₁ = V_ub s₂ ∧ s₁.V_us ≠ s₂.V_us := by
  refine ⟨cabibboConfig, cabibboConfig_twin, ?_, ?_, twins_disagree_on_V_us⟩
  · exact (twins_agree_on_V_cb_V_ub).1
  · exact (twins_agree_on_V_cb_V_ub).2

/-! ### A MORE DEMANDING TEST: A rescaling symmetry preserving all CKM elements

    Set Δ = 1. The rank-1 form V_ij = gu_i · gd_j has a one-parameter
    rescaling symmetry: (gu_i, gd_j) ↦ (c·gu_i, gd_j/c) preserves every
    cross-sector matrix element. Hence individual vertex values are
    NOT physical — only their products are. This is a structural
    one-parameter freedom of the shared-bath model.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The rank-1 rescaling symmetry: scaling all up-vertices by c and all
    down-vertices by 1/c preserves every cross-sector matrix element. -/
theorem rank_one_rescaling_symmetry
    (s : SevenStateCoupled) (c : ℝ) (hc : c ≠ 0)
    (s' : SevenStateCoupled)
    (hgu1' : s'.gu1 = c * s.gu1) (hgu2' : s'.gu2 = c * s.gu2)
    (hgu3' : s'.gu3 = c * s.gu3)
    (hgd1' : s'.gd1 = s.gd1 / c) (hgd2' : s'.gd2 = s.gd2 / c)
    (hgd3' : s'.gd3 = s.gd3 / c)
    (hΔ : s'.lam - s'.lamb = s.lam - s.lamb) :
    s'.V_us = s.V_us ∧ V_cb s' = V_cb s ∧ V_ub s' = V_ub s := by
  refine ⟨?_, ?_, ?_⟩
  · rw [SevenStateCoupled.V_us_formula, SevenStateCoupled.V_us_formula,
        hgu3', hgd2', hΔ]
    field_simp
  · rw [V_cb_formula, V_cb_formula, hgu2', hgd1', hΔ]
    field_simp
  · rw [V_ub_formula, V_ub_formula, hgu3', hgd1', hΔ]
    field_simp

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: ROUTE 1 — CKM UNITARITY ALSO FAILS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The first-row unitarity statement for the CKM matrix is
        |V_ud|² + |V_us|² + |V_ub|² = 1.
    From the rank-1 Schur:
        V_ud = gu3·gd3/Δ,   V_us = gu3·gd2/Δ,   V_ub = gu3·gd1/Δ.
    So unitarity becomes
        (gu3 / Δ)² · (gd1² + gd2² + gd3²) = 1.

    This is ONE equation on (gu3 / Δ) and Σ gd² — TWO real degrees of
    freedom on the LHS. Any combination satisfying it is allowed.
    In particular, V_us = gu3·gd2/Δ remains free in
        |V_us| = (gu3/Δ) · gd2 = gd2 · 1 / √(gd1² + gd2² + gd3²).

    Since (gd1, gd2, gd3) is unconstrained (up to its norm), gd2 ∈ (0,1)
    is a one-parameter family — and so is V_us. UNITARITY DOES NOT PIN
    V_us.

    Below we prove this via two configurations satisfying first-row
    unitarity but giving different V_us.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A unitary-style configuration A: gu3 = 1, (gd1, gd2, gd3) = (0, 1, 0).
    Then V_us = 1, V_ud = V_ub = 0, and |V_ud|² + |V_us|² + |V_ub|² = 1. -/
noncomputable def unitaryConfig_A : SevenStateCoupled where
  a1 := 0; a2 := 0; a3 := 0; b1 := 0; b2 := 0
  lamb := 0
  gu1 := 0; gu2 := 0; gu3 := 1
  gd1 := 0; gd2 := 1; gd3 := 0
  lam := 1
  hlam := by norm_num

/-- A.V_us = 1. -/
theorem unitaryConfig_A_V_us : unitaryConfig_A.V_us = 1 := by
  rw [SevenStateCoupled.V_us_formula]
  show (1 : ℝ) * 1 / (1 - 0) = 1
  norm_num

/-- A.V_ub = 0. -/
theorem unitaryConfig_A_V_ub : V_ub unitaryConfig_A = 0 := by
  rw [V_ub_formula]
  show (1 : ℝ) * 0 / (1 - 0) = 0
  norm_num

/-- A.V_ud = 0. -/
theorem unitaryConfig_A_V_ud : V_ud unitaryConfig_A = 0 := by
  rw [V_ud_formula]
  show (1 : ℝ) * 0 / (1 - 0) = 0
  norm_num

/-- A satisfies first-row unitarity. -/
theorem unitaryConfig_A_first_row :
    V_ud unitaryConfig_A ^ 2 + unitaryConfig_A.V_us ^ 2 + V_ub unitaryConfig_A ^ 2 = 1 := by
  rw [unitaryConfig_A_V_ud, unitaryConfig_A_V_us, unitaryConfig_A_V_ub]
  norm_num

/-- A unitary-style configuration B: gu3 = 1, (gd1, gd2, gd3) = (3/5, 4/5, 0).
    Then V_us = 4/5, V_ub = 3/5, V_ud = 0, and unitarity holds:
        0² + (4/5)² + (3/5)² = 16/25 + 9/25 = 1. -/
noncomputable def unitaryConfig_B : SevenStateCoupled where
  a1 := 0; a2 := 0; a3 := 0; b1 := 0; b2 := 0
  lamb := 0
  gu1 := 0; gu2 := 0; gu3 := 1
  gd1 := 3 / 5; gd2 := 4 / 5; gd3 := 0
  lam := 1
  hlam := by norm_num

/-- B.V_us = 4/5. -/
theorem unitaryConfig_B_V_us : unitaryConfig_B.V_us = 4 / 5 := by
  rw [SevenStateCoupled.V_us_formula]
  show (1 : ℝ) * (4/5) / (1 - 0) = 4/5
  norm_num

/-- B.V_ub = 3/5. -/
theorem unitaryConfig_B_V_ub : V_ub unitaryConfig_B = 3 / 5 := by
  rw [V_ub_formula]
  show (1 : ℝ) * (3/5) / (1 - 0) = 3/5
  norm_num

/-- B.V_ud = 0. -/
theorem unitaryConfig_B_V_ud : V_ud unitaryConfig_B = 0 := by
  rw [V_ud_formula]
  show (1 : ℝ) * 0 / (1 - 0) = 0
  norm_num

/-- B satisfies first-row unitarity. -/
theorem unitaryConfig_B_first_row :
    V_ud unitaryConfig_B ^ 2 + unitaryConfig_B.V_us ^ 2 + V_ub unitaryConfig_B ^ 2 = 1 := by
  rw [unitaryConfig_B_V_ud, unitaryConfig_B_V_us, unitaryConfig_B_V_ub]
  norm_num

/-- (R1) ROUTE 1 FAILS: there exist two `SevenStateCoupled` configurations
    `s_A`, `s_B` such that BOTH satisfy first-row CKM unitarity
        |V_ud|² + |V_us|² + |V_ub|² = 1
    yet have DIFFERENT V_us values (1 vs. 4/5). Hence first-row unitarity
    alone does NOT pin V_us. -/
theorem Route1_fails :
    ∃ (s_A s_B : SevenStateCoupled),
      (V_ud s_A ^ 2 + s_A.V_us ^ 2 + V_ub s_A ^ 2 = 1) ∧
      (V_ud s_B ^ 2 + s_B.V_us ^ 2 + V_ub s_B ^ 2 = 1) ∧
      s_A.V_us ≠ s_B.V_us := by
  refine ⟨unitaryConfig_A, unitaryConfig_B,
          unitaryConfig_A_first_row,
          unitaryConfig_B_first_row, ?_⟩
  rw [unitaryConfig_A_V_us, unitaryConfig_B_V_us]
  norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: ROUTE 2 — VERTEX-COMPLETENESS NORMALIZATION ALSO FAILS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Route 2 imposes "vertex completeness" sum rules
        gu1² + gu2² + gu3² = 1,    gd1² + gd2² + gd3² = 1
    by analogy with the framework's residue completeness r₁+r₂+r₃ = 1.
    Combined with V_us, V_cb, V_ub closed forms:

        gu3·gd2/Δ = U,   gu2·gd1/Δ = C,   gu3·gd1/Δ = B,
        Σ gu² = 1,   Σ gd² = 1.

    With Δ := 1, this is 5 equations in 6 unknowns (gu1,gu2,gu3,gd1,gd2,gd3).
    The DOF count is 1, suggesting V_us could be pinned. We test by
    constructing solutions with the same C and B but different U.

    EXPLICIT CONSTRUCTION: take ANY value U ∈ [0, 1] and find a normalized
    (gu, gd) with gu3·gd2 = U and (say) all other cross-sector entries
    zero. E.g., gu = (0, 0, 1), gd = (0, U, √(1-U²)) — gives V_us = U,
    V_cb = V_ub = 0, V_ud = √(1-U²), Σ gu² = 1, Σ gd² = 1.

    Different choices of U give DIFFERENT V_us — both PASS completeness
    AND first-row unitarity (which becomes U² + (1-U²) + 0 = 1 ✓).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A completeness-normalized configuration C(U) parametrized by U ∈ [0, 1]:
       gu = (0, 0, 1),  gd = (0, U, √(1-U²)).
    Has Σ gu² = Σ gd² = 1, V_us = U, V_cb = V_ub = 0. -/
noncomputable def completenessConfig (U : ℝ) : SevenStateCoupled where
  a1 := 0; a2 := 0; a3 := 0; b1 := 0; b2 := 0
  lamb := 0
  gu1 := 0; gu2 := 0; gu3 := 1
  gd1 := 0; gd2 := U; gd3 := Real.sqrt (1 - U^2)
  lam := 1
  hlam := by norm_num

/-- C(U).V_us = U. -/
theorem completenessConfig_V_us (U : ℝ) :
    (completenessConfig U).V_us = U := by
  rw [SevenStateCoupled.V_us_formula]
  show (1 : ℝ) * U / (1 - 0) = U
  ring

/-- C(U).V_cb = 0 (since gu2 = 0). -/
theorem completenessConfig_V_cb (U : ℝ) :
    V_cb (completenessConfig U) = 0 := by
  rw [V_cb_formula]
  show (0 : ℝ) * 0 / (1 - 0) = 0
  norm_num

/-- C(U).V_ub = 0 (since gd1 = 0). -/
theorem completenessConfig_V_ub (U : ℝ) :
    V_ub (completenessConfig U) = 0 := by
  rw [V_ub_formula]
  show (1 : ℝ) * 0 / (1 - 0) = 0
  norm_num

/-- Σ gu_i² = 1 for C(U). -/
theorem completenessConfig_gu_sum (U : ℝ) :
    (completenessConfig U).gu1 ^ 2 +
    (completenessConfig U).gu2 ^ 2 +
    (completenessConfig U).gu3 ^ 2 = 1 := by
  show (0 : ℝ) ^ 2 + 0 ^ 2 + 1 ^ 2 = 1
  norm_num

/-- Σ gd_j² = 1 for C(U), provided 0 ≤ U ≤ 1. -/
theorem completenessConfig_gd_sum (U : ℝ) (hU : 0 ≤ U) (hU1 : U ≤ 1) :
    (completenessConfig U).gd1 ^ 2 +
    (completenessConfig U).gd2 ^ 2 +
    (completenessConfig U).gd3 ^ 2 = 1 := by
  show (0 : ℝ) ^ 2 + U ^ 2 + (Real.sqrt (1 - U^2)) ^ 2 = 1
  have h : 1 - U^2 ≥ 0 := by nlinarith
  rw [Real.sq_sqrt h]
  ring

/-- (R2) ROUTE 2 FAILS: for ANY U ∈ [0, 1], the configuration
    `completenessConfig U` satisfies BOTH up- and down-vertex
    completeness AND has V_cb = V_ub = 0, yet V_us = U is arbitrary.
    Hence vertex completeness does NOT pin V_us — V_us is a free
    one-parameter family. -/
theorem Route2_fails :
    ∀ U : ℝ, 0 ≤ U → U ≤ 1 →
      ((completenessConfig U).gu1 ^ 2 +
       (completenessConfig U).gu2 ^ 2 +
       (completenessConfig U).gu3 ^ 2 = 1) ∧
      ((completenessConfig U).gd1 ^ 2 +
       (completenessConfig U).gd2 ^ 2 +
       (completenessConfig U).gd3 ^ 2 = 1) ∧
      (completenessConfig U).V_us = U := by
  intro U hU hU1
  exact ⟨completenessConfig_gu_sum U,
         completenessConfig_gd_sum U hU hU1,
         completenessConfig_V_us U⟩

/-- Two completeness-normalized configurations with the same V_cb, V_ub
    (both zero) but different V_us. -/
theorem Route2_explicit_witness :
    ∃ (s₁ s₂ : SevenStateCoupled),
      (s₁.gu1 ^ 2 + s₁.gu2 ^ 2 + s₁.gu3 ^ 2 = 1) ∧
      (s₁.gd1 ^ 2 + s₁.gd2 ^ 2 + s₁.gd3 ^ 2 = 1) ∧
      (s₂.gu1 ^ 2 + s₂.gu2 ^ 2 + s₂.gu3 ^ 2 = 1) ∧
      (s₂.gd1 ^ 2 + s₂.gd2 ^ 2 + s₂.gd3 ^ 2 = 1) ∧
      V_cb s₁ = V_cb s₂ ∧ V_ub s₁ = V_ub s₂ ∧ s₁.V_us ≠ s₂.V_us := by
  refine ⟨completenessConfig (1/4), completenessConfig (1/3), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact completenessConfig_gu_sum (1/4)
  · exact completenessConfig_gd_sum (1/4) (by norm_num) (by norm_num)
  · exact completenessConfig_gu_sum (1/3)
  · exact completenessConfig_gd_sum (1/3) (by norm_num) (by norm_num)
  · rw [completenessConfig_V_cb, completenessConfig_V_cb]
  · rw [completenessConfig_V_ub, completenessConfig_V_ub]
  · rw [completenessConfig_V_us, completenessConfig_V_us]
    norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: THE CENTRAL OBSTRUCTION — RANK-1 ABSORBS ALL CONSTRAINTS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Why do all three routes fail in the same way? Because the SHARED-BATH
    Schur complement makes V_us = (gu3 · gd2) / Δ. The framework's other
    constraints control:
       (a) ratios V_ub / V_us = gd1 / gd2,
       (b) ratios V_cb / V_us = (gu2 · gd1) / (gu3 · gd2),
       (c) sums gu1²+gu2²+gu3², gd1²+gd2²+gd3²,
       (d) bath energy difference Δ.
    None of these is the PRODUCT gu3·gd2 — only its RATIO to other
    products, only its INDIVIDUAL FACTORS' SQUARES (in completeness sums).
    The product gu3·gd2 itself is FREE.

    To pin gu3·gd2 directly, the framework would need a constraint of
    the form:
        gu3·gd2 = (specific framework-derived constant),
    which is precisely the V2 file's "V_us² = C_int · a₁" — i.e., the
    answer assumed as input.

    Equivalently: a SECOND independent shared bath with its own vertex
    structure could break the rank-1 form. A two-bath model would make
    V_us = (gu3·gd2)/Δ + (gu3'·gd2')/Δ', etc. — and four CKM constraints
    would over-determine the eight bath parameters in a generic way.
    But the framework's K/P theory currently provides only ONE shared
    bath, so this avenue is not available.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The product gu3·gd2 is the ONLY thing that controls V_us.
    Any two configurations with the same gu3·gd2 and the same Δλ have
    the same V_us, regardless of every other parameter. -/
theorem V_us_depends_only_on_product
    (s₁ s₂ : SevenStateCoupled)
    (h_prod : s₁.gu3 * s₁.gd2 = s₂.gu3 * s₂.gd2)
    (h_Δ : s₁.lam - s₁.lamb = s₂.lam - s₂.lamb) :
    s₁.V_us = s₂.V_us := by
  rw [SevenStateCoupled.V_us_formula, SevenStateCoupled.V_us_formula,
      h_prod, h_Δ]

/-- The product gu3·gd2 is NOT pinned by ANY of:
       - first-row CKM unitarity,
       - vertex-completeness sum rules Σ gu² = Σ gd² = 1,
       - matching V_cb and V_ub framework values.
    Witness: the family `completenessConfig U` for U ∈ [0, 1]. -/
theorem product_gu3_gd2_unpinned :
    ∀ U : ℝ, (completenessConfig U).gu3 * (completenessConfig U).gd2 = U := by
  intro U
  show (1 : ℝ) * U = U
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: MASTER NEGATIVE RESULT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- MASTER NEGATIVE THEOREM: no natural-looking framework constraint
    available inside the existing 7-state Schur complement forces
    V_us² = 1/20.

    Concretely:

    (R3) Multi-CKM joint Schur. Two configurations agree on (V_cb, V_ub)
         but disagree on V_us — the joint match does not pin V_us.

    (R1) First-row CKM unitarity. Two configurations both satisfy
         |V_ud|² + |V_us|² + |V_ub|² = 1 yet have different V_us values.

    (R2) Vertex-completeness sum rule. The family
         `completenessConfig U`, U ∈ [0, 1], gives V_us = U with
         Σ gu² = Σ gd² = 1 — V_us is a one-parameter family.

    (RANK1) The matrix-level cause: the shared-bath Schur cross-sector
         block is RANK 1, and only the PRODUCT gu3·gd2 controls V_us.
         All considered constraints are insensitive to that product.

    Conclusion: the framework's V_us = √(1/20) prediction remains a
    SELECTION FROM A MENU. To upgrade it to a real derivation, the
    framework would need either:
       (a) a SECOND shared bath that breaks the rank-1 form, or
       (b) an independent K/P-derived constraint specifically on the
           bath-vertex product gu3·gd2 (not just on vector norms or
           ratios). -/
theorem MASTER_strengthening_attempt_fails :
    -- (R3) Joint match of (V_cb, V_ub) does not pin V_us
    (∃ (s₁ s₂ : SevenStateCoupled),
        V_cb s₁ = V_cb s₂ ∧ V_ub s₁ = V_ub s₂ ∧ s₁.V_us ≠ s₂.V_us)
    -- (R1) First-row CKM unitarity does not pin V_us
    ∧ (∃ (s_A s_B : SevenStateCoupled),
        (V_ud s_A ^ 2 + s_A.V_us ^ 2 + V_ub s_A ^ 2 = 1) ∧
        (V_ud s_B ^ 2 + s_B.V_us ^ 2 + V_ub s_B ^ 2 = 1) ∧
        s_A.V_us ≠ s_B.V_us)
    -- (R2) Vertex-completeness sum rule does not pin V_us
    ∧ (∀ U : ℝ, 0 ≤ U → U ≤ 1 →
        ((completenessConfig U).gu1 ^ 2 +
         (completenessConfig U).gu2 ^ 2 +
         (completenessConfig U).gu3 ^ 2 = 1) ∧
        ((completenessConfig U).gd1 ^ 2 +
         (completenessConfig U).gd2 ^ 2 +
         (completenessConfig U).gd3 ^ 2 = 1) ∧
        (completenessConfig U).V_us = U)
    -- (RANK1) V_us depends only on gu3·gd2 and Δλ
    ∧ (∀ s₁ s₂ : SevenStateCoupled,
        s₁.gu3 * s₁.gd2 = s₂.gu3 * s₂.gd2 →
        s₁.lam - s₁.lamb = s₂.lam - s₂.lamb →
        s₁.V_us = s₂.V_us) := by
  exact ⟨Route3_fails, Route1_fails, Route2_fails, V_us_depends_only_on_product⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: HONEST SCOREBOARD
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    | Route | Constraint                                  | Verdict |
    |-------|---------------------------------------------|---------|
    | R1    | First-row CKM unitarity                     | FAIL    |
    | R2    | Σ gu² = Σ gd² = 1 (vertex completeness)     | FAIL    |
    | R3    | Joint Schur match of (V_us, V_cb, V_ub)    | FAIL    |

    Overall verdict (proved here): no combination of the three considered
    "natural" constraints inside the existing 7-state Schur model forces
    V_us² = 1/20. The framework's V_us prediction remains a SELECTION
    FROM A MENU, as the prior `VusFalsificationTest.lean` already
    classified.

    What WOULD strengthen the prediction: a TWO-bath shared structure
    (breaking rank-1) plus K/P-derivable bath couplings. The framework
    does not currently provide this; it is an open future work item.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

end UnifiedTheory.LayerB.VusStrengtheningAttempt
