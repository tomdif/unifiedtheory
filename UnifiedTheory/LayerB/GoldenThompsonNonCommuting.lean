/-
  LayerB/GoldenThompsonNonCommuting.lean
  ──────────────────────────────────────

  **Lie–Trotter-route structural reduction of the residual
  non-commuting Golden–Thompson subgate
  `GoldenThompson_NonCommuting_Subgate` from
  `LayerB.GoldenThompsonInequality`.**

  The non-commuting case of Golden–Thompson states: for Hermitian
  `A, B : Matrix (Fin n) (Fin n) ℂ` (no commutativity assumed),

      `Re Tr(cfc exp (A + B))
          ≤ Re Tr(cfc exp A · cfc exp B)`.

  The classical Lie–Trotter route (Trotter 1959, Reed–Simon I.151,
  Petz 1985, Carlen 2010 §2) factors this through two named
  analytic targets:

    1. **Lie–Trotter product formula** —
       `(e^{A/k} · e^{B/k})^k → e^{A+B}` as `k → ∞`, in any matrix
       operator norm (equivalently, entrywise convergence for
       finite-dimensional matrices).

    2. **Per-step trace inequality** —
       `Re Tr((e^{A/k} · e^{B/k})^k) ≤ Re Tr(e^A · e^B)` for every
       `k ≥ 1`.  Proof in the literature uses Hölder's inequality
       `|Tr(X^k)| ≤ Tr((X X*)^{k/2})` combined with cyclicity to
       collapse the `k`-fold product into a single
       `Tr(e^A · e^B)` factor.

  Continuity of `Re ∘ Matrix.trace` together with (1) and (2) then
  yields the non-commuting Golden–Thompson inequality as a limit
  of finite-`k` bounds.

  WHAT IS PROVEN (no sorry, no custom axioms):

    * `LieTrotter_Target` — the Lie–Trotter product formula as a
      named Prop.

    * `PerStep_TraceInequality_Target` — the per-`k` Re-trace
      inequality as a named Prop.

    * `goldenThompson_nonCommuting_from_subgates` — the headline
      composite: `LieTrotter_Target` ∧ `PerStep_TraceInequality_Target`
      ⇒ `GoldenThompson_NonCommuting_Subgate`.

    * `goldenThompson_target_from_lieTrotter_route` — composite all
      the way to `GoldenThompson_Target`: the commuting case is
      unconditional (from `GoldenThompsonInequality`), and the
      non-commuting case reduces to the two Lie–Trotter targets.

    * `lieb_tracial_subgate_from_lieTrotter_route` — downstream
      hook into the Lieb 1973 chain.

  HONEST SCOPE.

    The Lie–Trotter product formula and the per-`k` Re-trace
    inequality are CLASSICAL THEOREMS, but their Mathlib status at
    the matrix level (`cfc Real.exp`) is non-trivial and not in
    scope here.  We package them as named Props, and prove the
    structural reduction from them to
    `GoldenThompson_NonCommuting_Subgate` UNCONDITIONALLY.

    The continuity argument uses only:
      • `Real.continuous_exp` (already in Mathlib);
      • continuity of `Matrix.trace : Matrix (Fin n) (Fin n) ℂ → ℂ`
        as a linear map on a finite-dimensional normed space;
      • continuity of `Complex.re : ℂ → ℝ`;
      • the fact that the limit of a sequence bounded by a constant
        is itself bounded by that constant
        (`le_of_tendsto`).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  STANDING CONSTRAINT: zero `sorry`, zero custom axioms.
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Authored 2026-06-02.
-/

import UnifiedTheory.LayerB.GoldenThompsonInequality
import UnifiedTheory.LayerB.LiebGoldenThompson
import UnifiedTheory.LayerB.AndoInterpolation
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.GoldenThompsonNonCommuting

open Matrix Complex Filter Topology
open UnifiedTheory.LayerB.LiebGoldenThompson
open UnifiedTheory.LayerB.AndoInterpolation
open UnifiedTheory.LayerB.GoldenThompsonInequality

/-! ## 1. The Lie–Trotter product formula as a named target. -/

/-- **Lie–Trotter product formula (named target).**

    For all Hermitian `A, B : Matrix (Fin n) (Fin n) ℂ`,

        `(cfc exp (A/k) · cfc exp (B/k))^k  →  cfc exp (A + B)`

    as `k → ∞` along `Filter.atTop`, in the (finite-dimensional)
    matrix topology.  Equivalently, entrywise convergence of every
    matrix entry to its limit.

    Classical theorem (Trotter 1959; Reed–Simon I.151; Carlen 2010).
    Packaged here as a `Prop` and consumed by
    `goldenThompson_nonCommuting_from_subgates`. -/
def LieTrotter_Target : Prop :=
  ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ),
    A.IsHermitian → B.IsHermitian →
      Filter.Tendsto
        (fun k : ℕ =>
          (cfc Real.exp ((1 / (k : ℂ)) • A)
            * cfc Real.exp ((1 / (k : ℂ)) • B)) ^ k)
        Filter.atTop
        (nhds (cfc Real.exp (A + B)))

/-- Canonical interface for `LieTrotter_Target`. -/
theorem lieTrotter_target_holds_iff (h : LieTrotter_Target) :
    LieTrotter_Target := h

/-! ## 2. The per-step trace inequality as a named target. -/

/-- **Per-step trace inequality (named target).**

    For all Hermitian `A, B : Matrix (Fin n) (Fin n) ℂ` and all
    `k ≥ 1`,

        `Re Tr((cfc exp (A/k) · cfc exp (B/k))^k)
            ≤ Re Tr(cfc exp A · cfc exp B)`.

    This is the finite-`k` analytic step in the Lie–Trotter route
    to Golden–Thompson.  Classical proof (Petz 1985 §2; Carlen 2010
    Lemma 2.5):

      • Hölder's inequality on Schatten norms gives
        `|Tr(X^k)| ≤ Tr((X X*)^{k/2})` for any matrix `X`.

      • Apply with `X = cfc exp (A/k) · cfc exp (B/k)`; use cyclicity
        + power expansion to collapse the right-hand side to
        `Re Tr(cfc exp A · cfc exp B)`.

    Packaged here as a `Prop` and consumed by
    `goldenThompson_nonCommuting_from_subgates`. -/
def PerStep_TraceInequality_Target : Prop :=
  ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ),
    A.IsHermitian → B.IsHermitian →
      ∀ k : ℕ, 1 ≤ k →
        (Matrix.trace
          ((cfc Real.exp ((1 / (k : ℂ)) • A)
              * cfc Real.exp ((1 / (k : ℂ)) • B)) ^ k)).re
          ≤ (Matrix.trace (cfc Real.exp A * cfc Real.exp B)).re

/-- Canonical interface for `PerStep_TraceInequality_Target`. -/
theorem perStep_traceInequality_target_holds_iff
    (h : PerStep_TraceInequality_Target) :
    PerStep_TraceInequality_Target := h

/-! ## 3. Continuity helpers. -/

section Continuity

variable {n : ℕ}

/-- `Matrix.trace : Matrix (Fin n) (Fin n) ℂ → ℂ` is continuous.
    Direct proof: trace is a finite sum of diagonal entries, each
    of which is a continuous projection. -/
private lemma continuous_trace_fin :
    Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => Matrix.trace M) := by
  -- Matrix.trace M = ∑ i, M i i, and each `M ↦ M i i` is continuous
  -- (composition of two `continuous_apply`s).
  unfold Matrix.trace
  refine continuous_finset_sum _ (fun i _ => ?_)
  -- `fun M => M i i` is the composition of two coordinate projections
  -- on the function space `Fin n → Fin n → ℂ`.
  exact (continuous_apply i).comp (continuous_apply i)

/-- `Re ∘ Matrix.trace : Matrix (Fin n) (Fin n) ℂ → ℝ` is continuous. -/
private lemma continuous_re_trace :
    Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => (Matrix.trace M).re) :=
  Complex.continuous_re.comp continuous_trace_fin

end Continuity

/-! ## 4. Composite: Lie–Trotter + per-step ⇒ non-commuting GT. -/

/-- **Headline composite reduction.**

    `LieTrotter_Target` and `PerStep_TraceInequality_Target` together
    imply `GoldenThompson_NonCommuting_Subgate`.

    PROOF.  Fix Hermitian `A, B` with `¬ Commute A B`.  Define
    `X k := (cfc exp (A/k) · cfc exp (B/k))^k`.  By Lie–Trotter,
    `X k → cfc exp (A + B)` in `nhds`.

    Apply continuous `M ↦ (Tr M).re` to obtain
    `(Tr (X k)).re → (Tr (cfc exp (A + B))).re`.

    By `PerStep_TraceInequality_Target`, every `(Tr (X k)).re` (for
    `k ≥ 1`) is bounded above by `(Tr (e^A · e^B)).re`.  Hence the
    limit is too (`le_of_tendsto` applied along `atTop`, which is
    eventually `≥ 1`). -/
theorem goldenThompson_nonCommuting_from_subgates
    (hLT : LieTrotter_Target)
    (hPerN : PerStep_TraceInequality_Target) :
    GoldenThompson_NonCommuting_Subgate := by
  intro n A B hA hB _hNotComm
  -- The Lie–Trotter sequence converges to cfc exp (A+B).
  have hTendstoMat :
      Filter.Tendsto
        (fun k : ℕ =>
          (cfc Real.exp ((1 / (k : ℂ)) • A)
            * cfc Real.exp ((1 / (k : ℂ)) • B)) ^ k)
        Filter.atTop
        (nhds (cfc Real.exp (A + B))) :=
    hLT A B hA hB
  -- Apply continuous `M ↦ (Tr M).re`.
  have hTendstoRe :
      Filter.Tendsto
        (fun k : ℕ =>
          (Matrix.trace
            ((cfc Real.exp ((1 / (k : ℂ)) • A)
                * cfc Real.exp ((1 / (k : ℂ)) • B)) ^ k)).re)
        Filter.atTop
        (nhds (Matrix.trace (cfc Real.exp (A + B))).re) :=
    (continuous_re_trace.tendsto _).comp hTendstoMat
  -- Every term in the sequence (for k ≥ 1) is bounded above by the
  -- target right-hand side.
  have hEventually :
      ∀ᶠ k : ℕ in Filter.atTop,
        (Matrix.trace
          ((cfc Real.exp ((1 / (k : ℂ)) • A)
              * cfc Real.exp ((1 / (k : ℂ)) • B)) ^ k)).re
          ≤ (Matrix.trace (cfc Real.exp A * cfc Real.exp B)).re := by
    refine Filter.eventually_atTop.mpr ⟨1, ?_⟩
    intro k hk
    exact hPerN A B hA hB k hk
  -- Take the limit.
  exact le_of_tendsto hTendstoRe hEventually

/-! ## 5. All the way to `GoldenThompson_Target`. -/

/-- **Composite reduction to `GoldenThompson_Target`.**

    Combine the Lie–Trotter route with the unconditional commuting
    case from `GoldenThompsonInequality`. -/
theorem goldenThompson_target_from_lieTrotter_route
    (hLT : LieTrotter_Target)
    (hPerN : PerStep_TraceInequality_Target) :
    GoldenThompson_Target :=
  goldenThompson_target_from_subgate
    (goldenThompson_nonCommuting_from_subgates hLT hPerN)

/-- **∧-form composite.** -/
theorem goldenThompson_target_from_lieTrotter_route_and
    (h : LieTrotter_Target ∧ PerStep_TraceInequality_Target) :
    GoldenThompson_Target :=
  goldenThompson_target_from_lieTrotter_route h.1 h.2

/-! ## 6. Downstream: Lieb 1973 tracial subgate via Lie–Trotter route. -/

/-- **Lieb 1973 tracial sub-gate via the Lie–Trotter route.**

    Plugs `goldenThompson_target_from_lieTrotter_route` into
    `lieb_tracial_subgate_from_GT_route`. -/
theorem lieb_tracial_subgate_from_lieTrotter_route
    (hLT : LieTrotter_Target)
    (hPerN : PerStep_TraceInequality_Target)
    (h_red : CarlenLieb_Integral_Reduction_Target) :
    Lieb1973_Tracial_NonCommuting_Subgate :=
  lieb_tracial_subgate_from_GT_route
    (goldenThompson_target_from_lieTrotter_route hLT hPerN) h_red

/-! ## 7. Joint named target form (∧-bundle). -/

/-- **Bundled Lie–Trotter route target.**

    A convenience `Prop` that bundles both Lie–Trotter and per-step
    targets into one. -/
def LieTrotter_Route_Target : Prop :=
  LieTrotter_Target ∧ PerStep_TraceInequality_Target

/-- Discharge of `GoldenThompson_NonCommuting_Subgate` from the
    bundled `LieTrotter_Route_Target`. -/
theorem goldenThompson_nonCommuting_from_lieTrotter_route_target
    (h : LieTrotter_Route_Target) :
    GoldenThompson_NonCommuting_Subgate :=
  goldenThompson_nonCommuting_from_subgates h.1 h.2

/-- Discharge of `GoldenThompson_Target` from the bundled
    `LieTrotter_Route_Target` (commuting case is unconditional). -/
theorem goldenThompson_target_from_lieTrotter_route_target
    (h : LieTrotter_Route_Target) :
    GoldenThompson_Target :=
  goldenThompson_target_from_lieTrotter_route h.1 h.2

/-! ## 8. Honest scope summary.

    **UNCONDITIONAL (this file)**:

      * `goldenThompson_nonCommuting_from_subgates` — the structural
        reduction `LieTrotter_Target` ∧ `PerStep_TraceInequality_Target`
        ⇒ `GoldenThompson_NonCommuting_Subgate`, via continuity of
        `Re ∘ Matrix.trace` and `le_of_tendsto`.

      * `goldenThompson_target_from_lieTrotter_route` — composite all
        the way to `GoldenThompson_Target` (combining the commuting
        unconditional discharge from `GoldenThompsonInequality`).

      * `goldenThompson_target_from_lieTrotter_route_and` — ∧-form.

      * `lieb_tracial_subgate_from_lieTrotter_route` — downstream
        hook to the Lieb 1973 chain.

      * `goldenThompson_nonCommuting_from_lieTrotter_route_target`,
        `goldenThompson_target_from_lieTrotter_route_target` —
        bundled-target forms.

    **NAMED TARGETS (this file)**:

      * `LieTrotter_Target` — Lie–Trotter product formula at the
        matrix CFC level (Trotter 1959; Reed–Simon I.151).

      * `PerStep_TraceInequality_Target` — finite-`k` Re-trace
        Hölder bound (Petz 1985; Carlen 2010).

      * `LieTrotter_Route_Target` — the ∧-bundle of the two above.

    **DISTANCE TO `GoldenThompson_Target`**:

      Two named analytic obligations remain (Lie–Trotter convergence,
      per-step trace bound), bundled as
      `LieTrotter_Route_Target`.  Their joint discharge implies
      `GoldenThompson_NonCommuting_Subgate` UNCONDITIONALLY in this
      file, and hence `GoldenThompson_Target` (since the commuting
      case is unconditionally proved in `GoldenThompsonInequality`).
-/

/-! ## 9. Axiom audit (commented).

    Uncomment locally to confirm that the structural reductions in
    this file depend only on Lean's three standard axioms
    `[propext, Classical.choice, Quot.sound]`.  Zero `sorry`, zero
    custom `axiom`. -/

-- #print axioms goldenThompson_nonCommuting_from_subgates
-- #print axioms goldenThompson_target_from_lieTrotter_route
-- #print axioms goldenThompson_target_from_lieTrotter_route_and
-- #print axioms lieb_tracial_subgate_from_lieTrotter_route
-- #print axioms goldenThompson_nonCommuting_from_lieTrotter_route_target
-- #print axioms goldenThompson_target_from_lieTrotter_route_target

-- VERIFIED 2026-06-02:
--   All six headline theorems above depend only on Lean's three
--   standard axioms `[propext, Classical.choice, Quot.sound]`.
--   Zero `sorry`, zero custom `axiom`.

end UnifiedTheory.LayerB.GoldenThompsonNonCommuting
