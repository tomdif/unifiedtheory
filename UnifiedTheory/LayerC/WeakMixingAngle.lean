/-
  UnifiedTheory/LayerC/WeakMixingAngle.lean
  ──────────────────────────────────────────

  **The SU(5) GUT prediction `sin²θ_W = 3/8` at unification (GAP-ATTACK).**

  THE famous Georgi–Glashow result: at the grand-unification scale, with
  the SU(5)-normalised hypercharge, the weak mixing angle is FIXED by
  representation theory alone:

      sin²θ_W = Tr(T₃²) / Tr(Q²)

  summed over any complete SU(5) multiplet (the `5̄`, or the full
  `5̄ ⊕ 10` generation).  Both give exactly `3/8`.  This is pure,
  provable rational arithmetic — a genuine group-theoretic prediction,
  not a fit.

  ## The computation over the `5` ( = (d, d, d, e, ν) )
  The SU(5) fundamental `5` contains a color triplet of down-type states
  (SU(2) singlets, `T₃ = 0`, `|Q| = 1/3`) and the lepton doublet
  `(ν, e)` (`T₃ = ±1/2`).

    * `Tr(T₃²)` = only the (ν, e) doublet contributes:
        `(1/2)² + (1/2)² = 1/2`.
    * `Tr(Q²)`  = `3·(1/3)² + (−1)² + 0² = 1/3 + 1 = 4/3`.
    * `sin²θ_W` = `(1/2)/(4/3) = 3/8`.   ✓

  ## The computation over the full `5̄ ⊕ 10` (one generation, 15 states)
  By completeness it MUST give the same ratio; we verify it directly:

    * `Tr(T₃²)` = 4 SU(2) doublets (3 colored quark doublets `Q` + the
      lepton doublet `L`), each `(1/2)²+(1/2)² = 1/2`:  `4·(1/2) = 2`.
    * `Tr(Q²)`  = `3·(2/3)² + 3·(1/3)² + 3·(2/3)² + 3·(1/3)² + 1² + 0² + 1²`
                = `30/9 + 2 = 16/3`.
    * `sin²θ_W` = `2 / (16/3) = 3/8`.   ✓

  ## Connection to the existing files
  The `|Q|` values used here are exactly the per-particle electric
  charges proved in `LayerC.ChargeQuantization` (down `−1/3`, up `2/3`,
  electron `−1`, neutrino `0`), themselves downstream of the anomaly-fixed
  SM hypercharges.  The state counts `5̄ + 10 = 15` are those of
  `LayerC.GUTEmbedding`.

  ## Standing constraint
  Zero `sorry`, zero custom `axiom`.  Every quantity is an exact rational
  and every theorem closes by genuine arithmetic.
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic
import UnifiedTheory.LayerC.ChargeQuantization
import UnifiedTheory.LayerC.GUTEmbedding

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.WeakMixingAngle

open UnifiedTheory.LayerC.ChargeQuantization
  (Q_up Q_down Q_electron Q_neutrino
   Q_up_eq Q_down_eq Q_electron_eq_neg_one Q_neutrino_eq_zero)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 0: THE TRACE FUNCTIONALS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- `Tr(T₃²)` over a list of `T₃` quantum numbers: `Σ T₃²`. -/
def trT3sq (T3s : List ℚ) : ℚ := (T3s.map (fun x => x ^ 2)).sum

/-- `Tr(Q²)` over a list of electric charges: `Σ Q²`. -/
def trQsq (Qs : List ℚ) : ℚ := (Qs.map (fun x => x ^ 2)).sum

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE SU(5) FUNDAMENTAL `5` = (d, d, d, e, ν)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The 3 down-type quark states are SU(2) SINGLETS (`T₃ = 0`); only the
    lepton doublet `(e, ν)` carries weak isospin (`T₃ = ∓1/2`). -/

/-- `T₃` quantum numbers of the SU(5) `5`: three SU(2)-singlet quark
    states (`T₃ = 0`) and the lepton doublet `(e, ν)` with `T₃ = ∓1/2`. -/
def five_T3 : List ℚ := [0, 0, 0, -1/2, 1/2]

/-- `|Q|` values of the SU(5) `5`: three down-type quarks (`|Q| = 1/3`),
    the electron (`|Q| = 1`) and the neutrino (`Q = 0`). -/
def five_Q : List ℚ := [1/3, 1/3, 1/3, -1, 0]

/-- `Tr(T₃²)` over the `5` equals `1/2` (only the lepton doublet). -/
theorem trT3sq_five : trT3sq five_T3 = 1/2 := by
  unfold trT3sq five_T3; norm_num

/-- `Tr(Q²)` over the `5` equals `4/3`:  `3·(1/3)² + 1² + 0² = 4/3`. -/
theorem trQsq_five : trQsq five_Q = 4/3 := by
  unfold trQsq five_Q; norm_num

/-- **The weak mixing angle at the GUT scale**, defined group-theoretically
    as `Tr(T₃²)/Tr(Q²)` over the SU(5) `5`. -/
def sin2thetaW : ℚ := trT3sq five_T3 / trQsq five_Q

/-- **THE SU(5) PREDICTION.**  `sin²θ_W = 3/8` at the unification scale —
    the celebrated Georgi–Glashow result, here an EXACT rational theorem
    forced by SU(5) representation theory:
        `sin²θ_W = (1/2)/(4/3) = 3/8`. -/
theorem sin2thetaW_eq_three_eighths : sin2thetaW = 3/8 := by
  unfold sin2thetaW
  rw [trT3sq_five, trQsq_five]
  norm_num

/-! ### Anchor the `|Q|` entries to `ChargeQuantization`.

    The non-trivial charges in `five_Q` are exactly the electric charges
    proved downstream of the anomaly-fixed hypercharges: the down-type
    `|1/3|` and the electron `|−1|`. -/

/-- The down-quark entry of `five_Q` is `|Q_down|`. -/
theorem five_Q_down_charge : (1/3 : ℚ) = -Q_down := by
  rw [Q_down_eq]; norm_num

/-- The electron entry of `five_Q` is `Q_electron`. -/
theorem five_Q_electron_charge : (-1 : ℚ) = Q_electron := by
  rw [Q_electron_eq_neg_one]

/-- The neutrino entry of `five_Q` is `Q_neutrino`. -/
theorem five_Q_neutrino_charge : (0 : ℚ) = Q_neutrino := by
  rw [Q_neutrino_eq_zero]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: THE FULL GENERATION  `5̄ ⊕ 10`  (15 states)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    By completeness the same ratio must emerge from the whole generation.
    We verify it over all 15 left-handed Weyl states of one SM
    generation:

      • Q  (quark doublet)  : (u, d) × 3 colors  → 6 states, 3 doublets;
      • uᶜ (up antiquark)   : 3 states, SU(2) singlets;
      • dᶜ (down antiquark) : 3 states, SU(2) singlets;
      • L  (lepton doublet) : (ν, e)            → 2 states, 1 doublet;
      • eᶜ (positron)       : 1 state, SU(2) singlet.

    Total: 6 + 3 + 3 + 2 + 1 = 15 = dim(5̄) + dim(10). -/

/-- `T₃` quantum numbers of the 15 states of `5̄ ⊕ 10`.  Four SU(2)
    doublets contribute `±1/2` (the three colored `Q` doublets and the
    lepton `L`); all antiquark singlets and `eᶜ` have `T₃ = 0`. -/
def gen_T3 : List ℚ :=
  [ 1/2, -1/2,    -- Q, color red   (u_r, d_r)
    1/2, -1/2,    -- Q, color green (u_g, d_g)
    1/2, -1/2,    -- Q, color blue  (u_b, d_b)
    0, 0, 0,      -- uᶜ × 3   (SU(2) singlets)
    0, 0, 0,      -- dᶜ × 3   (SU(2) singlets)
    1/2, -1/2,    -- L = (ν, e)
    0 ]           -- eᶜ        (SU(2) singlet)

/-- Electric charges of the 15 states of `5̄ ⊕ 10`.  Antiparticles carry
    opposite charge to the corresponding particle. -/
def gen_Q : List ℚ :=
  [ 2/3, -1/3,    -- Q, red   (u, d)
    2/3, -1/3,    -- Q, green
    2/3, -1/3,    -- Q, blue
    -2/3, -2/3, -2/3,   -- uᶜ × 3   (Q = −2/3)
    1/3, 1/3, 1/3,      -- dᶜ × 3   (Q = +1/3)
    0, -1,        -- L = (ν, e)
    1 ]           -- eᶜ        (Q = +1)

/-- The generation has exactly 15 states (= `dim 5̄ + dim 10`). -/
theorem gen_T3_length : gen_T3.length = 15 := by decide
theorem gen_Q_length : gen_Q.length = 15 := by decide

/-- `Tr(T₃²)` over the full generation equals `2`: four SU(2) doublets,
    each contributing `(1/2)²+(1/2)² = 1/2`. -/
theorem trT3sq_gen : trT3sq gen_T3 = 2 := by
  unfold trT3sq gen_T3; norm_num

/-- `Tr(Q²)` over the full generation equals `16/3`:
    `4·3·(2/3)² + 2·3·(1/3)² + 1² + 0² + 1² = 16/3`. -/
theorem trQsq_gen : trQsq gen_Q = 16/3 := by
  unfold trQsq gen_Q; norm_num

/-- The weak mixing angle computed over the FULL generation `5̄ ⊕ 10`. -/
def sin2thetaW_gen : ℚ := trT3sq gen_T3 / trQsq gen_Q

/-- **Completeness check.**  The full `5̄ ⊕ 10` generation gives the SAME
    prediction `sin²θ_W = 3/8`:  `2 / (16/3) = 3/8`. -/
theorem sin2thetaW_gen_eq_three_eighths : sin2thetaW_gen = 3/8 := by
  unfold sin2thetaW_gen
  rw [trT3sq_gen, trQsq_gen]
  norm_num

/-- The `5` and the full `5̄ ⊕ 10` agree: both predict `3/8`. -/
theorem sin2thetaW_complete_consistency : sin2thetaW = sin2thetaW_gen := by
  rw [sin2thetaW_eq_three_eighths, sin2thetaW_gen_eq_three_eighths]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **WEAK-MIXING-ANGLE MASTER THEOREM.**

    The full SU(5) prediction bundled:

      (I)   over the `5`:  `Tr(T₃²) = 1/2`, `Tr(Q²) = 4/3`,
            `sin²θ_W = 3/8`;
      (II)  over the full `5̄ ⊕ 10`: `Tr(T₃²) = 2`, `Tr(Q²) = 16/3`,
            `sin²θ_W = 3/8`;
      (III) the two multiplets give the SAME ratio — the famous
            **`sin²θ_W = 3/8` at the grand-unification scale**. -/
theorem weak_mixing_master :
    (trT3sq five_T3 = 1/2 ∧ trQsq five_Q = 4/3 ∧ sin2thetaW = 3/8) ∧
    (trT3sq gen_T3 = 2 ∧ trQsq gen_Q = 16/3 ∧ sin2thetaW_gen = 3/8) ∧
    (sin2thetaW = sin2thetaW_gen) :=
  ⟨⟨trT3sq_five, trQsq_five, sin2thetaW_eq_three_eighths⟩,
   ⟨trT3sq_gen, trQsq_gen, sin2thetaW_gen_eq_three_eighths⟩,
   sin2thetaW_complete_consistency⟩

-- Axiom audit (only Lean's three core axioms should appear; no custom
-- axiom, no sorryAx).
section AxiomAudit
#print axioms sin2thetaW_eq_three_eighths
#print axioms sin2thetaW_gen_eq_three_eighths
#print axioms weak_mixing_master
end AxiomAudit

end UnifiedTheory.LayerC.WeakMixingAngle
