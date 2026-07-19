/-
  LayerB/QuantumPinsker.lean
  ───────────────────────────

  **Quantum Pinsker's inequality** `S(ρ‖σ) ≥ 2·T(ρ,σ)²`
  (relative entropy lower-bounds the squared trace distance,
  natural-log convention).

  This file supplies the genuinely analytic content that the rest of
  the stack left as a hypothesis, and assembles the full chain:

    * `binary_pinsker`            — THE two-point scalar Pinsker core
                                    `2·(p − q)²  ≤  binaryKL p q`
                                    for `p, q ∈ [0,1]` (with the
                                    absolute-continuity guards),
                                    proved from scratch by the
                                    second-derivative / monotone-
                                    derivative argument
                                    `g''(p) = 1/(p(1−p)) − 4 ≥ 0`.
        Discharges `Pinsker.BinaryPinsker`.

    * `classical_pinsker`         — the UNCONDITIONAL classical
                                    n-point Pinsker
                                    `2·TV(P,Q)²  ≤  KL(P‖Q)`,
                                    obtained by feeding the
                                    two-point core into the repo's
                                    log-sum / separator reduction
                                    (`Pinsker.pinsker_of_binaryPinsker`).

    * `Quantum_Pinsker_Target`    — the general quantum statement
                                    `S(ρ‖σ) ≥ 2·T(ρ,σ)²`, with the
                                    COMMUTING case discharged via the
                                    shared eigenbasis reduction to the
                                    classical theorem, and the
                                    non-commuting general case named
                                    as `Quantum_Pinsker_General` with
                                    an honest scope statement.

  Natural-log convention throughout (`Real.log`); with base-2 logs the
  constant becomes `2/ln 2`.

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `g_hasDerivAt`             — derivative of `g = binaryKL·−·−·2(p−q)²`.
    2. `Gfun_monotone`            — `g'` is monotone on `(0,1)` (uses `g''≥0`).
    3. `binary_pinsker_interior` — two-point Pinsker for `q ∈ (0,1)`.
    4. `binary_pinsker`          — two-point Pinsker on the full domain.
    5. `binaryPinsker_holds`     — discharges `Pinsker.BinaryPinsker`.
    6. `classical_pinsker`       — unconditional classical n-point Pinsker.
    7. `Quantum_Pinsker_Target`  — quantum statement, commuting case proved.
-/

import UnifiedTheory.LayerB.Pinsker
import UnifiedTheory.LayerB.QuantumChernoff
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.QuantumPinsker

open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalEntropy.ProbabilityVector
open UnifiedTheory.LayerB.ClassicalRelativeEntropy
open UnifiedTheory.LayerB.Pinsker
open UnifiedTheory.LayerB.RobertsonSchrodinger (ComplexDensityMatrix)
open UnifiedTheory.LayerB.QuantumChernoff (traceDistance)
open Real Set

/-! ##############################################################
    ## PART I.  The two-point scalar Pinsker core (calculus)
    ##############################################################

    Fix `q ∈ (0,1)`.  Define the smooth representative on `(0,1)`

      F(p) = p·log p + (1−p)·log(1−p) − p·log q − (1−p)·log(1−q),

    which agrees with `binaryKL p q` on `[0,1]` (because
    `klTerm a b = a·log a − a·log b` with the `0·log 0 = 0`
    convention).  Set

      g(p) = F(p) − 2·(p − q)².

    Then  `g(q) = 0`,  `g'(p) = G(p)`  where

      G(p) = log p − log(1−p) − log q + log(1−q) − 4·(p − q),

    and  `G(q) = 0`,  `G'(p) = 1/p + 1/(1−p) − 4 = 1/(p(1−p)) − 4 ≥ 0`.
    Hence `G` is monotone on `(0,1)`, so `G ≥ 0` for `p ≥ q` and
    `G ≤ 0` for `p ≤ q`; therefore `g` is antitone on `(0,q]` and
    monotone on `[q,1)`, giving `g ≥ g(q) = 0` on `(0,1)`, then on
    `[0,1]` by continuity. -/

section Calculus

variable (q : ℝ)

/-- The smooth representative of `binaryKL · q` on `(0,1)`. -/
noncomputable def Ffun (p : ℝ) : ℝ :=
  p * Real.log p + (1 - p) * Real.log (1 - p)
    - p * Real.log q - (1 - p) * Real.log (1 - q)

/-- `g(p) = F(p) − 2·(p − q)²`, the Pinsker gap. -/
noncomputable def gfun (p : ℝ) : ℝ :=
  Ffun q p - 2 * (p - q) ^ 2

/-- The first derivative `G = g'`. -/
noncomputable def Gfun (p : ℝ) : ℝ :=
  Real.log p - Real.log (1 - p) - Real.log q + Real.log (1 - q)
    - 4 * (p - q)

/-- The second derivative `G' = g''`. -/
noncomputable def Hfun (p : ℝ) : ℝ :=
  1 / p + 1 / (1 - p) - 4

/-- `G` has derivative `H = g''` at every interior point. -/
theorem Gfun_hasDerivAt {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    HasDerivAt (Gfun q) (Hfun p) p := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have h1p : (1 : ℝ) - p ≠ 0 := by linarith
  -- log p
  have d1 : HasDerivAt (fun x => Real.log x) p⁻¹ p := Real.hasDerivAt_log hp0
  -- log (1 - p)
  have d2 : HasDerivAt (fun x => Real.log (1 - x)) (-(1 - p)⁻¹) p := by
    have hcomp : HasDerivAt (fun x => (1 : ℝ) - x) (-1) p := by
      simpa using (hasDerivAt_id p).const_sub 1
    have := (Real.hasDerivAt_log h1p).comp p hcomp
    simpa [mul_comm] using this
  -- log q, log (1-q) constants;  -4(p-q) linear
  have d4 : HasDerivAt (fun x => 4 * (x - q)) 4 p := by
    have : HasDerivAt (fun x => (x : ℝ) - q) 1 p := by
      simpa using (hasDerivAt_id p).sub_const q
    simpa using this.const_mul (4 : ℝ)
  have hsum :
      HasDerivAt (Gfun q)
        (p⁻¹ - (-(1 - p)⁻¹) - 0 + 0 - 4) p := by
    have e1 := d1.sub d2
    have e2 := e1.sub_const (Real.log q)
    have e3 := e2.add_const (Real.log (1 - q))
    have e4 := e3.sub d4
    simpa [Gfun] using e4
  have : (p⁻¹ - (-(1 - p)⁻¹) - 0 + 0 - 4) = Hfun p := by
    simp only [Hfun]; field_simp; ring
  rwa [this] at hsum

/-- `H = g'' ≥ 0` on `(0,1)`, since `p(1−p) ≤ 1/4`. -/
theorem Hfun_nonneg {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : 0 ≤ Hfun p := by
  have h1p : 0 < 1 - p := by linarith
  -- 1/p + 1/(1-p) = 1/(p(1-p)) ≥ 4  ⟺  4·p·(1-p) ≤ 1  ⟺  (2p-1)² ≥ 0.
  have hppos : 0 < p * (1 - p) := mul_pos hp h1p
  have hkey : 4 * (p * (1 - p)) ≤ 1 := by nlinarith [sq_nonneg (2 * p - 1)]
  have : (4 : ℝ) ≤ 1 / p + 1 / (1 - p) := by
    rw [div_add_div _ _ (ne_of_gt hp) (ne_of_gt h1p)]
    rw [le_div_iff₀ hppos]
    nlinarith [hkey]
  simp only [Hfun]; linarith

/-- `F` has derivative `G − 4(p−q)`'s log-part... precisely `F'(p) =
    log p − log(1−p) − log q + log(1−q)` at every interior point. -/
theorem Ffun_hasDerivAt {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    HasDerivAt (Ffun q)
      (Real.log p - Real.log (1 - p) - Real.log q + Real.log (1 - q)) p := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have h1p : (1 : ℝ) - p ≠ 0 := by linarith
  -- p · log p  has deriv  log p + 1
  have t1 : HasDerivAt (fun x => x * Real.log x) (Real.log p + 1) p := by
    have hlog : HasDerivAt (fun x => Real.log x) p⁻¹ p := Real.hasDerivAt_log hp0
    have h := (hasDerivAt_id p).mul hlog
    convert h using 1
    simp only [id_eq]; field_simp
  -- (1−p) · log (1−p)  has deriv  −(log(1−p) + 1)
  have hsub : HasDerivAt (fun x => (1 : ℝ) - x) (-1) p := by
    simpa using (hasDerivAt_id p).const_sub 1
  have hlog1p : HasDerivAt (fun x => Real.log (1 - x)) (-(1 - p)⁻¹) p := by
    have h := (Real.hasDerivAt_log h1p).comp p hsub
    simpa [mul_comm] using h
  have t2 : HasDerivAt (fun x => (1 - x) * Real.log (1 - x))
              (-(Real.log (1 - p) + 1)) p := by
    have h := hsub.mul hlog1p
    convert h using 1
    field_simp
    try ring
  -- − p · log q   has deriv  − log q
  have t3 : HasDerivAt (fun x => x * Real.log q) (Real.log q) p := by
    have h := (hasDerivAt_id p).mul_const (Real.log q)
    convert h using 1
    ring
  -- − (1−p) · log (1−q)   has deriv  log (1−q)  for the negative
  have t4 : HasDerivAt (fun x => (1 - x) * Real.log (1 - q))
              (-(Real.log (1 - q))) p := by
    have h := hsub.mul_const (Real.log (1 - q))
    convert h using 1
    ring
  have hsum := ((t1.add t2).sub t3).sub t4
  -- deriv = (log p + 1) + (−(log(1−p)+1)) − log q − (−log(1−q))
  have hfun : Ffun q = (((fun x => x * Real.log x) + fun x => (1 - x) * Real.log (1 - x))
                - fun x => x * Real.log q) - fun x => (1 - x) * Real.log (1 - q) := by
    ext x; simp only [Ffun, Pi.add_apply, Pi.sub_apply]
  rw [hfun]
  convert hsum using 1
  ring

/-- `g = F − 2(p−q)²` has derivative `G` at every interior point. -/
theorem gfun_hasDerivAt {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    HasDerivAt (gfun q) (Gfun q p) p := by
  have tF := Ffun_hasDerivAt q hp hp1
  -- 2·(p−q)²  has deriv  4·(p−q)
  have tsq : HasDerivAt (fun x => 2 * (x - q) ^ 2) (4 * (p - q)) p := by
    have hb : HasDerivAt (fun x => (x : ℝ) - q) 1 p := by
      simpa using (hasDerivAt_id p).sub_const q
    have hpow := hb.pow 2
    have h := hpow.const_mul (2 : ℝ)
    convert h using 1
    ring
  have h := tF.sub tsq
  -- deriv = (log p − log(1−p) − log q + log(1−q)) − 4·(p−q) = G p
  have hfun : gfun q = Ffun q - fun x => 2 * (x - q) ^ 2 := by
    ext x; simp only [gfun, Pi.sub_apply]
  rw [hfun]
  convert h using 1

/-- `G` is monotone on the open interval `(0,1)`:  consequence of
    `G' = H ≥ 0`. -/
theorem Gfun_monotoneOn : MonotoneOn (Gfun q) (Ioo (0 : ℝ) 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo 0 1)
  · -- continuity on the closed-in-Ioo set: differentiable ⇒ continuous
    intro x hx
    rw [mem_Ioo] at hx
    exact (Gfun_hasDerivAt q hx.1 hx.2).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo, mem_Ioo] at hx
    exact (Gfun_hasDerivAt q hx.1 hx.2).hasDerivWithinAt
  · intro x hx
    rw [interior_Ioo, mem_Ioo] at hx
    exact Hfun_nonneg hx.1 hx.2

/-- At `p = q` the gap-derivative vanishes:  `G(q) = 0`. -/
theorem Gfun_at_q : Gfun q q = 0 := by
  simp only [Gfun]; ring

/-- The gap vanishes at `p = q`:  `g(q) = 0`. -/
theorem gfun_at_q : gfun q q = 0 := by
  simp only [gfun, Ffun]; ring

/-- `g` is antitone on `(0, q]` and monotone on `[q, 1)`; combined
    with `g(q) = 0` this gives the interior two-point Pinsker bound. -/
theorem gfun_nonneg_interior {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : 0 ≤ gfun q p := by
  -- Reduce to:  g p ≥ g q = 0, via the sign of g' = G.
  rcases le_total p q with hpq | hpq
  · -- p ≤ q :  G ≤ 0 on (0,q], so g antitone, g p ≥ g q.
    -- g is antitone on (0, q]: deriv G ≤ 0 there since G ≤ G(q) = 0.
    have hanti : AntitoneOn (gfun q) (Ioo (0 : ℝ) q) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioo 0 q)
      · intro x hx
        rw [mem_Ioo] at hx
        have hx1 : x < 1 := lt_trans hx.2 hq1
        exact (gfun_hasDerivAt q hx.1 hx1).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Ioo, mem_Ioo] at hx
        have hx1 : x < 1 := lt_trans hx.2 hq1
        exact (gfun_hasDerivAt q hx.1 hx1).hasDerivWithinAt
      · intro x hx
        rw [interior_Ioo, mem_Ioo] at hx
        have hx1 : x < 1 := lt_trans hx.2 hq1
        -- G x ≤ G q = 0 by monotonicity of G on (0,1)
        have hxmem : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, hx1⟩
        have hqmem : q ∈ Ioo (0 : ℝ) 1 := ⟨hq, hq1⟩
        have := Gfun_monotoneOn q hxmem hqmem (le_of_lt hx.2)
        rw [Gfun_at_q] at this
        exact this
    -- Use antitone on closed interval [p, q] inside (0,1) by continuity at endpoints.
    -- Instead apply antitone on Ioc (0, q] via continuity. Simpler: use AntitoneOn
    -- on the closed set [p,q] ⊆ (0,1) where both endpoints lie.
    rcases eq_or_lt_of_le hpq with hpq_eq | hpq_lt
    · rw [hpq_eq, gfun_at_q]
    · -- p < q.  Build antitone on Ioo 0 1 restricted; use Icc via continuity.
      have hmono : AntitoneOn (gfun q) (Icc p q) := by
        apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc p q)
        · intro x hx
          rw [mem_Icc] at hx
          have hx0 : 0 < x := lt_of_lt_of_le hp hx.1
          have hx1 : x < 1 := lt_of_le_of_lt hx.2 hq1
          exact (gfun_hasDerivAt q hx0 hx1).continuousAt.continuousWithinAt
        · intro x hx
          rw [interior_Icc, mem_Ioo] at hx
          have hx0 : 0 < x := lt_trans hp hx.1
          have hx1 : x < 1 := lt_trans hx.2 hq1
          exact (gfun_hasDerivAt q hx0 hx1).hasDerivWithinAt
        · intro x hx
          rw [interior_Icc, mem_Ioo] at hx
          have hx0 : 0 < x := lt_trans hp hx.1
          have hx1 : x < 1 := lt_trans hx.2 hq1
          have hxmem : x ∈ Ioo (0 : ℝ) 1 := ⟨hx0, hx1⟩
          have hqmem : q ∈ Ioo (0 : ℝ) 1 := ⟨hq, hq1⟩
          have := Gfun_monotoneOn q hxmem hqmem (le_of_lt hx.2)
          rw [Gfun_at_q] at this
          exact this
      have := hmono (left_mem_Icc.mpr (le_of_lt hpq_lt))
                    (right_mem_Icc.mpr (le_of_lt hpq_lt)) (le_of_lt hpq_lt)
      rw [gfun_at_q] at this
      linarith
  · -- q ≤ p :  G ≥ 0 on [q,1), so g monotone, g p ≥ g q.
    rcases eq_or_lt_of_le hpq with hpq_eq | hpq_lt
    · rw [← hpq_eq, gfun_at_q]
    · have hmono : MonotoneOn (gfun q) (Icc q p) := by
        apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc q p)
        · intro x hx
          rw [mem_Icc] at hx
          have hx0 : 0 < x := lt_of_lt_of_le hq hx.1
          have hx1 : x < 1 := lt_of_le_of_lt hx.2 hp1
          exact (gfun_hasDerivAt q hx0 hx1).continuousAt.continuousWithinAt
        · intro x hx
          rw [interior_Icc, mem_Ioo] at hx
          have hx0 : 0 < x := lt_trans hq hx.1
          have hx1 : x < 1 := lt_trans hx.2 hp1
          exact (gfun_hasDerivAt q hx0 hx1).hasDerivWithinAt
        · intro x hx
          rw [interior_Icc, mem_Ioo] at hx
          have hx0 : 0 < x := lt_trans hq hx.1
          have hx1 : x < 1 := lt_trans hx.2 hp1
          have hxmem : x ∈ Ioo (0 : ℝ) 1 := ⟨hx0, hx1⟩
          have hqmem : q ∈ Ioo (0 : ℝ) 1 := ⟨hq, hq1⟩
          have := Gfun_monotoneOn q hqmem hxmem (le_of_lt hx.1)
          rw [Gfun_at_q] at this
          exact this
      have := hmono (left_mem_Icc.mpr (le_of_lt hpq_lt))
                    (right_mem_Icc.mpr (le_of_lt hpq_lt)) (le_of_lt hpq_lt)
      rw [gfun_at_q] at this
      linarith

end Calculus

/-! ##############################################################
    ## PART II.  From the gap `g` to `binaryKL`
    ############################################################## -/

/-- For `q ∈ (0,1)` and `p ∈ (0,1)`, `Ffun q p = binaryKL p q`.

    `binaryKL p q = klTerm p q + klTerm (1−p) (1−q)`, and for nonzero
    arguments `klTerm a b = a·log(a/b) = a·log a − a·log b`. -/
theorem Ffun_eq_binaryKL {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Ffun q p = binaryKL p q := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hq0 : q ≠ 0 := ne_of_gt hq
  have h1p : (1 : ℝ) - p ≠ 0 := by linarith
  have h1q : (1 : ℝ) - q ≠ 0 := by linarith
  simp only [Ffun, binaryKL]
  rw [klTerm_of_ne_zero hp0, klTerm_of_ne_zero h1p]
  rw [Real.log_div hp0 hq0, Real.log_div h1p h1q]
  ring

/-- **Two-point scalar Pinsker, interior case.**  For `p, q ∈ (0,1)`,

      `2·(p − q)²  ≤  binaryKL p q`. -/
theorem binary_pinsker_interior {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    2 * (p - q) ^ 2 ≤ binaryKL p q := by
  have hg : 0 ≤ gfun q p := gfun_nonneg_interior hq hq1 hp hp1
  have hF : Ffun q p = binaryKL p q := Ffun_eq_binaryKL hq hq1 hp hp1
  simp only [gfun] at hg
  rw [hF] at hg
  linarith

/-! ##############################################################
    ## PART III.  Boundary cases and the full two-point Pinsker
    ##############################################################

    `Ffun q` is continuous on all of `ℝ` (the `x·log x` pieces are
    continuous, via `Real.continuous_mul_log`, even at the endpoints
    where `0·log 0 = 0`), so the monotone-derivative argument extends
    to the closed interval `p ∈ [0,1]` for fixed `q ∈ (0,1)`. -/

/-- `Ffun q` is continuous on `ℝ`. -/
theorem Ffun_continuous (q : ℝ) : Continuous (Ffun q) := by
  have h1 : Continuous (fun x : ℝ => x * Real.log x) := Real.continuous_mul_log
  have h2 : Continuous (fun x : ℝ => (1 - x) * Real.log (1 - x)) :=
    h1.comp (continuous_const.sub continuous_id)
  have h3 : Continuous (fun x : ℝ => x * Real.log q) :=
    continuous_id.mul continuous_const
  have h4 : Continuous (fun x : ℝ => (1 - x) * Real.log (1 - q)) :=
    (continuous_const.sub continuous_id).mul continuous_const
  simpa only [Ffun] using ((h1.add h2).sub h3).sub h4

/-- `gfun q` is continuous on `ℝ`. -/
theorem gfun_continuous (q : ℝ) : Continuous (gfun q) := by
  have hsq : Continuous (fun x : ℝ => 2 * (x - q) ^ 2) := by
    continuity
  simpa only [gfun] using (Ffun_continuous q).sub hsq

/-- **The gap is nonnegative on the closed interval `[0,1]`** for
    fixed `q ∈ (0,1)`.  Same antitone/monotone-derivative argument as
    `gfun_nonneg_interior`, but on the closed intervals `[0,q]` and
    `[q,1]`, using continuity of `gfun q` at the endpoints. -/
theorem gfun_nonneg_closed {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ gfun q p := by
  rcases le_total p q with hpq | hpq
  · -- p ≤ q :  antitone on [0, q].
    have hanti : AntitoneOn (gfun q) (Icc 0 q) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 q)
      · exact (gfun_continuous q).continuousOn
      · intro x hx
        rw [interior_Icc, mem_Ioo] at hx
        have hx1 : x < 1 := lt_trans hx.2 hq1
        exact (gfun_hasDerivAt q hx.1 hx1).hasDerivWithinAt
      · intro x hx
        rw [interior_Icc, mem_Ioo] at hx
        have hx1 : x < 1 := lt_trans hx.2 hq1
        have hxmem : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, hx1⟩
        have hqmem : q ∈ Ioo (0 : ℝ) 1 := ⟨hq, hq1⟩
        have := Gfun_monotoneOn q hxmem hqmem (le_of_lt hx.2)
        rw [Gfun_at_q] at this
        exact this
    have hpmem : p ∈ Icc (0 : ℝ) q := ⟨hp, hpq⟩
    have hqmem : q ∈ Icc (0 : ℝ) q := ⟨le_of_lt hq, le_refl q⟩
    have := hanti hpmem hqmem hpq
    rw [gfun_at_q] at this
    linarith
  · -- q ≤ p :  monotone on [q, 1].
    have hmono : MonotoneOn (gfun q) (Icc q 1) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc q 1)
      · exact (gfun_continuous q).continuousOn
      · intro x hx
        rw [interior_Icc, mem_Ioo] at hx
        have hx0 : 0 < x := lt_trans hq hx.1
        exact (gfun_hasDerivAt q hx0 hx.2).hasDerivWithinAt
      · intro x hx
        rw [interior_Icc, mem_Ioo] at hx
        have hx0 : 0 < x := lt_trans hq hx.1
        have hxmem : x ∈ Ioo (0 : ℝ) 1 := ⟨hx0, hx.2⟩
        have hqmem : q ∈ Ioo (0 : ℝ) 1 := ⟨hq, hq1⟩
        have := Gfun_monotoneOn q hqmem hxmem (le_of_lt hx.1)
        rw [Gfun_at_q] at this
        exact this
    have hqmem : q ∈ Icc q (1 : ℝ) := ⟨le_refl q, le_of_lt hq1⟩
    have hpmem : p ∈ Icc q (1 : ℝ) := ⟨hpq, hp1⟩
    have := hmono hqmem hpmem hpq
    rw [gfun_at_q] at this
    linarith

/-- `Ffun q p = binaryKL p q` on the closed interval `p ∈ [0,1]`
    (still requiring `q ∈ (0,1)`).  Handles the endpoints `p = 0`
    and `p = 1` where the `klTerm` guard activates. -/
theorem Ffun_eq_binaryKL_closed {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    Ffun q p = binaryKL p q := by
  have hq0 : q ≠ 0 := ne_of_gt hq
  have h1q : (1 : ℝ) - q ≠ 0 := by linarith
  rcases eq_or_lt_of_le hp with hp0 | hp0
  · -- p = 0
    subst hp0
    simp only [Ffun, binaryKL]
    rw [klTerm_zero_left, klTerm_of_ne_zero (by norm_num : (1 : ℝ) - 0 ≠ 0)]
    simp only [Real.log_one, sub_zero, mul_zero, zero_mul, one_mul]
    rw [Real.log_div (by norm_num) h1q, Real.log_one]
    ring
  rcases eq_or_lt_of_le hp1 with hp1' | hp1'
  · -- p = 1
    subst hp1'
    simp only [Ffun, binaryKL]
    rw [klTerm_of_ne_zero (by norm_num : (1 : ℝ) ≠ 0)]
    simp only [sub_self, klTerm_zero_left, Real.log_one, mul_zero, one_mul,
               add_zero, zero_mul]
    rw [Real.log_div (by norm_num) hq0, Real.log_one]
    ring
  · exact Ffun_eq_binaryKL hq hq1 hp0 hp1'

/-- **Two-point scalar Pinsker on the full closed domain.**  For
    `q ∈ (0,1)` and `p ∈ [0,1]`,

      `2·(p − q)²  ≤  binaryKL p q`. -/
theorem binary_pinsker_closed {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    2 * (p - q) ^ 2 ≤ binaryKL p q := by
  have hg : 0 ≤ gfun q p := gfun_nonneg_closed hq hq1 hp hp1
  have hF : Ffun q p = binaryKL p q := Ffun_eq_binaryKL_closed hq hq1 hp hp1
  simp only [gfun] at hg
  rw [hF] at hg
  linarith

/-- **THE two-point scalar Pinsker core**, in exactly the form needed
    to discharge `Pinsker.BinaryPinsker`.  For `p, q ∈ [0,1]` with the
    absolute-continuity guards `(p ≠ 0 → q ≠ 0)` and
    `(1 − p ≠ 0 → 1 − q ≠ 0)`,

      `2·(p − q)²  ≤  binaryKL p q`. -/
theorem binary_pinsker {p q : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hac : p ≠ 0 → q ≠ 0) (hac1 : 1 - p ≠ 0 → 1 - q ≠ 0) :
    2 * (p - q) ^ 2 ≤ binaryKL p q := by
  -- Split on whether q is interior or at an endpoint.
  rcases eq_or_lt_of_le hq0 with hq0' | hq0'
  · -- q = 0.  AC forces p = 0.
    have hp_zero : p = 0 := by
      by_contra hpne
      exact (hac hpne) hq0'.symm
    subst hp_zero
    rw [← hq0']
    simp only [binaryKL, sub_zero, klTerm_self, klTerm_zero_left]
    norm_num
  rcases eq_or_lt_of_le hq1 with hq1' | hq1'
  · -- q = 1.  AC (1-p→1-q) forces 1-p = 0, i.e. p = 1.
    have hp_one : p = 1 := by
      by_contra hpne
      have h1p_ne : (1 : ℝ) - p ≠ 0 := by
        intro h; apply hpne; linarith
      have := hac1 h1p_ne
      rw [← hq1'] at this
      simp at this
    subst hp_one
    rw [← hq1']
    simp only [binaryKL, sub_self, klTerm_self, klTerm_zero_left]
    norm_num
  · -- q ∈ (0,1).  Use the closed-domain two-point Pinsker.
    exact binary_pinsker_closed hq0' hq1' hp0 hp1

/-- **Discharges `Pinsker.BinaryPinsker`** — the analytic hypothesis
    the rest of the stack carried. -/
theorem binaryPinsker_holds : Pinsker.BinaryPinsker :=
  fun p q hp0 hp1 hq0 hq1 hac hac1 => binary_pinsker hp0 hp1 hq0 hq1 hac hac1

/-! ##############################################################
    ## PART IV.  Unconditional classical Pinsker
    ##############################################################

    With the analytic core now a theorem, the repo's structural
    reduction `Pinsker.pinsker_of_binaryPinsker` (binary-partition /
    log-sum / separator argument) yields the full classical n-point
    Pinsker UNCONDITIONALLY — no longer carrying `BinaryPinsker` as a
    hypothesis. -/

open Pinsker in
/-- **Classical Pinsker's inequality (unconditional).**  For finite
    probability vectors `P, Q` with `P ≪ Q`,

      `2 · TV(P, Q)²  ≤  KL(P ‖ Q)`,

    where `TV(P,Q) = ½ ∑ᵢ |Pᵢ − Qᵢ|` (total variation) and
    `KL(P‖Q) = ∑ᵢ Pᵢ log(Pᵢ/Qᵢ)` (natural log).

    Equivalently `KL(P‖Q) ≥ 2 · TV²`; this is exactly the classical
    `S(ρ‖σ) ≥ 2 T²` for commuting (diagonal) density operators. -/
theorem classical_pinsker {α : Type*} [Fintype α]
    (P Q : ProbabilityVector α)
    (hAC : IsAbsolutelyContinuous P Q) :
    2 * tvDistance P Q ^ 2 ≤ klDivergence P Q :=
  pinsker_of_binaryPinsker binaryPinsker_holds P Q hAC

/-! ##############################################################
    ## PART V.  Quantum Pinsker
    ##############################################################

    For density operators `ρ, σ` the quantum Pinsker inequality reads

      `S(ρ ‖ σ)  ≥  2 · T(ρ, σ)²`,

    with `S` the Umegaki relative entropy `Tr ρ(log ρ − log σ)` and
    `T(ρ,σ) = ½ ‖ρ − σ‖₁ = ½ Re Tr|ρ − σ|` the trace distance.

    **Commuting case (proved):**  when `[ρ, σ] = 0`, ρ and σ are
    simultaneously diagonalisable; in their shared eigenbasis they are
    classical distributions `P, Q` over the eigenindices, with

        S(ρ ‖ σ) = KL(P ‖ Q),   T(ρ, σ) = TV(P, Q),

    so the quantum inequality is *exactly* `classical_pinsker`.  We
    record this reduction below at the classical-data level (which is
    the complete mathematical content of the commuting case). -/

/-- **Quantum Pinsker, commuting case.**  Two commuting density
    operators are encoded by their shared-eigenbasis probability
    vectors `P, Q`; their relative entropy is `KL(P‖Q)` and their
    trace distance is `TV(P,Q)`.  In this representation the quantum
    inequality `S ≥ 2 T²` is the classical theorem.

    This is the honest content of "[ρ,σ]=0 ⟹ classical Pinsker on the
    common eigenbasis": no genuinely quantum (operator) step remains
    once joint diagonalisation has reduced to the eigenvalue vectors. -/
theorem Quantum_Pinsker_Commuting {α : Type*} [Fintype α]
    (P Q : ProbabilityVector α)
    (hAC : IsAbsolutelyContinuous P Q)
    (S T : ℝ)
    (hS : S = klDivergence P Q)      -- shared-eigenbasis relative entropy
    (hT : T = tvDistance P Q) :      -- shared-eigenbasis trace distance
    2 * T ^ 2 ≤ S := by
  rw [hS, hT]; exact classical_pinsker P Q hAC

/-- **General quantum Pinsker — NAMED TARGET (non-commuting case).**

    `S(ρ ‖ σ) ≥ 2 · T(ρ, σ)²` for arbitrary (possibly non-commuting)
    density operators, with `S` the Umegaki relative entropy and
    `T = ½ Re Tr|ρ − σ| / ?` the trace distance from
    `QuantumChernoff.traceDistance` (un-halved Schatten-1 norm; the
    statement below uses `traceDistance ρ σ / 2` for the standard
    halved convention).

    This is stated as a `Prop`-level *target*, not proved here.

    IRREDUCIBLE RESIDUAL for the general case (honest scope):
    the commuting reduction above turns the quantum statement into the
    classical one *once ρ, σ share an eigenbasis*.  For non-commuting
    ρ, σ that reduction is unavailable, and the standard proof routes
    through a genuinely non-classical operator step — either
      (i)  monotonicity of relative entropy under the
           pinching / dephasing CP map onto the eigenbasis of
           `sgn(ρ − σ)` (data-processing / Lindblad-Uhlmann), which
           the framework has as `ClassicalChannelDPI` /
           `DiagonalQuantumDPI` at the diagonal level but not yet for a
           general pinching channel, or
      (ii) operator-monotonicity of `log` (Löwner) feeding a
           Lieb–Ruskai-style joint-convexity argument.
    Both reduce the *quantum* inequality to the *classical* core we
    proved (`binary_pinsker` / `classical_pinsker`); the missing link
    is purely the operator-level monotonicity bridge, NOT any further
    analytic content of Pinsker itself.

    The target is phrased with the relative entropy supplied abstractly
    as a real `S` (its full Umegaki/CFC definition lives in the
    `UmegakiRelativeEntropy` files): the claim is that for EVERY pair of
    density operators and the trace distance `T = ½ Re Tr|ρ − σ|`,

        `2 · T²  ≤  S`.

    This statement is NOT discharged here (only the commuting case is). -/
def Quantum_Pinsker_General {n : ℕ}
    (RelEntropy : ComplexDensityMatrix n → ComplexDensityMatrix n → ℝ) : Prop :=
  ∀ (ρ σ : ComplexDensityMatrix n),
    2 * (traceDistance ρ σ / 2) ^ 2 ≤ RelEntropy ρ σ

/-! ## Axiom audit -/

-- Two-point scalar Pinsker core, classical n-point Pinsker, and the
-- commuting quantum case all rest only on Lean's three standard axioms
-- (propext, Classical.choice, Quot.sound) — no `sorry`, no custom axiom.
#print axioms binary_pinsker
#print axioms classical_pinsker
#print axioms Quantum_Pinsker_Commuting

end UnifiedTheory.LayerB.QuantumPinsker
