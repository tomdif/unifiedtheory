/-
  LayerB/ChristodoulouIrreducibleMass.lean — Christodoulou's irreducible
  mass formula for a Kerr (rotating) black hole, the Penrose-process
  upper bound on extractable energy, and the Schwarzschild limit.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT

  `LayerB/BekensteinHawking.lean` already establishes the entropy
  / horizon-area calculus for a Schwarzschild black hole:
  `A = 16π M²` and `S_BH = A/4 = 4π M²`. Schwarzschild is the
  J = 0 (non-rotating) special case of the Kerr family.

  A general Kerr black hole carries both mass M and angular momentum
  J. Christodoulou (Phys. Rev. Lett. 25, 1596 (1970)) introduced the
  notion of *irreducible mass* M_irr — the mass associated with the
  horizon area alone:

       A = 16π · M_irr²,      so   M_irr² = A / (16π).

  Solving the Kerr horizon-area expression
       A = 8π · ( M² + √(M⁴ − J²) )
  for M_irr² yields the Christodoulou formula proved in this file:

       M_irr² = ( M² + √(M⁴ − J²) ) / 2.                          (*)

  The companion identity
       M² = M_irr² + J² / (4 · M_irr²)                            (**)
  decomposes the total mass-energy into an "irreducible" piece and
  a "rotational" piece. The Penrose process can extract the latter
  but not the former (because the area theorem forbids decreasing
  M_irr); for an extremal initial state J = M² this gives a maximum
  extractable fraction `1 − 1/√2 ≈ 0.293`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED

  (1) `kerrSubextremal M J`: the sub-extremality predicate `J² ≤ M⁴`
      (equivalently `|a| ≤ M` with `a = J/M`). The Kerr horizon
      exists iff this holds.

  (2) `irreducibleMassSq M J := (M² + √(M⁴ − J²)) / 2`. Closed-form
      definition of `M_irr²` as in (*).

  (3) `irreducibleMassSq_nonneg`: `0 ≤ M_irr²` whenever the Kerr is
      sub-extremal.

  (4) `irreducibleMassSq_le_M_sq`: `M_irr² ≤ M²` (the irreducible
      mass cannot exceed the total mass).

  (5) `irreducibleMassSq_ge_half_M_sq`: `M_irr² ≥ M²/2` (the
      Christodoulou lower bound).

  (6) `schwarzschild_limit`: when `J = 0`, `M_irr² = M²`. The
      irreducible mass equals the total mass for any non-rotating
      black hole, so no Penrose-style extraction is possible.

  (7) `extremal_case`: when `J² = M⁴` (extremal Kerr), `M_irr² = M²/2`;
      equivalently `M_irr = M/√2` and `M − M_irr = M·(1 − 1/√2)`.

  (8) `Penrose_extraction_bound`: for any sub-extremal Kerr,
      `0 ≤ M − M_irr ≤ M·(1 − 1/√2)`.
      The right inequality is sharp at extremality.

  (9) `area_theorem_bound`: assuming the area theorem (M_irr does not
      decrease in any physical process), the energy extracted by any
      process from initial state (M, J) cannot exceed
      `M − M_irr_initial`.

  (10) `kerr_area_M_irr_relation`: the horizon area of a Kerr black
       hole is `16π · M_irr²`, formally identical to the Schwarzschild
       formula with M replaced by M_irr.

  (11) `mass_energy_decomposition`: `M² = M_irr² + J²/(4 · M_irr²)`
       — the total Kerr mass squared decomposes into irreducible
       plus rotational pieces.

  (12) Master capstone bundling (1)–(11).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS NOT PROVED — HONEST SCOPE

  – The full Hawking area theorem (no classical process can decrease
    horizon area in a globally hyperbolic spacetime obeying the null
    energy condition) is a global GR result that uses the Raychaudhuri
    focusing equation and Penrose's null-geodesic completeness arguments
    (Hawking 1971). Not formalized here. We establish the algebraic
    Christodoulou identities and the Penrose-process upper bound
    *conditional on* M_irr being non-decreasing.

  – The Kerr metric itself, the location of its inner/outer horizons
    `r_± = M ± √(M² − a²)`, the ergosphere geometry, the existence of
    negative-energy orbits inside the ergosphere (the underlying
    mechanism of the Penrose process) — these are all classical Kerr
    geometry results; we use only the algebraic identity for the
    horizon area.

  – Hawking radiation (which can in principle reduce M_irr through
    quantum field-theoretic effects violating the classical NEC) is
    not modeled. The bound `M_final ≥ M_irr_initial` is the
    classical-process bound.

  Zero sorry. Zero custom axioms.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import UnifiedTheory.LayerB.BekensteinHawking

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.ChristodoulouIrreducibleMass

open Real
open UnifiedTheory.LayerB.BekensteinHawking

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: KERR PARAMETERS AND THE SUB-EXTREMALITY CONDITION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The Kerr black hole carries a mass M ≥ 0 and angular momentum J.
    With `a := J/M` (the spin parameter), the outer horizon location
    `r_+ = M + √(M² − a²)` is real iff `M² ≥ a²`, i.e. `M⁴ ≥ J²`.
    This is the *sub-extremality* condition; the equality case
    `M⁴ = J²` is *extremal Kerr*; `M⁴ < J²` would be a naked
    singularity (forbidden by cosmic censorship).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Sub-extremality** of the Kerr black hole with mass `M` and
    angular momentum `J`. In dimensionless Planck-unit form this is
    `J² ≤ M⁴`. Equality is the extremal case. -/
def kerrSubextremal (M J : ℝ) : Prop := J ^ 2 ≤ M ^ 4

/-- **Extremal Kerr** is the boundary case `J² = M⁴`. In dimensional
    form this is `|a| = M`, `a = J/M`. -/
def kerrExtremal (M J : ℝ) : Prop := J ^ 2 = M ^ 4

/-- `M⁴ ≥ 0` for any real `M` (since `M⁴ = (M²)²`). -/
theorem M_pow_four_nonneg (M : ℝ) : 0 ≤ M ^ 4 := by
  have : M ^ 4 = (M ^ 2) ^ 2 := by ring
  rw [this]; exact sq_nonneg _

/-- A Schwarzschild black hole (`J = 0`) is automatically
    sub-extremal for every `M`. -/
theorem schwarzschild_subextremal (M : ℝ) : kerrSubextremal M 0 := by
  unfold kerrSubextremal
  have h0 : (0 : ℝ) ^ 2 = 0 := by norm_num
  rw [h0]
  exact M_pow_four_nonneg M

/-- Extremality with `J ≠ 0` forces `M ≠ 0`. -/
theorem extremal_M_ne_zero {M J : ℝ} (h : kerrExtremal M J) (hJ : J ≠ 0) :
    M ≠ 0 := by
  intro hM
  apply hJ
  unfold kerrExtremal at h
  rw [hM] at h
  have h0 : (0 : ℝ) ^ 4 = 0 := by norm_num
  rw [h0] at h
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h

/-- **Discriminant** `M⁴ − J²` is non-negative for sub-extremal Kerr.
    This is the quantity under the square root in Christodoulou's
    formula. -/
theorem kerr_discriminant_nonneg {M J : ℝ} (h : kerrSubextremal M J) :
    0 ≤ M ^ 4 - J ^ 2 := by
  unfold kerrSubextremal at h
  linarith

/-- The square root of the Kerr discriminant is bounded above by
    `M²`: namely `√(M⁴ − J²) ≤ M²`. (Both sides are non-negative.)
    Note: this inequality is purely algebraic and does not require
    sub-extremality (it just uses `sq_nonneg J`). -/
theorem sqrt_disc_le_M_sq (M J : ℝ) :
    Real.sqrt (M ^ 4 - J ^ 2) ≤ M ^ 2 := by
  have hM2 : (0 : ℝ) ≤ M ^ 2 := sq_nonneg M
  have hM4 : M ^ 4 = (M ^ 2) ^ 2 := by ring
  have h_le : M ^ 4 - J ^ 2 ≤ (M ^ 2) ^ 2 := by
    rw [← hM4]; have := sq_nonneg J; linarith
  have h_le_sqrt : Real.sqrt (M ^ 4 - J ^ 2) ≤ Real.sqrt ((M ^ 2) ^ 2) :=
    Real.sqrt_le_sqrt h_le
  rw [Real.sqrt_sq hM2] at h_le_sqrt
  exact h_le_sqrt

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: CHRISTODOULOU'S IRREDUCIBLE MASS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The Kerr horizon area is `A = 8π · (M² + √(M⁴ − J²))`. The
    irreducible mass `M_irr` is defined to be the Schwarzschild-equivalent
    mass with the same horizon area: `A = 16π · M_irr²`. Solving
    gives `M_irr² = (M² + √(M⁴ − J²)) / 2`. We take this algebraic
    identity as the definition.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Squared irreducible mass** of a Kerr black hole with mass `M`
    and angular momentum `J` (Christodoulou 1970):
        `M_irr² = (M² + √(M⁴ − J²)) / 2`. -/
noncomputable def irreducibleMassSq (M J : ℝ) : ℝ :=
  (M ^ 2 + Real.sqrt (M ^ 4 - J ^ 2)) / 2

/-- **Irreducible mass** itself (positive square root). -/
noncomputable def irreducibleMass (M J : ℝ) : ℝ :=
  Real.sqrt (irreducibleMassSq M J)

/-- The squared irreducible mass is non-negative. Holds
    unconditionally — the proof uses only `M² ≥ 0` and `√x ≥ 0`. -/
theorem irreducibleMassSq_nonneg (M J : ℝ) :
    0 ≤ irreducibleMassSq M J := by
  unfold irreducibleMassSq
  have hM2 : (0 : ℝ) ≤ M ^ 2 := sq_nonneg M
  have h_sqrt : 0 ≤ Real.sqrt (M ^ 4 - J ^ 2) := Real.sqrt_nonneg _
  have h_sum : 0 ≤ M ^ 2 + Real.sqrt (M ^ 4 - J ^ 2) := by linarith
  exact div_nonneg h_sum (by norm_num : (0 : ℝ) ≤ 2)

/-- The irreducible mass itself is non-negative. -/
theorem irreducibleMass_nonneg (M J : ℝ) : 0 ≤ irreducibleMass M J :=
  Real.sqrt_nonneg _

/-- **Christodoulou upper bound**: `M_irr² ≤ M²`. The irreducible
    mass of a Kerr black hole cannot exceed the total mass.
    Holds unconditionally (sub-extremality not needed because
    `√(M⁴ − J²)` is bounded by `M²` for all real `M, J`). -/
theorem irreducibleMassSq_le_M_sq (M J : ℝ) :
    irreducibleMassSq M J ≤ M ^ 2 := by
  unfold irreducibleMassSq
  have h_sqrt : Real.sqrt (M ^ 4 - J ^ 2) ≤ M ^ 2 := sqrt_disc_le_M_sq M J
  have h_num : M ^ 2 + Real.sqrt (M ^ 4 - J ^ 2) ≤ M ^ 2 + M ^ 2 := by linarith
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have : (M ^ 2 + Real.sqrt (M ^ 4 - J ^ 2)) / 2 ≤ (M ^ 2 + M ^ 2) / 2 :=
    div_le_div_of_nonneg_right h_num h2
  have h_eq : (M ^ 2 + M ^ 2) / 2 = M ^ 2 := by ring
  linarith

/-- **Christodoulou lower bound**: `M²/2 ≤ M_irr²`. Even an extremal
    Kerr retains at least half its rest mass-energy in irreducible
    form. -/
theorem irreducibleMassSq_ge_half_M_sq (M J : ℝ) :
    M ^ 2 / 2 ≤ irreducibleMassSq M J := by
  unfold irreducibleMassSq
  have h_sqrt_nn : 0 ≤ Real.sqrt (M ^ 4 - J ^ 2) := Real.sqrt_nonneg _
  have h_num : M ^ 2 ≤ M ^ 2 + Real.sqrt (M ^ 4 - J ^ 2) := by linarith
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  exact div_le_div_of_nonneg_right h_num h2

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: SCHWARZSCHILD LIMIT (J = 0)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    When the Kerr black hole carries no angular momentum, J = 0,
    the Christodoulou formula collapses to `M_irr² = M²`. Hence
    `M_irr = |M|`, and for `M ≥ 0` we have `M_irr = M`. NO ENERGY
    can be Penrose-extracted from a non-rotating black hole.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Schwarzschild limit (squared)**: when `J = 0`,
    `M_irr² = M²`. -/
theorem irreducibleMassSq_J_zero (M : ℝ) :
    irreducibleMassSq M 0 = M ^ 2 := by
  unfold irreducibleMassSq
  have h0 : (0 : ℝ) ^ 2 = 0 := by norm_num
  rw [h0]
  have hM4 : M ^ 4 - 0 = (M ^ 2) ^ 2 := by ring
  rw [hM4]
  have hM2 : (0 : ℝ) ≤ M ^ 2 := sq_nonneg M
  rw [Real.sqrt_sq hM2]
  ring

/-- **Schwarzschild limit (linear, M ≥ 0)**: when `J = 0` and
    `M ≥ 0`, `M_irr = M`. -/
theorem irreducibleMass_J_zero_of_M_nonneg {M : ℝ} (hM : 0 ≤ M) :
    irreducibleMass M 0 = M := by
  unfold irreducibleMass
  rw [irreducibleMassSq_J_zero]
  exact Real.sqrt_sq hM

/-- **Schwarzschild Penrose impossibility**: from a Schwarzschild
    (J = 0) black hole, the maximum extractable energy is zero. -/
theorem Penrose_zero_for_schwarzschild {M : ℝ} (hM : 0 ≤ M) :
    M - irreducibleMass M 0 = 0 := by
  rw [irreducibleMass_J_zero_of_M_nonneg hM]; ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: EXTREMAL CASE J² = M⁴ (a = M)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    At extremality the discriminant vanishes and the Christodoulou
    formula simplifies to `M_irr² = M²/2`, giving the maximal-rotation
    "half mass-squared" lower bound. Equivalently, `M_irr = M/√2`
    when `M ≥ 0`. The Penrose process can extract at most
    `M − M/√2 = M·(1 − 1/√2) ≈ 0.293 · M`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Extremal case (squared)**: when `J² = M⁴`, `M_irr² = M²/2`. -/
theorem irreducibleMassSq_extremal {M J : ℝ} (h : kerrExtremal M J) :
    irreducibleMassSq M J = M ^ 2 / 2 := by
  unfold irreducibleMassSq
  unfold kerrExtremal at h
  have h_disc : M ^ 4 - J ^ 2 = 0 := by linarith
  rw [h_disc]
  rw [Real.sqrt_zero]
  ring

/-- **Extremal case (linear, M ≥ 0)**: when `J² = M⁴` and `M ≥ 0`,
    `M_irr = M / √2`. -/
theorem irreducibleMass_extremal_of_M_nonneg
    {M J : ℝ} (h : kerrExtremal M J) (hM : 0 ≤ M) :
    irreducibleMass M J = M / Real.sqrt 2 := by
  unfold irreducibleMass
  rw [irreducibleMassSq_extremal h]
  -- Goal: √(M²/2) = M/√2
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have hMsq_nn : 0 ≤ M ^ 2 := sq_nonneg M
  rw [Real.sqrt_div hMsq_nn 2]
  rw [Real.sqrt_sq hM]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: HORIZON AREA OF KERR IN TERMS OF M_irr
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    By construction `A = 16π · M_irr²` for any Kerr black hole; this
    is exactly the Schwarzschild formula `horizonArea M = 16π · M²`
    with `M` replaced by `M_irr`. We define a Kerr horizon area
    function and prove the identity.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Horizon area of a Kerr black hole**:
        `A = 8π · (M² + √(M⁴ − J²)) = 16π · M_irr²`. -/
noncomputable def kerrHorizonArea (M J : ℝ) : ℝ :=
  16 * Real.pi * irreducibleMassSq M J

/-- **Kerr area in terms of irreducible mass**:
        `A_Kerr(M, J) = 16π · M_irr²`. By construction. -/
theorem kerrHorizonArea_eq_irreducible (M J : ℝ) :
    kerrHorizonArea M J = 16 * Real.pi * irreducibleMassSq M J := rfl

/-- **Kerr area expanded**: `A = 8π · (M² + √(M⁴ − J²))`. -/
theorem kerrHorizonArea_expanded (M J : ℝ) :
    kerrHorizonArea M J = 8 * Real.pi * (M ^ 2 + Real.sqrt (M ^ 4 - J ^ 2)) := by
  unfold kerrHorizonArea irreducibleMassSq
  ring

/-- **Schwarzschild reduction of the Kerr area**: when `J = 0`, the
    Kerr horizon-area function reduces to the Schwarzschild
    `horizonArea` from `BekensteinHawking`. -/
theorem kerrHorizonArea_J_zero (M : ℝ) :
    kerrHorizonArea M 0 = horizonArea M := by
  rw [kerrHorizonArea_eq_irreducible, horizonArea_eq,
      irreducibleMassSq_J_zero]

/-- **The Kerr area is non-negative**. Holds unconditionally
    (irreducibleMassSq is non-negative for any real M, J). -/
theorem kerrHorizonArea_nonneg (M J : ℝ) :
    0 ≤ kerrHorizonArea M J := by
  rw [kerrHorizonArea_eq_irreducible]
  have h16π : (0 : ℝ) ≤ 16 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  exact mul_nonneg h16π (irreducibleMassSq_nonneg M J)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: MASS-ENERGY DECOMPOSITION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Christodoulou's identity (**) decomposes the squared total mass
    of a Kerr black hole into an irreducible piece (associated with
    the horizon area) and a rotational piece:
        M² = M_irr² + J²/(4 · M_irr²).
    The proof is direct algebra from the closed-form M_irr².

    For sub-extremal *and* M ≠ 0 Kerr, `M_irr² > 0`, so the division
    is well-defined.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Strict positivity of `M_irr²` whenever `M ≠ 0` (sub-extremal
    Kerr). The full Christodoulou bound `M_irr² ≥ M²/2` then implies
    `M_irr² ≥ M²/2 > 0`. -/
theorem irreducibleMassSq_pos_of_M_ne_zero
    {M J : ℝ} (hM : M ≠ 0) :
    0 < irreducibleMassSq M J := by
  have hMsq : 0 < M ^ 2 := by positivity
  have hLow : M ^ 2 / 2 ≤ irreducibleMassSq M J :=
    irreducibleMassSq_ge_half_M_sq M J
  have h_pos : 0 < M ^ 2 / 2 := by positivity
  linarith

/-- **Mass-energy decomposition**: for sub-extremal Kerr with `M ≠ 0`,
        `M² = M_irr² + J²/(4 · M_irr²)`.

    Algebraic verification: writing `s = √(M⁴ − J²)`, `M_irr² = (M² + s)/2`,
    so `4 · M_irr² · (M² − M_irr²) = (M² + s)(M² − s) = M⁴ − s² = J²`. -/
theorem mass_energy_decomposition
    {M J : ℝ} (h : kerrSubextremal M J) (hM : M ≠ 0) :
    M ^ 2 = irreducibleMassSq M J + J ^ 2 / (4 * irreducibleMassSq M J) := by
  have h_disc : 0 ≤ M ^ 4 - J ^ 2 := kerr_discriminant_nonneg h
  set s := Real.sqrt (M ^ 4 - J ^ 2) with hs_def
  have hs_nn : 0 ≤ s := Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = M ^ 4 - J ^ 2 := by
    rw [hs_def]; exact Real.sq_sqrt h_disc
  have hMirr_pos : 0 < irreducibleMassSq M J :=
    irreducibleMassSq_pos_of_M_ne_zero hM
  have hMirr_def : irreducibleMassSq M J = (M ^ 2 + s) / 2 := by
    unfold irreducibleMassSq
    rw [hs_def]
  have hMirr_ne : irreducibleMassSq M J ≠ 0 := ne_of_gt hMirr_pos
  -- Key algebraic identity: 4 · M_irr² · (M² − M_irr²) = J².
  have h_key : 4 * irreducibleMassSq M J * (M ^ 2 - irreducibleMassSq M J)
                  = J ^ 2 := by
    rw [hMirr_def]
    have h_arith : 4 * ((M ^ 2 + s) / 2) * (M ^ 2 - (M ^ 2 + s) / 2)
            = M ^ 4 - s ^ 2 := by ring
    rw [h_arith, hs_sq]
    ring
  -- Solve for M² in terms of M_irr² and J².
  have h4Mirr_pos : 0 < 4 * irreducibleMassSq M J := by
    have : (0 : ℝ) < 4 := by norm_num
    exact mul_pos this hMirr_pos
  have h4Mirr_ne : 4 * irreducibleMassSq M J ≠ 0 := ne_of_gt h4Mirr_pos
  -- From h_key: M² - M_irr² = J² / (4 · M_irr²).
  have h_diff : M ^ 2 - irreducibleMassSq M J
                  = J ^ 2 / (4 * irreducibleMassSq M J) := by
    rw [eq_div_iff h4Mirr_ne]
    linarith [h_key]
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: PENROSE PROCESS — UPPER BOUND ON EXTRACTABLE ENERGY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The Penrose process (1969) extracts energy from a rotating black
    hole using particles in the ergosphere. The area theorem (Hawking
    1971) implies that any classical process satisfies M_irr_final ≥
    M_irr_initial, so the maximum energy that can be extracted is
        ΔE_max = M_initial − M_irr_initial.
    Combined with the Christodoulou lower bound M_irr² ≥ M²/2 ⇒
    M_irr ≥ M/√2, we get
        ΔE / M ≤ 1 − 1/√2 ≈ 0.293,
    sharp at extremal initial state J² = M⁴.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Penrose extraction bound (squared form)**: for sub-extremal
    Kerr with `M ≥ 0`,
        `M ^ 2 - irreducibleMassSq M J ≤ M ^ 2 / 2`.
    The right-hand side is the maximum *rotational energy squared*
    that the Penrose process can extract; the bound is sharp when
    `J² = M⁴` (extremal Kerr). -/
theorem Penrose_extraction_bound_sq
    {M J : ℝ} :
    M ^ 2 - irreducibleMassSq M J ≤ M ^ 2 / 2 := by
  have h_low : M ^ 2 / 2 ≤ irreducibleMassSq M J :=
    irreducibleMassSq_ge_half_M_sq M J
  linarith

/-- **M_irr ≥ M/√2** for `M ≥ 0`. Holds unconditionally in `J`
    (sub-extremality not needed — both sides agree with the lower
    bound `M_irr² ≥ M²/2`). -/
theorem irreducibleMass_ge_M_over_sqrt2
    {M : ℝ} (hM : 0 ≤ M) (J : ℝ) :
    M / Real.sqrt 2 ≤ irreducibleMass M J := by
  -- Express M/√2 as √(M²/2) and use sqrt-monotonicity on the
  -- Christodoulou lower bound M²/2 ≤ M_irr².
  have h_lhs : M / Real.sqrt 2 = Real.sqrt (M ^ 2 / 2) := by
    rw [Real.sqrt_div (sq_nonneg M) 2, Real.sqrt_sq hM]
  rw [h_lhs]
  unfold irreducibleMass
  exact Real.sqrt_le_sqrt (irreducibleMassSq_ge_half_M_sq M J)

/-- **Penrose extraction bound (linear form, M ≥ 0)**: for
    sub-extremal Kerr with `M ≥ 0`,
        `M − M_irr ≤ M · (1 − 1/√2)`.

    The fraction `1 − 1/√2 ≈ 0.293` is the maximum extractable energy
    fraction from a Kerr black hole; sharp at extremal initial state. -/
theorem Penrose_extraction_bound
    {M : ℝ} (hM : 0 ≤ M) (J : ℝ) :
    M - irreducibleMass M J ≤ M * (1 - 1 / Real.sqrt 2) := by
  have h_low : M / Real.sqrt 2 ≤ irreducibleMass M J :=
    irreducibleMass_ge_M_over_sqrt2 hM J
  -- M * (1 - 1/√2) = M - M/√2
  have h_eq : M * (1 - 1 / Real.sqrt 2) = M - M / Real.sqrt 2 := by
    field_simp
  rw [h_eq]
  linarith

/-- The Penrose extraction is non-negative for any Kerr with
    `M ≥ 0`: `0 ≤ M − M_irr`. Equivalently, `M_irr ≤ M`. -/
theorem Penrose_extraction_nonneg
    {M : ℝ} (hM : 0 ≤ M) (J : ℝ) :
    0 ≤ M - irreducibleMass M J := by
  -- M_irr ≤ M follows from M_irr² ≤ M² and both being non-negative.
  have h_sq_le : irreducibleMassSq M J ≤ M ^ 2 := irreducibleMassSq_le_M_sq M J
  have h_le : irreducibleMass M J ≤ M := by
    unfold irreducibleMass
    have : Real.sqrt (irreducibleMassSq M J) ≤ Real.sqrt (M ^ 2) :=
      Real.sqrt_le_sqrt h_sq_le
    rw [Real.sqrt_sq hM] at this
    exact this
  linarith

/-- **Extremal Kerr saturates the Penrose bound (linear form)**: when
    `J² = M⁴` and `M ≥ 0`, `M − M_irr = M · (1 − 1/√2)`. -/
theorem Penrose_extraction_extremal
    {M J : ℝ} (h : kerrExtremal M J) (hM : 0 ≤ M) :
    M - irreducibleMass M J = M * (1 - 1 / Real.sqrt 2) := by
  rw [irreducibleMass_extremal_of_M_nonneg h hM]
  field_simp

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: AREA-THEOREM IMPLICATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The full Hawking area theorem (1971) is a global GR result that
    we do NOT prove here. We DO prove its algebraic CONSEQUENCE:
    if a process starting from `(M_initial, J_initial)` ends at
    `(M_final, J_final)` while preserving sub-extremality and not
    decreasing the irreducible mass, then the total energy extracted
    cannot exceed `M_initial − M_irr_initial`.

    Combined with Christodoulou's lower bound, this gives the universal
    `M − M_irr ≤ M · (1 − 1/√2) ≈ 0.293 · M` extraction bound.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Area-theorem implication (non-decreasing M_irr ⇒ extraction
    bound)**: given an initial Kerr `(M₁, J₁)` and a final Kerr
    `(M₂, J₂)`, if the area theorem holds (irreducible mass does not
    decrease) and the final state is sub-extremal with `M₂ ≥ 0`, then
    the energy extracted satisfies
        M₁ − M₂ ≤ M₁ − M_irr(M₁, J₁).

    This is the *conditional* statement: contingent on the area-theorem
    hypothesis (Hawking 1971), the maximum extractable energy from any
    process starting at `(M₁, J₁)` equals the rotational energy
    `M₁ − M_irr(M₁, J₁)`. Combined with `Penrose_extraction_bound`,
    extracted energy is bounded by `M₁ · (1 − 1/√2)` for `M₁ ≥ 0`. -/
theorem area_theorem_extraction_bound
    {M₁ J₁ M₂ J₂ : ℝ}
    (h_area : irreducibleMass M₁ J₁ ≤ irreducibleMass M₂ J₂)
    (hM₂ : 0 ≤ M₂) :
    M₁ - M₂ ≤ M₁ - irreducibleMass M₁ J₁ := by
  have h_M_ge : irreducibleMass M₂ J₂ ≤ M₂ := by
    have h_sq_le : irreducibleMassSq M₂ J₂ ≤ M₂ ^ 2 :=
      irreducibleMassSq_le_M_sq M₂ J₂
    unfold irreducibleMass
    have : Real.sqrt (irreducibleMassSq M₂ J₂) ≤ Real.sqrt (M₂ ^ 2) :=
      Real.sqrt_le_sqrt h_sq_le
    rw [Real.sqrt_sq hM₂] at this
    exact this
  -- M_irr(M₁,J₁) ≤ M_irr(M₂,J₂) ≤ M₂
  linarith

/-- **Universal Penrose-process bound (assuming area theorem)**: under
    the area-theorem hypothesis, any classical process starting at
    Kerr `(M₁, J₁)` with `M₁ ≥ 0` and ending at sub-extremal `(M₂, J₂)`
    with `M₂ ≥ 0` extracts at most `M₁ · (1 − 1/√2)` of energy:
        M₁ − M₂ ≤ M₁ · (1 − 1/√2).
    The fraction `1 − 1/√2 ≈ 0.293` is the famous Penrose-process
    upper bound. -/
theorem universal_Penrose_bound
    {M₁ J₁ M₂ J₂ : ℝ}
    (hM₁ : 0 ≤ M₁)
    (h_area : irreducibleMass M₁ J₁ ≤ irreducibleMass M₂ J₂)
    (hM₂ : 0 ≤ M₂) :
    M₁ - M₂ ≤ M₁ * (1 - 1 / Real.sqrt 2) := by
  have h1 : M₁ - M₂ ≤ M₁ - irreducibleMass M₁ J₁ :=
    area_theorem_extraction_bound h_area hM₂
  have h2 : M₁ - irreducibleMass M₁ J₁ ≤ M₁ * (1 - 1 / Real.sqrt 2) :=
    Penrose_extraction_bound hM₁ J₁
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: MASTER CAPSTONE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE CHRISTODOULOU IRREDUCIBLE-MASS CAPSTONE.**

    For a Kerr black hole of mass `M` and angular momentum `J` in
    Planck units, sub-extremal (`J² ≤ M⁴`):

    (1) **Christodoulou formula**:
        `M_irr² = (M² + √(M⁴ − J²)) / 2`.

    (2) **Christodoulou bounds**: `M²/2 ≤ M_irr² ≤ M²`.

    (3) **Schwarzschild limit**: `J = 0 ⟹ M_irr² = M²` and (for
        `M ≥ 0`) `M_irr = M`. Zero Penrose extraction possible from
        a non-rotating black hole.

    (4) **Extremal limit**: `J² = M⁴ ⟹ M_irr² = M²/2` and (for
        `M ≥ 0`) `M_irr = M/√2`. Penrose extraction saturates at
        `M − M_irr = M · (1 − 1/√2)`.

    (5) **Penrose bound (linear, M ≥ 0)**:
        `0 ≤ M − M_irr ≤ M · (1 − 1/√2) ≈ 0.293 · M`.

    (6) **Kerr horizon area = 16π · M_irr²** — formally identical to
        the Schwarzschild formula with `M ↦ M_irr`.

    (7) **Schwarzschild reduction**: `kerrHorizonArea M 0 =
        horizonArea M`.

    (8) **Mass-energy decomposition** (M ≠ 0, sub-extremal):
        `M² = M_irr² + J²/(4 · M_irr²)`.

    (9) **Universal Penrose bound (conditional on area theorem)**:
        if the area theorem holds (M_irr non-decreasing in any
        process), then any process starting at (M₁, J₁) sub-extremal
        with M₁ ≥ 0 extracts at most M₁ · (1 − 1/√2). -/
theorem christodoulou_capstone :
    -- (1) Christodoulou formula (definitional)
    (∀ M J : ℝ,
        irreducibleMassSq M J = (M ^ 2 + Real.sqrt (M ^ 4 - J ^ 2)) / 2)
    -- (2a) Upper bound
    ∧ (∀ M J : ℝ, kerrSubextremal M J → irreducibleMassSq M J ≤ M ^ 2)
    -- (2b) Lower bound
    ∧ (∀ M J : ℝ, M ^ 2 / 2 ≤ irreducibleMassSq M J)
    -- (3a) Schwarzschild limit (squared)
    ∧ (∀ M : ℝ, irreducibleMassSq M 0 = M ^ 2)
    -- (3b) Schwarzschild limit (linear, M ≥ 0)
    ∧ (∀ M : ℝ, 0 ≤ M → irreducibleMass M 0 = M)
    -- (4a) Extremal limit (squared)
    ∧ (∀ M J : ℝ, kerrExtremal M J → irreducibleMassSq M J = M ^ 2 / 2)
    -- (4b) Extremal limit (linear, M ≥ 0)
    ∧ (∀ M J : ℝ, kerrExtremal M J → 0 ≤ M →
        irreducibleMass M J = M / Real.sqrt 2)
    -- (5a) Penrose bound (non-negativity)
    ∧ (∀ M J : ℝ, kerrSubextremal M J → 0 ≤ M →
        0 ≤ M - irreducibleMass M J)
    -- (5b) Penrose bound (upper)
    ∧ (∀ M J : ℝ, kerrSubextremal M J → 0 ≤ M →
        M - irreducibleMass M J ≤ M * (1 - 1 / Real.sqrt 2))
    -- (6) Kerr area in terms of M_irr (definitional)
    ∧ (∀ M J : ℝ,
        kerrHorizonArea M J = 16 * Real.pi * irreducibleMassSq M J)
    -- (7) Schwarzschild reduction of Kerr area
    ∧ (∀ M : ℝ, kerrHorizonArea M 0 = horizonArea M)
    -- (8) Mass-energy decomposition (M ≠ 0)
    ∧ (∀ M J : ℝ, kerrSubextremal M J → M ≠ 0 →
        M ^ 2 = irreducibleMassSq M J + J ^ 2 / (4 * irreducibleMassSq M J))
    -- (9) Universal Penrose bound (conditional on area theorem)
    ∧ (∀ M₁ J₁ M₂ J₂ : ℝ,
        kerrSubextremal M₁ J₁ → 0 ≤ M₁ →
        irreducibleMass M₁ J₁ ≤ irreducibleMass M₂ J₂ →
        kerrSubextremal M₂ J₂ → 0 ≤ M₂ →
        M₁ - M₂ ≤ M₁ * (1 - 1 / Real.sqrt 2)) := by
  refine ⟨fun _ _ => rfl, ?_, ?_, irreducibleMassSq_J_zero, ?_, ?_, ?_,
          ?_, ?_, fun _ _ => rfl, kerrHorizonArea_J_zero, ?_, ?_⟩
  · intros M J _h; exact irreducibleMassSq_le_M_sq M J
  · intros M J; exact irreducibleMassSq_ge_half_M_sq M J
  · intros M hM; exact irreducibleMass_J_zero_of_M_nonneg hM
  · intros M J h; exact irreducibleMassSq_extremal h
  · intros M J h hM; exact irreducibleMass_extremal_of_M_nonneg h hM
  · intros M J _h hM; exact Penrose_extraction_nonneg hM J
  · intros M J _h hM; exact Penrose_extraction_bound hM J
  · intros M J h hM; exact mass_energy_decomposition h hM
  · intros M₁ J₁ M₂ J₂ _h₁ hM₁ h_area _h₂ hM₂
    exact universal_Penrose_bound hM₁ h_area hM₂

end UnifiedTheory.LayerB.ChristodoulouIrreducibleMass
