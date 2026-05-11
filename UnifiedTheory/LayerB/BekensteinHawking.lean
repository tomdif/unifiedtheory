/-
  LayerB/BekensteinHawking.lean — The Bekenstein-Hawking entropy S = A/4

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT

  `LayerA/CosmologicalConstantN.lean` already discusses the
  Bekenstein-Hawking horizon area count A_dS / 4 ~ 10^{122} bits as one
  of three independent estimates of the cosmic substrate count N. The
  COEFFICIENT 1/4 entered there as an external numerical input.

  This file extracts the *algebraic content* of the Bekenstein-Hawking
  entropy law for a Schwarzschild black hole and proves the basic
  consequences: the formula S_BH = π·r_s² = 4π·M² (in natural Planck
  units M_P = ℏ = c = G = 1), monotonicity in mass M (a stripped-down
  version of the second law), and the area-vs-volume scaling that
  feeds the holographic comparison in `LayerA.CosmologicalConstantN`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED

  (1) `schwarzschildRadius M = 2 M` (natural units, c = G = 1).

  (2) `horizonArea M = 4π · r_s² = 16π · M²`.

  (3) `bekensteinHawkingEntropy M = horizonArea M / 4 = 4π · M²`.

  (4) The entropy is positive when M > 0 and monotonically increasing
      in M. This is the algebraic shadow of the second law of black
      hole mechanics (Hawking's area theorem) — one cannot reduce the
      area of a Schwarzschild black hole by adding more mass.

  (5) `S_BH(M) = π · r_s²` — entropy scales as horizon area, NOT as
      bulk volume. This is the holographic principle in its sharpest
      Schwarzschild form: every bit of black hole information lives on
      the 2-sphere boundary at r = r_s, not in the 3-ball interior.
      In Planck units, S_BH equals one bit per (Planck length)² · 1/4.

  (6) Connection to the Sorkin-counting framework: at the de Sitter
      horizon scale r ~ 1/√Λ, the BH entropy formula gives
      S_BH ~ (1/Λ) / 4, which is the holographic (NOT bulk-volume)
      estimate of N already analyzed in
      `LayerA.CosmologicalConstantN.BHArea`. The framework's bulk
      Sorkin count is N = 1/Λ², which is the SQUARE of S_BH.

  (7) Master capstone bundling (1)–(6) into one theorem.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS NOT PROVED — HONEST SCOPE

  – The numerical coefficient 1/4 is NOT derived from first principles
    in this file. It is the standard Bekenstein-Hawking convention
    fixed by Hawking's 1974/1975 quantum field theory in curved
    spacetime calculation (more precisely, by matching the temperature
    T_H = κ/(2π) extracted from the surface gravity κ = 1/(4M) to
    the first law dM = T dS, which forces dS = 8π M dM and hence
    S = 4π M² = A/4). The standard derivations are either:

      (a) Hawking's original 1974/1975 calculation of the thermal
          spectrum of a collapsing star (Bogoliubov coefficients of
          modes propagated through the collapse geometry), which fixes
          T_H = 1/(8π M), then integration of the first law fixes
          the entropy normalization.

      (b) The Gibbons-Hawking 1977 Euclidean path integral with the
          Gibbons-Hawking-York boundary term: the on-shell Euclidean
          action of the Schwarzschild geometry equals β · M − S_BH,
          and matching to thermodynamics gives S_BH = A/4.

    Both routes go through quantum field theory in a curved background
    and lie OUTSIDE the present Lean development. We take the
    coefficient 1/4 as a definitional input (an algebraic CONVENTION,
    not a custom Lean axiom) and prove what follows from it.

  – The interpretation of S_BH as the logarithm of a Hilbert-space
    dimension (the "microscopic" interpretation) is not derived. The
    framework's substrate-counting picture (bulk N causal elements)
    suggests this is a count of horizon crossings; that identification
    is structural commentary, not a theorem here.

  – The second law (`area_theorem`) is established only in its
    algebraic form: S_BH(M) is monotone in M. The full Hawking area
    theorem (no classical process can decrease total horizon area)
    requires the null energy condition and is proved in general
    relativity literature — not here.

  Zero sorry. Zero custom axioms.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import UnifiedTheory.LayerA.CosmologicalConstantN

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.BekensteinHawking

open Real
open UnifiedTheory.LayerA.CosmologicalConstantN

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: SCHWARZSCHILD GEOMETRY IN PLANCK UNITS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    In natural units c = ℏ = G = 1 (Planck units), the Schwarzschild
    radius of a black hole of mass M is r_s = 2M. The dimensionful
    formula r_s = 2GM/c² reduces to r_s = 2M in Planck units; the
    framework throughout uses Planck units (see e.g. the documentation
    of `LayerA.CosmologicalConstantN`).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Schwarzschild radius** in Planck units: `r_s = 2 M`.
    Standard formula `r_s = 2GM/c²` with G = c = 1. -/
def schwarzschildRadius (M : ℝ) : ℝ := 2 * M

/-- The Schwarzschild radius is positive whenever the mass is positive. -/
theorem schwarzschildRadius_pos (M : ℝ) (hM : 0 < M) :
    0 < schwarzschildRadius M := by
  unfold schwarzschildRadius
  linarith

/-- The Schwarzschild radius is strictly monotone in mass. -/
theorem schwarzschildRadius_mono {M₁ M₂ : ℝ} (h : M₁ ≤ M₂) :
    schwarzschildRadius M₁ ≤ schwarzschildRadius M₂ := by
  unfold schwarzschildRadius
  linarith

/-- The Schwarzschild radius vanishes iff the mass vanishes. -/
theorem schwarzschildRadius_eq_zero_iff (M : ℝ) :
    schwarzschildRadius M = 0 ↔ M = 0 := by
  unfold schwarzschildRadius
  constructor
  · intro h; linarith
  · intro h; linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: HORIZON AREA — A SCHWARZSCHILD HORIZON IS A 2-SPHERE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The event horizon of a Schwarzschild black hole is the round
    2-sphere of radius r_s. Its surface area is `A = 4π r_s²`, the
    standard area of a 2-sphere of radius r_s embedded in the
    spatial slice. (The induced metric on the horizon is round; this
    is a textbook differential-geometry computation.)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Horizon area** of a Schwarzschild black hole: `A = 4π · r_s²`.
    The horizon is the 2-sphere of radius `r_s = 2M`. -/
noncomputable def horizonArea (M : ℝ) : ℝ :=
  4 * Real.pi * (schwarzschildRadius M) ^ 2

/-- **Closed-form horizon area**: `A(M) = 16π · M²`. -/
theorem horizonArea_eq (M : ℝ) :
    horizonArea M = 16 * Real.pi * M ^ 2 := by
  unfold horizonArea schwarzschildRadius
  ring

/-- The horizon area is non-negative for every real M. -/
theorem horizonArea_nonneg (M : ℝ) : 0 ≤ horizonArea M := by
  rw [horizonArea_eq]
  have hπ : 0 ≤ Real.pi := Real.pi_pos.le
  have h16 : (0 : ℝ) ≤ 16 := by norm_num
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  have h16π : (0 : ℝ) ≤ 16 * Real.pi := mul_nonneg h16 hπ
  exact mul_nonneg h16π hM2

/-- The horizon area is strictly positive when the mass is nonzero. -/
theorem horizonArea_pos (M : ℝ) (hM : M ≠ 0) : 0 < horizonArea M := by
  rw [horizonArea_eq]
  have hπ : 0 < Real.pi := Real.pi_pos
  have h16 : (0 : ℝ) < 16 := by norm_num
  have hM2 : 0 < M ^ 2 := by positivity
  exact mul_pos (mul_pos h16 hπ) hM2

/-- The horizon area vanishes iff M = 0. -/
theorem horizonArea_eq_zero_iff (M : ℝ) :
    horizonArea M = 0 ↔ M = 0 := by
  rw [horizonArea_eq]
  constructor
  · intro h
    have hπne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have h16 : (16 : ℝ) ≠ 0 := by norm_num
    have hπ16 : (16 * Real.pi) ≠ 0 := mul_ne_zero h16 hπne
    have : M ^ 2 = 0 := by
      have := mul_left_cancel₀ hπ16 (by linarith : 16 * Real.pi * M ^ 2 = 16 * Real.pi * 0)
      linarith [this]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  · intro h
    rw [h]; ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: BEKENSTEIN-HAWKING ENTROPY S = A/4
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The coefficient 1/4 is the famous Bekenstein-Hawking constant. In
    Planck units (ℓ_P = 1) the formula reads simply S_BH = A/4. In
    full SI units it is S_BH = A · k_B · c³ / (4 ℏ G) — the four
    fundamental constants conspire to give a *dimensionless* entropy
    bit count when divided by k_B.

    The 1/4 itself is fixed by Hawking's 1974/1975 calculation (see
    file header for both standard derivation routes). The present file
    takes 1/4 as a definitional convention.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Bekenstein-Hawking entropy** of a Schwarzschild black hole in
    Planck units: `S_BH = A / 4`. The coefficient 1/4 is the standard
    Bekenstein-Hawking convention (Hawking 1974/1975). -/
noncomputable def bekensteinHawkingEntropy (M : ℝ) : ℝ :=
  horizonArea M / 4

/-- **Closed-form BH entropy**: `S_BH(M) = 4π · M²`. -/
theorem BH_entropy_eq (M : ℝ) :
    bekensteinHawkingEntropy M = 4 * Real.pi * M ^ 2 := by
  unfold bekensteinHawkingEntropy
  rw [horizonArea_eq]
  ring

/-- The BH entropy is non-negative for any real M. -/
theorem BH_entropy_nonneg (M : ℝ) : 0 ≤ bekensteinHawkingEntropy M := by
  rw [BH_entropy_eq]
  have hπ : 0 ≤ Real.pi := Real.pi_pos.le
  have h4 : (0 : ℝ) ≤ 4 := by norm_num
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  exact mul_nonneg (mul_nonneg h4 hπ) hM2

/-- The BH entropy is strictly positive when M ≠ 0. -/
theorem BH_entropy_pos (M : ℝ) (hM : M ≠ 0) :
    0 < bekensteinHawkingEntropy M := by
  rw [BH_entropy_eq]
  have hπ : 0 < Real.pi := Real.pi_pos
  have h4 : (0 : ℝ) < 4 := by norm_num
  have hM2 : 0 < M ^ 2 := by positivity
  exact mul_pos (mul_pos h4 hπ) hM2

/-- The BH entropy vanishes iff M = 0. -/
theorem BH_entropy_eq_zero_iff (M : ℝ) :
    bekensteinHawkingEntropy M = 0 ↔ M = 0 := by
  unfold bekensteinHawkingEntropy
  rw [div_eq_zero_iff]
  constructor
  · intro h
    rcases h with h | h
    · exact (horizonArea_eq_zero_iff M).mp h
    · exfalso; norm_num at h
  · intro h
    left; exact (horizonArea_eq_zero_iff M).mpr h

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: MONOTONICITY — ALGEBRAIC SHADOW OF THE SECOND LAW
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For non-negative M, the BH entropy is monotonically non-decreasing
    in M: dropping additional mass into a Schwarzschild black hole
    only increases its entropy. This is the simplest algebraic version
    of Hawking's area theorem; the FULL area theorem (no classical
    process can decrease total horizon area) requires the null energy
    condition and a global causal-structure argument from general
    relativity, which is not formalized here.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Monotonicity of horizon area in mass** (M ≥ 0).
    A is monotone non-decreasing in M for non-negative M. -/
theorem horizonArea_mono {M₁ M₂ : ℝ} (h₁ : 0 ≤ M₁) (h_le : M₁ ≤ M₂) :
    horizonArea M₁ ≤ horizonArea M₂ := by
  rw [horizonArea_eq, horizonArea_eq]
  have h₂ : 0 ≤ M₂ := le_trans h₁ h_le
  have h_sq : M₁ ^ 2 ≤ M₂ ^ 2 := by
    have := mul_self_le_mul_self h₁ h_le
    rw [show M₁ ^ 2 = M₁ * M₁ from sq M₁,
        show M₂ ^ 2 = M₂ * M₂ from sq M₂]
    exact this
  have h16π : (0 : ℝ) ≤ 16 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  exact mul_le_mul_of_nonneg_left h_sq h16π

/-- **Monotonicity of BH entropy in mass** (M ≥ 0). The algebraic
    shadow of the second law of black hole mechanics. -/
theorem BH_entropy_mono {M₁ M₂ : ℝ} (h₁ : 0 ≤ M₁) (h_le : M₁ ≤ M₂) :
    bekensteinHawkingEntropy M₁ ≤ bekensteinHawkingEntropy M₂ := by
  unfold bekensteinHawkingEntropy
  have hA : horizonArea M₁ ≤ horizonArea M₂ := horizonArea_mono h₁ h_le
  have h4 : (0 : ℝ) ≤ 4 := by norm_num
  exact div_le_div_of_nonneg_right hA h4

/-- **Strict monotonicity** of horizon area for strictly positive masses. -/
theorem horizonArea_strictMono {M₁ M₂ : ℝ} (h₁ : 0 < M₁) (h_lt : M₁ < M₂) :
    horizonArea M₁ < horizonArea M₂ := by
  rw [horizonArea_eq, horizonArea_eq]
  have h_sq : M₁ ^ 2 < M₂ ^ 2 := by nlinarith [h₁, h_lt]
  have h16π : (0 : ℝ) < 16 * Real.pi :=
    mul_pos (by norm_num) Real.pi_pos
  exact mul_lt_mul_of_pos_left h_sq h16π

/-- **Strict monotonicity** of BH entropy for strictly positive masses
    (sharp form of the second law for Schwarzschild black holes). -/
theorem BH_entropy_strictMono {M₁ M₂ : ℝ} (h₁ : 0 < M₁) (h_lt : M₁ < M₂) :
    bekensteinHawkingEntropy M₁ < bekensteinHawkingEntropy M₂ := by
  unfold bekensteinHawkingEntropy
  have hA : horizonArea M₁ < horizonArea M₂ := horizonArea_strictMono h₁ h_lt
  have h4 : (0 : ℝ) < 4 := by norm_num
  exact div_lt_div_of_pos_right hA h4

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: HOLOGRAPHIC SCALING — S_BH = π · r_s²
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Solved in terms of the Schwarzschild radius, the Bekenstein-Hawking
    entropy is `S_BH = π · r_s²` — the entropy scales as the area of
    the 2-sphere boundary, NOT as the volume of the 3-ball interior.
    This is the cleanest statement of the holographic principle for
    Schwarzschild black holes:

      • Bulk volume of interior: V ~ (4π/3) r_s³ ~ M³  (cubic in M)
      • Boundary area / entropy: S ~ A/4 ~ M²        (quadratic in M)

    The entropy is fixed by area, not volume — a black hole of radius
    r holds at most A/4 bits of information, NOT (4π/3) r³ bits as a
    naïve bulk count would suggest. This area-dominance is the seed
    of all subsequent holographic reasoning ('t Hooft, Susskind,
    AdS/CFT).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Holographic form of BH entropy**: `S_BH = π · r_s²`. The entropy
    is set by the AREA of the horizon (a 2-sphere), not by any bulk
    volume. Equivalently: `S_BH · 4 = horizonArea M`, so `S_BH` is
    exactly one bit per (Planck length)² · 1/4. -/
theorem BH_entropy_eq_pi_rs_squared (M : ℝ) :
    bekensteinHawkingEntropy M = Real.pi * (schwarzschildRadius M) ^ 2 := by
  rw [BH_entropy_eq]
  unfold schwarzschildRadius
  ring

/-- **`r_s² = (1/4) · horizon area`** in Planck units. This is the
    explicit area-counting relation: the squared horizon radius equals
    one quarter of the horizon area divided by π. -/
theorem rs_squared_eq_quarter_area_over_pi (M : ℝ) :
    (schwarzschildRadius M) ^ 2 = horizonArea M / (4 * Real.pi) := by
  rw [horizonArea]
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have h4 : (4 : ℝ) ≠ 0 := by norm_num
  have h4π : (4 * Real.pi) ≠ 0 := mul_ne_zero h4 hπ
  field_simp

/-- **The horizon area equals 4π times r_s²** — restated as a one-line
    theorem to emphasise the standard 2-sphere area formula. -/
theorem horizonArea_as_sphere (M : ℝ) :
    horizonArea M = 4 * Real.pi * (schwarzschildRadius M) ^ 2 := rfl

/-- **Sorkin-style horizon-area COUNT**: in Planck units, the BH
    entropy is the number of "Planck patches" on the horizon divided
    by 4. Algebraically:
      S_BH = horizonArea M / 4
    counted in dimensionless units (one bit per quarter-Planck-area).
    This is the Sorkin discrete-spacetime reading: a black hole of
    horizon area A consists of A Planck plaquettes, each carrying
    1/4 of a bit. -/
theorem BH_entropy_is_quarter_area (M : ℝ) :
    bekensteinHawkingEntropy M = horizonArea M / 4 := rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: CONNECTION TO THE COSMOLOGICAL-CONSTANT FRAMEWORK
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    `LayerA.CosmologicalConstantN.BHArea` defines the de Sitter
    horizon area as A_dS = 1/Λ in Planck units. The "Bekenstein-Hawking
    bit count" extracted there is `A_dS / 4`. Specialising the BH
    entropy formula to a Schwarzschild black hole whose horizon area
    matches the de Sitter horizon (A = 1/Λ) recovers the same count.

    More concretely: if a Schwarzschild black hole has horizon area
    `A`, then its BH entropy is `A/4`, regardless of the geometry that
    produced that area. The framework's `BHArea Λ = 1/Λ` then plugs
    in to give `S = 1/(4Λ)`, which at the observed Λ ~ 10^{-122}
    yields S ~ 10^{122} bits — the SQUARE ROOT of the bulk Sorkin
    count `Nsub Λ = 1/Λ²`. This square-root relation is the standard
    bulk-vs-boundary holographic comparison.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Generic A → S correspondence**: for any non-negative horizon
    area `A`, the BH entropy of a black hole carrying that area is
    `S = A/4`. This is the framework-level statement underlying the
    de Sitter horizon entropy of `LayerA.CosmologicalConstantN`. -/
noncomputable def bekensteinHawkingFromArea (A : ℝ) : ℝ := A / 4

/-- The generic A → S map agrees with the Schwarzschild-specific
    formula whenever evaluated on the Schwarzschild horizon area. -/
theorem bekensteinHawkingFromArea_eq_BH (M : ℝ) :
    bekensteinHawkingFromArea (horizonArea M) = bekensteinHawkingEntropy M := rfl

/-- **De Sitter horizon entropy** in the framework's notation: applied
    to `BHArea Λ = 1/Λ`, the BH formula gives `S = 1/(4Λ)`. -/
theorem deSitter_BH_entropy (Λ : ℝ) :
    bekensteinHawkingFromArea (BHArea Λ) = 1 / (4 * Λ) := by
  unfold bekensteinHawkingFromArea BHArea
  field_simp

/-- **De Sitter BH entropy is the square root of the framework's bulk
    count.** Numerically: at Λ = 10^{-122}, `bekensteinHawkingFromArea
    (BHArea Λ) = 1/(4Λ) ~ 0.25 · 10^{122}` bits, while the bulk
    `Nsub Λ ~ 10^{244}`. The bulk count is roughly the SQUARE of the
    boundary entropy times the universal factor 16, capturing the
    holographic bulk-vs-boundary scaling. -/
theorem bulk_is_boundary_squared_times_16 (Λ : ℝ) (hΛ : Λ ≠ 0) :
    Nsub Λ = 16 * (bekensteinHawkingFromArea (BHArea Λ)) ^ 2 := by
  unfold Nsub bekensteinHawkingFromArea BHArea
  have hΛ2 : Λ ^ 2 ≠ 0 := pow_ne_zero 2 hΛ
  field_simp
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: MASTER CAPSTONE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE BEKENSTEIN-HAWKING ENTROPY CAPSTONE.**

    For a Schwarzschild black hole of mass M in Planck units (G = c = ℏ = 1):

    (1) Schwarzschild radius: `r_s = 2M`.

    (2) Horizon area: `A = 4π r_s² = 16π M²`.

    (3) Bekenstein-Hawking entropy: `S_BH = A/4 = 4π M² = π r_s²`.

    (4) Monotonicity (algebraic second law): for `0 ≤ M₁ ≤ M₂`,
        `S_BH(M₁) ≤ S_BH(M₂)`. Strict for `0 < M₁ < M₂`.

    (5) Positivity: `M ≠ 0 ⟹ S_BH(M) > 0`.

    (6) Holographic scaling: `S_BH = π · r_s²` — entropy lives on the
        2-area horizon, not in the 3-volume interior.

    (7) Connection to the cosmological-constant framework: applied
        to the de Sitter horizon area `BHArea Λ = 1/Λ`, the BH
        formula gives `S = 1/(4Λ)`, the square root (up to a factor
        of 4) of the bulk Sorkin count `Nsub Λ = 1/Λ²`.

    The coefficient 1/4 in (3) is the standard Bekenstein-Hawking
    convention (Hawking 1974/1975); see file header for honest
    scope. Everything else follows algebraically. -/
theorem bekenstein_hawking_capstone :
    -- (1) Schwarzschild radius
    (∀ M : ℝ, schwarzschildRadius M = 2 * M)
    -- (2) Horizon area closed form
    ∧ (∀ M : ℝ, horizonArea M = 16 * Real.pi * M ^ 2)
    -- (3a) BH entropy closed form
    ∧ (∀ M : ℝ, bekensteinHawkingEntropy M = 4 * Real.pi * M ^ 2)
    -- (3b) BH entropy = A/4
    ∧ (∀ M : ℝ, bekensteinHawkingEntropy M = horizonArea M / 4)
    -- (3c) BH entropy = π r_s²
    ∧ (∀ M : ℝ,
        bekensteinHawkingEntropy M = Real.pi * (schwarzschildRadius M) ^ 2)
    -- (4) Monotonicity (algebraic second law)
    ∧ (∀ M₁ M₂ : ℝ, 0 ≤ M₁ → M₁ ≤ M₂ →
        bekensteinHawkingEntropy M₁ ≤ bekensteinHawkingEntropy M₂)
    -- (4') Strict monotonicity
    ∧ (∀ M₁ M₂ : ℝ, 0 < M₁ → M₁ < M₂ →
        bekensteinHawkingEntropy M₁ < bekensteinHawkingEntropy M₂)
    -- (5) Positivity
    ∧ (∀ M : ℝ, M ≠ 0 → 0 < bekensteinHawkingEntropy M)
    -- (6) Holographic / area scaling: S = A/4 generic
    ∧ (∀ A : ℝ, bekensteinHawkingFromArea A = A / 4)
    -- (7) De Sitter horizon entropy
    ∧ (∀ Λ : ℝ, bekensteinHawkingFromArea (BHArea Λ) = 1 / (4 * Λ))
    -- (8) Bulk = 16 · (boundary entropy)² (holographic comparison)
    ∧ (∀ Λ : ℝ, Λ ≠ 0 →
        Nsub Λ = 16 * (bekensteinHawkingFromArea (BHArea Λ)) ^ 2) := by
  refine ⟨fun _ => rfl, horizonArea_eq, BH_entropy_eq, fun _ => rfl,
          BH_entropy_eq_pi_rs_squared, ?_, ?_, ?_, fun _ => rfl,
          deSitter_BH_entropy, bulk_is_boundary_squared_times_16⟩
  · intros M₁ M₂ h₁ h_le
    exact BH_entropy_mono h₁ h_le
  · intros M₁ M₂ h₁ h_lt
    exact BH_entropy_strictMono h₁ h_lt
  · intros M hM
    exact BH_entropy_pos M hM

end UnifiedTheory.LayerB.BekensteinHawking
