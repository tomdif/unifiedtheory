/-
  LayerB/HawkingTemperature.lean — The Hawking temperature T_H = 1/(8πM)

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT

  `LayerB/BekensteinHawking.lean` derives the Bekenstein-Hawking
  entropy `S_BH(M) = 4π·M²` of a Schwarzschild black hole. Combined
  with the energy E = M (mass-energy equivalence in Planck units)
  and the first law of black hole thermodynamics dE = T·dS (at
  fixed angular momentum and charge), the temperature is fixed by

      T = (dE/dS) = 1 / (dS/dM) = 1 / (8π·M).

  This file states and proves the *algebraic content* of that
  derivation: a closed-form definition of `hawkingTemperature M`,
  the first-law identity `T_H · (dS/dM) = 1`, monotonicity
  (smaller black holes are HOTTER), a Planck-scale numerical
  bracket, and the cubic-in-M evaporation lifetime that follows
  from coupling T_H to a Stefan-Boltzmann luminosity.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED

  (1) `hawkingTemperature M = 1 / (8π·M)` for `M > 0`.

  (2) `entropyDerivative M = 8π·M` — the algebraic derivative
      `dS_BH/dM = d(4πM²)/dM = 8π·M`.

  (3) **First-law identity** (algebraic form):
      `T_H(M) · (dS/dM)(M) = 1`, equivalent to `T_H = dE/dS`
      with `E = M`.

  (4) **Anti-monotonicity in mass**: smaller Schwarzschild black
      holes are HOTTER. For `0 < M₁ < M₂`,
      `T_H(M₂) < T_H(M₁)`. This is the "negative specific heat"
      hallmark of black hole thermodynamics.

  (5) Numerical bracket: for `M = 1` Planck mass,
      `T_H = 1/(8π) ≈ 0.039789` Planck units; in particular
      `0.039 < T_H(1) < 0.04`.

  (6) **Evaporation lifetime scales as M³**: from the
      Stefan-Boltzmann law `dM/dt ~ -A·T⁴` with `A ~ M²` and
      `T ~ 1/M`, one finds `dM/dt ~ -1/M²`, hence
      `τ_evap(M) ~ M³`. Formalised here as an algebraic identity
      `evaporationRate M = -k / M²` with `k > 0`, and the
      proportionality `evaporationLifetime M ∝ M³`.

  (7) **Master capstone** bundling (1)-(6) into one theorem.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS NOT PROVED — HONEST SCOPE

  The temperature `T_H = 1/(8π M)` is established here from the
  algebraic combination of:

    • `S_BH = 4π M²` (taken from `BekensteinHawking.lean`, whose
      coefficient 1/4 is itself the standard convention fixed by
      Hawking's QFT calculation — see file header there).

    • `E = M` (mass-energy equivalence, Planck units).

    • `dE = T · dS` (first law of BH thermodynamics, taken as
      thermodynamic input).

  The TWO genuinely physical derivations of T_H are NOT formalised:

    (a) Hawking's 1974/1975 QFT-in-curved-spacetime calculation,
        which extracts T_H = κ/(2π) from the Bogoliubov
        coefficients of mode mismatch between past and future
        null infinity (collapsing-star geometry). Here
        κ = 1/(4M) is the surface gravity of the Schwarzschild
        horizon. Formalising this requires QFT in curved
        spacetime, which is outside the present development.

    (b) Gibbons-Hawking 1977 Euclidean-action / periodic-imaginary-
        time argument: the Schwarzschild metric in Euclidean
        signature is regular only when imaginary time has period
        β = 8π M, yielding T = 1/β = 1/(8π M) by the KMS
        condition. Formalising this requires Euclidean path
        integrals with the Gibbons-Hawking-York boundary term,
        also outside the present development.

  Both routes give the *same* T_H = 1/(8π M); this file simply
  packages the algebraic shadow of the thermodynamic derivation.

  Likewise, the M³ evaporation lifetime is the algebraic
  consequence of dM/dt ∝ -A·T⁴ (Stefan-Boltzmann times horizon
  area). The grey-body factors, the species-dependent coefficient,
  back-reaction, and the final-flash regime at M ~ M_Planck are
  all OUTSIDE the algebraic scope here.

  Zero sorry. Zero custom axioms.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import UnifiedTheory.LayerB.BekensteinHawking

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.HawkingTemperature

open Real
open UnifiedTheory.LayerB.BekensteinHawking

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE HAWKING TEMPERATURE FORMULA
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    In Planck units (c = ℏ = G = k_B = 1), the Hawking temperature
    of a Schwarzschild black hole of mass M is

        T_H(M) = 1 / (8π·M).

    Equivalently T_H = κ/(2π) where κ = 1/(4M) is the surface
    gravity of the horizon. This file does not derive the
    coefficient from QFT — see file header. We take T_H = 1/(8πM)
    as the algebraic output of (E = M) + (S = 4πM²) + first law.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Hawking temperature** of a Schwarzschild black hole in Planck
    units: `T_H(M) = 1 / (8π·M)`. The algebraic output of the first
    law `dE = T dS` with `E = M` and `S = 4π M²`. -/
noncomputable def hawkingTemperature (M : ℝ) : ℝ :=
  1 / (8 * Real.pi * M)

/-- The Hawking temperature is strictly positive when the mass is
    strictly positive. Smaller black holes have HIGHER positive
    temperature, but always positive. -/
theorem hawkingTemperature_pos (M : ℝ) (hM : 0 < M) :
    0 < hawkingTemperature M := by
  unfold hawkingTemperature
  have h8 : (0 : ℝ) < 8 := by norm_num
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have h8π : (0 : ℝ) < 8 * Real.pi := mul_pos h8 hπ
  have h8πM : (0 : ℝ) < 8 * Real.pi * M := mul_pos h8π hM
  exact one_div_pos.mpr h8πM

/-- The Hawking temperature times mass equals `1/(8π)`. Useful
    invariant form: `M · T_H(M) = 1/(8π)` is mass-independent. -/
theorem M_times_hawkingTemperature (M : ℝ) (hM : 0 < M) :
    M * hawkingTemperature M = 1 / (8 * Real.pi) := by
  unfold hawkingTemperature
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hM_ne : M ≠ 0 := ne_of_gt hM
  have h8 : (8 : ℝ) ≠ 0 := by norm_num
  field_simp

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: ENTROPY DERIVATIVE — dS/dM = 8π·M
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The derivative of `S_BH(M) = 4π·M²` with respect to M is
    `dS/dM = 8π·M`. This is just the calculus identity
    `d(M²)/dM = 2M` times the prefactor 4π.

    We avoid the full Mathlib calculus library and instead use an
    *algebraic placeholder* `entropyDerivative M := 8π·M` which is
    the closed-form derivative. The first-law identity (next
    section) then uses only ring arithmetic.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Algebraic derivative of the BH entropy with respect to mass:
    `dS_BH/dM = d(4π M²)/dM = 8π · M`. -/
noncomputable def entropyDerivative (M : ℝ) : ℝ :=
  8 * Real.pi * M

/-- `entropyDerivative` is non-negative for non-negative M. -/
theorem entropyDerivative_nonneg (M : ℝ) (hM : 0 ≤ M) :
    0 ≤ entropyDerivative M := by
  unfold entropyDerivative
  have h8 : (0 : ℝ) ≤ 8 := by norm_num
  have hπ : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  exact mul_nonneg (mul_nonneg h8 hπ) hM

/-- `entropyDerivative` is strictly positive for strictly positive M. -/
theorem entropyDerivative_pos (M : ℝ) (hM : 0 < M) :
    0 < entropyDerivative M := by
  unfold entropyDerivative
  have h8 : (0 : ℝ) < 8 := by norm_num
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  exact mul_pos (mul_pos h8 hπ) hM

/-- **Difference quotient identity**: the algebraic derivative
    matches the symmetric difference quotient of `S_BH` exactly
    for any pair of masses with average M (this is the special
    feature of polynomial-quadratic functions). Concretely:

      [S_BH(M+h) − S_BH(M−h)] / (2h) = 8π·M = entropyDerivative M.

    This certifies `entropyDerivative` as the genuine derivative
    (not just a placeholder definition). -/
theorem entropyDerivative_is_diff_quotient (M h : ℝ) (hh : h ≠ 0) :
    (bekensteinHawkingEntropy (M + h) - bekensteinHawkingEntropy (M - h)) / (2 * h)
      = entropyDerivative M := by
  rw [BH_entropy_eq, BH_entropy_eq]
  unfold entropyDerivative
  have h2h : (2 * h) ≠ 0 := mul_ne_zero (by norm_num) hh
  field_simp
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: THE FIRST-LAW IDENTITY T_H · (dS/dM) = 1
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The first law of BH thermodynamics (at fixed J, Q) reads
    `dE = T dS`. With `E = M` this is `dM = T dS`, equivalently
    `T = (dM/dS) = 1 / (dS/dM)`. The Hawking temperature is then
    the unique T satisfying

        T_H(M) · entropyDerivative(M) = 1

    for every M > 0. This is the central algebraic statement of
    this file.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **First-law identity** in algebraic form: the Hawking
    temperature is the reciprocal of the entropy derivative,

        T_H(M) · dS/dM = 1   for M > 0.

    Equivalently `T_H = dE/dS = 1/(dS/dE) = 1/(dS/dM)` since
    `E = M` in Planck units. -/
theorem hawkingTemp_from_entropy_derivative (M : ℝ) (hM : 0 < M) :
    hawkingTemperature M * entropyDerivative M = 1 := by
  unfold hawkingTemperature entropyDerivative
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hM_ne : M ≠ 0 := ne_of_gt hM
  have h8 : (8 : ℝ) ≠ 0 := by norm_num
  field_simp

/-- **Reciprocal form** of the first law: the entropy derivative
    is the reciprocal of the Hawking temperature. -/
theorem entropyDerivative_eq_reciprocal_hawkingTemp (M : ℝ) (hM : 0 < M) :
    entropyDerivative M = 1 / hawkingTemperature M := by
  have h := hawkingTemp_from_entropy_derivative M hM
  have hT : 0 < hawkingTemperature M := hawkingTemperature_pos M hM
  have hT_ne : hawkingTemperature M ≠ 0 := ne_of_gt hT
  field_simp
  linarith

/-- **Hawking temperature as reciprocal of dS/dM**. -/
theorem hawkingTemp_eq_reciprocal_entropyDerivative (M : ℝ) (hM : 0 < M) :
    hawkingTemperature M = 1 / entropyDerivative M := by
  have h := hawkingTemp_from_entropy_derivative M hM
  have hSp : 0 < entropyDerivative M := entropyDerivative_pos M hM
  have hSp_ne : entropyDerivative M ≠ 0 := ne_of_gt hSp
  field_simp
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: ANTI-MONOTONICITY — SMALLER BLACK HOLES ARE HOTTER
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Because `T_H ∝ 1/M`, the temperature is a strictly DECREASING
    function of mass. Equivalently, a Schwarzschild black hole has
    NEGATIVE specific heat dE/dT < 0:

        dT/dM = -1/(8π M²) < 0   ⟹   smaller is hotter.

    This is the famous thermodynamic instability of asymptotically-
    flat black holes — they cannot be in stable equilibrium with an
    infinite radiation bath. The algebraic monotonicity statement
    below is the precise shadow.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Anti-monotonicity** of the Hawking temperature: a strictly
    smaller positive-mass Schwarzschild black hole is strictly
    HOTTER. For `0 < M₁ < M₂`, `T_H(M₂) < T_H(M₁)`. -/
theorem hawkingTemperature_antimono {M₁ M₂ : ℝ}
    (h₁ : 0 < M₁) (h_lt : M₁ < M₂) :
    hawkingTemperature M₂ < hawkingTemperature M₁ := by
  unfold hawkingTemperature
  have h₂ : 0 < M₂ := lt_trans h₁ h_lt
  have h8 : (0 : ℝ) < 8 := by norm_num
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have h8π : (0 : ℝ) < 8 * Real.pi := mul_pos h8 hπ
  have h8πM₁ : (0 : ℝ) < 8 * Real.pi * M₁ := mul_pos h8π h₁
  have h8πM₂ : (0 : ℝ) < 8 * Real.pi * M₂ := mul_pos h8π h₂
  have h8πlt : 8 * Real.pi * M₁ < 8 * Real.pi * M₂ :=
    mul_lt_mul_of_pos_left h_lt h8π
  exact one_div_lt_one_div_of_lt h8πM₁ h8πlt

/-- **Weak anti-monotonicity** of the Hawking temperature: for
    positive masses with `M₁ ≤ M₂`, `T_H(M₂) ≤ T_H(M₁)`. -/
theorem hawkingTemperature_antimono_le {M₁ M₂ : ℝ}
    (h₁ : 0 < M₁) (h_le : M₁ ≤ M₂) :
    hawkingTemperature M₂ ≤ hawkingTemperature M₁ := by
  rcases lt_or_eq_of_le h_le with h_lt | h_eq
  · exact (hawkingTemperature_antimono h₁ h_lt).le
  · rw [h_eq]

/-- **Negative specific heat** in algebraic shadow form: for
    M₁ < M₂ (both positive), the temperature DROPS as mass grows.
    Equivalently, ENERGY (= mass) absorbed makes the system
    COOLER — the defining symptom of negative specific heat. -/
theorem hawkingTemp_strictAnti {M₁ M₂ : ℝ}
    (h₁ : 0 < M₁) (h_lt : M₁ < M₂) :
    hawkingTemperature M₁ - hawkingTemperature M₂ > 0 := by
  have h := hawkingTemperature_antimono h₁ h_lt
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: NUMERICAL BRACKET AT THE PLANCK MASS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For `M = 1` (one Planck mass), the Hawking temperature is
    `T_H(1) = 1/(8π) ≈ 0.039789` Planck units. We bracket it by
    `0.039 < T_H(1) < 0.04` using only numerical bounds on π.

    For comparison, `S_BH(1) = 4π ≈ 12.57`, so the entropy of a
    Planck-mass black hole is roughly 12.57 bits.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The Hawking temperature at unit Planck mass equals `1/(8π)`. -/
theorem hawkingTemperature_at_one :
    hawkingTemperature 1 = 1 / (8 * Real.pi) := by
  unfold hawkingTemperature
  ring

/-- **Numerical bracket** at the Planck mass: `T_H(1) < 0.04`.
    Uses the Mathlib bound `π > 3.1415`. -/
theorem hawkingTemperature_at_one_lt :
    hawkingTemperature 1 < 0.04 := by
  rw [hawkingTemperature_at_one]
  have hπ : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have h8 : (0 : ℝ) < 8 := by norm_num
  have h8π : (8 * 3.1415 : ℝ) < 8 * Real.pi :=
    mul_lt_mul_of_pos_left hπ h8
  have h25 : (25.132 : ℝ) < 8 * Real.pi := by
    have : (8 * 3.1415 : ℝ) = 25.132 := by norm_num
    linarith
  have h25_pos : (0 : ℝ) < 25.132 := by norm_num
  -- 1/(8π) < 1/25.132 < 0.04
  have step1 : 1 / (8 * Real.pi) < 1 / 25.132 :=
    one_div_lt_one_div_of_lt h25_pos h25
  have step2 : (1 : ℝ) / 25.132 < 0.04 := by norm_num
  linarith

/-- **Numerical bracket** at the Planck mass: `T_H(1) > 0.039`.
    Uses the Mathlib bound `π < 3.1416`. -/
theorem hawkingTemperature_at_one_gt :
    0.039 < hawkingTemperature 1 := by
  rw [hawkingTemperature_at_one]
  have hπ : Real.pi < 3.1416 := Real.pi_lt_d4
  have h8 : (0 : ℝ) < 8 := by norm_num
  have h8π : 8 * Real.pi < 8 * 3.1416 :=
    mul_lt_mul_of_pos_left hπ h8
  have h8π_calc : (8 * 3.1416 : ℝ) = 25.1328 := by norm_num
  have h8π_lt : 8 * Real.pi < 25.1328 := by linarith
  have hπ_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h8π_pos : (0 : ℝ) < 8 * Real.pi :=
    mul_pos (by norm_num) hπ_pos
  -- 1/(8π) > 1/25.1328 > 0.039
  have step1 : 1 / (25.1328 : ℝ) < 1 / (8 * Real.pi) :=
    one_div_lt_one_div_of_lt h8π_pos h8π_lt
  have step2 : (0.039 : ℝ) < 1 / 25.1328 := by norm_num
  linarith

/-- **Combined Planck-mass bracket**: `0.039 < T_H(1) < 0.04`.
    The actual value is `1/(8π) ≈ 0.039789`. -/
theorem hawkingTemperature_at_one_bracket :
    0.039 < hawkingTemperature 1 ∧ hawkingTemperature 1 < 0.04 :=
  ⟨hawkingTemperature_at_one_gt, hawkingTemperature_at_one_lt⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: EVAPORATION LIFETIME ∝ M³
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Treating the black hole as a black body of area `A = 16π M²`
    radiating at temperature `T = 1/(8π M)`, the Stefan-Boltzmann
    law gives a luminosity

        L ~ A · T⁴ ~ M² · (1/M)⁴ ~ 1/M².

    Equating mass loss with luminosity (`dM/dt = -L`),

        dM/dt ~ -1/M²,

    which integrates to `M(t)³ - M₀³ ∝ -t`, so the evaporation
    time scales as `τ_evap ~ M₀³`. We formalise this here as the
    algebraic identity for the *mass-loss rate*

        evaporationRate(M) := -k / M²,

    where the dimensionless prefactor `k` collects (Stefan-Boltzmann
    constant) × (16π for area) × (1/(8π)⁴ for T⁴). With `dM/dt =
    -k/M²` integrating gives `τ_evap = M₀³ / (3k)`. The cubic
    scaling itself is the algebraic content; the prefactor depends
    on number-of-radiating-species and grey-body factors and is
    NOT formalised here.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Stefan-Boltzmann luminosity proxy** for a Schwarzschild black
    hole, ignoring grey-body factors and species multiplicity:
    `L_alg(M) := horizonArea M · T_H(M)⁴`. The Stefan-Boltzmann
    constant and species-counting prefactor are absorbed into the
    user's choice of unit. -/
noncomputable def luminosity (M : ℝ) : ℝ :=
  horizonArea M * (hawkingTemperature M) ^ 4

/-- **Closed-form luminosity** in terms of M alone:
    `luminosity M = 1 / (256 π³ M²)`. This collects
    `A·T⁴ = (16π M²) · (1/(8π M))⁴ = 1 / (256 π³ M²)`. -/
theorem luminosity_eq (M : ℝ) (hM : 0 < M) :
    luminosity M = 1 / (256 * Real.pi ^ 3 * M ^ 2) := by
  unfold luminosity
  rw [horizonArea_eq]
  unfold hawkingTemperature
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hM_ne : M ≠ 0 := ne_of_gt hM
  have h8 : (8 : ℝ) ≠ 0 := by norm_num
  field_simp
  ring

/-- **Luminosity is positive** for positive mass. -/
theorem luminosity_pos (M : ℝ) (hM : 0 < M) : 0 < luminosity M := by
  rw [luminosity_eq M hM]
  have hπ : 0 < Real.pi := Real.pi_pos
  have hπ3 : 0 < Real.pi ^ 3 := by positivity
  have hM2 : 0 < M ^ 2 := by positivity
  have h256 : (0 : ℝ) < 256 := by norm_num
  have hden : 0 < 256 * Real.pi ^ 3 * M ^ 2 :=
    mul_pos (mul_pos h256 hπ3) hM2
  exact one_div_pos.mpr hden

/-- **Mass-loss rate**: `dM/dt = -L = -1/(256 π³ M²)`. The
    algebraic right-hand side, packaged as a function of M. -/
noncomputable def evaporationRate (M : ℝ) : ℝ :=
  -(1 / (256 * Real.pi ^ 3 * M ^ 2))

/-- The mass-loss rate is the negative of the luminosity. -/
theorem evaporationRate_eq_neg_luminosity (M : ℝ) (hM : 0 < M) :
    evaporationRate M = -luminosity M := by
  unfold evaporationRate
  rw [luminosity_eq M hM]

/-- **Mass-loss rate is strictly negative** for positive M
    (mass DECREASES with time during evaporation). -/
theorem evaporationRate_neg (M : ℝ) (hM : 0 < M) :
    evaporationRate M < 0 := by
  unfold evaporationRate
  have hπ : 0 < Real.pi := Real.pi_pos
  have hπ3 : 0 < Real.pi ^ 3 := by positivity
  have hM2 : 0 < M ^ 2 := by positivity
  have h256 : (0 : ℝ) < 256 := by norm_num
  have hden : 0 < 256 * Real.pi ^ 3 * M ^ 2 :=
    mul_pos (mul_pos h256 hπ3) hM2
  have hpos : 0 < 1 / (256 * Real.pi ^ 3 * M ^ 2) := one_div_pos.mpr hden
  linarith

/-- **Cubic scaling** of evaporation lifetime. With
    `dM/dt = -1/(256 π³ M²)` and the antiderivative
    `M³/3 = -t/(256 π³) + C`, the time to evaporate from initial
    mass `M₀ > 0` to `M = 0` is

        τ_evap(M₀) = (256 π³ / 3) · M₀³.

    We define `evaporationLifetime` as the algebraic right-hand
    side and prove the cubic scaling explicitly. -/
noncomputable def evaporationLifetime (M : ℝ) : ℝ :=
  (256 * Real.pi ^ 3 / 3) * M ^ 3

/-- **Evaporation lifetime is positive** for positive mass. -/
theorem evaporationLifetime_pos (M : ℝ) (hM : 0 < M) :
    0 < evaporationLifetime M := by
  unfold evaporationLifetime
  have hπ : 0 < Real.pi := Real.pi_pos
  have hπ3 : 0 < Real.pi ^ 3 := by positivity
  have h256 : (0 : ℝ) < 256 := by norm_num
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hpref : 0 < 256 * Real.pi ^ 3 / 3 := by positivity
  have hM3 : 0 < M ^ 3 := by positivity
  exact mul_pos hpref hM3

/-- **Cubic scaling identity**: doubling the mass multiplies the
    evaporation lifetime by 8. Concretely,

        evaporationLifetime (c · M) = c³ · evaporationLifetime M. -/
theorem evaporationLifetime_cubic_scaling (c M : ℝ) :
    evaporationLifetime (c * M) = c ^ 3 * evaporationLifetime M := by
  unfold evaporationLifetime
  ring

/-- **Lifetime ratio** for two black holes is the cube of the mass
    ratio: `τ(M₂)/τ(M₁) = (M₂/M₁)³`, the M³ scaling in its
    cleanest form. -/
theorem evaporationLifetime_ratio (M₁ M₂ : ℝ) :
    evaporationLifetime M₂ * M₁ ^ 3 = evaporationLifetime M₁ * M₂ ^ 3 := by
  unfold evaporationLifetime
  ring

/-- **Lifetime cubic dominance**: for `M₁ < M₂` with both positive,
    the larger black hole lives strictly longer. -/
theorem evaporationLifetime_strictMono {M₁ M₂ : ℝ}
    (h₁ : 0 < M₁) (h_lt : M₁ < M₂) :
    evaporationLifetime M₁ < evaporationLifetime M₂ := by
  unfold evaporationLifetime
  have hpref_pos : 0 < 256 * Real.pi ^ 3 / 3 := by
    have hπ : 0 < Real.pi := Real.pi_pos
    positivity
  have h_M1_3 : M₁ ^ 3 < M₂ ^ 3 := by
    have h₂ : 0 < M₂ := lt_trans h₁ h_lt
    nlinarith [sq_nonneg M₁, sq_nonneg M₂, sq_nonneg (M₂ - M₁),
               mul_pos h₁ h₁, mul_pos h₂ h₂]
  exact mul_lt_mul_of_pos_left h_M1_3 hpref_pos

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: CONNECTION TO BEKENSTEIN-HAWKING ENTROPY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Substituting `T_H = 1/(8πM)` and `S_BH = 4π M²` back into the
    differential first law `dE = T dS` gives a sanity check:

        T · dS = (1/(8πM)) · (8π M dM) = dM = dE. ✓

    We package the algebraic version of this loop here.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **First-law loop**: the product `T_H · (dS/dM)` equals the
    derivative `dE/dM = 1` (since `E = M`). Algebraically,
    `T_H(M) · entropyDerivative(M) = 1` for `M > 0`. -/
theorem first_law_dE_eq_TdS (M : ℝ) (hM : 0 < M) :
    hawkingTemperature M * entropyDerivative M = 1 :=
  hawkingTemp_from_entropy_derivative M hM

/-- **Energy at unit dE/dM**: the algebraic statement that with
    `E = M`, `dE/dM = 1`. Trivial but documented for the
    first-law packaging. -/
theorem energy_derivative_eq_one : (1 : ℝ) = 1 := rfl

/-- **Surface gravity** of the Schwarzschild horizon in Planck
    units: `κ = 1/(4M)`. This is the standard textbook value for
    the Schwarzschild geometry; combined with the Unruh-Hawking
    relation `T = κ/(2π)` it reproduces `T_H = 1/(8πM)`. -/
noncomputable def surfaceGravity (M : ℝ) : ℝ := 1 / (4 * M)

/-- **Hawking temperature from surface gravity**: `T_H = κ/(2π)`,
    the Unruh-Hawking relation evaluated on the Schwarzschild
    horizon. Algebraically, `T_H(M) = surfaceGravity(M) / (2π)`. -/
theorem hawkingTemp_eq_surfaceGravity_over_twopi (M : ℝ) (hM : 0 < M) :
    hawkingTemperature M = surfaceGravity M / (2 * Real.pi) := by
  unfold hawkingTemperature surfaceGravity
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hM_ne : M ≠ 0 := ne_of_gt hM
  field_simp
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: MASTER CAPSTONE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE HAWKING TEMPERATURE CAPSTONE.**

    For a Schwarzschild black hole of mass `M > 0` in Planck
    units (G = c = ℏ = k_B = 1):

    (1) `T_H(M) = 1 / (8π M)` — Hawking temperature formula.

    (2) `M · T_H(M) = 1/(8π)` — mass-temperature invariant.

    (3) `T_H(M) > 0` — temperature is strictly positive.

    (4) **First law**: `T_H(M) · dS/dM = 1`, i.e.
        `T_H · (8π M) = 1`, equivalently `T_H = 1/(dS/dM)`.

    (5) **Anti-monotonicity**: for `0 < M₁ < M₂`,
        `T_H(M₂) < T_H(M₁)`. Smaller black holes are hotter.
        This is the algebraic shadow of negative specific heat.

    (6) **Planck-mass bracket**: `0.039 < T_H(1) < 0.04`. The
        exact value is `1/(8π) ≈ 0.039789`.

    (7) **Surface gravity**: `T_H = κ/(2π)` with κ = 1/(4M)
        — Unruh-Hawking relation evaluated on the horizon.

    (8) **Cubic-in-M evaporation lifetime**:
        `evaporationLifetime M = (256π³/3) · M³`, hence
        `τ ∝ M³`. Larger BHs live strictly longer.

    The coefficient 1/(8π) is fixed by combining `S_BH = 4π M²`
    (whose 1/4 normalisation comes from Hawking's QFT
    calculation — see `BekensteinHawking.lean` header) with the
    first law `dE = T dS` and `E = M`. The Stefan-Boltzmann
    coefficient and species multiplicity in (8) are absorbed
    into the algebraic prefactor; cubic scaling is the
    universal content. See file header for honest scope.
-/
theorem hawking_temperature_capstone :
    -- (1) Closed form
    (∀ M : ℝ, hawkingTemperature M = 1 / (8 * Real.pi * M))
    -- (2) Mass-temperature invariant
    ∧ (∀ M : ℝ, 0 < M → M * hawkingTemperature M = 1 / (8 * Real.pi))
    -- (3) Positivity
    ∧ (∀ M : ℝ, 0 < M → 0 < hawkingTemperature M)
    -- (4) First-law identity T · dS/dM = 1
    ∧ (∀ M : ℝ, 0 < M →
        hawkingTemperature M * entropyDerivative M = 1)
    -- (5) Anti-monotonicity (smaller is hotter)
    ∧ (∀ M₁ M₂ : ℝ, 0 < M₁ → M₁ < M₂ →
        hawkingTemperature M₂ < hawkingTemperature M₁)
    -- (6) Planck-mass numerical bracket
    ∧ (0.039 < hawkingTemperature 1 ∧ hawkingTemperature 1 < 0.04)
    -- (7) Surface-gravity relation T = κ/(2π)
    ∧ (∀ M : ℝ, 0 < M →
        hawkingTemperature M = surfaceGravity M / (2 * Real.pi))
    -- (8a) Evaporation lifetime closed form
    ∧ (∀ M : ℝ, evaporationLifetime M = (256 * Real.pi ^ 3 / 3) * M ^ 3)
    -- (8b) Cubic scaling
    ∧ (∀ c M : ℝ,
        evaporationLifetime (c * M) = c ^ 3 * evaporationLifetime M)
    -- (8c) Lifetime monotonicity
    ∧ (∀ M₁ M₂ : ℝ, 0 < M₁ → M₁ < M₂ →
        evaporationLifetime M₁ < evaporationLifetime M₂) := by
  refine ⟨fun _ => rfl, ?_, ?_, ?_, ?_, hawkingTemperature_at_one_bracket,
          ?_, fun _ => rfl, evaporationLifetime_cubic_scaling, ?_⟩
  · intro M hM; exact M_times_hawkingTemperature M hM
  · intro M hM; exact hawkingTemperature_pos M hM
  · intro M hM; exact hawkingTemp_from_entropy_derivative M hM
  · intro M₁ M₂ h₁ h_lt; exact hawkingTemperature_antimono h₁ h_lt
  · intro M hM; exact hawkingTemp_eq_surfaceGravity_over_twopi M hM
  · intro M₁ M₂ h₁ h_lt; exact evaporationLifetime_strictMono h₁ h_lt

end UnifiedTheory.LayerB.HawkingTemperature
