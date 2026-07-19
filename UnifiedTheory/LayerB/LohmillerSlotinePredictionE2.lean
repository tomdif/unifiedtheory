/-
  LayerB/LohmillerSlotinePredictionE2.lean — Phase E2.

  GAUSSIAN PROFILE in the static matter-coupled curved-Schrödinger
  equilibrium.  Extends E1's polynomial-profile prediction to a
  one-parameter family, exposing the slow-r and sharp-profile limits
  explicitly.

  Internal-model framing (carrying E1's caveat forward):  the
  "Ricci scalar" here is the Ricci scalar of the emergent 1+1-dim
  conformal metric `g = r²·diag(−1,1)` constructed in
  `LohmillerSlotineBackreaction`.  Predictions are within the
  static matter-coupled curved-Schrödinger equilibrium sector of
  the LSBridge framework — they are not claims about general GR
  + standard QFT matter content.  Within that sector, however,
  the relations are exact algebraic theorems.

  Headline (proved here):  For the Gaussian profile
      r_σ(x) := exp(−x²/(2σ²)),
  in static matter-coupled curved equilibrium with
      V_σ(x) := (ℏ²/(2m·r²)) · (r_xx/r),
  the (derived) Ricci scalar of the emergent metric satisfies the
  closed-form law
      R_σ(x) = 2 / (σ² · r_σ(x)²) = 2·exp(x²/σ²) / σ².
  In particular `R_σ(x) > 0` everywhere, `R → 0` in the slow-r
  limit σ → ∞ (at fixed x), and `R → ∞` in the sharp-profile
  limit σ → 0.

  Zero sorry.  Standard axioms only.
-/
import UnifiedTheory.LayerB.LohmillerSlotinePredictionE1

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.LohmillerSlotinePredictionE2

open UnifiedTheory.LayerB.LohmillerSlotinePredictionE1

/-! ════════════════════════════════════════════════════════════════════════
    PART 1 — GAUSSIAN PROFILE SCALARS.

    We work at the **scalar** level:  `gaussianProfile σ x`,
    `gaussianProfile_x σ x`, `gaussianProfile_xx σ x` are defined as
    independent functions (the chain-rule formulas), without invoking
    Mathlib's `deriv` on `Real.exp`.  This makes the algebraic
    identities below tractable.  Verifying that the `_x` and `_xx`
    objects ARE the actual derivatives is an orthogonal task (chain
    rule + Real.exp.hasDerivAt + ...); the identities here hold as
    purely-algebraic theorems regardless.
    ════════════════════════════════════════════════════════════════════════ -/

/-- Gaussian amplitude profile `r_σ(x) := exp(−x²/(2σ²))`. -/
noncomputable def gaussianProfile (σ x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2) / (2 * σ ^ 2))

/-- Spatial derivative of the Gaussian (chain rule):
        `r_σ'(x) = −(x/σ²) · r_σ(x)`. -/
noncomputable def gaussianProfile_x (σ x : ℝ) : ℝ :=
  -(x / σ ^ 2) * gaussianProfile σ x

/-- Second spatial derivative of the Gaussian (chain rule):
        `r_σ''(x) = ((x² − σ²)/σ⁴) · r_σ(x)`. -/
noncomputable def gaussianProfile_xx (σ x : ℝ) : ℝ :=
  ((x ^ 2 - σ ^ 2) / σ ^ 4) * gaussianProfile σ x

/-- The Gaussian profile is strictly positive everywhere
    (since `Real.exp > 0`). -/
theorem gaussianProfile_pos (σ x : ℝ) : 0 < gaussianProfile σ x :=
  Real.exp_pos _

/-- The Gaussian profile is nonzero everywhere. -/
theorem gaussianProfile_ne_zero (σ x : ℝ) : gaussianProfile σ x ≠ 0 :=
  ne_of_gt (gaussianProfile_pos σ x)

/-! ════════════════════════════════════════════════════════════════════════
    PART 2 — EINSTEIN CORRECTION AND MATTER POTENTIAL FOR THE GAUSSIAN.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Einstein correction for the Gaussian**:
        `Δ_geom(σ, x) = 2x²/(σ⁴ · r_σ(x)²)`.
    Vanishes only at `x = 0` (peak of the Gaussian); strictly positive
    elsewhere. -/
theorem gaussianProfile_einsteinCorrection
    (σ x : ℝ) (hσ : σ ≠ 0) :
    einsteinCorrection (gaussianProfile σ x) (gaussianProfile_x σ x)
      = 2 * x ^ 2 / (σ ^ 4 * (gaussianProfile σ x) ^ 2) := by
  unfold einsteinCorrection gaussianProfile_x
  have hr := gaussianProfile_ne_zero σ x
  have hr2 : (gaussianProfile σ x) ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hσ2 : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  have hσ4 : σ ^ 4 ≠ 0 := pow_ne_zero 4 hσ
  field_simp

/-- **Matter-coupled curved equilibrium potential** for the Gaussian:
        `V_σ(x) = (ℏ²/(2m)) · (x² − σ²)/(σ⁴ · r_σ(x)²)`.
    Negative for `|x| < σ`, zero at `|x| = σ`, positive for `|x| > σ`. -/
noncomputable def gaussianMatterPotential
    (σ x hbar m : ℝ) : ℝ :=
  let r := gaussianProfile σ x
  let r_xx := gaussianProfile_xx σ x
  (hbar ^ 2 / (2 * m * r ^ 2)) * (r_xx / r)

theorem gaussianMatterPotential_eq
    (σ x hbar m : ℝ) (hσ : σ ≠ 0) (hm : m ≠ 0) :
    gaussianMatterPotential σ x hbar m
      = (hbar ^ 2 / (2 * m)) *
          ((x ^ 2 - σ ^ 2) / (σ ^ 4 * (gaussianProfile σ x) ^ 2)) := by
  unfold gaussianMatterPotential gaussianProfile_xx
  have hr := gaussianProfile_ne_zero σ x
  have hr2 : (gaussianProfile σ x) ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hr3 : (gaussianProfile σ x) ^ 3 ≠ 0 := pow_ne_zero 3 hr
  have hσ2 : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  have hσ4 : σ ^ 4 ≠ 0 := pow_ne_zero 4 hσ
  have h2m_ne : (2 * m) ≠ 0 := by
    intro h; exact hm (by linarith : m = 0)
  field_simp

/-! ════════════════════════════════════════════════════════════════════════
    PART 3 — RICCI SCALAR CLOSED FORM (DERIVED FROM THE IDENTITY).

    From the Einstein-like identity
        `R + (4m/ℏ²) · V = Δ_geom`,
    substituting the Gaussian forms for `V` and `Δ_geom` and using
    `Δ_geom − (4m/ℏ²) · V = (2x² − 2(x² − σ²))/(σ⁴ · r²) = 2σ²/(σ⁴ · r²)
                          = 2/(σ² · r²)`,
    we get the closed-form law
        `R_σ(x) = 2 / (σ² · r_σ(x)²) = 2·exp(x²/σ²)/σ²`.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Derived Ricci scalar for the Gaussian** (closed form):
        `R_σ(x) = 2 / (σ² · r_σ(x)²)`.
    From the Einstein-like identity + Gaussian closed forms of `Δ_geom`
    and `V`.

    Properties:
      • `R_σ(x) > 0` everywhere (positive curvature throughout).
      • Slow-r limit (σ → ∞): `R → 0` at fixed x — recovers vacuum.
      • Sharp limit (σ → 0): `R → ∞` exponentially.

    Note: unlike the polynomial profile (E1), the Gaussian admits NO
    cancellation point — the geometric correction always strictly
    exceeds the matter coupling term in magnitude, yielding strictly
    positive `R`. -/
theorem gaussianRicci_from_identity
    (σ x hbar m : ℝ) (hσ : σ ≠ 0) (hm : m ≠ 0) (hhbar : hbar ≠ 0)
    (R : ℝ)
    (h_identity :
      R + (4 * m / hbar ^ 2) * gaussianMatterPotential σ x hbar m
        = einsteinCorrection (gaussianProfile σ x) (gaussianProfile_x σ x)) :
    R = 2 / (σ ^ 2 * (gaussianProfile σ x) ^ 2) := by
  rw [gaussianProfile_einsteinCorrection σ x hσ,
      gaussianMatterPotential_eq σ x hbar m hσ hm] at h_identity
  have hr := gaussianProfile_ne_zero σ x
  have hr2 : (gaussianProfile σ x) ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hσ2 : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  have hσ4 : σ ^ 4 ≠ 0 := pow_ne_zero 4 hσ
  have hhbar2 : hbar ^ 2 ≠ 0 := pow_ne_zero 2 hhbar
  have h2m_ne : (2 * m) ≠ 0 := by
    intro h; exact hm (by linarith : m = 0)
  rw [eq_div_iff (mul_ne_zero hσ2 hr2)]
  -- Goal: R * (σ² · r²) = 2
  field_simp at h_identity
  -- h_identity: R * 2 * σ^4 * r^2 + 4 * (x^2 - σ^2) = 4 * x^2.
  -- Step 1: simplify h_identity to R * 2 * σ^4 * r^2 = 4 * σ^2.
  have h2 : R * 2 * σ ^ 4 * (gaussianProfile σ x) ^ 2 = 4 * σ ^ 2 := by linarith
  -- Step 2: rewrite as (R * σ^2 * r^2) * (2 * σ^2) = 2 * (2 * σ^2).
  have h3 : R * (σ ^ 2 * (gaussianProfile σ x) ^ 2) * (2 * σ ^ 2)
              = 2 * (2 * σ ^ 2) := by
    have : R * (σ ^ 2 * (gaussianProfile σ x) ^ 2) * (2 * σ ^ 2)
            = R * 2 * σ ^ 4 * (gaussianProfile σ x) ^ 2 := by ring
    rw [this, h2]; ring
  -- Step 3: cancel (2 * σ^2).
  have h2σ_ne : (2 * σ ^ 2 : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hσ2
  exact mul_right_cancel₀ h2σ_ne h3

/-! ════════════════════════════════════════════════════════════════════════
    PART 4 — SPECIFIC EVALUATIONS AND ASYMPTOTIC NOTES.
    ════════════════════════════════════════════════════════════════════════ -/

/-- At the Gaussian peak `x = 0`, `r_σ(0) = 1` (since exp(0) = 1). -/
theorem gaussianProfile_at_zero (σ : ℝ) (hσ : σ ≠ 0) :
    gaussianProfile σ 0 = 1 := by
  unfold gaussianProfile
  have hσ2 : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  have : -(0 : ℝ) ^ 2 / (2 * σ ^ 2) = 0 := by
    simp
  rw [this, Real.exp_zero]

/-- At the peak `x = 0` and `σ = 1`, the Einstein correction vanishes
    (because `r_x(0) = 0` — the Gaussian is flat at its peak). -/
theorem gaussianProfile_einsteinCorrection_at_peak (σ : ℝ) (hσ : σ ≠ 0) :
    einsteinCorrection (gaussianProfile σ 0) (gaussianProfile_x σ 0) = 0 := by
  rw [gaussianProfile_einsteinCorrection σ 0 hσ]
  simp

/-- At the peak `x = 0` (where `r_x = 0`), the matter potential is
    nonzero:  `V_σ(0) = -(ℏ²/(2m·σ²))` (the standard
    quantum-mechanical zero-point potential for a Gaussian). -/
theorem gaussianMatterPotential_at_peak
    (σ hbar m : ℝ) (hσ : σ ≠ 0) (hm : m ≠ 0) :
    gaussianMatterPotential σ 0 hbar m = -(hbar ^ 2 / (2 * m * σ ^ 2)) := by
  rw [gaussianMatterPotential_eq σ 0 hbar m hσ hm]
  rw [gaussianProfile_at_zero σ hσ]
  have hσ2 : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  have hσ4 : σ ^ 4 ≠ 0 := pow_ne_zero 4 hσ
  have h2m_ne : (2 * m) ≠ 0 := by
    intro h; exact hm (by linarith : m = 0)
  have h_simp : ((0:ℝ) ^ 2 - σ ^ 2) / (σ ^ 4 * 1 ^ 2) = -1 / σ ^ 2 := by
    have : ((0:ℝ) ^ 2 - σ ^ 2) = -σ ^ 2 := by ring
    rw [this]
    have : (σ ^ 4 * 1 ^ 2) = σ ^ 2 * σ ^ 2 := by ring
    rw [this, neg_div, ← div_div]
    rw [div_self hσ2]
    ring
  rw [h_simp]
  field_simp

/-- **Ricci at the peak**:  for the Gaussian, `R_σ(0) = 2/σ²`.
    Diverges as σ → 0;  vanishes as σ → ∞. -/
theorem gaussianRicci_at_peak
    (σ hbar m : ℝ) (hσ : σ ≠ 0) (hm : m ≠ 0) (hhbar : hbar ≠ 0)
    (R : ℝ)
    (h_identity :
      R + (4 * m / hbar ^ 2) * gaussianMatterPotential σ 0 hbar m
        = einsteinCorrection (gaussianProfile σ 0) (gaussianProfile_x σ 0)) :
    R = 2 / σ ^ 2 := by
  have h := gaussianRicci_from_identity σ 0 hbar m hσ hm hhbar R h_identity
  rw [gaussianProfile_at_zero σ hσ] at h
  rw [h]
  field_simp

/-- **No-cancellation theorem for the Gaussian**:  the geometric
    correction `Δ_geom` and the matter coupling `(4m/ℏ²)·V` are never
    equal (for the Gaussian profile and any `σ ≠ 0`).

    Equivalently, `R_σ(x) ≠ 0` everywhere.  This is the structural
    contrast with the polynomial profile (E1), where exact cancellation
    occurred at `x = 1`.  For the Gaussian, no such cancellation
    point exists. -/
theorem gaussianRicci_never_zero
    (σ x hbar m : ℝ) (hσ : σ ≠ 0) (hm : m ≠ 0) (hhbar : hbar ≠ 0)
    (R : ℝ)
    (h_identity :
      R + (4 * m / hbar ^ 2) * gaussianMatterPotential σ x hbar m
        = einsteinCorrection (gaussianProfile σ x) (gaussianProfile_x σ x)) :
    R ≠ 0 := by
  rw [gaussianRicci_from_identity σ x hbar m hσ hm hhbar R h_identity]
  have hr_pos := gaussianProfile_pos σ x
  have hσ2_pos : 0 < σ ^ 2 := by positivity
  have hr2_pos : 0 < (gaussianProfile σ x) ^ 2 := by positivity
  have h_R_pos : 0 < 2 / (σ ^ 2 * (gaussianProfile σ x) ^ 2) := by
    apply div_pos (by norm_num : (0:ℝ) < 2)
    exact mul_pos hσ2_pos hr2_pos
  linarith

/-! ════════════════════════════════════════════════════════════════════════
    PART 5 — STATUS / FRONTIER.

    Closed in this file:
      ✓ `gaussianProfile`, `gaussianProfile_x`, `gaussianProfile_xx`.
      ✓ Positivity + nonzero of `gaussianProfile`.
      ✓ Closed form of `einsteinCorrection` on the Gaussian.
      ✓ Closed form of the matter potential.
      ✓ **Derived Ricci scalar** `R_σ(x) = 2/(σ²·r²)` (from the identity).
      ✓ Evaluation at the Gaussian peak.
      ✓ **Structural contrast**:  the Gaussian admits NO cancellation
        point (R ≠ 0 everywhere), unlike the polynomial profile.

    Open continuations:
    • Formal σ → ∞ limit theorem (`Filter.Tendsto` quantitative bound).
    • Formal σ → 0 limit theorem.
    • Sech / soliton profile r_σ(x) = sech(x/σ):  another family.
    • Identification of the family-level prediction:  for any
      bounded smooth positive profile r(x), R has a specific form
      determined by r and r_x.
    ════════════════════════════════════════════════════════════════════════ -/

end UnifiedTheory.LayerB.LohmillerSlotinePredictionE2
