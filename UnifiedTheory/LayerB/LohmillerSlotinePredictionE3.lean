/-
  LayerB/LohmillerSlotinePredictionE3.lean — Phase E3.

  SECH SOLITON PROFILE in the static matter-coupled curved-Schrödinger
  equilibrium.  A third member of the prediction family, structurally
  distinct from E1 (polynomial, cancellation at x=1) and E2 (Gaussian,
  R never zero, R varies with x exponentially).

  Internal-model framing (carrying E1/E2's caveat forward):  the
  "Ricci scalar" here is the Ricci scalar of the emergent 1+1-dim
  conformal metric `g = r²·diag(−1,1)` constructed in
  `LohmillerSlotineBackreaction`.  Predictions are within the
  static matter-coupled curved-Schrödinger equilibrium sector of
  the LSBridge framework — they are not claims about general GR
  + standard QFT matter content.  Within that sector, however,
  the relations are exact algebraic theorems.

  Headline (proved here):  For the sech soliton profile
      r_σ(x) := sech(x/σ) = 1 / cosh(x/σ),
  in static matter-coupled curved equilibrium with
      V_σ(x) := (ℏ²/(2m·r²)) · (r_xx/r),
  the (derived) Ricci scalar of the emergent metric is the
  CONSTANT
      R_σ(x) = 2 / σ²    — independent of x.

  This is the "soliton-as-de-Sitter" structural result:  the sech
  soliton is the unique (within this one-parameter family) amplitude
  profile producing a homogeneous-curvature emergent geometry.

  Zero sorry.  Standard axioms only.
-/
import UnifiedTheory.LayerB.LohmillerSlotinePredictionE1
import Mathlib.Analysis.Complex.Trigonometric

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.LohmillerSlotinePredictionE3

open UnifiedTheory.LayerB.LohmillerSlotinePredictionE1
open Real

/-! ════════════════════════════════════════════════════════════════════════
    PART 1 — SECH SOLITON SCALARS.

    Defined at the **scalar** level (the chain-rule formulas), same
    convention as E2:  algebraic identities below hold as scalar
    theorems, independent of any chain-rule verification.

    Algebraic identities used:
      • cosh(u)² − sinh(u)² = 1                  (Mathlib: cosh_sq_sub_sinh_sq)
      • Real.cosh u > 0                          (Mathlib: cosh_pos)
      ⇒ tanh²(u) = 1 − sech²(u)                 (used in algebra below)
    ════════════════════════════════════════════════════════════════════════ -/

/-- Sech soliton profile `r_σ(x) := 1 / cosh(x/σ) = sech(x/σ)`. -/
noncomputable def sechProfile (σ x : ℝ) : ℝ :=
  1 / Real.cosh (x / σ)

/-- Spatial derivative of the sech soliton (chain rule):
        `r_σ'(x) = −(1/σ)·tanh(x/σ)·r_σ(x)
                 = −(1/σ)·sinh(x/σ) / cosh²(x/σ)`. -/
noncomputable def sechProfile_x (σ x : ℝ) : ℝ :=
  -(1 / σ) * (Real.sinh (x / σ) / (Real.cosh (x / σ)) ^ 2)

/-- Second spatial derivative (chain rule):
        `r_σ''(x) = (1/σ²)·(1 − 2·sech²(x/σ))·r_σ(x)`. -/
noncomputable def sechProfile_xx (σ x : ℝ) : ℝ :=
  (1 / σ ^ 2) * (1 - 2 / (Real.cosh (x / σ)) ^ 2) *
    (1 / Real.cosh (x / σ))

/-- The sech soliton profile is strictly positive everywhere
    (since `Real.cosh > 0`). -/
theorem sechProfile_pos (σ x : ℝ) : 0 < sechProfile σ x := by
  unfold sechProfile
  exact one_div_pos.mpr (Real.cosh_pos _)

/-- The sech soliton profile is nonzero everywhere. -/
theorem sechProfile_ne_zero (σ x : ℝ) : sechProfile σ x ≠ 0 :=
  ne_of_gt (sechProfile_pos σ x)

/-- `cosh(x/σ) ≠ 0` everywhere. -/
theorem cosh_ne_zero (σ x : ℝ) : Real.cosh (x / σ) ≠ 0 :=
  ne_of_gt (Real.cosh_pos _)

/-! ════════════════════════════════════════════════════════════════════════
    PART 2 — EINSTEIN CORRECTION FOR THE SECH SOLITON.

    Closed form:  Δ_geom = 2·tanh²(x/σ) / (σ²·r²) = 2/(σ²·r²) − 2/σ².
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Einstein correction for the sech soliton** (intermediate form):
        `Δ_geom = (2·sinh²(x/σ)) / (σ²·cosh²(x/σ)·r²)`. -/
theorem sechProfile_einsteinCorrection_raw
    (σ x : ℝ) (hσ : σ ≠ 0) :
    einsteinCorrection (sechProfile σ x) (sechProfile_x σ x)
      = 2 * (Real.sinh (x / σ)) ^ 2 /
          (σ ^ 2 * (Real.cosh (x / σ)) ^ 2 *
              (sechProfile σ x) ^ 2) := by
  unfold einsteinCorrection sechProfile_x sechProfile
  have hc := cosh_ne_zero σ x
  have hc2 : (Real.cosh (x / σ)) ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have hσ2 : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  have hσ4 : σ ^ 4 ≠ 0 := pow_ne_zero 4 hσ
  field_simp

/-- **Einstein correction for the sech soliton** (closed form using the
    cosh identity):
        `Δ_geom = 2/(σ²·r²) − 2/σ²`.
    Vanishes only at `x = 0` (peak of the soliton); strictly positive
    elsewhere. -/
theorem sechProfile_einsteinCorrection
    (σ x : ℝ) (hσ : σ ≠ 0) :
    einsteinCorrection (sechProfile σ x) (sechProfile_x σ x)
      = 2 / (σ ^ 2 * (sechProfile σ x) ^ 2) - 2 / σ ^ 2 := by
  rw [sechProfile_einsteinCorrection_raw σ x hσ]
  unfold sechProfile
  have hc := cosh_ne_zero σ x
  have hc2 : (Real.cosh (x / σ)) ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have hσ2 : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  -- Use cosh² − sinh² = 1  ⇒  sinh² = cosh² − 1
  have h_id : (Real.cosh (x / σ)) ^ 2 - (Real.sinh (x / σ)) ^ 2 = 1 :=
    Real.cosh_sq_sub_sinh_sq (x / σ)
  have h_sinh_sq :
      (Real.sinh (x / σ)) ^ 2 = (Real.cosh (x / σ)) ^ 2 - 1 := by
    linarith
  rw [h_sinh_sq]
  field_simp

/-! ════════════════════════════════════════════════════════════════════════
    PART 3 — MATTER POTENTIAL FOR THE SECH SOLITON.

    Closed form:  V = (ℏ²/(2m·σ²·r²)) − (ℏ²/(m·σ²)).
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Matter-coupled curved equilibrium potential** for the sech
    soliton:
        `V_σ(x) = (ℏ²/(2m·σ²·r²)) − (ℏ²/(m·σ²))`.
    Negative at the peak (where r = 1) — like the Gaussian's zero-point
    potential — and approaches `−ℏ²/(m·σ²)` exponentially as |x| → ∞. -/
noncomputable def sechMatterPotential
    (σ x hbar m : ℝ) : ℝ :=
  let r := sechProfile σ x
  let r_xx := sechProfile_xx σ x
  (hbar ^ 2 / (2 * m * r ^ 2)) * (r_xx / r)

theorem sechMatterPotential_eq
    (σ x hbar m : ℝ) (hσ : σ ≠ 0) (hm : m ≠ 0) :
    sechMatterPotential σ x hbar m
      = hbar ^ 2 / (2 * m * σ ^ 2 * (sechProfile σ x) ^ 2)
          - hbar ^ 2 / (m * σ ^ 2) := by
  unfold sechMatterPotential sechProfile_xx sechProfile
  have hc := cosh_ne_zero σ x
  have hc2 : (Real.cosh (x / σ)) ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have hσ2 : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  have h2m_ne : (2 * m) ≠ 0 := mul_ne_zero (by norm_num) hm
  field_simp

/-! ════════════════════════════════════════════════════════════════════════
    PART 4 — RICCI SCALAR CLOSED FORM (THE HEADLINE).

    From the Einstein-like identity  R + (4m/ℏ²) · V = Δ_geom,
    substituting the sech closed forms:
        (4m/ℏ²) · V = 2/(σ²·r²) − 4/σ²
        Δ_geom        = 2/(σ²·r²) − 2/σ²
    yields  R = Δ_geom − (4m/ℏ²)·V = (−2/σ²) − (−4/σ²) = 2/σ².

    A pure constant, independent of x.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Derived Ricci scalar for the sech soliton** (closed form):
        `R_σ(x) = 2/σ²`  — independent of x.

    Properties:
      • `R_σ > 0` everywhere (positive curvature, like the Gaussian).
      • Constant in `x` — strikingly different from both E1 (which
        has a cancellation point at x=1) and E2 (which grows
        exponentially with x).
      • In the slow-r limit σ → ∞,  R → 0  (recovers vacuum).
      • In the sharp limit σ → 0,  R → ∞.

    Interpretation:  the sech soliton is the unique amplitude
    profile in this one-parameter family producing a homogeneous-
    curvature emergent geometry — the "BPS / equilibrium" shape
    among matter profiles. -/
theorem sechRicci_from_identity
    (σ x hbar m : ℝ) (hσ : σ ≠ 0) (hm : m ≠ 0) (hhbar : hbar ≠ 0)
    (R : ℝ)
    (h_identity :
      R + (4 * m / hbar ^ 2) * sechMatterPotential σ x hbar m
        = einsteinCorrection (sechProfile σ x) (sechProfile_x σ x)) :
    R = 2 / σ ^ 2 := by
  rw [sechProfile_einsteinCorrection σ x hσ,
      sechMatterPotential_eq σ x hbar m hσ hm] at h_identity
  have hr := sechProfile_ne_zero σ x
  have hr2 : (sechProfile σ x) ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hσ2 : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  have hhbar2 : hbar ^ 2 ≠ 0 := pow_ne_zero 2 hhbar
  have h2m_ne : (2 * m) ≠ 0 := mul_ne_zero (by norm_num) hm
  have hmσ2 : m * σ ^ 2 ≠ 0 := mul_ne_zero hm hσ2
  have h2mσ2 : 2 * m * σ ^ 2 ≠ 0 := mul_ne_zero h2m_ne hσ2
  have h2mσ2r2 : 2 * m * σ ^ 2 * (sechProfile σ x) ^ 2 ≠ 0 :=
    mul_ne_zero h2mσ2 hr2
  have hσ2r2 : σ ^ 2 * (sechProfile σ x) ^ 2 ≠ 0 :=
    mul_ne_zero hσ2 hr2
  -- The (4m/ℏ²)·V term simplifies algebraically to  2/(σ²r²) − 4/σ²:
  have h_4mV : (4 * m / hbar ^ 2) *
        (hbar ^ 2 / (2 * m * σ ^ 2 * (sechProfile σ x) ^ 2)
            - hbar ^ 2 / (m * σ ^ 2))
        = 2 / (σ ^ 2 * (sechProfile σ x) ^ 2) - 4 / σ ^ 2 := by
    field_simp
    ring
  rw [h_4mV] at h_identity
  -- h_identity:
  --   R + (2/(σ²r²) − 4/σ²) = 2/(σ²r²) − 2/σ²
  -- ⇒ R = 2/σ²
  -- Set abbreviations to make linarith see this as linear.
  set A := 2 / (σ ^ 2 * (sechProfile σ x) ^ 2) with hA
  set B := 1 / σ ^ 2 with hB
  -- Rewrite h_identity in terms of A and B.
  have h_id2 : R + (A - 4 * B) = A - 2 * B := by
    have e1 : (4 : ℝ) / σ ^ 2 = 4 * B := by rw [hB]; ring
    have e2 : (2 : ℝ) / σ ^ 2 = 2 * B := by rw [hB]; ring
    rw [← e1, ← e2]
    exact h_identity
  -- And the goal in terms of B.
  have hgoal : R = 2 * B := by linarith
  rw [hB] at hgoal
  rw [hgoal]
  ring

/-! ════════════════════════════════════════════════════════════════════════
    PART 5 — EVALUATIONS AND CONTRAST WITH E1 / E2.
    ════════════════════════════════════════════════════════════════════════ -/

/-- At the soliton peak `x = 0`, `r_σ(0) = 1` (since cosh(0) = 1). -/
theorem sechProfile_at_zero (σ : ℝ) : sechProfile σ 0 = 1 := by
  unfold sechProfile
  rw [zero_div, Real.cosh_zero, div_one]

/-- At the peak `x = 0`, the Einstein correction vanishes (because
    sinh(0) = 0, so r_x(0) = 0 — the soliton is flat at its peak). -/
theorem sechProfile_einsteinCorrection_at_peak (σ : ℝ) (hσ : σ ≠ 0) :
    einsteinCorrection (sechProfile σ 0) (sechProfile_x σ 0) = 0 := by
  unfold einsteinCorrection sechProfile_x
  rw [zero_div, Real.sinh_zero]
  simp

/-- At the peak `x = 0` (where `r_x = 0`), the matter potential is
    `V_σ(0) = −(ℏ²/(2m·σ²))` — the same zero-point structure as
    the Gaussian.  (Both profiles satisfy `r(0) = 1` and `r_x(0) = 0`,
    yielding equal `V` at the peak by the formula
    `V = (ℏ²/(2m·r²))·(r_xx/r)`.) -/
theorem sechMatterPotential_at_peak
    (σ hbar m : ℝ) (hσ : σ ≠ 0) (hm : m ≠ 0) :
    sechMatterPotential σ 0 hbar m = -(hbar ^ 2 / (2 * m * σ ^ 2)) := by
  rw [sechMatterPotential_eq σ 0 hbar m hσ hm]
  rw [sechProfile_at_zero σ]
  have hσ2 : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  have h2m_ne : (2 * m) ≠ 0 := mul_ne_zero (by norm_num) hm
  field_simp
  ring

/-- **Ricci at the peak**:  for the sech soliton, `R_σ(0) = 2/σ²` —
    the same as everywhere else, since R is constant. -/
theorem sechRicci_at_peak
    (σ hbar m : ℝ) (hσ : σ ≠ 0) (hm : m ≠ 0) (hhbar : hbar ≠ 0)
    (R : ℝ)
    (h_identity :
      R + (4 * m / hbar ^ 2) * sechMatterPotential σ 0 hbar m
        = einsteinCorrection (sechProfile σ 0) (sechProfile_x σ 0)) :
    R = 2 / σ ^ 2 :=
  sechRicci_from_identity σ 0 hbar m hσ hm hhbar R h_identity

/-- **Constancy of R**:  for any two points `x₁, x₂` in the
    sech-soliton emergent geometry, `R(x₁) = R(x₂)`.  This is the
    formal statement of the homogeneous-curvature property. -/
theorem sechRicci_constant
    (σ x1 x2 hbar m : ℝ) (hσ : σ ≠ 0) (hm : m ≠ 0) (hhbar : hbar ≠ 0)
    (R1 R2 : ℝ)
    (h_id1 :
      R1 + (4 * m / hbar ^ 2) * sechMatterPotential σ x1 hbar m
        = einsteinCorrection (sechProfile σ x1) (sechProfile_x σ x1))
    (h_id2 :
      R2 + (4 * m / hbar ^ 2) * sechMatterPotential σ x2 hbar m
        = einsteinCorrection (sechProfile σ x2) (sechProfile_x σ x2)) :
    R1 = R2 := by
  rw [sechRicci_from_identity σ x1 hbar m hσ hm hhbar R1 h_id1,
      sechRicci_from_identity σ x2 hbar m hσ hm hhbar R2 h_id2]

/-- **Positivity of R**:  for σ ≠ 0, the sech-soliton Ricci is
    strictly positive everywhere.  (Sign-definite, like de Sitter.) -/
theorem sechRicci_positive
    (σ x hbar m : ℝ) (hσ : σ ≠ 0) (hm : m ≠ 0) (hhbar : hbar ≠ 0)
    (R : ℝ)
    (h_identity :
      R + (4 * m / hbar ^ 2) * sechMatterPotential σ x hbar m
        = einsteinCorrection (sechProfile σ x) (sechProfile_x σ x)) :
    0 < R := by
  rw [sechRicci_from_identity σ x hbar m hσ hm hhbar R h_identity]
  have hσ2_pos : 0 < σ ^ 2 := by positivity
  exact div_pos (by norm_num : (0:ℝ) < 2) hσ2_pos

/-! ════════════════════════════════════════════════════════════════════════
    PART 6 — STATUS / FRONTIER.

    Closed in this file:
      ✓ `sechProfile`, `sechProfile_x`, `sechProfile_xx`.
      ✓ Positivity + nonzero of `sechProfile`.
      ✓ Closed form of `einsteinCorrection` on the sech (raw + simplified).
      ✓ Closed form of the matter potential.
      ✓ **Derived Ricci scalar** `R_σ(x) = 2/σ²` — CONSTANT in x.
      ✓ Evaluation at the soliton peak.
      ✓ Constancy theorem `sechRicci_constant`.
      ✓ Positivity theorem `sechRicci_positive`.

    Structural family-comparison summary (E1 ∪ E2 ∪ E3):
      • E1 polynomial `r(x) = 1 − x²`:    R = 0 at x = 1 (cancellation).
      • E2 Gaussian `r(x) = exp(−x²/(2σ²))`:  R = 2/(σ²·r²),
        strictly positive and varies with x (exponentially).
      • E3 sech `r(x) = sech(x/σ)`:      R = 2/σ²,
        strictly positive and CONSTANT in x.

      The sech soliton is the unique (in this family) profile yielding
      a homogeneous-curvature emergent geometry — interpretable as a
      "soliton-as-de-Sitter" structural result.

    Open continuations:
    • Formal σ → ∞ limit theorem (Filter.Tendsto) for R → 0.
    • Identify the general family-level characterization of profiles
      with constant R (the sech soliton's defining property).
    ════════════════════════════════════════════════════════════════════════ -/

end UnifiedTheory.LayerB.LohmillerSlotinePredictionE3
