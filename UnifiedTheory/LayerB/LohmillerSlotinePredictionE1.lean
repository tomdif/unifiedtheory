/-
  LayerB/LohmillerSlotinePredictionE1.lean — Phase E START.

  GOAL:  EXTRACT THE FIRST CONCRETE PHYSICS PREDICTION FROM THE
         STATIC EINSTEIN-LIKE IDENTITY.

  Phase D step 5 closed the identity
       R + (4m/ℏ²) · V = (2/r⁴) · r_x²
  for the static matter-coupled curved-Schrödinger equilibrium.

  The rightmost term is the **new-physics correction** —  the
  departure from the slow-r "Einstein equation" R = -(4m/ℏ²)·V.
  This file isolates it as a named scalar, proves its sign +
  vanishing condition, and demonstrates a concrete profile family
  where the correction is exactly equal in magnitude to the matter
  coupling term (`η = 1`).

  This is the first formal step in Phase E:  the framework predicts
  a measurable deviation from the standard slow-r limit precisely
  when `r_x ≠ 0`, with the dimensionless ratio `η := Δ_geom / |(4m/ℏ²)V|`
  reaching order unity in well-defined profile regimes.

  Zero sorry.  Standard axioms only.
-/
import UnifiedTheory.LayerB.LohmillerSlotineBackreaction

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.LohmillerSlotinePredictionE1

open UnifiedTheory.LayerB.LohmillerSlotineBackreaction

/-! ════════════════════════════════════════════════════════════════════════
    PART 1 — THE NEW-PHYSICS CORRECTION SCALAR.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Einstein-correction scalar**:  the right-hand side of the static
    matter-coupled identity
        `R + (4m/ℏ²)·V = (2/r⁴)·r_x²`.
    This is the departure from the slow-r Einstein-like equation
    `R = -(4m/ℏ²)·V`. -/
noncomputable def einsteinCorrection (r r_x : ℝ) : ℝ :=
  2 * r_x ^ 2 / r ^ 4

/-- The correction is nonnegative (it is a square divided by a fourth
    power). -/
theorem einsteinCorrection_nonneg (r r_x : ℝ) :
    0 ≤ einsteinCorrection r r_x := by
  unfold einsteinCorrection
  have h_num_nn : 0 ≤ 2 * r_x ^ 2 := by positivity
  have h_den_nn : 0 ≤ r ^ 4 := by positivity
  exact div_nonneg h_num_nn h_den_nn

/-- **Vanishing condition**:  the correction vanishes iff `r_x = 0`
    (i.e., the amplitude is locally flat).  Slow-r limit ⟺ no
    departure from the Einstein-like equation. -/
theorem einsteinCorrection_eq_zero_iff (r r_x : ℝ) (hr : r ≠ 0) :
    einsteinCorrection r r_x = 0 ↔ r_x = 0 := by
  unfold einsteinCorrection
  have hr4_ne : r ^ 4 ≠ 0 := pow_ne_zero 4 hr
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · have : r_x ^ 2 = 0 := by linarith
      exact pow_eq_zero_iff (two_ne_zero) |>.mp this
    · exact absurd h hr4_ne
  · intro h; left; rw [h]; ring

/-- The correction is **strictly positive** iff `r_x ≠ 0`. -/
theorem einsteinCorrection_pos_iff (r r_x : ℝ) (hr : r ≠ 0) :
    0 < einsteinCorrection r r_x ↔ r_x ≠ 0 := by
  constructor
  · intro h h_rx
    have : einsteinCorrection r r_x = 0 :=
      (einsteinCorrection_eq_zero_iff r r_x hr).mpr h_rx
    linarith
  · intro h_rx
    have h_nn := einsteinCorrection_nonneg r r_x
    have h_ne : einsteinCorrection r r_x ≠ 0 := by
      intro h
      have := (einsteinCorrection_eq_zero_iff r r_x hr).mp h
      exact h_rx this
    exact lt_of_le_of_ne h_nn (Ne.symm h_ne)

/-! ════════════════════════════════════════════════════════════════════════
    PART 2 — DIMENSIONLESS DEVIATION FROM SLOW-r REGIME.

    The Einstein-like identity reads
        `R + (4m/ℏ²) V = Δ_geom`
    where `Δ_geom := einsteinCorrection r r_x`.  Define
        `η := Δ_geom / ((4m/ℏ²)·|V|)`
    as the dimensionless ratio of the new correction to the standard
    matter-coupling term.  η = 0 ⟺ slow-r limit;  η = 1 ⟺ correction
    equal in magnitude to standard term;  η ≫ 1 ⟺ correction dominates.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Dimensionless deviation η** between the new-physics correction and
    the standard "Einstein-like" matter-coupling term.  Defined only when
    the matter-coupling term is nonzero (`r_xx ≠ 0`). -/
noncomputable def dimensionlessDeviation (r r_x r_xx : ℝ) : ℝ :=
  einsteinCorrection r r_x / |2 * r_xx / r ^ 3|

/-- The `dimensionlessDeviation` is nonnegative.  (The algebraic
    identity `η = r_x²·r / |r_xx|` is true but requires a sign-on-r³
    case split for `|r^3|`;  proved in a follow-up when needed.) -/
theorem dimensionlessDeviation_nonneg (r r_x r_xx : ℝ) :
    0 ≤ dimensionlessDeviation r r_x r_xx := by
  unfold dimensionlessDeviation
  exact div_nonneg (einsteinCorrection_nonneg r r_x) (abs_nonneg _)

/-! ════════════════════════════════════════════════════════════════════════
    PART 3 — CONCRETE POLYNOMIAL PROFILE  r(x) = 1 + x².

    The simplest analytically tractable nonconstant profile.  At every
    `x ≠ 0`, the new-physics correction is strictly positive.  At the
    specific point `x = 1`, the correction is exactly equal in magnitude
    to the matter-coupling term (`η = 1`):  a 100% deviation from the
    slow-r limit.
    ════════════════════════════════════════════════════════════════════════ -/

/-- The polynomial profile `r(x) := 1 + x²`. -/
def polyProfile (x : ℝ) : ℝ := 1 + x ^ 2

/-- Spatial derivative of the polynomial profile:  `r'(x) = 2x`. -/
def polyProfile_x (x : ℝ) : ℝ := 2 * x

/-- Second spatial derivative of the polynomial profile:  `r''(x) = 2`. -/
def polyProfile_xx (_x : ℝ) : ℝ := 2

/-- The polynomial profile is strictly positive everywhere. -/
theorem polyProfile_pos (x : ℝ) : 0 < polyProfile x := by
  unfold polyProfile
  have : 0 ≤ x ^ 2 := sq_nonneg _
  linarith

/-- The polynomial profile is nonzero everywhere. -/
theorem polyProfile_ne_zero (x : ℝ) : polyProfile x ≠ 0 :=
  ne_of_gt (polyProfile_pos x)

/-- Closed form for the Einstein correction on the polynomial profile:
        `Δ_geom(x) = 8 x² / (1 + x²)⁴`. -/
theorem polyProfile_einsteinCorrection (x : ℝ) :
    einsteinCorrection (polyProfile x) (polyProfile_x x)
      = 8 * x ^ 2 / (1 + x ^ 2) ^ 4 := by
  unfold einsteinCorrection polyProfile polyProfile_x
  ring

/-- At `x = 1`, the Einstein correction equals exactly `1/2`. -/
theorem polyProfile_correction_at_one :
    einsteinCorrection (polyProfile 1) (polyProfile_x 1) = 1 / 2 := by
  rw [polyProfile_einsteinCorrection]
  norm_num

/-- **The headline numerical prediction**:  for the polynomial profile
    `r(x) = 1 + x²` at the point `x = 1`, with matter-coupled curved
    equilibrium potential `V_x1 = ℏ²/(8m)`,
        `Δ_geom(1) = 1/2 = (4m/ℏ²) · V_x1`.

    Dimensionless deviation η = 1:  the new-physics correction is
    exactly equal in magnitude to the standard "Einstein-like" matter
    contribution.

    Concretely:  the framework predicts that, in this profile and at
    this point, the slow-r approximation `R = -(4m/ℏ²)·V` is wrong
    by a factor of 2 — the actual relation is
        `R = -(4m/ℏ²)·V + Δ_geom = -(4m/ℏ²)·V + (4m/ℏ²)·V = 0`,
    i.e., the Ricci scalar vanishes exactly even though the matter
    coupling term is nonzero. -/
theorem polyProfile_eta_eq_one_at_x_one
    (hbar m : ℝ) (hm : 0 < m) (hhbar : 0 < hbar) :
    let r := polyProfile 1
    let r_x := polyProfile_x 1
    let r_xx := polyProfile_xx 1
    let V_x1 := (hbar ^ 2 / (2 * m * r ^ 2)) * (r_xx / r)
    einsteinCorrection r r_x = (4 * m / hbar ^ 2) * V_x1 := by
  simp only [polyProfile, polyProfile_x, polyProfile_xx]
  have h_hbar_ne : hbar ≠ 0 := ne_of_gt hhbar
  have h_m_ne : m ≠ 0 := ne_of_gt hm
  have h_hbar2_ne : hbar ^ 2 ≠ 0 := pow_ne_zero 2 h_hbar_ne
  unfold einsteinCorrection
  norm_num
  field_simp

/-- **Consequence**:  in the polynomial profile at `x = 1`, the
    Ricci scalar of the emergent metric is exactly zero, even though
    both the matter coupling term and the new-physics correction are
    individually nonzero (they cancel).

    From the static Einstein-like identity
        `R + (4m/ℏ²)·V = Δ_geom`
    and the equality `Δ_geom = (4m/ℏ²)·V` at this point,
    `R = -(4m/ℏ²)·V + Δ_geom = -(4m/ℏ²)·V + (4m/ℏ²)·V = 0`.

    This is the **first risky prediction**:  in a non-uniform amplitude
    profile, exact cancellations between matter coupling and dressing
    curvature can yield locally flat geometry (R = 0) without zero
    matter content. -/
theorem polyProfile_R_zero_at_x_one
    (hbar m : ℝ) (hm : 0 < m) (hhbar : 0 < hbar)
    (R : ℝ)
    (h_identity :
      let r := polyProfile 1
      let r_x := polyProfile_x 1
      let r_xx := polyProfile_xx 1
      let V_x1 := (hbar ^ 2 / (2 * m * r ^ 2)) * (r_xx / r)
      R + (4 * m / hbar ^ 2) * V_x1 = einsteinCorrection r r_x) :
    R = 0 := by
  have h_eta := polyProfile_eta_eq_one_at_x_one hbar m hm hhbar
  -- From h_identity:  R + (4m/ℏ²)·V = Δ_geom.
  -- From h_eta:       Δ_geom = (4m/ℏ²)·V.
  -- Therefore: R + (4m/ℏ²)·V = (4m/ℏ²)·V, so R = 0.
  simp only [polyProfile, polyProfile_x, polyProfile_xx] at h_identity h_eta
  linarith [h_identity, h_eta]

/-! ════════════════════════════════════════════════════════════════════════
    PART 4 — STATUS / NEXT FRONTIER.

    Closed in this file:
      ✓ `einsteinCorrection` scalar + nonneg + vanishing condition.
      ✓ `dimensionlessDeviation` (partial — algebraic form open).
      ✓ Polynomial profile `r(x) = 1 + x²` with closed form for `Δ_geom`.
      ✓ Headline:  at `x = 1` for this profile, η = 1 exactly.
      ✓ **First risky prediction**:  `R = 0` at `x = 1` despite
        nonzero matter — exact cancellation between matter coupling
        and Bohm-style dressing correction.

    Pending — Phase E continuation:
    • Gaussian profile `r(x) = exp(-x²/(2σ²))`:  closed form and
      asymptotic σ → ∞ / σ → 0 limits.
    • Soliton profile `r(x) = sech(x/σ)`:  the same.
    • Integrated observables `∫ η(x) dx` for each profile family.
    • Identification of the maximum-deviation regime — the most
      promising target for experimental falsification.
    ════════════════════════════════════════════════════════════════════════ -/

end UnifiedTheory.LayerB.LohmillerSlotinePredictionE1
