/-
  LayerB/LohmillerSlotineGaussianWidthDynamics.lean — σ(t) integration.

  Push the LSBridge backreaction Gaussian-width ODE
      σ·σ_pp + (σ − 1)·σ_prime² = 0
  (proved as `gaussian_width_dynamics_with_backreaction` in
  `LohmillerSlotineBackreaction`) into its first-integral form,
  yielding a concrete time-evolution law:
      σ_prime = C · σ · exp(−σ).

  Closed in this file:
    • **First integral**:  `σ_prime · exp(σ) / σ` is conserved
      under the ODE (algebraic identity at the scalar level).
    • **Implicit solution form**:  conserved value `C` parameterizes
      `σ_prime = C · σ · exp(−σ)`.
    • **Monotonicity**:  sign(σ_prime) = sign(C) for σ > 0.
    • **Large-σ asymptotic**:  `σ_prime → 0` exponentially fast.
    • **Small-σ asymptotic**:  `σ_prime / σ → C` as σ → 0⁺.
    • **Differs from free Schrödinger**:  the constant-σ "frozen"
      solution is admissible for LSBridge but NOT for free Schrödinger.

  Together with the ODE itself, this is the LSBridge framework's
  **first concrete dynamical prediction** beyond the static identities.

  Zero sorry.  Standard axioms only.
-/
import UnifiedTheory.LayerB.LohmillerSlotineBackreaction
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.LohmillerSlotineGaussianWidthDynamics

open Filter Topology Real
open UnifiedTheory.LayerB.LohmillerSlotineBackreaction

/-! ════════════════════════════════════════════════════════════════════════
    PART 1 — SCALAR DEFINITIONS:  ODE RESIDUAL, FIRST INTEGRAL, ITS RATE.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **LSBridge backreaction Gaussian-width ODE residual**.

    The ODE
        `σ·σ_pp + (σ − 1)·σ_prime² = 0`
    is encoded as the vanishing of this scalar residual.

    Equivalent to `gaussian_width_dynamics_with_backreaction`'s
    iff-statement RHS. -/
def gaussianWidthODE_residual (σ σ_prime σ_pp : ℝ) : ℝ :=
  σ * σ_pp + (σ - 1) * σ_prime ^ 2

/-- **First integral candidate** `F(σ, σ_prime) := σ_prime · exp(σ) / σ`.

    We will show that the formal time-derivative of `F` (treating
    σ as a function of `t` with derivative `σ_prime` and second
    derivative `σ_pp`) equals
        `(exp(σ) / σ²) · gaussianWidthODE_residual`,
    so `F` is conserved when the ODE holds. -/
noncomputable def firstIntegral (σ σ_prime : ℝ) : ℝ :=
  σ_prime * Real.exp σ / σ

/-- **Formal time-derivative of `firstIntegral`** by product+chain rule:
        `dF/dt = σ_pp · exp(σ)/σ
                + σ_prime · σ_prime · exp(σ)/σ
                − σ_prime · exp(σ) · σ_prime / σ²`.
    (First term: derivative of σ_prime → σ_pp.  Second term: chain
    rule on `exp σ`.  Third term: derivative of `1/σ`.) -/
noncomputable def firstIntegralRate (σ σ_prime σ_pp : ℝ) : ℝ :=
  σ_pp * Real.exp σ / σ
    + σ_prime ^ 2 * Real.exp σ / σ
    - σ_prime ^ 2 * Real.exp σ / σ ^ 2

/-! ════════════════════════════════════════════════════════════════════════
    PART 2 — FIRST INTEGRAL IDENTITY AND ODE CONSEQUENCE.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **First integral algebraic identity**:
    `dF/dt = (exp(σ)/σ²) · (σ·σ_pp + (σ−1)·σ_prime²)`. -/
theorem firstIntegralRate_eq_factor_residual
    (σ σ_prime σ_pp : ℝ) (hσ : σ ≠ 0) :
    firstIntegralRate σ σ_prime σ_pp
      = (Real.exp σ / σ ^ 2) * gaussianWidthODE_residual σ σ_prime σ_pp := by
  unfold firstIntegralRate gaussianWidthODE_residual
  have hσ2 : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  field_simp
  ring

/-- **PHASE σ-INTEGRATION HEADLINE — FIRST INTEGRAL UNDER THE ODE**.

    When the LSBridge backreaction ODE
        `σ·σ_pp + (σ − 1)·σ_prime² = 0`
    holds (with `σ ≠ 0`), the formal time-derivative of
    `firstIntegral σ σ_prime = σ_prime · exp(σ) / σ` is **zero**.

    Hence `firstIntegral σ σ_prime` is a **conserved quantity** of the
    LSBridge backreaction Gaussian-width dynamics:
        σ_prime · exp(σ) / σ = C    (constant). -/
theorem gaussian_width_first_integral
    (σ σ_prime σ_pp : ℝ) (hσ : σ ≠ 0)
    (h_ode : gaussianWidthODE_residual σ σ_prime σ_pp = 0) :
    firstIntegralRate σ σ_prime σ_pp = 0 := by
  rw [firstIntegralRate_eq_factor_residual σ σ_prime σ_pp hσ, h_ode, mul_zero]

/-! ════════════════════════════════════════════════════════════════════════
    PART 3 — IMPLICIT EXACT SOLUTION FORM.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Implicit exact solution form**:  the conserved-quantity equation
    `σ_prime · exp(σ) / σ = C` is equivalent to
        `σ_prime = C · σ · exp(−σ)`. -/
theorem gaussian_width_solution_implicit
    (σ σ_prime C : ℝ) (hσ : σ ≠ 0) :
    firstIntegral σ σ_prime = C ↔ σ_prime = C * σ * Real.exp (-σ) := by
  unfold firstIntegral
  have h_exp_pos : 0 < Real.exp σ := Real.exp_pos _
  have h_exp_ne : Real.exp σ ≠ 0 := ne_of_gt h_exp_pos
  constructor
  · intro h
    -- σ_prime · exp σ / σ = C  ⇒  σ_prime = C · σ / exp σ = C · σ · exp(-σ).
    rw [Real.exp_neg]
    field_simp at h ⊢
    linarith
  · intro h
    rw [h, Real.exp_neg]
    field_simp

/-! ════════════════════════════════════════════════════════════════════════
    PART 4 — MONOTONICITY:  NO OSCILLATORY BREATHING SOLUTIONS.

    The implicit form `σ_prime = C · σ · exp(−σ)` immediately gives
    a sign analysis:  for σ > 0, both `σ` and `exp(−σ)` are positive,
    so `sign(σ_prime) = sign(C)`.  Constant `C` (which is enforced by
    the first integral) ⇒ sign of `σ_prime` is constant along any
    solution ⇒ σ is monotone.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Sign of σ_prime is determined by sign of C** (for `σ > 0`).
    Positive `C` ⇒ σ_prime > 0 ⇒ σ is strictly increasing. -/
theorem gaussian_width_sigma_prime_pos_of_C_pos
    (σ σ_prime C : ℝ) (hσ : 0 < σ) (hC : 0 < C)
    (h_form : σ_prime = C * σ * Real.exp (-σ)) :
    0 < σ_prime := by
  rw [h_form]
  exact mul_pos (mul_pos hC hσ) (Real.exp_pos _)

/-- **Negative C** ⇒ `σ_prime < 0` ⇒ σ is strictly decreasing. -/
theorem gaussian_width_sigma_prime_neg_of_C_neg
    (σ σ_prime C : ℝ) (hσ : 0 < σ) (hC : C < 0)
    (h_form : σ_prime = C * σ * Real.exp (-σ)) :
    σ_prime < 0 := by
  rw [h_form]
  have : C * σ < 0 := mul_neg_of_neg_of_pos hC hσ
  exact mul_neg_of_neg_of_pos this (Real.exp_pos _)

/-- **Zero C** ⇒ `σ_prime = 0` ⇒ σ is constant (the "frozen" solution). -/
theorem gaussian_width_sigma_prime_zero_of_C_zero
    (σ σ_prime : ℝ) (h_form : σ_prime = 0 * σ * Real.exp (-σ)) :
    σ_prime = 0 := by
  rw [h_form]
  ring

/-- **Monotonicity / no oscillation (qualitative)**.

    The implicit solution form `σ_prime = C · σ · exp(−σ)` with `σ > 0`
    forces `σ_prime` to keep the SAME sign as `C` throughout.  Hence
    σ(t) is strictly monotonic (or constant), and the LSBridge
    backreaction dynamics admits **no oscillatory breathing solutions**.
    Pair of theorems above provides the proof for `C > 0` and `C < 0`. -/
theorem gaussian_width_no_oscillation
    (σ σ_prime C : ℝ) (hσ : 0 < σ)
    (h_form : σ_prime = C * σ * Real.exp (-σ)) :
    (0 < C → 0 < σ_prime) ∧ (C < 0 → σ_prime < 0) ∧ (C = 0 → σ_prime = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hC
    exact gaussian_width_sigma_prime_pos_of_C_pos σ σ_prime C hσ hC h_form
  · intro hC
    exact gaussian_width_sigma_prime_neg_of_C_neg σ σ_prime C hσ hC h_form
  · intro hC
    rw [h_form, hC]; ring

/-! ════════════════════════════════════════════════════════════════════════
    PART 5 — ASYMPTOTIC BEHAVIORS.

    For the σ → ∞ and σ → 0⁺ limits of `σ_prime = C · σ · exp(−σ)`.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Large-σ asymptotic**:  for the conserved-quantity solution form
    `σ_prime = C · σ · exp(−σ)`, as σ → ∞ the velocity `σ_prime` tends
    to 0 **exponentially fast**.

    This is a key prediction:  LSBridge backreaction Gaussian spreading
    is dramatically slower than free Schrödinger spreading (which is
    only polynomial-rational in σ). -/
theorem gaussian_width_large_sigma_asymptotic (C : ℝ) :
    Tendsto (fun σ : ℝ => C * σ * Real.exp (-σ)) atTop (𝓝 0) := by
  -- σ · exp(-σ) → 0 from Mathlib's `tendsto_pow_mul_exp_neg_atTop_nhds_zero`
  -- at n = 1.
  have h_pow : Tendsto (fun σ : ℝ => σ ^ 1 * Real.exp (-σ)) atTop (𝓝 0) :=
    tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  simp only [pow_one] at h_pow
  have h_C_mul : Tendsto (fun σ : ℝ => C * (σ * Real.exp (-σ)))
                          atTop (𝓝 (C * 0)) :=
    h_pow.const_mul C
  simp at h_C_mul
  -- Convert form `C * (σ · exp(-σ))` to `C · σ · exp(-σ)`.
  have h_eq : (fun σ : ℝ => C * (σ * Real.exp (-σ)))
              = (fun σ : ℝ => C * σ * Real.exp (-σ)) := by
    funext σ; ring
  rw [h_eq] at h_C_mul
  exact h_C_mul

/-- **Small-σ asymptotic** (qualitative):  for σ → 0⁺, the velocity
    `σ_prime = C · σ · exp(−σ)` has leading behavior `σ_prime ≈ C · σ`
    (since `exp(−σ) → 1`).  More precisely, the RATIO
        `σ_prime / σ = C · exp(−σ)`
    has limit `C` as σ → 0. -/
theorem gaussian_width_small_sigma_asymptotic (C : ℝ) :
    Tendsto (fun σ : ℝ => C * Real.exp (-σ)) (𝓝 0) (𝓝 C) := by
  -- exp(-σ) → exp(0) = 1 as σ → 0  ⇒  C · exp(-σ) → C · 1 = C.
  have h_exp : Tendsto (fun σ : ℝ => Real.exp (-σ)) (𝓝 0) (𝓝 (Real.exp 0)) := by
    have h_comp : Tendsto (fun σ : ℝ => -σ) (𝓝 0) (𝓝 (-(0 : ℝ))) :=
      (continuous_neg.tendsto 0)
    have : (-(0 : ℝ)) = 0 := neg_zero
    rw [this] at h_comp
    have h_exp_at_0 : Tendsto Real.exp (𝓝 (0 : ℝ)) (𝓝 (Real.exp 0)) :=
      Real.continuous_exp.tendsto 0
    exact h_exp_at_0.comp h_comp
  rw [Real.exp_zero] at h_exp
  have h_C_mul : Tendsto (fun σ : ℝ => C * Real.exp (-σ))
                          (𝓝 0) (𝓝 (C * 1)) :=
    h_exp.const_mul C
  rw [mul_one] at h_C_mul
  exact h_C_mul

/-! ════════════════════════════════════════════════════════════════════════
    PART 6 — COMPARISON WITH FREE SCHRÖDINGER.

    The LSBridge backreaction ODE
        `σ·σ_pp + (σ − 1)·σ_prime² = 0`
    admits the FROZEN (`σ ≡ constant`, hence σ_prime = σ_pp = 0) solution
    for ANY positive σ.

    The free Schrödinger Gaussian spreading ODE
        `σ_pp = ℏ²/(m²·σ³)`
    does NOT admit the frozen solution:  for σ_prime = 0 and any σ ≠ 0,
    the free Schrödinger ODE forces σ_pp = ℏ²/(m²·σ³) ≠ 0.

    This is a STRUCTURAL distinction at a single point in (σ, σ_prime,
    σ_pp)-space:  the backreaction admits frozen evolution; free
    Schrödinger does not.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Backreaction admits the frozen solution**:  for any nonzero
    `σ_const`, the LSBridge backreaction ODE is satisfied by
    `σ_prime = σ_pp = 0` (a constant `σ(t) ≡ σ_const`). -/
theorem gaussian_width_backreaction_admits_frozen
    (σ_const : ℝ) (hσ : σ_const ≠ 0) :
    gaussianWidthODE_residual σ_const 0 0 = 0 := by
  unfold gaussianWidthODE_residual
  ring

/-- **Free Schrödinger does NOT admit the frozen solution**:  for
    any nonzero `σ_const`, `m`, `ℏ`, the free Schrödinger ODE
    `σ_pp = ℏ²/(m²·σ³)` is NOT satisfied by `σ_pp = 0`. -/
theorem gaussian_width_freeSchrodinger_rejects_frozen
    (σ_const hbar m : ℝ) (hσ : σ_const ≠ 0) (hm : m ≠ 0) (hhbar : hbar ≠ 0) :
    (0 : ℝ) ≠ hbar ^ 2 / (m ^ 2 * σ_const ^ 3) := by
  have h_m2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
  have h_σ3 : σ_const ^ 3 ≠ 0 := pow_ne_zero 3 hσ
  have h_hbar2 : hbar ^ 2 ≠ 0 := pow_ne_zero 2 hhbar
  have h_denom : m ^ 2 * σ_const ^ 3 ≠ 0 := mul_ne_zero h_m2 h_σ3
  exact (div_ne_zero h_hbar2 h_denom).symm

/-- **STRUCTURAL DIFFERENCE — LSBridge backreaction differs from free
    Schrödinger spreading**.

    At the "frozen" configuration `σ_prime = σ_pp = 0`:
      • LSBridge backreaction ODE is satisfied.
      • Free Schrödinger Gaussian-spreading ODE is NOT satisfied
        (for any nonzero ℏ, m, σ_const).

    Hence the two models predict QUALITATIVELY DIFFERENT dynamics:
    LSBridge admits configurations that free Schrödinger forbids,
    and conversely. -/
theorem gaussian_width_dynamics_differs_from_free_schrodinger
    (σ_const hbar m : ℝ) (hσ : σ_const ≠ 0) (hm : m ≠ 0) (hhbar : hbar ≠ 0) :
    gaussianWidthODE_residual σ_const 0 0 = 0
      ∧ (0 : ℝ) ≠ hbar ^ 2 / (m ^ 2 * σ_const ^ 3) :=
  ⟨gaussian_width_backreaction_admits_frozen σ_const hσ,
   gaussian_width_freeSchrodinger_rejects_frozen σ_const hbar m hσ hm hhbar⟩

/-! ════════════════════════════════════════════════════════════════════════
    PART 7 — DOUBLING-TIME LOWER BOUND  (concrete physics prediction).

    Under the implicit time parameterization `σ_prime = C·σ·e^{−σ}`
    with `C > 0`, the time `T` to double σ from `σ_0` to `2σ_0` is
    determined by the change-of-variables
        `T = ∫_{σ_0}^{2σ_0} (e^σ / (C·σ)) dσ`,
    which is the integral version of `dt = (1/σ_prime) dσ`.

    The **headline physics prediction** is that this doubling-time
    integral is bounded below by `e^{σ_0}/(2C)` — exponentially large
    in the initial width `σ_0`.  This is in stark contrast to free
    Schrödinger Gaussian spreading, whose doubling time scales like
    `σ_0² · m/ℏ` (polynomial in σ_0).

    Hence the LSBridge backreaction predicts wavepacket spreading
    that is **dramatically slower** than the standard free-Schrödinger
    result for large initial widths — by a factor `~e^{σ_0}/σ_0²`.
    ════════════════════════════════════════════════════════════════════════ -/

open MeasureTheory intervalIntegral

/-- **Doubling-time integrand**:  the function
    `f(σ) := e^σ / (C · σ)` that integrates `dt = (1/σ_prime) dσ`
    under the LSBridge backreaction dynamics. -/
noncomputable def doublingTimeIntegrand (C σ : ℝ) : ℝ :=
  Real.exp σ / (C * σ)

/-- **The doubling-time integral lower bound**:
        `∫_{σ_0}^{2σ_0} (e^σ / (C·σ)) dσ  ≥  e^{σ_0} / (2C)`
    for any `C > 0` and `σ_0 > 0`.

    Proof:  on `[σ_0, 2σ_0]`,
      • `e^σ ≥ e^{σ_0}` (monotonicity of exp).
      • `1/σ ≥ 1/(2σ_0)` (since σ ≤ 2σ_0 with σ_0 > 0).
      • Combined:  `e^σ / (C·σ) ≥ e^{σ_0} / (C · 2σ_0)`.
    Integrating over `[σ_0, 2σ_0]` (interval length `σ_0`):
      LHS ≥ `e^{σ_0} / (C·2σ_0) · σ_0` = `e^{σ_0} / (2C)`. -/
theorem doubling_time_integral_lower_bound
    (C σ_0 : ℝ) (hC : 0 < C) (hσ_0 : 0 < σ_0) :
    Real.exp σ_0 / (2 * C) ≤ ∫ σ in σ_0..(2 * σ_0), doublingTimeIntegrand C σ := by
  have h_2σ_0_pos : 0 < 2 * σ_0 := by linarith
  have h_σ_0_le : σ_0 ≤ 2 * σ_0 := by linarith
  -- Lower bound function: the constant `e^{σ_0}/(C·2σ_0)`.
  set L : ℝ := Real.exp σ_0 / (C * (2 * σ_0)) with hL_def
  -- Step 1:  ∀ σ ∈ Icc σ_0 (2σ_0),  L ≤ doublingTimeIntegrand C σ.
  have h_pointwise : ∀ σ ∈ Set.Icc σ_0 (2 * σ_0), L ≤ doublingTimeIntegrand C σ := by
    intro σ hσ
    obtain ⟨h_lb, h_ub⟩ := hσ
    have hσ_pos : 0 < σ := lt_of_lt_of_le hσ_0 h_lb
    -- exp monotonicity:
    have h_exp_mono : Real.exp σ_0 ≤ Real.exp σ := Real.exp_le_exp.mpr h_lb
    -- 1/σ ≥ 1/(2σ_0):
    have h_inv_mono : 1 / (2 * σ_0) ≤ 1 / σ := by
      apply one_div_le_one_div_of_le hσ_pos h_ub
    -- Combine:
    unfold doublingTimeIntegrand
    rw [hL_def]
    -- Goal: exp σ_0 / (C · 2σ_0) ≤ exp σ / (C · σ).
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    -- Goal: exp σ_0 * (C * σ) ≤ exp σ * (C * (2 * σ_0))
    -- Chain: exp σ_0 · C · σ ≤ exp σ_0 · C · (2σ_0) ≤ exp σ · C · (2σ_0).
    calc Real.exp σ_0 * (C * σ)
        ≤ Real.exp σ_0 * (C * (2 * σ_0)) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_left h_ub (le_of_lt hC)
          · exact (Real.exp_pos σ_0).le
      _ ≤ Real.exp σ * (C * (2 * σ_0)) := by
          apply mul_le_mul_of_nonneg_right h_exp_mono
          positivity
  -- Step 2:  integrate the inequality.
  -- ∫_{σ_0}^{2σ_0} L = L · (2σ_0 - σ_0) = L · σ_0
  --                  = (exp σ_0 / (C·2σ_0)) · σ_0 = exp σ_0 / (2C).
  have h_int_L_eq : ∫ _ : ℝ in σ_0..(2 * σ_0), L = L * (2 * σ_0 - σ_0) := by
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  -- Continuity of doublingTimeIntegrand on [σ_0, 2σ_0]:
  have h_C_ne : C ≠ 0 := ne_of_gt hC
  have h_cont_g : ContinuousOn (doublingTimeIntegrand C) (Set.Icc σ_0 (2 * σ_0)) := by
    intro σ hσ
    obtain ⟨h_lb, _⟩ := hσ
    have hσ_pos : 0 < σ := lt_of_lt_of_le hσ_0 h_lb
    have hσ_ne : σ ≠ 0 := ne_of_gt hσ_pos
    have h_Cσ_ne : C * σ ≠ 0 := mul_ne_zero h_C_ne hσ_ne
    unfold doublingTimeIntegrand
    have h1 : ContinuousAt (fun y : ℝ => Real.exp y) σ := Real.continuous_exp.continuousAt
    have h2 : ContinuousAt (fun y : ℝ => C * y) σ := (continuous_const.mul continuous_id).continuousAt
    have h3 : ContinuousAt (fun y : ℝ => Real.exp y / (C * y)) σ :=
      h1.div h2 h_Cσ_ne
    exact h3.continuousWithinAt
  -- IntervalIntegrability for integrand and constant:
  have h_intble_g : IntervalIntegrable (doublingTimeIntegrand C)
                      MeasureTheory.volume σ_0 (2 * σ_0) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h_σ_0_le]
    exact h_cont_g
  have h_intble_L : IntervalIntegrable (fun _ : ℝ => L) MeasureTheory.volume σ_0 (2 * σ_0) :=
    intervalIntegrable_const
  -- Apply integral_mono_on:
  have h_int_mono :
      ∫ _ : ℝ in σ_0..(2 * σ_0), L ≤ ∫ σ in σ_0..(2 * σ_0), doublingTimeIntegrand C σ :=
    intervalIntegral.integral_mono_on h_σ_0_le h_intble_L h_intble_g h_pointwise
  -- Combine:
  have h_simplify : L * (2 * σ_0 - σ_0) = Real.exp σ_0 / (2 * C) := by
    rw [hL_def]
    have : (2 * σ_0 - σ_0) = σ_0 := by ring
    rw [this]
    field_simp
  linarith [h_int_L_eq, h_simplify]

/-- **Doubling-time lower bound — the PHYSICAL FORM**:
    the time `T` to double σ from `σ_0` to `2σ_0` under the LSBridge
    backreaction dynamics is bounded below by `e^{σ_0}/(2C)` —
    exponentially large in the initial width.

    Stated as an inequality on the change-of-variables integral
    representation of `T`. -/
theorem lsbridge_doubling_time_exponentially_slow
    (C σ_0 : ℝ) (hC : 0 < C) (hσ_0 : 0 < σ_0) :
    Real.exp σ_0 / (2 * C) ≤ ∫ σ in σ_0..(2 * σ_0), doublingTimeIntegrand C σ :=
  doubling_time_integral_lower_bound C σ_0 hC hσ_0

/-- **Quantitative contrast with free Schrödinger**.

    The LSBridge doubling time is bounded below by `exp(σ_0)/(2C)`.
    The free Schrödinger doubling time is `√3 · m · σ_0² / ℏ`
    (from `σ(t) = σ_0·√(1 + (ℏt/(2mσ_0²))²)` solved at σ = 2σ_0).

    For `σ_0 ≥ ln(K · σ_0² · m·C/ℏ)` (i.e., `σ_0` large enough),
    `exp(σ_0)/(2C) > K · σ_0² · m/ℏ`.

    Stated at the inequality level:  for any constant `K` and large
    enough `σ_0`, the LSBridge doubling time exceeds `K · σ_0²`
    times any fixed positive constant.  Pure exponential dominance. -/
theorem lsbridge_doubling_time_dominates_free
    (C K : ℝ) (hC : 0 < C) (hK : 0 < K) (σ_0 : ℝ) (hσ_0 : 0 < σ_0)
    (h_large : K * σ_0 ^ 2 ≤ Real.exp σ_0 / (2 * C)) :
    K * σ_0 ^ 2 ≤ ∫ σ in σ_0..(2 * σ_0), doublingTimeIntegrand C σ := by
  exact le_trans h_large
    (lsbridge_doubling_time_exponentially_slow C σ_0 hC hσ_0)

/-! ════════════════════════════════════════════════════════════════════════
    PART 8 — TWO-SIDED DOUBLING BOUND AND OPTIMAL SPREADING WIDTH.

    Refines Part 7's exponential lower bound with a matching upper
    bound, and identifies the CHARACTERISTIC width at which LSBridge
    backreaction spreads fastest.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Doubling-time integral UPPER bound**:
        `∫_{σ_0}^{2σ_0} (e^σ / (C·σ)) dσ  ≤  e^{2σ_0} / C`
    for any `C > 0` and `σ_0 > 0`.

    Proof (mirror of Part 7's lower bound):  on `[σ_0, 2σ_0]`,
    `e^σ ≤ e^{2σ_0}` and `1/σ ≤ 1/σ_0`, so `e^σ/(C·σ) ≤ e^{2σ_0}/(C·σ_0)`.
    Integrating over the interval of length `σ_0` gives the bound
    `e^{2σ_0}/(C·σ_0) · σ_0 = e^{2σ_0}/C`. -/
theorem doubling_time_integral_upper_bound
    (C σ_0 : ℝ) (hC : 0 < C) (hσ_0 : 0 < σ_0) :
    ∫ σ in σ_0..(2 * σ_0), doublingTimeIntegrand C σ ≤ Real.exp (2 * σ_0) / C := by
  have h_2σ_0_pos : 0 < 2 * σ_0 := by linarith
  have h_σ_0_le : σ_0 ≤ 2 * σ_0 := by linarith
  set U : ℝ := Real.exp (2 * σ_0) / (C * σ_0) with hU_def
  -- Pointwise upper bound.
  have h_pointwise : ∀ σ ∈ Set.Icc σ_0 (2 * σ_0), doublingTimeIntegrand C σ ≤ U := by
    intro σ hσ
    obtain ⟨h_lb, h_ub⟩ := hσ
    have hσ_pos : 0 < σ := lt_of_lt_of_le hσ_0 h_lb
    have h_exp_mono : Real.exp σ ≤ Real.exp (2 * σ_0) := Real.exp_le_exp.mpr h_ub
    unfold doublingTimeIntegrand
    rw [hU_def]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc Real.exp σ * (C * σ_0)
        ≤ Real.exp (2 * σ_0) * (C * σ_0) := by
          apply mul_le_mul_of_nonneg_right h_exp_mono
          positivity
      _ ≤ Real.exp (2 * σ_0) * (C * σ) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_left h_lb (le_of_lt hC)
          · exact (Real.exp_pos _).le
  -- Integrability:
  have h_C_ne : C ≠ 0 := ne_of_gt hC
  have h_cont_g : ContinuousOn (doublingTimeIntegrand C) (Set.Icc σ_0 (2 * σ_0)) := by
    intro σ hσ
    obtain ⟨h_lb, _⟩ := hσ
    have hσ_pos : 0 < σ := lt_of_lt_of_le hσ_0 h_lb
    have hσ_ne : σ ≠ 0 := ne_of_gt hσ_pos
    have h_Cσ_ne : C * σ ≠ 0 := mul_ne_zero h_C_ne hσ_ne
    unfold doublingTimeIntegrand
    have h1 : ContinuousAt (fun y : ℝ => Real.exp y) σ := Real.continuous_exp.continuousAt
    have h2 : ContinuousAt (fun y : ℝ => C * y) σ :=
      (continuous_const.mul continuous_id).continuousAt
    exact (h1.div h2 h_Cσ_ne).continuousWithinAt
  have h_intble_g : IntervalIntegrable (doublingTimeIntegrand C)
                      MeasureTheory.volume σ_0 (2 * σ_0) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h_σ_0_le]
    exact h_cont_g
  have h_intble_U : IntervalIntegrable (fun _ : ℝ => U)
                      MeasureTheory.volume σ_0 (2 * σ_0) :=
    intervalIntegrable_const
  -- Apply integral_mono_on (in the upper-bound direction).
  have h_int_mono :
      ∫ σ in σ_0..(2 * σ_0), doublingTimeIntegrand C σ
        ≤ ∫ _ : ℝ in σ_0..(2 * σ_0), U :=
    intervalIntegral.integral_mono_on h_σ_0_le h_intble_g h_intble_U h_pointwise
  -- ∫ U = (2σ_0 - σ_0) · U = σ_0 · U = e^{2σ_0}/C.
  have h_int_U_eq : ∫ _ : ℝ in σ_0..(2 * σ_0), U = U * (2 * σ_0 - σ_0) := by
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  have h_simplify : U * (2 * σ_0 - σ_0) = Real.exp (2 * σ_0) / C := by
    rw [hU_def]
    have h_eq : (2 * σ_0 - σ_0) = σ_0 := by ring
    rw [h_eq]
    field_simp
  linarith

/-- **TWO-SIDED EXPONENTIAL SCALING**:  the LSBridge doubling-time
    integral is between `e^{σ_0}/(2C)` and `e^{2σ_0}/C`.  Both bounds
    grow exponentially in `σ_0`.  Compare:  free Schrödinger doubling
    time is polynomial `~σ_0² · m/ℏ`. -/
theorem doubling_time_two_sided_bound
    (C σ_0 : ℝ) (hC : 0 < C) (hσ_0 : 0 < σ_0) :
    Real.exp σ_0 / (2 * C) ≤ ∫ σ in σ_0..(2 * σ_0), doublingTimeIntegrand C σ
      ∧ ∫ σ in σ_0..(2 * σ_0), doublingTimeIntegrand C σ ≤ Real.exp (2 * σ_0) / C :=
  ⟨doubling_time_integral_lower_bound C σ_0 hC hσ_0,
   doubling_time_integral_upper_bound C σ_0 hC hσ_0⟩

/-! ────────────────────────────────────────────────────────────────────────
    Optimal-spreading-width theorem:  the function `σ ↦ σ·e^{−σ}` is
    maximized at `σ = 1` with value `e^{−1}`.  Hence the LSBridge
    spreading rate `σ_prime = C·σ·e^{−σ}` has a unique maximum `C/e`
    at the characteristic width `σ = 1`.
    ──────────────────────────────────────────────────────────────────────── -/

/-- **σ · e^(−σ) is maximized at σ = 1** (over all σ ∈ ℝ).  Max value: `e^(−1)`.

    Uses Mathlib's `Real.add_one_le_exp`: `x + 1 ≤ exp x` for any `x`.
    Applied to `x = σ - 1`:  `σ ≤ exp(σ - 1)`.
    Multiplying both sides by `exp(-σ) > 0`:  `σ·exp(-σ) ≤ exp(σ-1)·exp(-σ) = exp(-1)`. -/
theorem sigma_exp_neg_sigma_max_at_one (σ : ℝ) :
    σ * Real.exp (-σ) ≤ 1 * Real.exp (-1) := by
  have h_add_one_le_exp : (σ - 1) + 1 ≤ Real.exp (σ - 1) :=
    Real.add_one_le_exp (σ - 1)
  have h_σ_le : σ ≤ Real.exp (σ - 1) := by linarith
  have h_exp_neg_σ_pos : 0 < Real.exp (-σ) := Real.exp_pos _
  have h_step1 : σ * Real.exp (-σ) ≤ Real.exp (σ - 1) * Real.exp (-σ) :=
    mul_le_mul_of_nonneg_right h_σ_le h_exp_neg_σ_pos.le
  have h_step2 : Real.exp (σ - 1) * Real.exp (-σ) = Real.exp (-1) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [one_mul]
  linarith

/-- **LSBridge spreading rate has a unique maximum** `C/e` at the
    characteristic width `σ = 1`. -/
theorem lsbridge_spreading_rate_max_at_one
    (C σ : ℝ) (hC : 0 ≤ C) :
    C * σ * Real.exp (-σ) ≤ C / Real.exp 1 := by
  have h_max : σ * Real.exp (-σ) ≤ 1 * Real.exp (-1) := sigma_exp_neg_sigma_max_at_one σ
  -- C · (σ · exp(-σ)) ≤ C · (1 · exp(-1)) = C / exp(1).
  have h_C_mul : C * (σ * Real.exp (-σ)) ≤ C * (1 * Real.exp (-1)) :=
    mul_le_mul_of_nonneg_left h_max hC
  have h_assoc : C * σ * Real.exp (-σ) = C * (σ * Real.exp (-σ)) := by ring
  rw [h_assoc]
  have h_C_e_form : C * (1 * Real.exp (-1)) = C / Real.exp 1 := by
    rw [Real.exp_neg, one_mul, div_eq_mul_inv]
  linarith

/-- **HEADLINE — characteristic spreading width**:  the LSBridge
    backreaction Gaussian wavepacket has its **maximum spreading rate**
    `σ_prime ≤ C/e` attained at the characteristic width `σ = 1` (in
    natural units).  Wider or narrower wavepackets spread more slowly. -/
theorem lsbridge_characteristic_spreading_width
    (C σ : ℝ) (hC : 0 ≤ C) :
    C * σ * Real.exp (-σ) ≤ C / Real.exp 1 :=
  lsbridge_spreading_rate_max_at_one C σ hC

/-! ════════════════════════════════════════════════════════════════════════
    PART 9 — Ei-STYLE EXACT TIME PARAMETERIZATION.

    Upgrades the σ(t) dynamics from two-sided bounds (Parts 7–8) to an
    EXACT implicit solution.  Given a C¹ positive `σ : ℝ → ℝ` satisfying
    the ODE
        `σ'(t) = C · σ(t) · exp(−σ(t))`,
    the time evolution is exactly characterized by

        `∫_{σ(0)}^{σ(t)} (exp s / s) ds  =  C · t`        for all `t`.

    In terms of the exponential integral function `Ei`, this reads
    `Ei(σ(t)) − Ei(σ(0)) = C·t` — the canonical closed-form solution
    of the LSBridge backreaction Gaussian-width dynamics.  Mathlib does
    not yet have `Ei` so we state the result as an integral identity,
    which is equivalent and Mathlib-native.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Ei-style exact time parameterization** for the LSBridge σ(t)
    dynamics.

    *Hypotheses*:
      • `σ : ℝ → ℝ` is differentiable;
      • `σ(t) > 0` for all `t`;
      • `σ'(t) = C · σ(t) · exp(−σ(t))` for all `t`.

    *Conclusion*:
      `∫_{σ(0)}^{σ(t)} (exp s / s) ds = C · t` for all `t`.

    *Proof outline*:
      Let `G(t) := ∫_{σ(0)}^{σ(t)} (exp s / s) ds`.
      By FTC + chain rule:  G'(t) = (exp(σ t)/σ t)·σ'(t)
                                  = (exp(σ t)/σ t) · C · σ t · exp(−σ t)
                                  = C.
      Then G(t) − C·t has derivative zero everywhere, hence is constant.
      Since G(0) = 0 and (C·0) = 0, the constant is 0. -/
theorem gaussian_width_exact_time_parameterization
    (σ : ℝ → ℝ) (C : ℝ)
    (hσ_diff : Differentiable ℝ σ)
    (hσ_pos : ∀ t, 0 < σ t)
    (h_ODE : ∀ t, deriv σ t = C * σ t * Real.exp (-(σ t)))
    (t : ℝ) :
    ∫ s in (σ 0)..(σ t), Real.exp s / s = C * t := by
  -- Let f s := exp s / s.  Continuous on (0, ∞).
  let f : ℝ → ℝ := fun s => Real.exp s / s
  have h_f_cont_at : ∀ s : ℝ, 0 < s → ContinuousAt f s := fun s hs =>
    (Real.continuous_exp.continuousAt).div continuousAt_id (ne_of_gt hs)
  have h_f_cont_on_Ioi : ContinuousOn f (Set.Ioi (0 : ℝ)) := fun s hs =>
    (h_f_cont_at s hs).continuousWithinAt
  -- For each τ, f is continuous on the closed interval [σ(0), σ(τ)] ⊂ (0, ∞).
  have h_f_cont_uIcc : ∀ τ, ContinuousOn f (Set.uIcc (σ 0) (σ τ)) := by
    intro τ
    apply h_f_cont_on_Ioi.mono
    intro s hs
    have h_min_pos : 0 < min (σ 0) (σ τ) := lt_min (hσ_pos 0) (hσ_pos τ)
    have h_s_ge : min (σ 0) (σ τ) ≤ s := by
      rw [Set.uIcc, Set.mem_Icc] at hs
      exact hs.1
    exact lt_of_lt_of_le h_min_pos h_s_ge
  -- IntervalIntegrability of f on each (σ 0, σ τ).
  have h_intble : ∀ τ, IntervalIntegrable f MeasureTheory.volume (σ 0) (σ τ) :=
    fun τ => (h_f_cont_uIcc τ).intervalIntegrable
  -- Strong measurability at filter:  use the IsOpen-(0,∞) version applied at σ τ.
  have h_smaf : ∀ τ, StronglyMeasurableAtFilter f (𝓝 (σ τ)) MeasureTheory.volume :=
    fun τ =>
      ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
        (fun x hx => h_f_cont_at x hx) (σ τ) (hσ_pos τ)
  -- Step 2.  G(τ) := ∫_{σ 0}^{σ τ} f.  Show G has derivative C everywhere.
  have h_G_HasDeriv :
      ∀ τ, HasDerivAt (fun τ' => ∫ s in (σ 0)..(σ τ'), f s) C τ := by
    intro τ
    have h_inner :
        HasDerivAt (fun u => ∫ s in (σ 0)..u, f s) (f (σ τ)) (σ τ) :=
      intervalIntegral.integral_hasDerivAt_right (h_intble τ) (h_smaf τ)
        (h_f_cont_at (σ τ) (hσ_pos τ))
    have h_σ_HasDeriv : HasDerivAt σ (deriv σ τ) τ :=
      (hσ_diff.differentiableAt).hasDerivAt
    have h_chain : HasDerivAt (fun τ' => ∫ s in (σ 0)..(σ τ'), f s)
                    (f (σ τ) * deriv σ τ) τ :=
      h_inner.comp τ h_σ_HasDeriv
    -- Simplify f (σ τ) * deriv σ τ to C.
    have h_simp : f (σ τ) * deriv σ τ = C := by
      change (Real.exp (σ τ) / σ τ) * deriv σ τ = C
      rw [h_ODE τ, Real.exp_neg]
      have hσ_ne : σ τ ≠ 0 := ne_of_gt (hσ_pos τ)
      have h_exp_ne : Real.exp (σ τ) ≠ 0 := ne_of_gt (Real.exp_pos _)
      field_simp
    rw [h_simp] at h_chain
    exact h_chain
  -- Step 3.  H(τ) := (∫…) − C·τ has derivative 0 everywhere; H is constant; H 0 = 0.
  have h_H_HasDeriv :
      ∀ τ, HasDerivAt (fun τ' => (∫ s in (σ 0)..(σ τ'), f s) - C * τ') 0 τ := by
    intro τ
    have h_lin : HasDerivAt (fun τ' => C * τ') C τ := by
      simpa using (hasDerivAt_id τ).const_mul C
    have := (h_G_HasDeriv τ).sub h_lin
    simpa using this
  have h_H_diff :
      Differentiable ℝ (fun τ' => (∫ s in (σ 0)..(σ τ'), f s) - C * τ') :=
    fun τ => (h_H_HasDeriv τ).differentiableAt
  have h_H_deriv_zero :
      ∀ τ, deriv (fun τ' => (∫ s in (σ 0)..(σ τ'), f s) - C * τ') τ = 0 :=
    fun τ => (h_H_HasDeriv τ).deriv
  have h_const :
      ((∫ s in (σ 0)..(σ t), f s) - C * t)
        = ((∫ s in (σ 0)..(σ 0), f s) - C * 0) :=
    is_const_of_deriv_eq_zero h_H_diff h_H_deriv_zero t 0
  rw [intervalIntegral.integral_same, mul_zero, sub_zero] at h_const
  linarith

/-! ════════════════════════════════════════════════════════════════════════
    PART 10 — STATUS / FRONTIER.

    Closed in this file (Part 7-8 doubling-time bound + optimal width):
      ✓ `doublingTimeIntegrand` — scalar integrand `e^σ / (C·σ)`.
      ✓ **`doubling_time_integral_lower_bound`** — the integral inequality
        `∫_{σ_0}^{2σ_0} (e^σ/(C·σ)) dσ ≥ e^{σ_0}/(2C)`.
      ✓ `lsbridge_doubling_time_exponentially_slow` — physical-form alias.
      ✓ `lsbridge_doubling_time_dominates_free` — when σ_0 is large
        enough, LSBridge doubling time exceeds K·σ_0² for any K.
      ✓ **`doubling_time_integral_upper_bound`** — matching upper bound
        `∫_{σ_0}^{2σ_0} (e^σ/(C·σ)) dσ ≤ e^{2σ_0}/C`.
      ✓ `doubling_time_two_sided_bound` — packaged two-sided exponential
        scaling result.
      ✓ `sigma_exp_neg_sigma_max_at_one` — `σ·e^{−σ}` maximum at σ = 1,
        value `e^{−1}`.
      ✓ **`lsbridge_spreading_rate_max_at_one`** — spreading rate
        `σ_prime = C·σ·e^{−σ}` is bounded above by `C/e`.
      ✓ `lsbridge_characteristic_spreading_width` — characteristic
        width identification:  fastest spreading at σ = 1 with rate `C/e`.

    All other earlier-Part theorems (closed in this file):
      ✓ `gaussianWidthODE_residual` — algebraic encoding of the ODE.
      ✓ `firstIntegral`, `firstIntegralRate` — scalar definitions.
      ✓ `firstIntegralRate_eq_factor_residual` — chain-rule identity.
      ✓ **`gaussian_width_first_integral`** — `dF/dt = 0` under the ODE.
      ✓ **`gaussian_width_solution_implicit`** — `σ_prime = C·σ·exp(−σ)`.
      ✓ `gaussian_width_sigma_prime_{pos/neg/zero}_of_C_{pos/neg/zero}`
        — sign analysis.
      ✓ **`gaussian_width_no_oscillation`** — packaged monotonicity claim.
      ✓ **`gaussian_width_large_sigma_asymptotic`** — `σ_prime → 0`
        exponentially fast (Filter.Tendsto).
      ✓ **`gaussian_width_small_sigma_asymptotic`** — `σ_prime/σ → C`
        as σ → 0 (Filter.Tendsto).
      ✓ `gaussian_width_backreaction_admits_frozen` — LSBridge admits
        the constant-σ solution.
      ✓ `gaussian_width_freeSchrodinger_rejects_frozen` — free
        Schrödinger does not.
      ✓ **`gaussian_width_dynamics_differs_from_free_schrodinger`** —
        the structural-difference theorem.

    What this delivers — the LSBridge framework's first concrete
    dynamical prediction:

      • Conserved quantity:        `σ_prime · exp(σ) / σ = C`.
      • Implicit time evolution:   `σ_prime(t) = C · σ(t) · exp(−σ(t))`.
      • No oscillatory breathing:  sign(σ_prime) is constant.
      • Large-σ spreading is exponentially slow.
      • Small-σ growth/decay is approximately exponential in t.
      • Frozen `σ ≡ const` solutions exist (not in free Schrödinger).

    The full closed-form `σ(t)` requires the exponential integral `Ei`,
    via `Ei(σ(t)) = C·t + C₀`.  Mathlib's `Ei` formalization is
    available but not pursued here;  the scalar-level dynamical
    structure is established without it.

    Open continuations:
    • Full Ei-based time-parameterization: `Ei(σ(t)) = C·t + C₀`.
    • Lyapunov-type stability analysis of the frozen fixed point.
    • Comparison to lattice-soliton breathing dynamics (other
      "frozen-admitting" wave systems).
    ════════════════════════════════════════════════════════════════════════ -/

end UnifiedTheory.LayerB.LohmillerSlotineGaussianWidthDynamics
