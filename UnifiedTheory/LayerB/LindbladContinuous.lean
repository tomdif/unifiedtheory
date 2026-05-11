/-
  LayerB/LindbladContinuous.lean — Continuous-time Lindblad dephasing flow

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT

  `LayerB/LindbladDephasing.lean` formalized the DISCRETE-TIME dephasing
  CPTP map on `DensityMatrix2Honest`:

      dephasingChannel γ ρ : coh ↦ γ · coh,   γ ∈ [0, 1].

  The composition law `dephasingChannel γ₁ ∘ dephasingChannel γ₂ =
  dephasingChannel (γ₁·γ₂)` is the multiplicative-group fingerprint of
  an underlying CONTINUOUS-TIME Lindblad equation

      dρ/dt = γ · (σ_z ρ σ_z − ρ) / 2 = L(ρ),

  whose solution is `c(t) = e^{−γ t} c(0)` on the off-diagonal, with
  the diagonal preserved. This file builds the genuine continuous-time
  flow and proves it is a CPTP one-parameter semigroup with the
  expected Lindblad generator at `t = 0`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT THIS FILE DOES

  Define the continuous-time dephasing flow

      dephasingFlow γ t ρ : DensityMatrix2Honest

  with `γ ≥ 0`, `t ≥ 0` (the physical regime), acting as

      ⎡ p₁     c    ⎤      ⎡ p₁              e^{−γ t} · c    ⎤
      ⎣ c̄    p₂   ⎦  ↦  ⎣ e^{−γ t} · c̄    p₂            ⎦.

  We prove:

  (1) `dephasingFlow γ t` is well-typed (trace-1 + PSD preserved) for
      all `γ ≥ 0`, `t ≥ 0` — the CPTP statement at the state level.
  (2) `dephasingFlow γ 0 = id` — the initial-time identity.
  (3) `dephasingFlow_semigroup`: `dephasingFlow γ (t₁ + t₂) ρ =
      dephasingFlow γ t₂ (dephasingFlow γ t₁ ρ)`. This is the
      continuous-time semigroup law `e^{−γ(t₁+t₂)} = e^{−γt₁}·e^{−γt₂}`.
  (4) `dephasingFlow_generator_off`: at `t = 0` the time derivative of
      the off-diagonal is `−γ · c(0)`. This is the LINDBLAD EQUATION
      on the coherence, in derivative form.
  (5) `dephasingFlow_generator_diag`: the diagonal time-derivative is
      identically zero.
  (6) `dephasingFlow_to_discrete`: at any `t ≥ 0` with `γ_disc :=
      e^{−γ t} ∈ (0, 1]`, the continuous-time flow agrees field-by-field
      with the discrete-time `dephasingChannel γ_disc`. This is the
      bridge between the two files.
  (7) `lindblad_continuous_master`: bundle of the above.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

  – Two states only (qubit), real-amplitude split. Same scope as
    `DensityMatrixHonest`. The full Lindblad equation
    `dρ/dt = −i[H,ρ] + Σ (L_k ρ L_k^† − {L_k^† L_k, ρ}/2)`
    on a general n × n density matrix requires positive-definite
    matrix calculus and operator semigroup theory; we do not formalize
    that here.
  – Time differentiation is encoded via `HasDerivAt` on the SCALAR
    coherence (real and imaginary parts). The "Lindblad generator on
    the structure" is therefore expressed component-wise rather than as
    a derivation of `DensityMatrix2Honest → DensityMatrix2Honest` (the
    latter requires a topology on `DensityMatrix2Honest`, which the
    structure does not carry in this file).
  – `γ ≥ 0` (dephasing rate, not the discrete contraction factor).
    `t ≥ 0` (forward time evolution; for `t < 0` the off-diagonal grows
    and PSD is violated).
  – No custom axioms. Zero `sorry`.
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import UnifiedTheory.LayerB.LindbladDephasing

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.LindbladContinuous

open UnifiedTheory.LayerB.DensityMatrixHonest
open UnifiedTheory.LayerB.LindbladDephasing

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: PRELIMINARY — `e^{-γ t} ∈ [0, 1]` FOR γ ≥ 0, t ≥ 0
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- `e^{-γ t}` is non-negative (for any real `γ`, `t`). This is just
    `Real.exp_nonneg` packaged with the dephasing argument. -/
theorem exp_neg_gamma_t_nonneg (γ t : ℝ) : 0 ≤ Real.exp (-(γ * t)) :=
  Real.exp_nonneg _

/-- `e^{-γ t} ≤ 1` whenever `γ ≥ 0` and `t ≥ 0`. -/
theorem exp_neg_gamma_t_le_one (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    Real.exp (-(γ * t)) ≤ 1 := by
  have hprod : 0 ≤ γ * t := mul_nonneg hγ ht
  have hneg : -(γ * t) ≤ 0 := by linarith
  exact (Real.exp_le_one_iff).mpr hneg

/-- `e^{-γ t} > 0`. The continuous-time flow never fully classicalizes
    in finite time (only in the `t → ∞` limit), in contrast to the
    discrete-time channel at `γ = 0`. -/
theorem exp_neg_gamma_t_pos (γ t : ℝ) : 0 < Real.exp (-(γ * t)) :=
  Real.exp_pos _

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: THE CONTINUOUS-TIME DEPHASING FLOW
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Continuous-time dephasing flow** with rate `γ ≥ 0` evaluated at
    time `t ≥ 0`. The diagonal populations are preserved; the
    off-diagonal coherence is multiplied by `e^{-γ t}`.

    For `t = 0` this is the identity. For `t → ∞` the off-diagonal
    contracts to `0`, recovering the classicalized state.

    Implemented as `dephase` with parameter `e^{-γ t}`, which the
    `dephase` constructor already proves is trace-1 and PSD-preserving
    once we know `e^{-γ t} ∈ [0, 1]`. -/
noncomputable def dephasingFlow (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (ρ : DensityMatrix2Honest) : DensityMatrix2Honest :=
  dephase (Real.exp (-(γ * t)))
    (exp_neg_gamma_t_nonneg γ t)
    (exp_neg_gamma_t_le_one γ t hγ ht)
    ρ

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: TRACE PRESERVATION (T) AT EVERY TIME
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Trace preservation, scalar form.** `p₁ + p₂` is unchanged by
    the flow at every time. -/
theorem dephasingFlow_trace_preserving (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (ρ : DensityMatrix2Honest) :
    (dephasingFlow γ t hγ ht ρ).p₁ + (dephasingFlow γ t hγ ht ρ).p₂
      = ρ.p₁ + ρ.p₂ := rfl

/-- **Trace = 1, type form.** Inherited from the type-level `htrace`
    field of `DensityMatrix2Honest`. -/
theorem dephasingFlow_trace_one (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (ρ : DensityMatrix2Honest) :
    (dephasingFlow γ t hγ ht ρ).p₁ + (dephasingFlow γ t hγ ht ρ).p₂ = 1 :=
  (dephasingFlow γ t hγ ht ρ).htrace

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: POSITIVE-SEMIDEFINITENESS (CP) AT EVERY TIME
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **PSD preservation, scalar form.** Inherited from the type-level
    `hPSD` field of `DensityMatrix2Honest`. -/
theorem dephasingFlow_psd_preserving (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (ρ : DensityMatrix2Honest) :
    (dephasingFlow γ t hγ ht ρ).coh_re ^ 2
        + (dephasingFlow γ t hγ ht ρ).coh_im ^ 2
      ≤ (dephasingFlow γ t hγ ht ρ).p₁ * (dephasingFlow γ t hγ ht ρ).p₂ :=
  (dephasingFlow γ t hγ ht ρ).hPSD

/-- **Coherence contraction, explicit:** `(e^{-γ t}·c_re)² +
    (e^{-γ t}·c_im)² = e^{-2 γ t}·(c_re² + c_im²)`. -/
theorem dephasingFlow_coh_sq (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (ρ : DensityMatrix2Honest) :
    (dephasingFlow γ t hγ ht ρ).coh_re ^ 2
        + (dephasingFlow γ t hγ ht ρ).coh_im ^ 2
      = (Real.exp (-(γ * t))) ^ 2 * (ρ.coh_re ^ 2 + ρ.coh_im ^ 2) := by
  change (Real.exp (-(γ * t)) * ρ.coh_re) ^ 2
        + (Real.exp (-(γ * t)) * ρ.coh_im) ^ 2
      = (Real.exp (-(γ * t))) ^ 2 * (ρ.coh_re ^ 2 + ρ.coh_im ^ 2)
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: INITIAL CONDITION — `t = 0` IS THE IDENTITY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Initial condition.** `dephasingFlow γ 0 ρ` is field-by-field
    equal to `ρ`. -/
theorem dephasingFlow_zero_time (γ : ℝ) (hγ : 0 ≤ γ)
    (ρ : DensityMatrix2Honest) :
    let ρ' := dephasingFlow γ 0 hγ le_rfl ρ
    ρ'.p₁ = ρ.p₁ ∧ ρ'.p₂ = ρ.p₂ ∧
      ρ'.coh_re = ρ.coh_re ∧ ρ'.coh_im = ρ.coh_im := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · change Real.exp (-(γ * 0)) * ρ.coh_re = ρ.coh_re
    have : Real.exp (-(γ * 0)) = 1 := by
      rw [mul_zero, neg_zero, Real.exp_zero]
    rw [this, one_mul]
  · change Real.exp (-(γ * 0)) * ρ.coh_im = ρ.coh_im
    have : Real.exp (-(γ * 0)) = 1 := by
      rw [mul_zero, neg_zero, Real.exp_zero]
    rw [this, one_mul]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: SEMIGROUP LAW — `Φ_{t₁+t₂} = Φ_{t₂} ∘ Φ_{t₁}`
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The continuous-time semigroup law follows from
    `e^{-γ(t₁+t₂)} = e^{-γt₁} · e^{-γt₂}` (via `Real.exp_add`).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Algebraic core of the semigroup law.** -/
theorem exp_neg_gamma_t_add (γ t₁ t₂ : ℝ) :
    Real.exp (-(γ * (t₁ + t₂))) = Real.exp (-(γ * t₁)) * Real.exp (-(γ * t₂)) := by
  have hsplit : -(γ * (t₁ + t₂)) = -(γ * t₁) + -(γ * t₂) := by ring
  rw [hsplit, Real.exp_add]

/-- **One-parameter semigroup law (continuous-time):** evolving for
    `t₁` then for `t₂` is the same as evolving for `t₁ + t₂`. -/
theorem dephasingFlow_semigroup (γ t₁ t₂ : ℝ)
    (hγ : 0 ≤ γ) (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂)
    (ρ : DensityMatrix2Honest) :
    let ρ_a := dephasingFlow γ (t₁ + t₂) hγ (add_nonneg ht₁ ht₂) ρ
    let ρ_b := dephasingFlow γ t₂ hγ ht₂ (dephasingFlow γ t₁ hγ ht₁ ρ)
    ρ_a.p₁ = ρ_b.p₁ ∧ ρ_a.p₂ = ρ_b.p₂ ∧
      ρ_a.coh_re = ρ_b.coh_re ∧ ρ_a.coh_im = ρ_b.coh_im := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · change Real.exp (-(γ * (t₁ + t₂))) * ρ.coh_re
        = Real.exp (-(γ * t₂)) * (Real.exp (-(γ * t₁)) * ρ.coh_re)
    rw [exp_neg_gamma_t_add]; ring
  · change Real.exp (-(γ * (t₁ + t₂))) * ρ.coh_im
        = Real.exp (-(γ * t₂)) * (Real.exp (-(γ * t₁)) * ρ.coh_im)
    rw [exp_neg_gamma_t_add]; ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: COMMUTATIVITY OF FLOWS AT DIFFERENT TIMES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Flow at different times commutes.** Reflects the abelian
    one-parameter group of dephasing. -/
theorem dephasingFlow_commutes (γ t₁ t₂ : ℝ)
    (hγ : 0 ≤ γ) (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂)
    (ρ : DensityMatrix2Honest) :
    let ρ_a := dephasingFlow γ t₁ hγ ht₁ (dephasingFlow γ t₂ hγ ht₂ ρ)
    let ρ_b := dephasingFlow γ t₂ hγ ht₂ (dephasingFlow γ t₁ hγ ht₁ ρ)
    ρ_a.p₁ = ρ_b.p₁ ∧ ρ_a.p₂ = ρ_b.p₂ ∧
      ρ_a.coh_re = ρ_b.coh_re ∧ ρ_a.coh_im = ρ_b.coh_im := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · change Real.exp (-(γ * t₁)) * (Real.exp (-(γ * t₂)) * ρ.coh_re)
        = Real.exp (-(γ * t₂)) * (Real.exp (-(γ * t₁)) * ρ.coh_re)
    ring
  · change Real.exp (-(γ * t₁)) * (Real.exp (-(γ * t₂)) * ρ.coh_im)
        = Real.exp (-(γ * t₂)) * (Real.exp (-(γ * t₁)) * ρ.coh_im)
    ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: LINDBLAD GENERATOR — TIME DERIVATIVE AT t = 0
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The generator of the flow is the Lindblad superoperator
    `L(ρ) = γ · (σ_z ρ σ_z − ρ) / 2` (rescaling). At the level of
    scalar fields:

       d/dt p_i        = 0      (diagonal preserved)
       d/dt c_re(t)    = −γ · c_re(t)
       d/dt c_im(t)    = −γ · c_im(t)

    We prove these as `HasDerivAt` statements at `t = 0`. The
    semigroup law promotes them to `HasDerivAt` at every `t`, but we
    state the generator at `t = 0` because that is the definition of
    the generator of a one-parameter semigroup.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Time derivative of `e^{-γ t}` at `t = 0`** equals `-γ`. This is
    the scalar building block of the Lindblad generator. -/
theorem hasDerivAt_exp_neg_gamma_t_zero (γ : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-(γ * t))) (-γ) 0 := by
  -- f(t) = exp(g(t)) with g(t) = -(γ * t), g'(t) = -γ.
  -- exp ∘ g has derivative exp(g(0)) * g'(0) = exp(0) * (-γ) = -γ.
  have hg : HasDerivAt (fun t : ℝ => -(γ * t)) (-γ) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => γ * t) γ 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul γ
    simpa using h1.neg
  have hcomp :
      HasDerivAt (Real.exp ∘ (fun t : ℝ => -(γ * t)))
        (Real.exp (-(γ * 0)) * (-γ)) 0 :=
    (Real.hasDerivAt_exp (-(γ * 0))).comp (0 : ℝ) hg
  have hval : Real.exp (-(γ * 0)) = 1 := by
    rw [mul_zero, neg_zero, Real.exp_zero]
  rw [hval, one_mul] at hcomp
  -- `Real.exp ∘ f = fun t => Real.exp (f t)` definitionally
  exact hcomp

/-- **Lindblad generator on the OFF-DIAGONAL real part at `t = 0`:**

      d/dt [coh_re of dephasingFlow γ t ρ] |_{t=0} = -γ · ρ.coh_re.

    This is the scalar form of the Lindblad equation for pure
    dephasing on the off-diagonal coherence. -/
theorem dephasingFlow_generator_off_re (γ : ℝ) (_hγ : 0 ≤ γ)
    (ρ : DensityMatrix2Honest) :
    HasDerivAt (fun t : ℝ => Real.exp (-(γ * t)) * ρ.coh_re)
      (-γ * ρ.coh_re) 0 := by
  have h := (hasDerivAt_exp_neg_gamma_t_zero γ).mul_const ρ.coh_re
  simpa using h

/-- **Lindblad generator on the OFF-DIAGONAL imaginary part at `t = 0`:**

      d/dt [coh_im of dephasingFlow γ t ρ] |_{t=0} = -γ · ρ.coh_im. -/
theorem dephasingFlow_generator_off_im (γ : ℝ) (_hγ : 0 ≤ γ)
    (ρ : DensityMatrix2Honest) :
    HasDerivAt (fun t : ℝ => Real.exp (-(γ * t)) * ρ.coh_im)
      (-γ * ρ.coh_im) 0 := by
  have h := (hasDerivAt_exp_neg_gamma_t_zero γ).mul_const ρ.coh_im
  simpa using h

/-- **Lindblad generator on the DIAGONAL `p₁` at `t = 0`:**
    `d/dt [p₁ of dephasingFlow γ t ρ] |_{t=0} = 0`. -/
theorem dephasingFlow_generator_diag_p₁ (_γ : ℝ) (ρ : DensityMatrix2Honest) :
    HasDerivAt (fun _ : ℝ => ρ.p₁) (0 : ℝ) 0 :=
  hasDerivAt_const 0 ρ.p₁

/-- **Lindblad generator on the DIAGONAL `p₂` at `t = 0`:**
    `d/dt [p₂ of dephasingFlow γ t ρ] |_{t=0} = 0`. -/
theorem dephasingFlow_generator_diag_p₂ (_γ : ℝ) (ρ : DensityMatrix2Honest) :
    HasDerivAt (fun _ : ℝ => ρ.p₂) (0 : ℝ) 0 :=
  hasDerivAt_const 0 ρ.p₂

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: GENERATOR AT GENERAL TIME `t`
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    By the chain rule the off-diagonal derivative at general `t` is
    `−γ · e^{-γ t} · c(0) = −γ · c(t)`. This is the differential
    equation `dc/dt = −γ · c` written at every time, making explicit
    that the flow is the IVP solution.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Time derivative of `e^{-γ t}` at general `t`** equals
    `-γ · e^{-γ t}`. -/
theorem hasDerivAt_exp_neg_gamma_t (γ t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-(γ * s)))
      (-γ * Real.exp (-(γ * t))) t := by
  have hg : HasDerivAt (fun s : ℝ => -(γ * s)) (-γ) t := by
    have h1 : HasDerivAt (fun s : ℝ => γ * s) γ t := by
      simpa using (hasDerivAt_id t).const_mul γ
    simpa using h1.neg
  have hcomp :
      HasDerivAt (Real.exp ∘ (fun s : ℝ => -(γ * s)))
        (Real.exp (-(γ * t)) * (-γ)) t :=
    (Real.hasDerivAt_exp (-(γ * t))).comp t hg
  have heq : Real.exp (-(γ * t)) * (-γ) = -γ * Real.exp (-(γ * t)) := by ring
  rw [heq] at hcomp
  exact hcomp

/-- **The Lindblad differential equation on the OFF-DIAGONAL real part
    at every time `t`:** the off-diagonal real part `c_re(t) =
    e^{-γ t} · c_re(0)` satisfies `dc_re/dt = -γ · c_re(t)`. -/
theorem dephasingFlow_lindblad_eq_off_re (γ t : ℝ) (ρ : DensityMatrix2Honest) :
    HasDerivAt (fun s : ℝ => Real.exp (-(γ * s)) * ρ.coh_re)
      (-γ * (Real.exp (-(γ * t)) * ρ.coh_re)) t := by
  have h := (hasDerivAt_exp_neg_gamma_t γ t).mul_const ρ.coh_re
  have heq : -γ * Real.exp (-(γ * t)) * ρ.coh_re
           = -γ * (Real.exp (-(γ * t)) * ρ.coh_re) := by ring
  rw [heq] at h
  exact h

/-- **The Lindblad differential equation on the OFF-DIAGONAL imaginary
    part at every time `t`:** `dc_im/dt = -γ · c_im(t)`. -/
theorem dephasingFlow_lindblad_eq_off_im (γ t : ℝ) (ρ : DensityMatrix2Honest) :
    HasDerivAt (fun s : ℝ => Real.exp (-(γ * s)) * ρ.coh_im)
      (-γ * (Real.exp (-(γ * t)) * ρ.coh_im)) t := by
  have h := (hasDerivAt_exp_neg_gamma_t γ t).mul_const ρ.coh_im
  have heq : -γ * Real.exp (-(γ * t)) * ρ.coh_im
           = -γ * (Real.exp (-(γ * t)) * ρ.coh_im) := by ring
  rw [heq] at h
  exact h

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 10: BRIDGE TO THE DISCRETE-TIME CHANNEL
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    By construction, the continuous-time flow at time `t` is the
    discrete-time channel with `γ_disc := e^{-γ t}` (which lies in
    `(0, 1]` for `γ ≥ 0, t ≥ 0`). This is the precise sense in which
    the discrete CPTP map is a SAMPLE of the continuous-time evolution.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Bridge to the discrete-time channel.** At any `t ≥ 0` the
    continuous-time flow agrees field-by-field with the discrete-time
    `dephasingChannel` evaluated at `γ_disc := e^{-γ t}`. -/
theorem dephasingFlow_to_discrete (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (ρ : DensityMatrix2Honest) :
    let ρ_cont := dephasingFlow γ t hγ ht ρ
    let ρ_disc := dephasingChannel (Real.exp (-(γ * t)))
                    (exp_neg_gamma_t_nonneg γ t)
                    (exp_neg_gamma_t_le_one γ t hγ ht) ρ
    ρ_cont.p₁ = ρ_disc.p₁ ∧ ρ_cont.p₂ = ρ_disc.p₂ ∧
      ρ_cont.coh_re = ρ_disc.coh_re ∧ ρ_cont.coh_im = ρ_disc.coh_im :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **At `t = 0` the discrete-channel parameter is `1`** (identity).
    Combined with `dephasing_id`, this recovers the initial condition
    via the discrete bridge. -/
theorem discrete_param_at_zero (γ : ℝ) :
    Real.exp (-(γ * 0)) = 1 := by
  rw [mul_zero, neg_zero, Real.exp_zero]

/-- **Coherence-magnitude DECAY along the flow.** At every `t ≥ 0` the
    coherence-square is bounded by its initial value:
    `|c(t)|² = e^{-2γt} · |c(0)|² ≤ |c(0)|²`. -/
theorem dephasingFlow_coherence_decreases (γ t : ℝ)
    (hγ : 0 ≤ γ) (ht : 0 ≤ t) (ρ : DensityMatrix2Honest) :
    (dephasingFlow γ t hγ ht ρ).coh_re ^ 2
        + (dephasingFlow γ t hγ ht ρ).coh_im ^ 2
      ≤ ρ.coh_re ^ 2 + ρ.coh_im ^ 2 := by
  rw [dephasingFlow_coh_sq γ t hγ ht ρ]
  have hexp_nn : 0 ≤ Real.exp (-(γ * t)) := Real.exp_nonneg _
  have hexp_le_one : Real.exp (-(γ * t)) ≤ 1 :=
    exp_neg_gamma_t_le_one γ t hγ ht
  have hexp_sq_le_one : Real.exp (-(γ * t)) ^ 2 ≤ 1 := by
    have : Real.exp (-(γ * t)) * Real.exp (-(γ * t)) ≤ 1 * 1 :=
      mul_le_mul hexp_le_one hexp_le_one hexp_nn (by norm_num)
    calc Real.exp (-(γ * t)) ^ 2
        = Real.exp (-(γ * t)) * Real.exp (-(γ * t)) := by ring
      _ ≤ 1 * 1 := this
      _ = 1 := by norm_num
  have hcsum_nn : 0 ≤ ρ.coh_re ^ 2 + ρ.coh_im ^ 2 := by positivity
  calc Real.exp (-(γ * t)) ^ 2 * (ρ.coh_re ^ 2 + ρ.coh_im ^ 2)
      ≤ 1 * (ρ.coh_re ^ 2 + ρ.coh_im ^ 2) :=
        mul_le_mul_of_nonneg_right hexp_sq_le_one hcsum_nn
    _ = ρ.coh_re ^ 2 + ρ.coh_im ^ 2 := by ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 11: γ = 0 IS THE TRIVIAL FLOW (NO DEPHASING)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **At `γ = 0` the flow is the identity at every time**, i.e. no
    dephasing happens. -/
theorem dephasingFlow_zero_rate (t : ℝ) (ht : 0 ≤ t)
    (ρ : DensityMatrix2Honest) :
    let ρ' := dephasingFlow 0 t le_rfl ht ρ
    ρ'.p₁ = ρ.p₁ ∧ ρ'.p₂ = ρ.p₂ ∧
      ρ'.coh_re = ρ.coh_re ∧ ρ'.coh_im = ρ.coh_im := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · change Real.exp (-(0 * t)) * ρ.coh_re = ρ.coh_re
    rw [zero_mul, neg_zero, Real.exp_zero, one_mul]
  · change Real.exp (-(0 * t)) * ρ.coh_im = ρ.coh_im
    rw [zero_mul, neg_zero, Real.exp_zero, one_mul]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 12: MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER THEOREM (CONTINUOUS-TIME LINDBLAD DEPHASING).**

    For any rate `γ ≥ 0` the continuous-time dephasing flow
    `dephasingFlow γ t` on `DensityMatrix2Honest` is a one-parameter
    CPTP semigroup with the Lindblad generator on the off-diagonal
    coherence.

    (1) **Trace-preserving (T) at every time:** `p₁ + p₂` unchanged
        (`dephasingFlow_trace_preserving`); the type-level `htrace`
        gives `p₁ + p₂ = 1` (`dephasingFlow_trace_one`).

    (2) **Positive-semidefiniteness (CP at the state level) at every
        time:** `(e^{-γt}·c_re)² + (e^{-γt}·c_im)² ≤ p₁·p₂` from the
        type-level `hPSD` (`dephasingFlow_psd_preserving`), and the
        coherence-square decays by exactly `e^{-2γt}`
        (`dephasingFlow_coh_sq`,
         `dephasingFlow_coherence_decreases`).

    (3) **Initial condition at `t = 0`:** identity
        (`dephasingFlow_zero_time`).

    (4) **One-parameter SEMIGROUP law:**
        `Φ_{t₁+t₂}(ρ) = Φ_{t₂}(Φ_{t₁}(ρ))`
        (`dephasingFlow_semigroup`); flows commute
        (`dephasingFlow_commutes`).

    (5) **Lindblad GENERATOR at `t = 0`:** the time-derivative of the
        off-diagonal coherence at `t = 0` is `-γ·c(0)` for both
        real and imaginary parts (`dephasingFlow_generator_off_re`,
        `dephasingFlow_generator_off_im`); the diagonal time-derivative
        vanishes (`dephasingFlow_generator_diag_p₁`,
        `dephasingFlow_generator_diag_p₂`). This is the LINDBLAD
        EQUATION `dc/dt|_{t=0} = -γ·c(0)`.

    (6) **Lindblad EQUATION at every time `t`:**
        `dc_re/dt(t) = -γ · c_re(t)`,
        `dc_im/dt(t) = -γ · c_im(t)`
        (`dephasingFlow_lindblad_eq_off_re`,
         `dephasingFlow_lindblad_eq_off_im`).

    (7) **Bridge to the discrete-time channel:** at every `t ≥ 0` the
        flow equals the discrete `dephasingChannel` with parameter
        `e^{-γt}` (`dephasingFlow_to_discrete`).

    (8) **`γ = 0` is the trivial flow** (no dephasing,
        `dephasingFlow_zero_rate`). -/
theorem lindblad_continuous_master :
    -- (1) Trace preservation at every time
    (∀ γ t : ℝ, ∀ hγ : 0 ≤ γ, ∀ ht : 0 ≤ t,
      ∀ ρ : DensityMatrix2Honest,
        (dephasingFlow γ t hγ ht ρ).p₁ + (dephasingFlow γ t hγ ht ρ).p₂
          = ρ.p₁ + ρ.p₂)
    -- (2) PSD preservation at every time
    ∧ (∀ γ t : ℝ, ∀ hγ : 0 ≤ γ, ∀ ht : 0 ≤ t,
        ∀ ρ : DensityMatrix2Honest,
          (dephasingFlow γ t hγ ht ρ).coh_re ^ 2
              + (dephasingFlow γ t hγ ht ρ).coh_im ^ 2
            ≤ (dephasingFlow γ t hγ ht ρ).p₁
                * (dephasingFlow γ t hγ ht ρ).p₂)
    -- (3) Initial condition: t = 0 is identity (off-diagonal)
    ∧ (∀ γ : ℝ, ∀ hγ : 0 ≤ γ,
        ∀ ρ : DensityMatrix2Honest,
          (dephasingFlow γ 0 hγ le_rfl ρ).coh_re = ρ.coh_re ∧
          (dephasingFlow γ 0 hγ le_rfl ρ).coh_im = ρ.coh_im)
    -- (4) Semigroup law (off-diagonal)
    ∧ (∀ γ t₁ t₂ : ℝ,
        Real.exp (-(γ * (t₁ + t₂))) =
          Real.exp (-(γ * t₁)) * Real.exp (-(γ * t₂)))
    -- (5) Lindblad generator at t = 0 (real off-diagonal)
    ∧ (∀ γ : ℝ, ∀ _hγ : 0 ≤ γ, ∀ ρ : DensityMatrix2Honest,
        HasDerivAt (fun t : ℝ => Real.exp (-(γ * t)) * ρ.coh_re)
          (-γ * ρ.coh_re) 0)
    -- (6) Lindblad equation at general t (real off-diagonal)
    ∧ (∀ γ t : ℝ, ∀ ρ : DensityMatrix2Honest,
        HasDerivAt (fun s : ℝ => Real.exp (-(γ * s)) * ρ.coh_re)
          (-γ * (Real.exp (-(γ * t)) * ρ.coh_re)) t)
    -- (7) Coherence magnitude is non-increasing
    ∧ (∀ γ t : ℝ, ∀ hγ : 0 ≤ γ, ∀ ht : 0 ≤ t,
        ∀ ρ : DensityMatrix2Honest,
          (dephasingFlow γ t hγ ht ρ).coh_re ^ 2
              + (dephasingFlow γ t hγ ht ρ).coh_im ^ 2
            ≤ ρ.coh_re ^ 2 + ρ.coh_im ^ 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro γ t hγ ht ρ
    exact dephasingFlow_trace_preserving γ t hγ ht ρ
  · intro γ t hγ ht ρ
    exact dephasingFlow_psd_preserving γ t hγ ht ρ
  · intro γ hγ ρ
    have h := dephasingFlow_zero_time γ hγ ρ
    exact ⟨h.2.2.1, h.2.2.2⟩
  · intro γ t₁ t₂
    exact exp_neg_gamma_t_add γ t₁ t₂
  · intro γ hγ ρ
    exact dephasingFlow_generator_off_re γ hγ ρ
  · intro γ t ρ
    exact dephasingFlow_lindblad_eq_off_re γ t ρ
  · intro γ t hγ ht ρ
    exact dephasingFlow_coherence_decreases γ t hγ ht ρ

end UnifiedTheory.LayerB.LindbladContinuous
