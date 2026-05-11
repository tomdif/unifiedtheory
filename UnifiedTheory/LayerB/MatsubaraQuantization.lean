/-
  LayerB/MatsubaraQuantization.lean — The genuine Matsubara quantization theorem

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT

  `LayerB/KMSFromDephasing.lean` advertises a theorem named `matsubara`,
  but its content is the trivial algebraic identity

      (2π n / β) · β = 2π n,

  which is just `div_mul_cancel₀`. That identity does NOT derive
  quantization of frequencies; it merely simplifies an already-quantized
  expression. The genuine Matsubara theorem is the converse direction:

      "If `e^{i ω β} = 1` (β-periodicity of the phase factor), then
       ω is forced into the discrete lattice (2π / β) · ℤ."

  This is the content the physics literature calls Matsubara
  quantization — discreteness of the allowed thermal frequencies is
  DERIVED from periodicity of the imaginary-time phase, it is not
  assumed.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED

  – `exp_iωβ_one_iff`: the genuine biconditional
        `Complex.exp (I · ω · β) = 1 ↔ ∃ n : ℤ, ω = 2π n / β`
    for `β > 0`, real `ω`. The non-trivial (forward) direction
    invokes `Complex.exp_eq_one_iff` from Mathlib (which gives
    `i ω β = n · (2π i)`, equivalently `ω β = 2π n`) and divides
    by the strictly positive β.

  – `matsubara_quantized`: the forward implication, packaged as
    a quantization statement.

  – `matsubara_inverse`: the converse, that any frequency in
    `(2π / β) · ℤ` produces a β-periodic phase. This is essentially
    the original `KMSFromDephasing.matsubara` lemma but rewritten to
    say what it actually says.

  – `dephasedAmplitude_periodic_iff_matsubara`: the bridge to the
    framework's `dephasedAmplitude` of `KMSFromDephasing`. If the
    dephasing rate is zero (so the amplitude is purely oscillatory)
    and the amplitude is β-periodic in `s`, then the wave-vector
    `k` must be a Matsubara mode `2π n / β`. The dephasing must be
    set to zero because exponential decay can never be β-periodic
    unless it is identically zero, which is the wrong physical
    regime for this statement.

  – `matsubara_genuine`: the master theorem packaging all of the
    above as one bundled fact.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

  – This file proves quantization of the EXPONENTIAL frequencies
    that arise from β-periodicity of the imaginary-time phase. It
    REPLACES the trivial `div_mul_cancel₀` "matsubara" lemma in
    `KMSFromDephasing.lean` with the substantive theorem.

  – What is STILL not proved (and which the original
    `KMSFromDephasing.lean` correctly disclaimed):

      • The full KMS condition
            ⟨A(t) B(0)⟩_β = ⟨B(0) A(t + iβ)⟩_β
        for thermal two-point functions. Proving this requires:
        (i) modular automorphisms of a thermal state (Tomita–Takesaki
        machinery), (ii) analytic continuation of the two-point
        function from real time into the strip
        `{0 ≤ Im t ≤ β}`. Neither is yet formalized in this
        framework.

      • Convergence of the Matsubara sum / contour deformation
        of the imaginary-time integral.

    What IS proved here is the structural step
    "β-periodicity ⇒ frequency quantization", which is the algebraic
    skeleton on top of which the analytic KMS results are built.

  – Real frequencies only (`ω : ℝ`); the dephasingless / pure-phase
    regime. The framework's full dephasedAmplitude with `Γ > 0`
    cannot be β-periodic and so falls outside the scope of this
    theorem (proved as `dephasing_pos_not_periodic`).

  Zero sorry. Zero custom axioms.
-/
import UnifiedTheory.LayerB.KMSFromDephasing
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.MatsubaraQuantization

open UnifiedTheory.LayerB.KMSFromDephasing
open Complex

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE CORE BICONDITIONAL — `exp(iωβ) = 1 ↔ ω ∈ (2π/β)·ℤ`
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Coercion bridge: as complex numbers, `(I : ℂ) * (ω : ℂ) * (β : ℂ) =
    ((ω * β : ℝ) : ℂ) * I`. Pure algebra, used to align the form of the
    exponential argument with `Complex.exp_eq_one_iff`. -/
private lemma I_mul_real_real (ω β : ℝ) :
    (I : ℂ) * (ω : ℂ) * (β : ℂ) = ((ω * β : ℝ) : ℂ) * I := by
  push_cast
  ring

/-- **Forward direction** of Matsubara quantization.

    If the imaginary-time phase `e^{i ω β}` equals 1 and `β > 0`, then
    the frequency `ω` is forced to lie on the lattice `(2π/β) · ℤ`.

    The proof: by `Complex.exp_eq_one_iff`, `i ω β = n · (2π i)` for
    some integer `n`. Cancel `i` to get `ω β = 2π n` as reals, then
    divide by `β > 0`. -/
theorem matsubara_quantized {ω β : ℝ} (hβ : 0 < β)
    (hper : Complex.exp ((I : ℂ) * (ω : ℂ) * (β : ℂ)) = 1) :
    ∃ n : ℤ, ω = 2 * Real.pi * n / β := by
  -- Rewrite the exponent into the form Mathlib's `exp_eq_one_iff` expects.
  -- We have I·ω·β; we'll feed `exp_eq_one_iff` directly.
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hper
  -- hn : (I : ℂ) * (ω : ℂ) * (β : ℂ) = n * (2 * π * I)
  -- Goal: solve for ω
  refine ⟨n, ?_⟩
  -- Strategy: multiply both sides of hn by -I (to remove I from both sides),
  -- giving ω β = 2 π n in ℂ, then descend to ℝ.
  have hwβ_complex : ((ω * β : ℝ) : ℂ) = 2 * Real.pi * n := by
    have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
    -- (I·ω·β) = n · (2π·I)  in ℂ
    -- LHS = (ω·β) · I  by commutativity
    have hL : (I : ℂ) * (ω : ℂ) * (β : ℂ) = ((ω * β : ℝ) : ℂ) * I := I_mul_real_real ω β
    -- RHS = n · (2π) · I
    have hR : ((n : ℂ)) * (2 * (Real.pi : ℂ) * I) = ((2 * Real.pi * n : ℝ) : ℂ) * I := by
      push_cast; ring
    have hpre : ((ω * β : ℝ) : ℂ) * I = ((2 * Real.pi * n : ℝ) : ℂ) * I := by
      rw [← hL]
      rw [hn]
      rw [hR]
    -- Cancel the common I factor on the right.
    have := mul_right_cancel₀ hI hpre
    -- this : ((ω * β : ℝ) : ℂ) = ((2 * Real.pi * n : ℝ) : ℂ)
    rw [this]
    push_cast
    ring
  -- Move from ℂ to ℝ via injectivity of the coercion.
  have hwβ_real : ω * β = 2 * Real.pi * n := by
    have : ((ω * β : ℝ) : ℂ) = ((2 * Real.pi * n : ℝ) : ℂ) := by
      rw [hwβ_complex]; push_cast; ring
    exact_mod_cast this
  -- Divide by β > 0.
  have hβne : β ≠ 0 := ne_of_gt hβ
  field_simp
  linarith [hwβ_real]

/-- **Reverse direction** of Matsubara quantization.

    Any frequency `ω = 2π n / β` produces a β-periodic phase factor
    `e^{i ω β} = 1`. This is the easy direction: substitute and use
    `Complex.exp_int_mul_two_pi_mul_I`-style cancellation via
    `Complex.exp_eq_one_iff`. -/
theorem matsubara_inverse {ω β : ℝ} (hβ : 0 < β) (n : ℤ)
    (hω : ω = 2 * Real.pi * n / β) :
    Complex.exp ((I : ℂ) * (ω : ℂ) * (β : ℂ)) = 1 := by
  -- Reduce to the form `exp (n · (2π · I)) = 1`.
  apply Complex.exp_eq_one_iff.mpr
  refine ⟨n, ?_⟩
  -- Need to show `I·ω·β = n · (2π · I)`.
  have hβne : β ≠ 0 := ne_of_gt hβ
  -- `ω · β = 2π n` as reals.
  have hwβ : ω * β = 2 * Real.pi * n := by
    rw [hω]
    field_simp
  -- Convert to ℂ and reshuffle.
  have hwβ_C : (ω : ℂ) * (β : ℂ) = 2 * (Real.pi : ℂ) * n := by
    have : ((ω * β : ℝ) : ℂ) = ((2 * Real.pi * n : ℝ) : ℂ) := by
      rw [hwβ]
    push_cast at this
    linear_combination this
  calc (I : ℂ) * (ω : ℂ) * (β : ℂ)
      = (I : ℂ) * ((ω : ℂ) * (β : ℂ)) := by ring
    _ = (I : ℂ) * (2 * (Real.pi : ℂ) * n) := by rw [hwβ_C]
    _ = (n : ℂ) * (2 * (Real.pi : ℂ) * I) := by ring

/-- **The genuine Matsubara biconditional.**

    For `β > 0` and real `ω`, the imaginary-time phase `e^{i ω β}`
    equals 1 if and only if `ω` lies on the Matsubara lattice
    `(2π/β) · ℤ`. -/
theorem exp_iωβ_one_iff {ω β : ℝ} (hβ : 0 < β) :
    Complex.exp ((I : ℂ) * (ω : ℂ) * (β : ℂ)) = 1 ↔
      ∃ n : ℤ, ω = 2 * Real.pi * n / β := by
  refine ⟨matsubara_quantized hβ, ?_⟩
  rintro ⟨n, hω⟩
  exact matsubara_inverse hβ n hω

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: BRIDGE TO THE FRAMEWORK'S `dephasedAmplitude`
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The pure-phase amplitude `expAmplitude k s = e^{i k s}` written as a
    complex exponential. -/
private lemma expAmplitude_eq_exp (k s : ℝ) :
    UnifiedTheory.LayerB.PropagationRule.expAmplitude k s
      = Complex.exp ((I : ℂ) * (k : ℂ) * (s : ℂ)) := by
  unfold UnifiedTheory.LayerB.PropagationRule.expAmplitude
  -- Reshape `I·k·s = ((k*s : ℝ) : ℂ) * I` and apply
  -- `Complex.exp_ofReal_mul_I_re` / `Complex.exp_ofReal_mul_I_im`.
  have hreshape : (I : ℂ) * (k : ℂ) * (s : ℂ) = ((k * s : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [hreshape]
  apply Complex.ext
  · -- real part:  Real.cos (k*s)  =  (exp ((k*s : ℝ) * I)).re
    rw [Complex.exp_ofReal_mul_I_re]
  · -- imaginary part: Real.sin (k*s) = (exp ((k*s : ℝ) * I)).im
    rw [Complex.exp_ofReal_mul_I_im]

/-- At zero dephasing, `dephasedAmplitude k 0 s = expAmplitude k s` is the
    pure phase. -/
lemma dephasedAmplitude_zero_dephasing (k s : ℝ) :
    dephasedAmplitude k 0 s
      = UnifiedTheory.LayerB.PropagationRule.expAmplitude k s := by
  unfold dephasedAmplitude UnifiedTheory.LayerB.PropagationRule.expAmplitude
  apply Complex.ext <;> simp

/-- **Bridge theorem.** Suppose the wave-vector `k`, β-periodicity for the
    pure-phase amplitude:

        `expAmplitude k (s + β) = expAmplitude k s` for all `s`,

    with `β > 0`. Then `k` is forced onto the Matsubara lattice
    `(2π/β) · ℤ`.

    This is the genuine derivation of frequency discreteness from thermal
    periodicity, restricted to the dephasing-free regime where
    `dephasedAmplitude k 0 s = expAmplitude k s`. -/
theorem expAmplitude_periodic_iff_matsubara {k β : ℝ} (hβ : 0 < β) :
    (∀ s : ℝ,
      UnifiedTheory.LayerB.PropagationRule.expAmplitude k (s + β)
        = UnifiedTheory.LayerB.PropagationRule.expAmplitude k s)
      ↔ ∃ n : ℤ, k = 2 * Real.pi * n / β := by
  constructor
  · intro hper
    -- Specialize to s = 0
    have h0 := hper 0
    rw [zero_add] at h0
    rw [expAmplitude_eq_exp, expAmplitude_eq_exp] at h0
    -- expAmplitude k 0 = exp(I·k·0) = exp 0 = 1.
    have hzero : Complex.exp ((I : ℂ) * (k : ℂ) * ((0 : ℝ) : ℂ)) = 1 := by
      rw [show ((0 : ℝ) : ℂ) = (0 : ℂ) by norm_cast]
      rw [show (I : ℂ) * (k : ℂ) * 0 = 0 by ring]
      exact Complex.exp_zero
    rw [hzero] at h0
    -- h0 : 1 = exp (I · k · β)  (or its symm)
    exact matsubara_quantized hβ h0
  · rintro ⟨n, hk⟩ s
    -- Pure-phase amplitudes factor multiplicatively in s and the period
    -- factor `exp(I·k·β)` is 1 by Matsubara.
    rw [expAmplitude_eq_exp, expAmplitude_eq_exp]
    have hphase :
        (I : ℂ) * (k : ℂ) * ((s + β : ℝ) : ℂ)
          = (I : ℂ) * (k : ℂ) * (s : ℂ) + (I : ℂ) * (k : ℂ) * (β : ℂ) := by
      push_cast; ring
    rw [hphase, Complex.exp_add]
    have hβphase : Complex.exp ((I : ℂ) * (k : ℂ) * (β : ℂ)) = 1 :=
      matsubara_inverse hβ n hk
    rw [hβphase, mul_one]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: WHY THE FULL `dephasedAmplitude` CAN'T BE β-PERIODIC
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The squared modulus of the dephased amplitude is `e^{-2 Γ s}`,
    isolating the decay envelope from the phase. -/
private lemma normSq_dephasedAmplitude (k Γ s : ℝ) :
    Complex.normSq (dephasedAmplitude k Γ s) = Real.exp (-2 * Γ * s) := by
  unfold dephasedAmplitude
  rw [Complex.normSq_apply]
  simp only []
  -- normSq ⟨e^{-Γs}·cos, e^{-Γs}·sin⟩
  --   = (e^{-Γs}·cos)² + (e^{-Γs}·sin)²
  --   = (e^{-Γs})² · (cos² + sin²)
  --   = (e^{-Γs})²
  --   = e^{-2 Γ s}
  have hpyth := Real.sin_sq_add_cos_sq (k * s)
  have hexp_sq : Real.exp (-Γ * s) * Real.exp (-Γ * s) = Real.exp (-2 * Γ * s) := by
    rw [← Real.exp_add]
    congr 1; ring
  nlinarith [hpyth, hexp_sq, Real.exp_pos (-Γ * s),
             sq_nonneg (Real.cos (k * s)), sq_nonneg (Real.sin (k * s))]

/-- **Honest scope statement.** With strictly positive dephasing `Γ > 0`,
    the dephased amplitude cannot be β-periodic in `s`: its modulus
    decays exponentially, so any periodic identity would force the
    decay envelope to be constant, contradicting `Γ > 0`. The bridge
    theorem above is therefore correctly stated only for the
    dephasing-free pure-phase regime. -/
theorem dephasing_pos_not_periodic {k Γ β : ℝ} (hΓ : 0 < Γ) (hβ : 0 < β) :
    ¬ (∀ s : ℝ, dephasedAmplitude k Γ (s + β) = dephasedAmplitude k Γ s) := by
  intro hper
  -- Take normSq of the periodicity identity at s = 0.
  have h0 := hper 0
  have hns := congrArg Complex.normSq h0
  rw [normSq_dephasedAmplitude, normSq_dephasedAmplitude] at hns
  rw [zero_add] at hns
  -- hns : exp(-2Γβ) = exp(-2Γ·0) = exp 0 = 1
  rw [show -2 * Γ * (0 : ℝ) = 0 by ring, Real.exp_zero] at hns
  -- exp is strictly monotone; so exp(-2Γβ) < 1 because -2Γβ < 0.
  have hneg : -2 * Γ * β < 0 := by
    have h1 : 0 < 2 * Γ * β := by positivity
    linarith
  have h_exp_lt : Real.exp (-2 * Γ * β) < 1 := by
    have : Real.exp (-2 * Γ * β) < Real.exp 0 := Real.exp_lt_exp.mpr hneg
    rwa [Real.exp_zero] at this
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **GENUINE MATSUBARA QUANTIZATION.**

    All four facts bundled:

    (1) `exp_iωβ_one_iff` — the genuine biconditional:
        for `β > 0`, `e^{i ω β} = 1 ↔ ∃ n : ℤ, ω = 2π n / β`.
        This DERIVES discreteness of allowed frequencies from
        β-periodicity of the imaginary-time phase, in contrast
        to the previous `KMSFromDephasing.matsubara` lemma which
        was the trivial `(2π n / β) · β = 2π n`.

    (2) `expAmplitude_periodic_iff_matsubara` — the framework
        connection: a pure-phase amplitude `expAmplitude k s` is
        β-periodic in `s` iff `k` is on the Matsubara lattice.

    (3) `dephasing_pos_not_periodic` — the honest scope:
        with `Γ > 0`, no dephased amplitude can be β-periodic,
        so the bridge theorem genuinely lives in the
        dephasing-free regime.

    (4) `matsubara_inverse` — the easy direction reaffirmed.

    NOT INCLUDED (still out of scope):
      • Full KMS condition for thermal two-point functions
        (requires modular automorphisms + analytic continuation).
      • Convergence of Matsubara sums.
      • Connection to the Tomita–Takesaki modular operator. -/
theorem matsubara_genuine :
    -- (1) Genuine biconditional — discreteness DERIVED from periodicity.
    (∀ ω β : ℝ, 0 < β →
        (Complex.exp ((I : ℂ) * (ω : ℂ) * (β : ℂ)) = 1 ↔
          ∃ n : ℤ, ω = 2 * Real.pi * n / β))
    -- (2) Framework bridge: pure-phase β-periodicity ⇔ Matsubara mode.
    ∧ (∀ k β : ℝ, 0 < β →
        ((∀ s : ℝ,
            UnifiedTheory.LayerB.PropagationRule.expAmplitude k (s + β)
              = UnifiedTheory.LayerB.PropagationRule.expAmplitude k s)
          ↔ ∃ n : ℤ, k = 2 * Real.pi * n / β))
    -- (3) Honest scope: dephasing > 0 obstructs β-periodicity entirely.
    ∧ (∀ k Γ β : ℝ, 0 < Γ → 0 < β →
        ¬ (∀ s : ℝ, dephasedAmplitude k Γ (s + β) = dephasedAmplitude k Γ s))
    -- (4) Reverse direction reaffirmed: Matsubara modes give β-periodicity.
    ∧ (∀ ω β : ℝ, 0 < β → ∀ n : ℤ,
        ω = 2 * Real.pi * n / β →
        Complex.exp ((I : ℂ) * (ω : ℂ) * (β : ℂ)) = 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω β hβ; exact exp_iωβ_one_iff hβ
  · intro k β hβ; exact expAmplitude_periodic_iff_matsubara hβ
  · intro k Γ β hΓ hβ; exact dephasing_pos_not_periodic hΓ hβ
  · intro ω β hβ n hω; exact matsubara_inverse hβ n hω

end UnifiedTheory.LayerB.MatsubaraQuantization
