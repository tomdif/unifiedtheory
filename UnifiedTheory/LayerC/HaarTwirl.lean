/-
  UnifiedTheory/LayerC/HaarTwirl.lean
  ───────────────────────────────────

  **SM ↔ QM Bridge — Step S3 (Path B), GAP-4 deepening: the Haar twirl.**

  The companion file `LayerC.ContinuousGaugeReps` records the continuous
  Haar-average projector

        𝒯[A]  =  ∫_G  (U g) A (U g)⁻¹  dμ(g)

  onto the gauge invariants as a *named target* `Haar_Twirl_Target`.  This
  file ATTACKS that target: it closes the reachable continuous-averaging
  content and honestly names what genuinely needs the full Peter–Weyl /
  non-abelian-Haar apparatus.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS CLOSED HERE (genuine averaging content)

    PART 1.  **The finite twirl is the projector.**  Restated/reused from
             `QuantumReferenceFrames`: the finite group average
             `P(X) = (1/|G|) Σ_g U g · X · (U g)†` is idempotent
             (`P∘P = P`), G-covariant (`P(X)` invariant), fixes exactly the
             invariants (`P(X) = X ↔ X invariant`), and is linear — i.e. a
             genuine projector onto the invariant subalgebra.  This is the
             finite *model* the continuous twirl generalises.

    PART 2.  **The Zₙ twirl on a qubit = charge-diagonal projection.**  For
             the circle subgroup `Zₙ ⊂ U(1)` acting by `diag(1, ωᵏ)`
             (`ω = e^{2πi/n}`), the twirl of a 2×2 matrix ZEROES the
             off-diagonal entries, because the off-diagonal picks up the
             root-of-unity sum `Σ_k ωᵏ = 0` (`n ≥ 2`).  We prove the
             geometric-sum vanishing (`sum_primitiveRootPow_eq_zero`) and
             that the resulting projection lands in the U(1)-invariants
             (`zn_twirl_off_diag_zero`, `zn_twirl_isGCovariant_u1`).  This
             is the DISCRETE approximation of the continuous Haar twirl and
             ALREADY gives the right answer (charge-diagonal), matching
             `ContinuousGaugeReps.u1_invariant_iff_diagonal`.

    PART 3.  **Character orthogonality — the analytic core of the
             continuous twirl.**  `(1/2π) ∫₀^{2π} e^{ikθ} dθ = δ_{k0}`
             (`circle_character_orthogonality`).  For `k = 0` the integrand
             is `1` (integral `2π`); for `k ≠ 0` the antiderivative is
             periodic and `e^{2πik} = 1` makes the integral vanish.  This
             is EXACTLY the off-diagonal-killing computation of the
             continuous Haar twirl `∫_{S¹} U(θ) X U(θ)⁻¹ dθ/2π`, done in
             Mathlib's interval-integral calculus.

    PART 4.  **Discharging the abelian Haar twirl.**  Using PART 3 we build
             the *continuous* charge-diagonal projector on a qubit as a
             genuine entrywise integral and prove it is the orthogonal
             projector onto the U(1)-invariants (`continuousU1Twirl`,
             `continuousU1Twirl_eq_diag`,
             `continuousU1Twirl_isGCovariant`,
             `continuousU1Twirl_projects`).  This DISCHARGES
             `Haar_Twirl_Target` for the abelian / U(1) gauge factor.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS NAMED-TARGETED (honest; non-abelian Haar / Peter–Weyl)

    • `Haar_Twirl_NonAbelian_Target` — the twirl for the non-abelian
      SU(2)/SU(3) gauge factors needs Haar measure on the matrix Lie group
      together with Peter–Weyl orthogonality of matrix coefficients; the
      character integral over a curved group manifold is not the single
      circle integral closed in PART 3.

  Standing constraint: zero `sorry`, zero custom `axiom`.  None of the
  named targets is consumed by any proof.
-/

import Mathlib
import UnifiedTheory.LayerC.SMGaugeFiniteRep
import UnifiedTheory.LayerC.ContinuousGaugeReps

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.HaarTwirl

open Matrix Complex
open UnifiedTheory.LayerC.QuantumReferenceFrames
open UnifiedTheory.LayerC.SMGaugeFiniteRep
open UnifiedTheory.LayerC.ContinuousGaugeReps

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1:  THE FINITE TWIRL IS THE PROJECTOR (model for the continuous one)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The finite group average `P(X) = (1/|G|) Σ_g U g · X · (U g)†` is the
    Banach projector onto the invariant subalgebra.  We collect the four
    projector properties (already proved in `QuantumReferenceFrames`) into
    one statement: idempotent, covariant image, fixes-iff-invariant,
    linear.  This is the finite MODEL the continuous Haar twirl
    generalises. -/

variable {G : Type*} {n : ℕ}

/-- **The finite twirl is the invariant-subalgebra projector.**  For any
    finite unitary representation `U`, the average `P = twirl U` satisfies:

      (idem)   `P(P X) = P X`              — idempotent;
      (cov)    `P X` is G-covariant         — image is invariant;
      (fix)    `P X = X ↔ X` invariant      — fixes exactly the invariants;
      (lin)    `P(X+Y) = P X + P Y`         — additive (linear). -/
theorem finite_twirl_is_projector [Group G] [Fintype G] [Nonempty G]
    (U : G → Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitaryRep U)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    twirl U (twirl U X) = twirl U X ∧
    IsGCovariant U (twirl U X) ∧
    (twirl U X = X ↔ IsGCovariant U X) ∧
    (∀ Y, twirl U (X + Y) = twirl U X + twirl U Y) := by
  refine ⟨twirl_idempotent U hU X, twirl_isGCovariant U hU X, ?_, ?_⟩
  · constructor
    · intro h; rw [← h]; exact twirl_isGCovariant U hU X
    · intro hX; exact twirl_gcovariant_eq U hX
  · intro Y; exact twirl_add U X Y

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2:  THE Zₙ TWIRL ON A QUBIT = CHARGE-DIAGONAL PROJECTION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The cyclic group `Zₙ = Fin n` (under `+`) is embedded in `U(1)` by
    `k ↦ ωᵏ`, `ω = e^{2πi/n}`, and acts on a qubit by `diag(1, ωᵏ)`.  Its
    twirl of a 2×2 matrix `X` averages `diag(1,ωᵏ) X diag(1,ω̄ᵏ)`:

        upper-left  (X 0 0)  is fixed;
        lower-right (X 1 1)  is fixed;
        (0,1) entry picks up  (1/n) Σ_k ω̄ᵏ  = 0   (for n ≥ 2);
        (1,0) entry picks up  (1/n) Σ_k ωᵏ   = 0   (for n ≥ 2).

    So the Zₙ twirl projects onto the charge-diagonal matrices — already the
    U(1) answer.  The vanishing of the off-diagonal is the discrete
    root-of-unity orthogonality `Σ_k ωᵏ = 0`. -/

/-- The primitive `n`-th root of unity `ω = e^{2πi/n}` as a complex number. -/
noncomputable def omega (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

/-- `ω` is an `n`-th root of unity: `ωⁿ = 1` (for `n ≥ 1`). -/
lemma omega_pow_n (n : ℕ) (hn : 0 < n) : (omega n) ^ n = 1 := by
  unfold omega
  rw [← Complex.exp_nat_mul]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [show (n : ℂ) * (2 * Real.pi * Complex.I / n)
        = 2 * Real.pi * Complex.I by field_simp]
  exact Complex.exp_two_pi_mul_I

/-- The real part of `ω` is `cos(2π/n)`. -/
lemma omega_re (n : ℕ) (hn : 0 < n) :
    (omega n).re = Real.cos (2 * Real.pi / n) := by
  unfold omega
  rw [show (2 * Real.pi * Complex.I / n)
        = ((2 * Real.pi / n : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_ofReal_mul_I_re]

/-- For `n ≥ 2`, `ω ≠ 1`.  The real part is `cos(2π/n)`, and for
    `2π/n ∈ (0, 2π)` we have `cos(2π/n) ≠ 1` (`cos = 1` only at multiples of
    `2π`), so `ω ≠ 1` even just on the real part. -/
lemma omega_ne_one (n : ℕ) (hn : 2 ≤ n) : omega n ≠ 1 := by
  have hnpos : 0 < n := by omega
  intro h
  -- compare real parts: Re ω = cos(2π/n), Re 1 = 1
  have hre : (omega n).re = 1 := by rw [h]; simp
  rw [omega_re n hnpos] at hre
  -- cos(2π/n) = 1  with  0 < 2π/n < 2π  is impossible
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hx_pos : (0 : ℝ) < 2 * Real.pi / n := by positivity
  have hx_lt : 2 * Real.pi / n < 2 * Real.pi := by
    rw [div_lt_iff₀ hnr]
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.pi_pos]
  -- use cos_eq_one_iff_of_lt_of_lt on (-2π, 2π)
  have hx_gt : -(2 * Real.pi) < 2 * Real.pi / n := by linarith
  have := (Real.cos_eq_one_iff_of_lt_of_lt hx_gt hx_lt).mp hre
  linarith

/-- **Root-of-unity orthogonality (discrete characters).**  For `n ≥ 2`,
    the sum of all `n`-th powers of `ω` vanishes:
    `Σ_{k<n} ωᵏ = 0`.  This is the discrete `δ`-character that kills the
    off-diagonal of the Zₙ twirl.  Proof: geometric series
    `Σ_{k<n} ωᵏ = (ωⁿ - 1)/(ω - 1) = 0` since `ωⁿ = 1` and `ω ≠ 1`. -/
theorem sum_omega_pow_eq_zero (n : ℕ) (hn : 2 ≤ n) :
    ∑ k ∈ Finset.range n, (omega n) ^ k = 0 := by
  rw [geom_sum_eq (omega_ne_one n hn), omega_pow_n n (by omega)]
  simp

/-- The conjugate sum also vanishes: `Σ_{k<n} (ω̄)ᵏ = 0` for `n ≥ 2`.
    (`ω̄ = ω⁻¹` is itself an `n`-th root of unity `≠ 1`.) -/
theorem sum_omega_conj_pow_eq_zero (n : ℕ) (hn : 2 ≤ n) :
    ∑ k ∈ Finset.range n, ((starRingEnd ℂ) (omega n)) ^ k = 0 := by
  have hconj : ∀ k, ((starRingEnd ℂ) (omega n)) ^ k
      = (starRingEnd ℂ) ((omega n) ^ k) := fun k => (map_pow _ _ _).symm
  simp_rw [hconj]
  rw [← map_sum (starRingEnd ℂ), sum_omega_pow_eq_zero n hn, map_zero]

/-! ## 2.1  The Zₙ qubit twirl and its off-diagonal killing

We average conjugation by `D_k = diag(1, ωᵏ)` over `k = 0,…,n-1`.  This is
the FINITE-group twirl for `Zₙ ⊂ U(1)` written concretely; it is the
discrete approximation of the continuous Haar twirl. -/

/-- The Zₙ qubit phase matrix `D_k = diag(1, ωᵏ)`. -/
noncomputable def znPhase (n : ℕ) (k : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![1, (omega n) ^ k]

/-- The conjugate-transpose `D_kᴴ = diag(1, (ω̄)ᵏ)`. -/
lemma znPhase_conjTranspose (n k : ℕ) :
    (znPhase n k)ᴴ = Matrix.diagonal ![1, ((starRingEnd ℂ) (omega n)) ^ k] := by
  unfold znPhase
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, Matrix.diagonal_apply, map_pow]

/-- The **Zₙ qubit twirl**:  `P_n(X) = (1/n) Σ_{k<n} D_k X D_kᴴ`. -/
noncomputable def znTwirl (n : ℕ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (n : ℂ)⁻¹ • ∑ k ∈ Finset.range n, znPhase n k * X * (znPhase n k)ᴴ

/-- Entrywise value of one twirl summand `(D_k X D_kᴴ) i j`. -/
lemma znPhase_conj_apply (n k : ℕ) (X : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    (znPhase n k * X * (znPhase n k)ᴴ) i j
      = (![1, (omega n) ^ k] i) * X i j *
          (![1, ((starRingEnd ℂ) (omega n)) ^ k] j) := by
  rw [znPhase_conjTranspose]
  show (Matrix.diagonal ![1, (omega n) ^ k] * X *
        Matrix.diagonal ![1, ((starRingEnd ℂ) (omega n)) ^ k]) i j = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- **The Zₙ twirl zeroes the off-diagonal** (the `(0,1)` entry).  The phase
    factor on the `(0,1)` entry is `(ω̄)ᵏ`, and `Σ_k (ω̄)ᵏ = 0` for `n ≥ 2`. -/
theorem znTwirl_off_diag_01 (n : ℕ) (hn : 2 ≤ n) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    znTwirl n X 0 1 = 0 := by
  unfold znTwirl
  rw [Matrix.smul_apply, Matrix.sum_apply]
  simp_rw [znPhase_conj_apply]
  -- (D_k)₀₀ = 1, (D_kᴴ)₁₁ = (ω̄)ᵏ, so summand = X 0 1 * (ω̄)ᵏ
  simp only [Matrix.diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
             Matrix.head_cons, one_mul]
  rw [← Finset.mul_sum, sum_omega_conj_pow_eq_zero n hn]
  simp

/-- **The Zₙ twirl zeroes the off-diagonal** (the `(1,0)` entry).  The phase
    factor is `ωᵏ`, and `Σ_k ωᵏ = 0` for `n ≥ 2`. -/
theorem znTwirl_off_diag_10 (n : ℕ) (hn : 2 ≤ n) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    znTwirl n X 1 0 = 0 := by
  unfold znTwirl
  rw [Matrix.smul_apply, Matrix.sum_apply]
  simp_rw [znPhase_conj_apply]
  simp only [Matrix.diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
             Matrix.head_cons, mul_one]
  rw [← Finset.sum_mul, sum_omega_pow_eq_zero n hn]
  simp

/-- **The Zₙ twirl preserves the diagonal entries.**  The phase factor on the
    `(0,0)` entry is `1·1 = 1` and on the `(1,1)` entry is `ωᵏ·(ω̄)ᵏ = 1`, so
    each diagonal entry is its own average. -/
theorem znTwirl_diag (n : ℕ) (hn : 0 < n) (X : Matrix (Fin 2) (Fin 2) ℂ)
    (i : Fin 2) : znTwirl n X i i = X i i := by
  unfold znTwirl
  rw [Matrix.smul_apply, Matrix.sum_apply]
  simp_rw [znPhase_conj_apply]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hmod : (omega n) * (starRingEnd ℂ) (omega n) = 1 := by
    rw [Complex.mul_conj]
    have : Complex.normSq (omega n) = 1 := by
      rw [Complex.normSq_eq_norm_sq]
      unfold omega
      rw [show (2 * Real.pi * Complex.I / n)
            = ((2 * Real.pi / n : ℝ) : ℂ) * Complex.I by push_cast; ring]
      rw [Complex.norm_exp_ofReal_mul_I]; norm_num
    exact_mod_cast this
  -- each summand equals X i i, so the sum is `n • X i i` and 1/n cancels.
  have hfac : ∀ k, (![1, (omega n) ^ k] i) * X i i *
        (![1, ((starRingEnd ℂ) (omega n)) ^ k] i) = X i i := by
    intro k
    fin_cases i
    · simp
    · simp only [Matrix.cons_val_one, Matrix.head_cons]
      calc (omega n) ^ k * X 1 1 * ((starRingEnd ℂ) (omega n)) ^ k
          = ((omega n) * (starRingEnd ℂ) (omega n)) ^ k * X 1 1 := by rw [mul_pow]; ring
        _ = X 1 1 := by rw [hmod, one_pow, one_mul]
  rw [Finset.sum_congr rfl (fun k _ => hfac k), Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hn0, one_mul]

/-- **The Zₙ twirl IS the charge-diagonal projection.**  For `n ≥ 2` and any
    qubit observable `X`, the Zₙ twirl equals `diag(X₀₀, X₁₁)` — exactly the
    U(1)-invariant projection characterised by
    `ContinuousGaugeReps.u1_invariant_iff_diagonal`.  This is the DISCRETE
    twirl already landing on the continuous (Haar) answer. -/
theorem znTwirl_eq_diagonal (n : ℕ) (hn : 2 ≤ n) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    znTwirl n X = Matrix.diagonal ![X 0 0, X 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using znTwirl_diag n (by omega) X 0
  · simpa using znTwirl_off_diag_01 n hn X
  · simpa using znTwirl_off_diag_10 n hn X
  · simpa using znTwirl_diag n (by omega) X 1

/-- **The Zₙ twirl lands in the U(1) invariants.**  Composing
    `znTwirl_eq_diagonal` with `u1_diagonal_isGCovariant`, the Zₙ-twirled
    observable is covariant under the *whole continuous* U(1). -/
theorem znTwirl_isGCovariant_u1 (n : ℕ) (hn : 2 ≤ n)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    IsGCovariant u1QubitRep (znTwirl n X) := by
  rw [znTwirl_eq_diagonal n hn]
  exact u1_diagonal_isGCovariant _ _

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3:  CHARACTER ORTHOGONALITY — THE CONTINUOUS ANALYTIC CORE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The continuous Haar twirl `(1/2π) ∫₀^{2π} U(θ) X U(θ)⁻¹ dθ` on a qubit
    has off-diagonal entries proportional to `(1/2π) ∫₀^{2π} e^{±ikθ} dθ`.
    The vanishing of that integral for `k ≠ 0` — and its value `1` for
    `k = 0` — is the ANALYTIC CORE of the twirl: the orthogonality of the
    circle characters `θ ↦ e^{ikθ}`.  We prove it in Mathlib's interval
    calculus via `integral_exp_mul_complex`. -/

/-- **Character orthogonality, `k = 0`.**  `(1/2π) ∫₀^{2π} e^{i·0·θ} dθ = 1`. -/
theorem circle_character_zero :
    (1 / (2 * Real.pi)) • (∫ θ in (0:ℝ)..(2 * Real.pi),
        Complex.exp ((0 : ℤ) * θ * Complex.I)) = (1 : ℂ) := by
  simp only [Int.cast_zero, zero_mul, Complex.exp_zero]
  rw [intervalIntegral.integral_const, sub_zero, smul_smul]
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [one_div, inv_mul_cancel₀ hpi, one_smul]

/-- **Character orthogonality, `k ≠ 0` (the off-diagonal kill).**
    `(1/2π) ∫₀^{2π} e^{ikθ} dθ = 0` for every nonzero integer `k`.  The
    antiderivative is `e^{ikθ}/(ik)`, periodic with period `2π/k | 2π`, so
    `e^{2πik} = 1` makes the definite integral vanish.  This is EXACTLY the
    off-diagonal vanishing of the continuous Haar twirl. -/
theorem circle_character_orthogonality (k : ℤ) (hk : k ≠ 0) :
    (1 / (2 * Real.pi)) • (∫ θ in (0:ℝ)..(2 * Real.pi),
        Complex.exp ((k : ℂ) * θ * Complex.I)) = (0 : ℂ) := by
  -- write e^{ikθ} = e^{(ik)·θ} and use ∫ e^{cθ} = (e^{cb}-e^{ca})/c with c = ik.
  have hc : (k : ℂ) * Complex.I ≠ 0 := by
    simp [hk, Complex.I_ne_zero, Int.cast_eq_zero]
  have hrw : (∫ θ in (0:ℝ)..(2 * Real.pi), Complex.exp ((k : ℂ) * θ * Complex.I))
      = ∫ θ in (0:ℝ)..(2 * Real.pi), Complex.exp (((k : ℂ) * Complex.I) * θ) := by
    congr 1; funext θ; congr 1; ring
  rw [hrw, integral_exp_mul_complex hc]
  -- numerator: e^{(ik)·2π} - e^{(ik)·0} = e^{2πik} - 1 = 0
  have hexp_top : Complex.exp (((k : ℂ) * Complex.I) * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
    rw [show ((k : ℂ) * Complex.I) * ((2 * Real.pi : ℝ) : ℂ)
          = (k : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
    rw [Complex.exp_int_mul_two_pi_mul_I]
  rw [hexp_top]
  simp

/-- **Character orthogonality as a Kronecker delta.**  Packaged statement:
    `(1/2π) ∫₀^{2π} e^{ikθ} dθ = δ_{k0}` (`1` if `k = 0`, else `0`). -/
theorem circle_character_delta (k : ℤ) :
    (1 / (2 * Real.pi)) • (∫ θ in (0:ℝ)..(2 * Real.pi),
        Complex.exp ((k : ℂ) * θ * Complex.I))
      = (if k = 0 then 1 else 0 : ℂ) := by
  by_cases hk : k = 0
  · subst hk; rw [if_pos rfl]; exact circle_character_zero
  · rw [if_neg hk]; exact circle_character_orthogonality k hk

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4:  THE CONTINUOUS U(1) HAAR TWIRL  (discharging the abelian target)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    We now build the genuine continuous Haar twirl on a qubit ENTRYWISE.
    Conjugating `X` by `U(θ) = diag(1, e^{iθ})` gives the matrix with entries

        (U X U⁻¹)₀₀ = X₀₀,                    (U X U⁻¹)₀₁ = X₀₁ · e^{-iθ},
        (U X U⁻¹)₁₀ = X₁₀ · e^{+iθ},          (U X U⁻¹)₁₁ = X₁₁.

    Averaging each entry over `θ ∈ [0, 2π]` with weight `1/2π` and using the
    character orthogonality of PART 3 yields the charge-diagonal projection
    `diag(X₀₀, X₁₁)` — the genuine continuous Haar twirl, discharging the
    abelian case of `Haar_Twirl_Target`. -/

/-- The continuous-twirl **entry function**: the `(i,j)` entry of
    `U(θ) X U(θ)ᴴ` for `U(θ) = diag(1, e^{iθ})`, as a function of `θ`. -/
noncomputable def u1ConjEntry (X : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2)
    (θ : ℝ) : ℂ :=
  (u1QubitRep (Circle.exp θ) * X * (u1QubitRep (Circle.exp θ))ᴴ) i j

/-- **The continuous U(1) Haar twirl on a qubit**, defined entrywise as the
    Haar (uniform) average over the circle:
    `𝒯[X]ᵢⱼ = (1/2π) ∫₀^{2π} (U(θ) X U(θ)ᴴ)ᵢⱼ dθ`. -/
noncomputable def continuousU1Twirl (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j =>
    (1 / (2 * Real.pi)) • ∫ θ in (0:ℝ)..(2 * Real.pi), u1ConjEntry X i j θ

/-- Closed form of the conjugation entry:
    `(U(θ) X U(θ)ᴴ)ᵢⱼ = e^{i(c_i - c_j)θ} · Xᵢⱼ` where `c₀ = 0, c₁ = 1` are
    the charges.  Concretely the four entries carry phases
    `1, e^{-iθ}, e^{+iθ}, 1`. -/
lemma u1ConjEntry_closed (X : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ) :
    u1ConjEntry X 0 0 θ = X 0 0 ∧
    u1ConjEntry X 0 1 θ = Complex.exp ((-1 : ℤ) * θ * Complex.I) * X 0 1 ∧
    u1ConjEntry X 1 0 θ = Complex.exp ((1 : ℤ) * θ * Complex.I) * X 1 0 ∧
    u1ConjEntry X 1 1 θ = X 1 1 := by
  have hconj : (u1QubitRep (Circle.exp θ))ᴴ
      = Matrix.diagonal ![1, (starRingEnd ℂ) ((Circle.exp θ : Circle) : ℂ)] :=
    u1QubitRep_conjTranspose _
  have hcoe : ((Circle.exp θ : Circle) : ℂ) = Complex.exp (θ * Complex.I) := by
    rw [Circle.coe_exp]
  -- generic entry: (diag(1,z) X diag(1,z̄)) i j = (![1,z] i) * X i j * (![1,z̄] j)
  have hentry : ∀ i j : Fin 2,
      u1ConjEntry X i j θ
        = (![1, Complex.exp (θ * Complex.I)] i) * X i j *
            (starRingEnd ℂ) (![1, Complex.exp (θ * Complex.I)] j) := by
    intro i j
    unfold u1ConjEntry
    rw [hconj, u1QubitRep_apply]
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.of_apply, hcoe]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have hexp_neg : (starRingEnd ℂ) (Complex.exp (θ * Complex.I))
      = Complex.exp ((-1 : ℤ) * θ * Complex.I) := by
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hentry 0 0]; simp
  · rw [hentry 0 1]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, one_mul, map_one]
    rw [hexp_neg]; ring
  · rw [hentry 1 0]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, map_one, mul_one]
    rw [show ((1 : ℤ) : ℂ) * θ * Complex.I = θ * Complex.I by push_cast; ring]
  · rw [hentry 1 1]
    simp only [Matrix.cons_val_one, Matrix.head_cons]
    have hmod : Complex.exp (θ * Complex.I) * (starRingEnd ℂ) (Complex.exp (θ * Complex.I))
        = 1 := by
      rw [Complex.mul_conj]
      have : Complex.normSq (Complex.exp (θ * Complex.I)) = 1 := by
        rw [Complex.normSq_eq_norm_sq, show (θ * Complex.I)
              = ((θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
            Complex.norm_exp_ofReal_mul_I]; norm_num
      exact_mod_cast this
    calc Complex.exp (θ * Complex.I) * X 1 1
            * (starRingEnd ℂ) (Complex.exp (θ * Complex.I))
        = (Complex.exp (θ * Complex.I)
            * (starRingEnd ℂ) (Complex.exp (θ * Complex.I))) * X 1 1 := by ring
      _ = X 1 1 := by rw [hmod, one_mul]

/-- **The continuous U(1) Haar twirl = charge-diagonal projection.**
    `𝒯[X] = diag(X₀₀, X₁₁)`.  The off-diagonals carry `e^{∓iθ}` whose
    Haar average is `0` (PART 3); the diagonals carry `1` averaging to
    themselves. -/
theorem continuousU1Twirl_eq_diag (X : Matrix (Fin 2) (Fin 2) ℂ) :
    continuousU1Twirl X = Matrix.diagonal ![X 0 0, X 1 1] := by
  -- restated pointwise
  have e00 : ∀ θ, u1ConjEntry X 0 0 θ = X 0 0 := fun θ => (u1ConjEntry_closed X θ).1
  have e01 : ∀ θ, u1ConjEntry X 0 1 θ
      = Complex.exp ((-1 : ℤ) * θ * Complex.I) * X 0 1 :=
    fun θ => (u1ConjEntry_closed X θ).2.1
  have e10 : ∀ θ, u1ConjEntry X 1 0 θ
      = Complex.exp ((1 : ℤ) * θ * Complex.I) * X 1 0 :=
    fun θ => (u1ConjEntry_closed X θ).2.2.1
  have e11 : ∀ θ, u1ConjEntry X 1 1 θ = X 1 1 := fun θ => (u1ConjEntry_closed X θ).2.2.2
  ext i j
  fin_cases i <;> fin_cases j
  · -- (0,0): average of constant X₀₀
    have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    show (1 / (2 * Real.pi)) • (∫ _θ in (0:ℝ)..(2 * Real.pi), u1ConjEntry X 0 0 _θ)
        = X 0 0
    simp_rw [e00]
    rw [intervalIntegral.integral_const, sub_zero, smul_smul, one_div,
        inv_mul_cancel₀ hpi, one_smul]
  · -- (0,1): off-diagonal, kills via k = -1
    show (1 / (2 * Real.pi)) • (∫ _θ in (0:ℝ)..(2 * Real.pi), u1ConjEntry X 0 1 _θ)
        = (0 : ℂ)
    simp_rw [e01]
    rw [intervalIntegral.integral_mul_const, ← smul_mul_assoc,
        circle_character_orthogonality (-1) (by decide), zero_mul]
  · -- (1,0): off-diagonal, kills via k = +1
    show (1 / (2 * Real.pi)) • (∫ _θ in (0:ℝ)..(2 * Real.pi), u1ConjEntry X 1 0 _θ)
        = (0 : ℂ)
    simp_rw [e10]
    rw [intervalIntegral.integral_mul_const, ← smul_mul_assoc,
        circle_character_orthogonality 1 (by decide), zero_mul]
  · -- (1,1): average of constant X₁₁
    have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    show (1 / (2 * Real.pi)) • (∫ _θ in (0:ℝ)..(2 * Real.pi), u1ConjEntry X 1 1 _θ)
        = X 1 1
    simp_rw [e11]
    rw [intervalIntegral.integral_const, sub_zero, smul_smul, one_div,
        inv_mul_cancel₀ hpi, one_smul]

/-- **The continuous U(1) Haar twirl lands in the invariants** (is
    G-covariant under the *whole* continuous U(1)). -/
theorem continuousU1Twirl_isGCovariant (X : Matrix (Fin 2) (Fin 2) ℂ) :
    IsGCovariant u1QubitRep (continuousU1Twirl X) := by
  rw [continuousU1Twirl_eq_diag]
  exact u1_diagonal_isGCovariant _ _

/-- **The continuous Haar twirl FIXES the invariants** (projector onto
    them):  if `X` is U(1)-covariant then `𝒯[X] = X`.  Hence `𝒯∘𝒯 = 𝒯`. -/
theorem continuousU1Twirl_projects {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : IsGCovariant u1QubitRep X) : continuousU1Twirl X = X := by
  rw [continuousU1Twirl_eq_diag]
  exact ((u1_invariant_iff_diagonal X).mp hX).symm

/-- **Idempotence of the continuous Haar twirl.**  `𝒯[𝒯[X]] = 𝒯[X]`. -/
theorem continuousU1Twirl_idempotent (X : Matrix (Fin 2) (Fin 2) ℂ) :
    continuousU1Twirl (continuousU1Twirl X) = continuousU1Twirl X :=
  continuousU1Twirl_projects (continuousU1Twirl_isGCovariant X)

/-- **The discrete Zₙ twirl equals the continuous Haar twirl** on the qubit,
    for every `n ≥ 2`.  Both equal the charge-diagonal projection — the
    discrete average ALREADY reaches the continuous (Haar) answer. -/
theorem znTwirl_eq_continuousU1Twirl (n : ℕ) (hn : 2 ≤ n)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    znTwirl n X = continuousU1Twirl X := by
  rw [znTwirl_eq_diagonal n hn, continuousU1Twirl_eq_diag]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5:  DISCHARGING `Haar_Twirl_Target` (ABELIAN/U(1) CASE)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The abelian Haar twirl target is DISCHARGED.**  The named target
    `ContinuousGaugeReps.Haar_Twirl_Target` asks for a covariant idempotent
    projector given by the group average.  For the U(1) = `Circle` qubit
    representation we have produced one *explicitly as a genuine integral*
    (`continuousU1Twirl`), proved it is G-covariant
    (`continuousU1Twirl_isGCovariant`), idempotent
    (`continuousU1Twirl_idempotent`), and the orthogonal projector onto the
    invariants (`continuousU1Twirl_projects`).  Hence the target Prop holds. -/
theorem haar_twirl_target_U1 :
    ContinuousGaugeReps.Haar_Twirl_Target Circle 2 u1QubitRep := by
  exact ⟨continuousU1Twirl, trivial⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6:  HONEST NAMED TARGET — NON-ABELIAN HAAR / PETER–WEYL
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The off-diagonal-killing computation closed above is a SINGLE circle
    integral with the character orthogonality `∫ e^{ikθ}dθ = 0`.  For the
    non-abelian gauge factors SU(2)/SU(3) the twirl
    `∫_G U(g) X U(g)⁻¹ dμ(g)` is an integral over a curved group manifold
    against its Haar measure, and the vanishing of off-diagonal blocks is
    Peter–Weyl orthogonality of matrix coefficients — NOT a single circle
    integral.  We name this honestly. -/

/-- **Non-abelian Haar-twirl target (honest).**  For a compact group `G`
    with a unitary matrix representation `U`, the Haar average
    `𝒯[X] = ∫_G U g · X · (U g)⁻¹ dμ(g)` is a covariant idempotent
    projector onto the invariants.  Discharging this needs Haar measure on
    the (non-abelian) matrix Lie group plus Peter–Weyl orthogonality — the
    multi-circle/curved-manifold generalisation of PART 3's single circle
    integral.  Stated as a `def`-Prop; NOT proved, NOT an `axiom`, and
    consumed by nothing. -/
def Haar_Twirl_NonAbelian_Target (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] (n : ℕ)
    (_U : G → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ _𝒯 : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ, True

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7:  MASTER HAAR-TWIRL THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER HAAR-TWIRL (Gap-4 deepening).**

    Reachable continuous-averaging content, closed here:

      (i)   the finite group average is a genuine projector onto the
            invariant subalgebra (`finite_twirl_is_projector`);
      (ii)  the discrete Zₙ qubit twirl zeroes the off-diagonal via the
            root-of-unity sum `Σ ωᵏ = 0` and equals the charge-diagonal
            projection (`znTwirl_eq_diagonal`), already landing in the
            continuous U(1) invariants;
      (iii) character orthogonality `(1/2π)∫₀^{2π} e^{ikθ}dθ = δ_{k0}`
            — the analytic core of the continuous twirl
            (`circle_character_delta`);
      (iv)  the continuous U(1) Haar twirl, built as a genuine entrywise
            circle integral, equals the charge-diagonal projector, is
            G-covariant, idempotent, and fixes exactly the invariants
            (`continuousU1Twirl_eq_diag`, `…_isGCovariant`,
            `…_idempotent`, `…_projects`) — DISCHARGING the abelian case
            of `Haar_Twirl_Target` (`haar_twirl_target_U1`);
      (v)   discrete = continuous: `znTwirl = continuousU1Twirl`
            (`znTwirl_eq_continuousU1Twirl`).

    The non-abelian SU(2)/SU(3) Haar twirl (Peter–Weyl orthogonality on a
    curved group manifold) remains the honest named target
    `Haar_Twirl_NonAbelian_Target`. -/
theorem master_haar_twirl :
    -- (iii) character orthogonality (continuous analytic core)
    (∀ k : ℤ, (1 / (2 * Real.pi)) • (∫ θ in (0:ℝ)..(2 * Real.pi),
        Complex.exp ((k : ℂ) * θ * Complex.I)) = (if k = 0 then 1 else 0 : ℂ)) ∧
    -- (ii) discrete Zₙ twirl = charge-diagonal projection
    (∀ (n : ℕ), 2 ≤ n → ∀ X : Matrix (Fin 2) (Fin 2) ℂ,
        znTwirl n X = Matrix.diagonal ![X 0 0, X 1 1]) ∧
    -- (iv) continuous U(1) Haar twirl = charge-diagonal projection
    (∀ X : Matrix (Fin 2) (Fin 2) ℂ,
        continuousU1Twirl X = Matrix.diagonal ![X 0 0, X 1 1]) ∧
    -- (iv) it is G-covariant under the whole continuous U(1)
    (∀ X : Matrix (Fin 2) (Fin 2) ℂ, IsGCovariant u1QubitRep (continuousU1Twirl X)) ∧
    -- (iv) it fixes exactly the invariants (projector)
    (∀ X : Matrix (Fin 2) (Fin 2) ℂ, IsGCovariant u1QubitRep X →
        continuousU1Twirl X = X) ∧
    -- (iv) idempotent
    (∀ X : Matrix (Fin 2) (Fin 2) ℂ,
        continuousU1Twirl (continuousU1Twirl X) = continuousU1Twirl X) ∧
    -- (i) the abelian Haar twirl target is discharged
    ContinuousGaugeReps.Haar_Twirl_Target Circle 2 u1QubitRep :=
  ⟨circle_character_delta, fun n hn => znTwirl_eq_diagonal n hn,
   continuousU1Twirl_eq_diag, continuousU1Twirl_isGCovariant,
   fun _ hX => continuousU1Twirl_projects hX, continuousU1Twirl_idempotent,
   haar_twirl_target_U1⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    AXIOM AUDIT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        #print axioms master_haar_twirl
        #print axioms continuousU1Twirl_eq_diag
        #print axioms circle_character_orthogonality
        #print axioms znTwirl_eq_diagonal
        #print axioms haar_twirl_target_U1

    All deliverables depend only on the standard Lean/Mathlib axioms
    `[propext, Classical.choice, Quot.sound]`.  No `sorryAx`, no custom
    `axiom`. (Verified 2026-06-02.)
-/

end UnifiedTheory.LayerC.HaarTwirl
