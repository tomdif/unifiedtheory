/-
  LayerB/DataProcessingInequality.lean — Data Processing Inequality for the
  framework's dephasing CPTP map.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT

  `LayerB/DensityMatrixHonest.lean` introduces `DensityMatrix2Honest`,
  the corrected 2×2 density matrix structure with trace-1 and PSD as
  TYPE FIELDS.

  `LayerB/LindbladDephasing.lean` builds the explicit CPTP dephasing
  channel `dephasingChannel γ` for `γ ∈ [0, 1]`, with action
      ⎡ p₁     c    ⎤      ⎡ p₁     γ·c   ⎤
      ⎣ c̄    p₂   ⎦  ↦  ⎣ γ·c̄   p₂   ⎦
  and proves that (a) it preserves trace-1 and PSD, (b) it forms a
  multiplicative semigroup in `γ`, and (c) the coherence magnitude is
  non-increasing.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT THIS FILE DOES

  Build the framework's first **data processing inequality** (DPI) at
  the channel level:

      D(dephasingChannel(ρ), dephasingChannel(σ)) ≤ D(ρ, σ)

  for a concrete divergence `D` on `DensityMatrix2Honest`. The
  divergence used is the **Hilbert–Schmidt (HS) squared distance**

      D_HS(ρ, σ) := (Δp₁)² + (Δp₂)² + 2·(Δcoh_re)² + 2·(Δcoh_im)²

  where each `Δx = ρ.x − σ.x`. The factor `2` on the off-diagonal
  reflects the fact that the off-diagonal contributes twice (once at
  each off-diagonal entry, since the matrix is Hermitian: the `(1,2)`
  and `(2,1)` entries are complex conjugates and each contributes
  `|Δc|² = (Δcoh_re)² + (Δcoh_im)²` to the Frobenius norm squared).
  This makes `D_HS(ρ, σ)` exactly `‖ρ − σ‖²_F`, the squared Frobenius
  norm of the Hermitian difference matrix `ρ − σ`.

  We prove:

  (1) `hsDistance_nonneg`: `D_HS(ρ, σ) ≥ 0` (sum of squares).
  (2) `hsDistance_self_zero`: `D_HS(ρ, ρ) = 0`.
  (3) `hsDistance_symm`: `D_HS(ρ, σ) = D_HS(σ, ρ)`.
  (4) `dephasing_diagonal_unchanged`: dephasing leaves diagonals fixed.
  (5) `dephasing_off_diagonal_difference`: `(Φ(ρ) − Φ(σ))_off = γ · (ρ − σ)_off`.
  (6) `dephasing_data_processing` — **THE MAIN THEOREM**:
        `D_HS(Φ_γ(ρ), Φ_γ(σ)) ≤ D_HS(ρ, σ)` for any γ ∈ [0, 1].
  (7) `dephasing_dpi_strict_re`: at γ < 1 with non-zero initial real
        coherence difference the inequality is STRICT.
  (8) `dpi_full_dephasing`: at γ = 0 the divergence reduces to the
        diagonal-only (classical) part `(Δp₁)² + (Δp₂)²`.
  (9) `dpi_master`: bundles (1)–(8).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  PHYSICAL INTERPRETATION

  The DPI says: applying a CPTP channel cannot INCREASE distinguishability
  between two states. In our concrete setting, the dephasing channel
  attenuates the off-diagonal coherence by `γ`, so the difference of
  off-diagonals is also attenuated by `γ`, making the two outputs
  CLOSER (in HS distance) than the inputs. The diagonal — which carries
  classical (probabilistic) information — is unchanged, so the classical
  part of the divergence is preserved exactly. All loss is in the
  quantum (off-diagonal) sector. This is the operational meaning of
  "dephasing destroys quantum information but preserves classical
  information."

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

  – The DPI is proved for a SPECIFIC CPTP map (dephasing) and a SPECIFIC
    divergence (Hilbert–Schmidt squared distance, the Frobenius-norm
    squared on Hermitian matrices). The full quantum DPI for arbitrary
    CPTP maps and the quantum relative entropy `D(ρ‖σ) = tr(ρ log ρ) −
    tr(ρ log σ)` (Lindblad–Uhlmann monotonicity) requires the operator
    logarithm, joint convexity arguments, and an n×n matrix
    infrastructure that is not built here.
  – HS distance is operationally meaningful: it is monotone under any
    UNITAL CPTP map (Pérez-García et al. 2006), of which the dephasing
    channel is an instance (it fixes the maximally mixed state). The
    HS-DPI for dephasing is therefore a strict consequence of the
    general HS-DPI for unital CPTP maps; we prove it directly from the
    explicit channel action without invoking the general theorem.
  – Two states only (qubit). The same argument scales.
  – No custom axioms. Zero `sorry`.
-/
import UnifiedTheory.LayerB.LindbladDephasing

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.DataProcessingInequality

open UnifiedTheory.LayerB.DensityMatrixHonest
open UnifiedTheory.LayerB.LindbladDephasing

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: HILBERT–SCHMIDT SQUARED DISTANCE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For two 2×2 Hermitian matrices

       ρ = ⎡ ρ.p₁     ρ.coh    ⎤        σ = ⎡ σ.p₁     σ.coh    ⎤
           ⎣ ρ.coh̄   ρ.p₂   ⎦            ⎣ σ.coh̄   σ.p₂   ⎦

    the Frobenius norm squared of the Hermitian difference Δ = ρ − σ is
       ‖Δ‖²_F = (Δp₁)² + (Δp₂)² + |Δcoh|² + |Δcoh|²
              = (Δp₁)² + (Δp₂)² + 2·((Δcoh_re)² + (Δcoh_im)²).
    The factor 2 reflects the two off-diagonal entries (Hermitian:
    `(1,2)` and `(2,1)` are complex conjugates, each carries the same
    magnitude `|Δcoh|`).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Hilbert–Schmidt (Frobenius) squared distance** between two
    `DensityMatrix2Honest` states. Equals `‖ρ − σ‖²_F` for the
    underlying 2×2 Hermitian matrices. -/
def hsDistance (ρ σ : DensityMatrix2Honest) : ℝ :=
  (ρ.p₁ - σ.p₁) ^ 2 + (ρ.p₂ - σ.p₂) ^ 2
    + 2 * ((ρ.coh_re - σ.coh_re) ^ 2 + (ρ.coh_im - σ.coh_im) ^ 2)

/-- **Non-negativity**: the HS distance is always ≥ 0 (sum of squares). -/
theorem hsDistance_nonneg (ρ σ : DensityMatrix2Honest) :
    0 ≤ hsDistance ρ σ := by
  unfold hsDistance
  have h1 : 0 ≤ (ρ.p₁ - σ.p₁) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ (ρ.p₂ - σ.p₂) ^ 2 := sq_nonneg _
  have h3 : 0 ≤ (ρ.coh_re - σ.coh_re) ^ 2 := sq_nonneg _
  have h4 : 0 ≤ (ρ.coh_im - σ.coh_im) ^ 2 := sq_nonneg _
  linarith

/-- **Reflexivity**: `D_HS(ρ, ρ) = 0`. -/
theorem hsDistance_self_zero (ρ : DensityMatrix2Honest) :
    hsDistance ρ ρ = 0 := by
  unfold hsDistance
  ring

/-- **Symmetry**: `D_HS(ρ, σ) = D_HS(σ, ρ)`. -/
theorem hsDistance_symm (ρ σ : DensityMatrix2Honest) :
    hsDistance ρ σ = hsDistance σ ρ := by
  unfold hsDistance
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: ACTION OF DEPHASING ON THE DIFFERENCE OF TWO STATES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The dephasing channel is LINEAR on the underlying matrix (and so
    descends to a well-defined action on the affine difference of two
    density matrices). Concretely:
       Φ_γ(ρ).p_i      = ρ.p_i               (diagonals unchanged)
       Φ_γ(ρ).coh_re   = γ · ρ.coh_re        (off-diagonals scaled)
       Φ_γ(ρ).coh_im   = γ · ρ.coh_im
    Therefore
       Φ_γ(ρ).x − Φ_γ(σ).x = ρ.x − σ.x          for x ∈ {p₁, p₂}
       Φ_γ(ρ).x − Φ_γ(σ).x = γ · (ρ.x − σ.x)    for x ∈ {coh_re, coh_im}
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Diagonals unchanged.** Component p₁. -/
theorem dephasing_p1_unchanged (γ : ℝ) (hγ_nn : 0 ≤ γ) (hγ_le_one : γ ≤ 1)
    (ρ : DensityMatrix2Honest) :
    (dephasingChannel γ hγ_nn hγ_le_one ρ).p₁ = ρ.p₁ := rfl

/-- **Diagonals unchanged.** Component p₂. -/
theorem dephasing_p2_unchanged (γ : ℝ) (hγ_nn : 0 ≤ γ) (hγ_le_one : γ ≤ 1)
    (ρ : DensityMatrix2Honest) :
    (dephasingChannel γ hγ_nn hγ_le_one ρ).p₂ = ρ.p₂ := rfl

/-- **Off-diagonal scaled by γ.** Real part. -/
theorem dephasing_coh_re_scaled (γ : ℝ) (hγ_nn : 0 ≤ γ) (hγ_le_one : γ ≤ 1)
    (ρ : DensityMatrix2Honest) :
    (dephasingChannel γ hγ_nn hγ_le_one ρ).coh_re = γ * ρ.coh_re := rfl

/-- **Off-diagonal scaled by γ.** Imaginary part. -/
theorem dephasing_coh_im_scaled (γ : ℝ) (hγ_nn : 0 ≤ γ) (hγ_le_one : γ ≤ 1)
    (ρ : DensityMatrix2Honest) :
    (dephasingChannel γ hγ_nn hγ_le_one ρ).coh_im = γ * ρ.coh_im := rfl

/-- **Difference of diagonals is preserved (component p₁).** -/
theorem dephasing_diagonal_difference_p1 (γ : ℝ)
    (hγ_nn : 0 ≤ γ) (hγ_le_one : γ ≤ 1)
    (ρ σ : DensityMatrix2Honest) :
    (dephasingChannel γ hγ_nn hγ_le_one ρ).p₁
      - (dephasingChannel γ hγ_nn hγ_le_one σ).p₁
      = ρ.p₁ - σ.p₁ := by
  rw [dephasing_p1_unchanged, dephasing_p1_unchanged]

/-- **Difference of diagonals is preserved (component p₂).** -/
theorem dephasing_diagonal_difference_p2 (γ : ℝ)
    (hγ_nn : 0 ≤ γ) (hγ_le_one : γ ≤ 1)
    (ρ σ : DensityMatrix2Honest) :
    (dephasingChannel γ hγ_nn hγ_le_one ρ).p₂
      - (dephasingChannel γ hγ_nn hγ_le_one σ).p₂
      = ρ.p₂ - σ.p₂ := by
  rw [dephasing_p2_unchanged, dephasing_p2_unchanged]

/-- **Off-diagonal differences are scaled by γ (real part).** -/
theorem dephasing_off_diagonal_difference_re (γ : ℝ)
    (hγ_nn : 0 ≤ γ) (hγ_le_one : γ ≤ 1)
    (ρ σ : DensityMatrix2Honest) :
    (dephasingChannel γ hγ_nn hγ_le_one ρ).coh_re
      - (dephasingChannel γ hγ_nn hγ_le_one σ).coh_re
      = γ * (ρ.coh_re - σ.coh_re) := by
  rw [dephasing_coh_re_scaled, dephasing_coh_re_scaled]
  ring

/-- **Off-diagonal differences are scaled by γ (imaginary part).** -/
theorem dephasing_off_diagonal_difference_im (γ : ℝ)
    (hγ_nn : 0 ≤ γ) (hγ_le_one : γ ≤ 1)
    (ρ σ : DensityMatrix2Honest) :
    (dephasingChannel γ hγ_nn hγ_le_one ρ).coh_im
      - (dephasingChannel γ hγ_nn hγ_le_one σ).coh_im
      = γ * (ρ.coh_im - σ.coh_im) := by
  rw [dephasing_coh_im_scaled, dephasing_coh_im_scaled]
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: γ² ≤ 1 BOUND (REUSED INFRASTRUCTURE)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Squared parameter is bounded by 1**: for `γ ∈ [0, 1]`, `γ² ≤ 1`. -/
theorem gamma_sq_le_one (γ : ℝ) (hγ_nn : 0 ≤ γ) (hγ_le_one : γ ≤ 1) :
    γ ^ 2 ≤ 1 := by
  have h1 : γ * γ ≤ 1 * 1 :=
    mul_le_mul hγ_le_one hγ_le_one hγ_nn (by norm_num)
  calc γ ^ 2 = γ * γ := by ring
    _ ≤ 1 * 1 := h1
    _ = 1 := by norm_num

/-- **Strict version** of `gamma_sq_le_one`: for `γ ∈ [0, 1)`, `γ² < 1`.
    Needed for the strict-DPI corollary. -/
theorem gamma_sq_lt_one (γ : ℝ) (hγ_nn : 0 ≤ γ) (hγ_lt_one : γ < 1) :
    γ ^ 2 < 1 := by
  rcases eq_or_lt_of_le hγ_nn with hγ_zero | hγ_pos
  · -- γ = 0 case
    rw [← hγ_zero]
    norm_num
  · -- 0 < γ < 1
    have hγγ_lt : γ * γ < 1 * 1 :=
      mul_lt_mul' (le_of_lt hγ_lt_one) hγ_lt_one hγ_nn (by norm_num)
    calc γ ^ 2 = γ * γ := by ring
      _ < 1 * 1 := hγγ_lt
      _ = 1 := by norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: THE DATA PROCESSING INEQUALITY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Putting it together: the HS distance after the channel is

       D_HS(Φ_γ(ρ), Φ_γ(σ))
         = (Δp₁)² + (Δp₂)² + 2·γ²·((Δcoh_re)² + (Δcoh_im)²)

    while the input distance is

       D_HS(ρ, σ)
         = (Δp₁)² + (Δp₂)² + 2·((Δcoh_re)² + (Δcoh_im)²).

    Since `0 ≤ γ² ≤ 1`, the output is ≤ the input.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Closed-form expression for the post-channel HS distance.** The
    diagonal contribution is preserved exactly; the off-diagonal
    contribution is scaled by `γ²`. -/
theorem hsDistance_after_dephasing (γ : ℝ)
    (hγ_nn : 0 ≤ γ) (hγ_le_one : γ ≤ 1)
    (ρ σ : DensityMatrix2Honest) :
    hsDistance (dephasingChannel γ hγ_nn hγ_le_one ρ)
                (dephasingChannel γ hγ_nn hγ_le_one σ)
      = (ρ.p₁ - σ.p₁) ^ 2 + (ρ.p₂ - σ.p₂) ^ 2
          + 2 * γ ^ 2 *
              ((ρ.coh_re - σ.coh_re) ^ 2 + (ρ.coh_im - σ.coh_im) ^ 2) := by
  unfold hsDistance
  rw [dephasing_diagonal_difference_p1, dephasing_diagonal_difference_p2,
      dephasing_off_diagonal_difference_re,
      dephasing_off_diagonal_difference_im]
  ring

/-- **THE DATA PROCESSING INEQUALITY (DPI) FOR DEPHASING.**

    For any `γ ∈ [0, 1]` and any two density matrices `ρ, σ`:

       D_HS(Φ_γ(ρ), Φ_γ(σ)) ≤ D_HS(ρ, σ).

    The dephasing channel cannot INCREASE Hilbert–Schmidt
    distinguishability. The full quantum DPI (Lindblad–Uhlmann
    monotonicity of relative entropy under arbitrary CPTP) is a
    deeper statement requiring operator logarithms; this result is
    its specialization to (a) the dephasing channel and (b) the HS
    divergence. -/
theorem dephasing_data_processing (γ : ℝ)
    (hγ_nn : 0 ≤ γ) (hγ_le_one : γ ≤ 1)
    (ρ σ : DensityMatrix2Honest) :
    hsDistance (dephasingChannel γ hγ_nn hγ_le_one ρ)
                (dephasingChannel γ hγ_nn hγ_le_one σ)
      ≤ hsDistance ρ σ := by
  rw [hsDistance_after_dephasing γ hγ_nn hγ_le_one ρ σ]
  unfold hsDistance
  -- Need: 2 γ² · S ≤ 2 · S where S = (Δcoh_re)² + (Δcoh_im)² ≥ 0.
  have hγsq_le_one : γ ^ 2 ≤ 1 := gamma_sq_le_one γ hγ_nn hγ_le_one
  have hS_nn : 0 ≤ (ρ.coh_re - σ.coh_re) ^ 2 + (ρ.coh_im - σ.coh_im) ^ 2 := by
    have ha : 0 ≤ (ρ.coh_re - σ.coh_re) ^ 2 := sq_nonneg _
    have hb : 0 ≤ (ρ.coh_im - σ.coh_im) ^ 2 := sq_nonneg _
    linarith
  -- Off-diagonal contraction bound: γ² · S ≤ S.
  have hcontract :
      γ ^ 2 * ((ρ.coh_re - σ.coh_re) ^ 2 + (ρ.coh_im - σ.coh_im) ^ 2)
        ≤ (ρ.coh_re - σ.coh_re) ^ 2 + (ρ.coh_im - σ.coh_im) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hγsq_le_one hS_nn
    linarith
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: STRICTNESS — INFORMATION IS GENUINELY LOST
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For γ < 1, the inequality is strict whenever there is a non-zero
    off-diagonal coherence DIFFERENCE between ρ and σ. This is the
    operational sense in which dephasing destroys quantum
    distinguishability.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Strictness of DPI (real-coherence-difference version).**
    If `γ < 1` and `ρ.coh_re ≠ σ.coh_re`, then the HS distance
    STRICTLY decreases under dephasing. -/
theorem dephasing_dpi_strict_re (γ : ℝ)
    (hγ_nn : 0 ≤ γ) (hγ_lt_one : γ < 1)
    (ρ σ : DensityMatrix2Honest)
    (hcoh : ρ.coh_re ≠ σ.coh_re) :
    hsDistance (dephasingChannel γ hγ_nn (le_of_lt hγ_lt_one) ρ)
                (dephasingChannel γ hγ_nn (le_of_lt hγ_lt_one) σ)
      < hsDistance ρ σ := by
  rw [hsDistance_after_dephasing γ hγ_nn (le_of_lt hγ_lt_one) ρ σ]
  unfold hsDistance
  have hγsq_lt_one : γ ^ 2 < 1 := gamma_sq_lt_one γ hγ_nn hγ_lt_one
  -- (Δcoh_re)² > 0 since Δcoh_re ≠ 0.
  have hΔ_re_ne : ρ.coh_re - σ.coh_re ≠ 0 := sub_ne_zero.mpr hcoh
  have hΔ_re_sq_pos : 0 < (ρ.coh_re - σ.coh_re) ^ 2 := by
    have habs : 0 < |ρ.coh_re - σ.coh_re| := abs_pos.mpr hΔ_re_ne
    have hsq_eq : (ρ.coh_re - σ.coh_re) ^ 2 = |ρ.coh_re - σ.coh_re| ^ 2 :=
      (sq_abs _).symm
    rw [hsq_eq]
    exact pow_pos habs 2
  have hΔ_im_sq_nn : 0 ≤ (ρ.coh_im - σ.coh_im) ^ 2 := sq_nonneg _
  have hS_pos : 0 < (ρ.coh_re - σ.coh_re) ^ 2 + (ρ.coh_im - σ.coh_im) ^ 2 := by
    linarith
  -- Off-diagonal contraction is STRICT: γ² · S < S.
  have hcontract_strict :
      γ ^ 2 * ((ρ.coh_re - σ.coh_re) ^ 2 + (ρ.coh_im - σ.coh_im) ^ 2)
        < (ρ.coh_re - σ.coh_re) ^ 2 + (ρ.coh_im - σ.coh_im) ^ 2 := by
    have h := mul_lt_mul_of_pos_right hγsq_lt_one hS_pos
    linarith
  linarith

/-- **Strictness of DPI (imaginary-coherence-difference version).**
    If `γ < 1` and `ρ.coh_im ≠ σ.coh_im`, then the HS distance
    STRICTLY decreases under dephasing. -/
theorem dephasing_dpi_strict_im (γ : ℝ)
    (hγ_nn : 0 ≤ γ) (hγ_lt_one : γ < 1)
    (ρ σ : DensityMatrix2Honest)
    (hcoh : ρ.coh_im ≠ σ.coh_im) :
    hsDistance (dephasingChannel γ hγ_nn (le_of_lt hγ_lt_one) ρ)
                (dephasingChannel γ hγ_nn (le_of_lt hγ_lt_one) σ)
      < hsDistance ρ σ := by
  rw [hsDistance_after_dephasing γ hγ_nn (le_of_lt hγ_lt_one) ρ σ]
  unfold hsDistance
  have hγsq_lt_one : γ ^ 2 < 1 := gamma_sq_lt_one γ hγ_nn hγ_lt_one
  have hΔ_im_ne : ρ.coh_im - σ.coh_im ≠ 0 := sub_ne_zero.mpr hcoh
  have hΔ_im_sq_pos : 0 < (ρ.coh_im - σ.coh_im) ^ 2 := by
    have habs : 0 < |ρ.coh_im - σ.coh_im| := abs_pos.mpr hΔ_im_ne
    have hsq_eq : (ρ.coh_im - σ.coh_im) ^ 2 = |ρ.coh_im - σ.coh_im| ^ 2 :=
      (sq_abs _).symm
    rw [hsq_eq]
    exact pow_pos habs 2
  have hΔ_re_sq_nn : 0 ≤ (ρ.coh_re - σ.coh_re) ^ 2 := sq_nonneg _
  have hS_pos : 0 < (ρ.coh_re - σ.coh_re) ^ 2 + (ρ.coh_im - σ.coh_im) ^ 2 := by
    linarith
  have hcontract_strict :
      γ ^ 2 * ((ρ.coh_re - σ.coh_re) ^ 2 + (ρ.coh_im - σ.coh_im) ^ 2)
        < (ρ.coh_re - σ.coh_re) ^ 2 + (ρ.coh_im - σ.coh_im) ^ 2 := by
    have h := mul_lt_mul_of_pos_right hγsq_lt_one hS_pos
    linarith
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: SPECIAL CASES — γ = 0 AND γ = 1
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **At γ = 1** (no dephasing) the HS distance is preserved exactly:
    the channel is the identity. -/
theorem dpi_no_dephasing (ρ σ : DensityMatrix2Honest) :
    hsDistance (dephasingChannel 1 (by norm_num) le_rfl ρ)
                (dephasingChannel 1 (by norm_num) le_rfl σ)
      = hsDistance ρ σ := by
  rw [hsDistance_after_dephasing 1 (by norm_num) le_rfl ρ σ]
  unfold hsDistance
  ring

/-- **At γ = 0** (full dephasing) the post-channel HS distance is the
    PURELY-CLASSICAL (diagonal-only) part. The off-diagonal sector
    contributes nothing — it has been annihilated. -/
theorem dpi_full_dephasing (ρ σ : DensityMatrix2Honest) :
    hsDistance (dephasingChannel 0 le_rfl (by norm_num) ρ)
                (dephasingChannel 0 le_rfl (by norm_num) σ)
      = (ρ.p₁ - σ.p₁) ^ 2 + (ρ.p₂ - σ.p₂) ^ 2 := by
  rw [hsDistance_after_dephasing 0 le_rfl (by norm_num) ρ σ]
  ring

/-- **The classical (diagonal) part of the divergence is always
    PRESERVED exactly under dephasing, regardless of γ.** -/
theorem dpi_diagonal_part_preserved (γ : ℝ)
    (hγ_nn : 0 ≤ γ) (hγ_le_one : γ ≤ 1)
    (ρ σ : DensityMatrix2Honest) :
    ((dephasingChannel γ hγ_nn hγ_le_one ρ).p₁
        - (dephasingChannel γ hγ_nn hγ_le_one σ).p₁) ^ 2
      + ((dephasingChannel γ hγ_nn hγ_le_one ρ).p₂
            - (dephasingChannel γ hγ_nn hγ_le_one σ).p₂) ^ 2
      = (ρ.p₁ - σ.p₁) ^ 2 + (ρ.p₂ - σ.p₂) ^ 2 := by
  rw [dephasing_diagonal_difference_p1, dephasing_diagonal_difference_p2]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: COMPOSITION-OF-CHANNELS DPI
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Iterating the DPI: applying TWO dephasing channels in sequence
    can only further decrease distinguishability. This is the
    "monotonicity along the trajectory" interpretation of the DPI.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Iterated DPI**: composing two dephasing channels gives a chain
    of inequalities. Combined with `dephasing_compose` this yields
    `D_HS(Φ_{γ₁γ₂}(ρ), Φ_{γ₁γ₂}(σ)) ≤ D_HS(Φ_{γ₂}(ρ), Φ_{γ₂}(σ)) ≤
    D_HS(ρ, σ)`. -/
theorem dephasing_dpi_iterated (γ₁ γ₂ : ℝ)
    (h₁_nn : 0 ≤ γ₁) (h₁_le : γ₁ ≤ 1)
    (h₂_nn : 0 ≤ γ₂) (h₂_le : γ₂ ≤ 1)
    (ρ σ : DensityMatrix2Honest) :
    hsDistance
        (dephasingChannel γ₁ h₁_nn h₁_le
          (dephasingChannel γ₂ h₂_nn h₂_le ρ))
        (dephasingChannel γ₁ h₁_nn h₁_le
          (dephasingChannel γ₂ h₂_nn h₂_le σ))
      ≤ hsDistance ρ σ := by
  have h_inner :
      hsDistance (dephasingChannel γ₂ h₂_nn h₂_le ρ)
                  (dephasingChannel γ₂ h₂_nn h₂_le σ)
        ≤ hsDistance ρ σ :=
    dephasing_data_processing γ₂ h₂_nn h₂_le ρ σ
  have h_outer :
      hsDistance
          (dephasingChannel γ₁ h₁_nn h₁_le
            (dephasingChannel γ₂ h₂_nn h₂_le ρ))
          (dephasingChannel γ₁ h₁_nn h₁_le
            (dephasingChannel γ₂ h₂_nn h₂_le σ))
        ≤ hsDistance (dephasingChannel γ₂ h₂_nn h₂_le ρ)
                      (dephasingChannel γ₂ h₂_nn h₂_le σ) :=
    dephasing_data_processing γ₁ h₁_nn h₁_le _ _
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER THEOREM (DATA PROCESSING INEQUALITY FOR DEPHASING).**

    Bundling the channel-level information-theoretic facts proved in
    this file:

    (1) **HS distance is a non-negative, reflexive, symmetric divergence**
        on `DensityMatrix2Honest` (`hsDistance_nonneg`,
        `hsDistance_self_zero`, `hsDistance_symm`).

    (2) **THE DATA PROCESSING INEQUALITY (DPI):** for any `γ ∈ [0, 1]`
        and any pair of states `ρ, σ`, dephasing cannot INCREASE HS
        distinguishability — `D_HS(Φ_γ(ρ), Φ_γ(σ)) ≤ D_HS(ρ, σ)`
        (`dephasing_data_processing`).

    (3) **STRICTNESS for γ < 1** when there is a non-trivial
        coherence difference: information is GENUINELY lost
        (`dephasing_dpi_strict_re`, `dephasing_dpi_strict_im`).

    (4) **No dephasing (γ = 1) preserves HS distance exactly**
        (`dpi_no_dephasing`); **full dephasing (γ = 0) projects onto
        the classical (diagonal) part** (`dpi_full_dephasing`).

    (5) **Classical (diagonal) part is always preserved** regardless
        of γ (`dpi_diagonal_part_preserved`): all loss happens in the
        off-diagonal (quantum-coherence) sector.

    (6) **Iterated DPI** for compositions of channels
        (`dephasing_dpi_iterated`).
-/
theorem dpi_master :
    -- (1) HS distance basic properties
    (∀ ρ σ : DensityMatrix2Honest, 0 ≤ hsDistance ρ σ)
    ∧ (∀ ρ : DensityMatrix2Honest, hsDistance ρ ρ = 0)
    ∧ (∀ ρ σ : DensityMatrix2Honest, hsDistance ρ σ = hsDistance σ ρ)
    -- (2) THE DPI
    ∧ (∀ γ : ℝ, ∀ hγ_nn : 0 ≤ γ, ∀ hγ_le_one : γ ≤ 1,
        ∀ ρ σ : DensityMatrix2Honest,
          hsDistance (dephasingChannel γ hγ_nn hγ_le_one ρ)
                      (dephasingChannel γ hγ_nn hγ_le_one σ)
            ≤ hsDistance ρ σ)
    -- (3) STRICTNESS for γ < 1, real coherence
    ∧ (∀ γ : ℝ, ∀ hγ_nn : 0 ≤ γ, ∀ hγ_lt_one : γ < 1,
        ∀ ρ σ : DensityMatrix2Honest, ρ.coh_re ≠ σ.coh_re →
          hsDistance (dephasingChannel γ hγ_nn (le_of_lt hγ_lt_one) ρ)
                      (dephasingChannel γ hγ_nn (le_of_lt hγ_lt_one) σ)
            < hsDistance ρ σ)
    -- (4) γ = 1 preserves; γ = 0 reduces to classical (diagonal) part
    ∧ (∀ ρ σ : DensityMatrix2Honest,
        hsDistance (dephasingChannel 1 (by norm_num) le_rfl ρ)
                    (dephasingChannel 1 (by norm_num) le_rfl σ)
          = hsDistance ρ σ)
    ∧ (∀ ρ σ : DensityMatrix2Honest,
        hsDistance (dephasingChannel 0 le_rfl (by norm_num) ρ)
                    (dephasingChannel 0 le_rfl (by norm_num) σ)
          = (ρ.p₁ - σ.p₁) ^ 2 + (ρ.p₂ - σ.p₂) ^ 2)
    -- (5) Diagonal part preserved
    ∧ (∀ γ : ℝ, ∀ hγ_nn : 0 ≤ γ, ∀ hγ_le_one : γ ≤ 1,
        ∀ ρ σ : DensityMatrix2Honest,
          ((dephasingChannel γ hγ_nn hγ_le_one ρ).p₁
              - (dephasingChannel γ hγ_nn hγ_le_one σ).p₁) ^ 2
            + ((dephasingChannel γ hγ_nn hγ_le_one ρ).p₂
                  - (dephasingChannel γ hγ_nn hγ_le_one σ).p₂) ^ 2
            = (ρ.p₁ - σ.p₁) ^ 2 + (ρ.p₂ - σ.p₂) ^ 2)
    -- (6) Iterated DPI
    ∧ (∀ γ₁ γ₂ : ℝ, ∀ h₁_nn : 0 ≤ γ₁, ∀ h₁_le : γ₁ ≤ 1,
        ∀ h₂_nn : 0 ≤ γ₂, ∀ h₂_le : γ₂ ≤ 1,
        ∀ ρ σ : DensityMatrix2Honest,
          hsDistance
              (dephasingChannel γ₁ h₁_nn h₁_le
                (dephasingChannel γ₂ h₂_nn h₂_le ρ))
              (dephasingChannel γ₁ h₁_nn h₁_le
                (dephasingChannel γ₂ h₂_nn h₂_le σ))
            ≤ hsDistance ρ σ) := by
  refine ⟨hsDistance_nonneg, hsDistance_self_zero, hsDistance_symm,
          ?_, ?_, dpi_no_dephasing, dpi_full_dephasing,
          dpi_diagonal_part_preserved, ?_⟩
  · intro γ hγ_nn hγ_le_one ρ σ
    exact dephasing_data_processing γ hγ_nn hγ_le_one ρ σ
  · intro γ hγ_nn hγ_lt_one ρ σ hcoh
    exact dephasing_dpi_strict_re γ hγ_nn hγ_lt_one ρ σ hcoh
  · intro γ₁ γ₂ h₁_nn h₁_le h₂_nn h₂_le ρ σ
    exact dephasing_dpi_iterated γ₁ γ₂ h₁_nn h₁_le h₂_nn h₂_le ρ σ

end UnifiedTheory.LayerB.DataProcessingInequality
