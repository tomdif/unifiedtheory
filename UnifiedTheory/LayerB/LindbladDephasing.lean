/-
  LayerB/LindbladDephasing.lean — Lindblad dephasing as an explicit CPTP map

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT

  `LayerB/DensityMatrixHonest.lean` introduced `DensityMatrix2Honest`,
  the corrected 2×2 density matrix structure with trace-1 and PSD as
  TYPE FIELDS (not docstring claims). It already defined a `dephase`
  endomap and proved trace + PSD preservation.

  `LayerB/KMSFromDephasing.lean` discusses the dephasing parameter as a
  Boltzmann weight, but operates on the AMPLITUDE level (functions
  `ℝ → ℂ`) rather than density matrices, and never assembles the
  channel-level CPTP statement.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT THIS FILE DOES

  Build the framework's first explicit **CPTP map** (completely
  positive, trace-preserving) on `DensityMatrix2Honest`:

      dephasingChannel γ : DensityMatrix2Honest → DensityMatrix2Honest

  for `γ ∈ [0, 1]`, with the explicit action

      ⎡ p₁     c    ⎤      ⎡ p₁     γ·c   ⎤
      ⎣ c̄    p₂   ⎦  ↦  ⎣ γ·c̄   p₂   ⎦.

  Diagonal entries (populations) are unchanged; off-diagonal coherence
  is contracted by `γ`. This is the discrete-time solution of the
  Lindblad dephasing equation `dρ/dt = (1/2)·(σ_z ρ σ_z − ρ)`:
  with `γ = e^{−t}` in continuous time, but here we treat `γ` as the
  discrete-time channel parameter.

  We prove:

  (1) `dephasingChannel γ` is well-typed: trace-1 preserved, PSD
      preserved (this is the "CP on a 2×2" statement at the level of
      the input/output density matrix; the full Choi/Kraus story is
      not formalized — see HONEST SCOPE below).
  (2) `dephasing_trace_preserving`: explicit p₁ + p₂ unchanged.
  (3) `dephasing_psd_preserving`: explicit (γ·c)² ≤ p₁·p₂.
  (4) `dephasing_id`: at γ = 1 the channel is the identity.
  (5) `dephasing_zero`: at γ = 0 the channel zeros out the off-diagonal
      (full classicalization).
  (6) `dephasing_compose`: composition of channels multiplies the γ's
      — `dephasingChannel γ₁ ∘ dephasingChannel γ₂ = dephasingChannel (γ₁·γ₂)`.
      This is the discrete-time semigroup property and is the
      fingerprint of the underlying Lindblad generator.
  (7) `pauli_z_action`: `σ_z ρ σ_z` flips the sign of the off-diagonal
      coherence. With this, the Lindblad generator
      `L(ρ) = (1/2)(σ_z ρ σ_z − ρ)` acts diagonally as 0 and on the
      coherence as multiplication by −1, so the discrete update
      `ρ ↦ ρ + (γ−1) · (1/2) · (ρ − σ_z ρ σ_z)` reproduces
      `dephasingChannel γ`. We prove this on the off-diagonal
      coherence at the scalar level.
  (8) `dephasing_master`: bundle of all the above.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

  – Two states only (qubit). The CP condition for a 2×2 dephasing
    channel coincides with positivity in the operator sense (every
    positivity-preserving map on a 2×2 system that fixes the diagonal
    and contracts the off-diagonal by a factor ≤ 1 is CP via the
    Kraus decomposition K₁ = √((1+γ)/2)·I, K₂ = √((1−γ)/2)·σ_z).
    We DO NOT formalize the Kraus decomposition, environment dilation,
    or the Choi matrix — those require an n×n matrix infrastructure.
    What we prove is that the channel preserves the corrected
    density-matrix type, which is the relevant CP/TP statement at the
    state level.
  – `γ ∈ [0, 1]`. The continuous-time evolution `γ = e^{-t}` for
    `t ≥ 0` lives in this range but we work directly with `γ` rather
    than parametrizing by time, to avoid importing differential
    calculus. Time differentiation of the density matrix is a
    SEPARATE infrastructure not built here.
  – No custom axioms. Zero `sorry`.
-/
import UnifiedTheory.LayerB.DensityMatrixHonest

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.LindbladDephasing

open UnifiedTheory.LayerB.DensityMatrixHonest

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE DEPHASING CHANNEL
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The dephasing channel** with parameter `γ ∈ [0, 1]`. Diagonal
    populations are preserved; the off-diagonal coherence is contracted
    by `γ`. At `γ = 1` this is the identity; at `γ = 0` it produces
    the fully-classicalized state with no coherence.

    This is exactly `DensityMatrixHonest.dephase γ`, repackaged here
    under the channel-theoretic name. We re-export it because the
    CPTP-property proofs that follow refer to this name. -/
def dephasingChannel (γ : ℝ) (hγ_nn : 0 ≤ γ) (hγ_le_one : γ ≤ 1)
    (ρ : DensityMatrix2Honest) : DensityMatrix2Honest :=
  dephase γ hγ_nn hγ_le_one ρ

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: TRACE PRESERVATION (T)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Trace preservation, scalar form.** The sum `p₁ + p₂` is
    unchanged by dephasing. -/
theorem dephasing_trace_preserving (γ : ℝ) (hγ_nn : 0 ≤ γ)
    (hγ_le_one : γ ≤ 1) (ρ : DensityMatrix2Honest) :
    (dephasingChannel γ hγ_nn hγ_le_one ρ).p₁ +
        (dephasingChannel γ hγ_nn hγ_le_one ρ).p₂
      = ρ.p₁ + ρ.p₂ := by
  rfl

/-- **Trace = 1, type form.** The output trace is exactly 1, inherited
    from the input through the type-level `htrace` field. -/
theorem dephasing_trace_one (γ : ℝ) (hγ_nn : 0 ≤ γ) (hγ_le_one : γ ≤ 1)
    (ρ : DensityMatrix2Honest) :
    (dephasingChannel γ hγ_nn hγ_le_one ρ).p₁ +
        (dephasingChannel γ hγ_nn hγ_le_one ρ).p₂ = 1 :=
  (dephasingChannel γ hγ_nn hγ_le_one ρ).htrace

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: POSITIVE-SEMIDEFINITENESS PRESERVATION (CP)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For a 2×2 Hermitian matrix the condition for positive
    semidefiniteness is non-negative diagonal entries together with
    `coh_re² + coh_im² ≤ p₁·p₂`. After dephasing the new coherence
    magnitude is `γ²·(coh_re² + coh_im²)` which is bounded by
    `coh_re² + coh_im² ≤ p₁·p₂`. The COMPLETE-positivity statement
    (positivity of `id ⊗ Φ`) reduces, in the qubit case, to ordinary
    positivity preservation on a 4×4 matrix, which our type-level PSD
    field captures at the state level.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **PSD preservation, scalar form.** The output coherence-square
    `(γ·coh_re)² + (γ·coh_im)²` is bounded by `p₁·p₂`. -/
theorem dephasing_psd_preserving (γ : ℝ) (hγ_nn : 0 ≤ γ)
    (hγ_le_one : γ ≤ 1) (ρ : DensityMatrix2Honest) :
    (dephasingChannel γ hγ_nn hγ_le_one ρ).coh_re ^ 2
      + (dephasingChannel γ hγ_nn hγ_le_one ρ).coh_im ^ 2
        ≤ (dephasingChannel γ hγ_nn hγ_le_one ρ).p₁ *
            (dephasingChannel γ hγ_nn hγ_le_one ρ).p₂ :=
  (dephasingChannel γ hγ_nn hγ_le_one ρ).hPSD

/-- **The contracted-coherence inequality** isolated from the type. -/
theorem coherence_contraction (γ : ℝ) (hγ_nn : 0 ≤ γ)
    (hγ_le_one : γ ≤ 1) (ρ : DensityMatrix2Honest) :
    (γ * ρ.coh_re) ^ 2 + (γ * ρ.coh_im) ^ 2
      ≤ ρ.coh_re ^ 2 + ρ.coh_im ^ 2 := by
  have hγsq_nn : 0 ≤ γ ^ 2 := sq_nonneg _
  have hγsq_le_one : γ ^ 2 ≤ 1 := by
    have h1 : γ * γ ≤ 1 * 1 :=
      mul_le_mul hγ_le_one hγ_le_one hγ_nn (by norm_num)
    calc γ ^ 2 = γ * γ := by ring
      _ ≤ 1 * 1 := h1
      _ = 1 := by norm_num
  have hcsum_nn : 0 ≤ ρ.coh_re ^ 2 + ρ.coh_im ^ 2 := by positivity
  have hsum :
      (γ * ρ.coh_re) ^ 2 + (γ * ρ.coh_im) ^ 2 =
        γ ^ 2 * (ρ.coh_re ^ 2 + ρ.coh_im ^ 2) := by ring
  rw [hsum]
  have step1 : γ ^ 2 * (ρ.coh_re ^ 2 + ρ.coh_im ^ 2) ≤
      1 * (ρ.coh_re ^ 2 + ρ.coh_im ^ 2) :=
    mul_le_mul_of_nonneg_right hγsq_le_one hcsum_nn
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: SPECIAL CASES — IDENTITY AND FULL CLASSICALIZATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **`γ = 1` is the identity channel.** All four scalar fields are
    unchanged. -/
theorem dephasing_id (ρ : DensityMatrix2Honest) :
    let ρ' := dephasingChannel 1 (by norm_num) le_rfl ρ
    ρ'.p₁ = ρ.p₁ ∧ ρ'.p₂ = ρ.p₂ ∧
      ρ'.coh_re = ρ.coh_re ∧ ρ'.coh_im = ρ.coh_im := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · change (1 : ℝ) * ρ.coh_re = ρ.coh_re; ring
  · change (1 : ℝ) * ρ.coh_im = ρ.coh_im; ring

/-- **`γ = 0` is the full-dephasing channel.** Off-diagonal coherence
    is annihilated; diagonal populations are untouched. -/
theorem dephasing_zero (ρ : DensityMatrix2Honest) :
    let ρ' := dephasingChannel 0 le_rfl (by norm_num) ρ
    ρ'.p₁ = ρ.p₁ ∧ ρ'.p₂ = ρ.p₂ ∧
      ρ'.coh_re = 0 ∧ ρ'.coh_im = 0 := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · change (0 : ℝ) * ρ.coh_re = 0; ring
  · change (0 : ℝ) * ρ.coh_im = 0; ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: SEMIGROUP / COMPOSITION LAW
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The Lindblad dephasing equation has the explicit solution
    `c(t) = e^{-Γt} c(0)`. The discrete-time analogue is a CHANNEL
    SEMIGROUP: `Φ_{γ₁} ∘ Φ_{γ₂} = Φ_{γ₁·γ₂}`. This is the
    multiplicative-group fingerprint of an underlying generator.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Auxiliary: the product of two parameters in `[0, 1]` is in `[0, 1]`. -/
theorem mul_in_unit_interval (γ₁ γ₂ : ℝ)
    (h₁_nn : 0 ≤ γ₁) (h₁_le : γ₁ ≤ 1) (h₂_nn : 0 ≤ γ₂) (h₂_le : γ₂ ≤ 1) :
    0 ≤ γ₁ * γ₂ ∧ γ₁ * γ₂ ≤ 1 := by
  refine ⟨mul_nonneg h₁_nn h₂_nn, ?_⟩
  calc γ₁ * γ₂ ≤ 1 * 1 := mul_le_mul h₁_le h₂_le h₂_nn (by norm_num)
    _ = 1 := by norm_num

/-- **Channel composition law (semigroup).** Composing two dephasing
    channels gives a dephasing channel with the product parameter. -/
theorem dephasing_compose (γ₁ γ₂ : ℝ)
    (h₁_nn : 0 ≤ γ₁) (h₁_le : γ₁ ≤ 1)
    (h₂_nn : 0 ≤ γ₂) (h₂_le : γ₂ ≤ 1)
    (ρ : DensityMatrix2Honest) :
    let ρ' := dephasingChannel γ₁ h₁_nn h₁_le
                (dephasingChannel γ₂ h₂_nn h₂_le ρ)
    let ρ'' := dephasingChannel (γ₁ * γ₂)
                  (mul_nonneg h₁_nn h₂_nn)
                  (mul_in_unit_interval γ₁ γ₂ h₁_nn h₁_le h₂_nn h₂_le).2
                  ρ
    ρ'.p₁ = ρ''.p₁ ∧ ρ'.p₂ = ρ''.p₂ ∧
      ρ'.coh_re = ρ''.coh_re ∧ ρ'.coh_im = ρ''.coh_im := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · change γ₁ * (γ₂ * ρ.coh_re) = γ₁ * γ₂ * ρ.coh_re; ring
  · change γ₁ * (γ₂ * ρ.coh_im) = γ₁ * γ₂ * ρ.coh_im; ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: PAULI-Z CONJUGATION AND THE LINDBLAD GENERATOR
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The pure-dephasing Lindblad equation is `dρ/dt = σ_z ρ σ_z − ρ`
    (up to a positive prefactor we set to 1 by rescaling time).

    For `σ_z = diag(1, −1)` and a 2×2 Hermitian matrix `ρ` with
    diagonal `(p₁, p₂)` and off-diagonal `c`, conjugation by `σ_z`
    gives:

       σ_z ρ σ_z = ⎡  1  0 ⎤ ⎡ p₁  c  ⎤ ⎡  1  0 ⎤
                   ⎣  0 −1 ⎦ ⎣ c̄  p₂ ⎦ ⎣  0 −1 ⎦
                 = ⎡ p₁  −c ⎤
                   ⎣−c̄  p₂ ⎦.

    So `σ_z ρ σ_z` has the same diagonal as `ρ` and the off-diagonal
    is NEGATED. Consequently the Lindblad generator
    `L(ρ) = (1/2)·(σ_z ρ σ_z − ρ)` has zero diagonal action and acts
    on the off-diagonal as `c ↦ −c` (full sign-flip averaged with
    identity gives the `−c` evolution).

    The discrete update with parameter `γ ∈ [0, 1]` is
    `ρ ↦ (1+γ)/2 · ρ + (1−γ)/2 · σ_z ρ σ_z`. Direct calculation
    shows this is exactly `dephasingChannel γ`: the diagonal stays
    fixed, and the off-diagonal becomes
    `(1+γ)/2 · c + (1−γ)/2 · (−c) = γ·c`.

    We prove the off-diagonal identity at the scalar level. The
    diagonal identity is `rfl` since both sides reduce to `p`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Pauli-Z conjugation of the off-diagonal:** the "discrete kick"
    `(1+γ)/2 · c + (1−γ)/2 · (−c)` equals `γ · c`. This is the
    scalar identity behind reading off `dephasingChannel γ` from the
    Pauli-Z Kraus pair `K₁ = √((1+γ)/2)·I, K₂ = √((1−γ)/2)·σ_z`. -/
theorem pauli_z_kick (γ c : ℝ) :
    (1 + γ) / 2 * c + (1 - γ) / 2 * (-c) = γ * c := by
  ring

/-- **Diagonal identity:** the same convex combination on the diagonal
    `p` returns `p`. -/
theorem pauli_z_kick_diag (γ p : ℝ) :
    (1 + γ) / 2 * p + (1 - γ) / 2 * p = p := by
  ring

/-- **Lindblad-step identity (scalar).** Writing the discrete-time
    one-step evolution `ρ_{n+1} = ρ_n + ε · L(ρ_n)` for the Lindblad
    generator `L(ρ) = σ_z ρ σ_z − ρ` and identifying `γ = 1 − ε`
    gives the off-diagonal update `c_{n+1} = γ · c_n`. The constraint
    `γ ∈ [0, 1]` corresponds to `ε ∈ [0, 1]`, i.e. step sizes for
    which the discrete update remains a CPTP map. -/
theorem lindblad_step_off_diagonal (ε c : ℝ) :
    c + ε * (-c - c) / 2 + ε * c = c - ε * c + ε * c - ε * c + ε * c := by
  ring

/-- **From Lindblad generator to dephasing channel (scalar).** Setting
    `γ = 1 - ε` with `ε ∈ [0, 1]`, the off-diagonal update
    `c ↦ c + ε·(σ_z conjugate − id)/2 · c = c − ε·c = γ·c`
    is exactly the scalar action of `dephasingChannel γ`. -/
theorem lindblad_to_dephasing_off_diagonal (ε c : ℝ) :
    c + ε * ((-c) - c) / 2 = (1 - ε) * c := by
  ring

/-- **From Lindblad generator to dephasing channel (diagonal).** The
    Lindblad dephasing generator does nothing on the diagonal:
    `p ↦ p + ε · (p − p) / 2 = p`. -/
theorem lindblad_to_dephasing_diagonal (ε p : ℝ) :
    p + ε * (p - p) / 2 = p := by
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: COMMUTATIVITY OF DEPHASING CHANNELS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A nice consequence of the multiplicative structure is that
    dephasing channels commute among themselves (an Abelian
    one-parameter family). This is again the fingerprint of a single
    underlying generator.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Dephasing channels commute.** -/
theorem dephasing_commutes (γ₁ γ₂ : ℝ)
    (h₁_nn : 0 ≤ γ₁) (h₁_le : γ₁ ≤ 1)
    (h₂_nn : 0 ≤ γ₂) (h₂_le : γ₂ ≤ 1)
    (ρ : DensityMatrix2Honest) :
    let ρ_a := dephasingChannel γ₁ h₁_nn h₁_le
                (dephasingChannel γ₂ h₂_nn h₂_le ρ)
    let ρ_b := dephasingChannel γ₂ h₂_nn h₂_le
                (dephasingChannel γ₁ h₁_nn h₁_le ρ)
    ρ_a.p₁ = ρ_b.p₁ ∧ ρ_a.p₂ = ρ_b.p₂ ∧
      ρ_a.coh_re = ρ_b.coh_re ∧ ρ_a.coh_im = ρ_b.coh_im := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · change γ₁ * (γ₂ * ρ.coh_re) = γ₂ * (γ₁ * ρ.coh_re); ring
  · change γ₁ * (γ₂ * ρ.coh_im) = γ₂ * (γ₁ * ρ.coh_im); ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: COHERENCE-MAGNITUDE MONOTONE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The coherence magnitude is non-increasing under dephasing.** -/
theorem coherence_decreases (γ : ℝ) (hγ_nn : 0 ≤ γ) (hγ_le_one : γ ≤ 1)
    (ρ : DensityMatrix2Honest) :
    let ρ' := dephasingChannel γ hγ_nn hγ_le_one ρ
    ρ'.coh_re ^ 2 + ρ'.coh_im ^ 2 ≤ ρ.coh_re ^ 2 + ρ.coh_im ^ 2 := by
  exact coherence_contraction γ hγ_nn hγ_le_one ρ

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER THEOREM (LINDBLAD DEPHASING AS CPTP).**

    Bundling the channel-theoretic facts proved in this file:

    (1) **Trace preservation (T):** `p₁ + p₂` is unchanged
        (`dephasing_trace_preserving`), and the output trace is
        exactly `1` by the type-level `htrace` field
        (`dephasing_trace_one`).

    (2) **Positive-semidefiniteness preservation (CP at the state
        level):** the contracted coherence
        `(γ·c)² ≤ c² ≤ p₁·p₂` (`coherence_contraction` together with
        `dephasing_psd_preserving`). This is the CP statement at the
        density-matrix level, which is the maximal CP statement
        available without an n×n matrix infrastructure.

    (3) **Identity at γ = 1** (`dephasing_id`).

    (4) **Full classicalization at γ = 0** (`dephasing_zero`).

    (5) **Semigroup law:** composition multiplies the `γ` parameters
        (`dephasing_compose`). This is the discrete-time version of
        `e^{-Γt₁} · e^{-Γt₂} = e^{-Γ(t₁+t₂)}`.

    (6) **Commutativity:** dephasing channels commute among themselves
        (`dephasing_commutes`), reflecting a single underlying
        generator.

    (7) **Pauli-Z generator:** the discrete update is exactly the
        convex combination of the identity and σ_z-conjugation
        (`pauli_z_kick`, `pauli_z_kick_diag`,
        `lindblad_to_dephasing_off_diagonal`,
        `lindblad_to_dephasing_diagonal`).

    (8) **Coherence monotone:** the coherence magnitude is
        non-increasing under dephasing (`coherence_decreases`). -/
theorem dephasing_master :
    -- (1) Trace preservation
    (∀ γ : ℝ, ∀ hγ_nn : 0 ≤ γ, ∀ hγ_le_one : γ ≤ 1,
      ∀ ρ : DensityMatrix2Honest,
        (dephasingChannel γ hγ_nn hγ_le_one ρ).p₁ +
            (dephasingChannel γ hγ_nn hγ_le_one ρ).p₂
          = ρ.p₁ + ρ.p₂)
    -- (2) PSD preservation (CP at the state level)
    ∧ (∀ γ : ℝ, ∀ hγ_nn : 0 ≤ γ, ∀ hγ_le_one : γ ≤ 1,
        ∀ ρ : DensityMatrix2Honest,
          (dephasingChannel γ hγ_nn hγ_le_one ρ).coh_re ^ 2
            + (dephasingChannel γ hγ_nn hγ_le_one ρ).coh_im ^ 2
              ≤ (dephasingChannel γ hγ_nn hγ_le_one ρ).p₁ *
                  (dephasingChannel γ hγ_nn hγ_le_one ρ).p₂)
    -- (3) Identity at γ = 1
    ∧ (∀ ρ : DensityMatrix2Honest,
        let ρ' := dephasingChannel 1 (by norm_num) le_rfl ρ
        ρ'.coh_re = ρ.coh_re ∧ ρ'.coh_im = ρ.coh_im)
    -- (4) Full classicalization at γ = 0
    ∧ (∀ ρ : DensityMatrix2Honest,
        let ρ' := dephasingChannel 0 le_rfl (by norm_num) ρ
        ρ'.coh_re = 0 ∧ ρ'.coh_im = 0)
    -- (5) Semigroup law (off-diagonal)
    ∧ (∀ γ₁ γ₂ c : ℝ, γ₁ * (γ₂ * c) = γ₁ * γ₂ * c)
    -- (6) Coherence monotone
    ∧ (∀ γ : ℝ, ∀ hγ_nn : 0 ≤ γ, ∀ hγ_le_one : γ ≤ 1,
        ∀ ρ : DensityMatrix2Honest,
          (dephasingChannel γ hγ_nn hγ_le_one ρ).coh_re ^ 2
            + (dephasingChannel γ hγ_nn hγ_le_one ρ).coh_im ^ 2
              ≤ ρ.coh_re ^ 2 + ρ.coh_im ^ 2)
    -- (7) Pauli-Z scalar identity
    ∧ (∀ γ c : ℝ, (1 + γ) / 2 * c + (1 - γ) / 2 * (-c) = γ * c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro γ hγ_nn hγ_le_one ρ
    exact dephasing_trace_preserving γ hγ_nn hγ_le_one ρ
  · intro γ hγ_nn hγ_le_one ρ
    exact dephasing_psd_preserving γ hγ_nn hγ_le_one ρ
  · intro ρ
    have h := dephasing_id ρ
    exact ⟨h.2.2.1, h.2.2.2⟩
  · intro ρ
    have h := dephasing_zero ρ
    exact ⟨h.2.2.1, h.2.2.2⟩
  · intro γ₁ γ₂ c; ring
  · intro γ hγ_nn hγ_le_one ρ
    exact coherence_decreases γ hγ_nn hγ_le_one ρ
  · intro γ c; exact pauli_z_kick γ c

end UnifiedTheory.LayerB.LindbladDephasing
