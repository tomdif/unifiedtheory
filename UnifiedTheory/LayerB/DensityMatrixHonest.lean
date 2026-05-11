/-
  LayerB/DensityMatrixHonest.lean — Density matrix with the constraints
  the docstring of the original file ALREADY claimed but did not enforce.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT — A STRUCTURAL FIX

  `LayerB/DensityMatrix.lean` declares its `DensityMatrix2` structure as

     /-- A **2-state density matrix** (Hermitian, trace-1, positive
         semidefinite). … -/
     structure DensityMatrix2 where
       p₁ p₂ : ℝ
       coh_re coh_im : ℝ
       p₁_nonneg : 0 ≤ p₁
       p₂_nonneg : 0 ≤ p₂

  but the FIELDS only enforce `0 ≤ p₁` and `0 ≤ p₂`. Trace-1 and positive
  semi-definiteness are NOT in the type. As a consequence the term

     ρ_path : DensityMatrix2 :=
       ⟨0, 0, 5, 0, le_refl 0, le_refl 0⟩

  type-checks. It has trace `0` (not `1`) and the 2 × 2 Hermitian matrix
  it represents

     ⎡ 0   5 ⎤
     ⎣ 5   0 ⎦

  has eigenvalues `±5`, so it is INDEFINITE — not positive
  semi-definite. The docstring is a lie about what the type encodes.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT THIS FILE DOES

  Introduce `DensityMatrix2Honest`, a corrected structure whose FIELDS
  enforce the docstring claim of the original:

      p₁_nn   : 0 ≤ p₁
      p₂_nn   : 0 ≤ p₂
      htrace  : p₁ + p₂ = 1                          -- TRACE-1
      hPSD    : coh_re ^ 2 + coh_im ^ 2 ≤ p₁ * p₂   -- POSITIVE
                                                       SEMI-DEFINITE

  The PSD condition is the standard 2 × 2 Hermitian PSD criterion:
  for `H = ⎡p₁ c⎤ / ⎣c̄ p₂⎦`, `H ⪰ 0` iff its diagonal entries are
  non-negative AND its determinant is non-negative, i.e.
  `p₁·p₂ - |c|² ≥ 0`, equivalently `coh_re² + coh_im² ≤ p₁·p₂`.

  We then prove:

  (1) `pathological_rejected`: there is NO `DensityMatrix2Honest` with
      `p₁ = 0, p₂ = 0, coh_re = 5, coh_im = 0`. The corrupt term that
      type-checked in the original is REJECTED by this type.

  (2) `fromAmplitudes` lifts a normalized amplitude pair `(z₁, z₂)`
      with `|z₁|² + |z₂|² = 1` to a genuine `DensityMatrix2Honest`,
      with PSD saturated (det = 0, the rank-1 pure-state case).

  (3) `totalObs`, `dephase`, `dephased_obs`,
      `full_dephasing_classical`, `no_dephasing_quantum` —
      the dynamical-decoherence story of the original file
      reproduced on the corrected structure. Dephasing preserves
      trace-1 AND PSD (with `0 ≤ γ ≤ 1`).

  (4) `toLoose`: the forgetful map `DensityMatrix2Honest →
      DensityMatrix2` (which only forgets `htrace, hPSD`). Together
      with `pathological_rejected` this witnesses that
      `DensityMatrix2Honest` is a STRICT subtype of the original —
      the original lets in non-density-matrices.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

  – Two states only (qubit). The same fix scales to n×n via Hermitian
    PSD matrices, but we restrict here to match the file we are
    correcting.
  – Real/imag split (rather than `ℂ`) is kept to match the original
    file's API exactly so the migration is a drop-in replacement.
  – No `DerivedBFSplit` or extra physics is imported. This file is
    pure mathematical hygiene.

  Zero `sorry`. Zero custom axioms.
-/
import UnifiedTheory.LayerB.DensityMatrix

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.DensityMatrixHonest

open UnifiedTheory.LayerB
open UnifiedTheory.LayerB.DensityMatrix

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE CORRECTED STRUCTURE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A **genuine 2-state density matrix**. Unlike `DensityMatrix2` from
    `LayerB/DensityMatrix.lean`, this structure ENFORCES Hermiticity
    (built in by the real/imag split), trace-1, AND positive
    semi-definiteness as TYPE FIELDS, not docstring claims. -/
structure DensityMatrix2Honest where
  /-- Population of state 1: `|z₁|²`. -/
  p₁ : ℝ
  /-- Population of state 2: `|z₂|²`. -/
  p₂ : ℝ
  /-- Coherence (real part): `Re(z₁ · z̄₂)`. -/
  coh_re : ℝ
  /-- Coherence (imaginary part): `Im(z₁ · z̄₂)`. -/
  coh_im : ℝ
  /-- Population of state 1 is non-negative. -/
  hp₁_nn : 0 ≤ p₁
  /-- Population of state 2 is non-negative. -/
  hp₂_nn : 0 ≤ p₂
  /-- **TRACE-1**: probabilities sum to one. -/
  htrace : p₁ + p₂ = 1
  /-- **POSITIVE SEMI-DEFINITE**: the off-diagonal magnitude is bounded
      by the geometric mean of the populations. Equivalently
      `det(ρ) = p₁·p₂ - |c|² ≥ 0`, the standard 2 × 2 Hermitian PSD
      criterion together with non-negative diagonal. -/
  hPSD : coh_re ^ 2 + coh_im ^ 2 ≤ p₁ * p₂

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: THE PATHOLOGICAL TERM IS REJECTED
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    In the original file the term `⟨0, 0, 5, 0, le_refl 0, le_refl 0⟩`
    has type `DensityMatrix2`. Here we prove no such inhabitant exists
    in `DensityMatrix2Honest`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The pathological corrupt term `⟨0, 0, 5, 0, …⟩` is REJECTED.**
    No `DensityMatrix2Honest` has populations `(0, 0)` and coherence
    real-part `5` — both the trace-1 field AND the PSD field rule it
    out. -/
theorem pathological_rejected :
    ¬ ∃ ρ : DensityMatrix2Honest,
        ρ.p₁ = 0 ∧ ρ.p₂ = 0 ∧ ρ.coh_re = 5 ∧ ρ.coh_im = 0 := by
  rintro ⟨ρ, hp₁, hp₂, hc_re, _⟩
  -- TRACE channel: 0 + 0 ≠ 1
  have htr : (0 : ℝ) + 0 = 1 := by
    have := ρ.htrace
    rw [hp₁, hp₂] at this
    exact this
  exact absurd htr (by norm_num)

/-- **Even if trace were not enforced, PSD already rejects the
    pathological term.** With `p₁ = 0` and `coh_re = 5`, the PSD
    inequality `25 ≤ 0` is false. -/
theorem pathological_rejected_by_PSD_alone :
    ¬ ∃ ρ : DensityMatrix2Honest,
        ρ.p₁ = 0 ∧ ρ.coh_re = 5 := by
  rintro ⟨ρ, hp₁, hc_re⟩
  have hPSD := ρ.hPSD
  rw [hp₁, hc_re] at hPSD
  -- 25 + ρ.coh_im² ≤ 0
  have h25 : (25 : ℝ) ≤ 0 + ρ.coh_im ^ 2 + 0 := by
    have hsq : (ρ.coh_im) ^ 2 ≥ 0 := sq_nonneg _
    have : (5 : ℝ) ^ 2 + ρ.coh_im ^ 2 ≤ 0 * ρ.p₂ := by
      simpa using hPSD
    have h0 : (0 : ℝ) * ρ.p₂ = 0 := zero_mul _
    rw [h0] at this
    nlinarith [sq_nonneg ρ.coh_im]
  nlinarith [sq_nonneg ρ.coh_im]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: BUILDING DENSITY MATRICES FROM NORMALIZED AMPLITUDES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A normalized pure state `(z₁, z₂)` with `|z₁|² + |z₂|² = 1` gives
    rise to a rank-1 density matrix `|ψ⟩⟨ψ|` whose trace is 1 and whose
    determinant is 0 (purity = saturation of the PSD inequality).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The Lagrange identity for two complex numbers, expanded into real
    components:

      (z₁.re² + z₁.im²) · (z₂.re² + z₂.im²)
        = (z₁.re·z₂.re + z₁.im·z₂.im)²
          + (z₁.im·z₂.re − z₁.re·z₂.im)²

    This is the algebraic core of the PSD field for `fromAmplitudes`:
    the right-hand side is exactly `coh_re² + coh_im²` and the
    left-hand side is `p₁ · p₂`, so the PSD field is satisfied with
    equality (det = 0, the pure-state condition). -/
theorem lagrange_two_complex (z₁ z₂ : ℂ) :
    (z₁.re ^ 2 + z₁.im ^ 2) * (z₂.re ^ 2 + z₂.im ^ 2) =
      (z₁.re * z₂.re + z₁.im * z₂.im) ^ 2
        + (z₁.im * z₂.re - z₁.re * z₂.im) ^ 2 := by
  ring

/-- Construct an honest density matrix from a NORMALIZED amplitude
    pair. The hypothesis `|z₁|² + |z₂|² = 1` is needed to enforce
    trace-1, which the original `DensityMatrix.fromAmplitudes` did
    NOT require (and indeed could not, given its weaker type). -/
noncomputable def fromAmplitudes (z₁ z₂ : ℂ)
    (hnorm : z₁.re ^ 2 + z₁.im ^ 2 + (z₂.re ^ 2 + z₂.im ^ 2) = 1) :
    DensityMatrix2Honest where
  p₁ := z₁.re ^ 2 + z₁.im ^ 2
  p₂ := z₂.re ^ 2 + z₂.im ^ 2
  coh_re := z₁.re * z₂.re + z₁.im * z₂.im
  coh_im := z₁.im * z₂.re - z₁.re * z₂.im
  hp₁_nn := by positivity
  hp₂_nn := by positivity
  htrace := hnorm
  hPSD := by
    -- Lagrange identity gives equality; in particular ≤ holds.
    have := lagrange_two_complex z₁ z₂
    linarith [this]

/-- A pure state has determinant exactly zero (PSD saturated). -/
theorem fromAmplitudes_pure_det_zero (z₁ z₂ : ℂ)
    (hnorm : z₁.re ^ 2 + z₁.im ^ 2 + (z₂.re ^ 2 + z₂.im ^ 2) = 1) :
    let ρ := fromAmplitudes z₁ z₂ hnorm
    ρ.coh_re ^ 2 + ρ.coh_im ^ 2 = ρ.p₁ * ρ.p₂ := by
  unfold fromAmplitudes
  simp only
  have := lagrange_two_complex z₁ z₂
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: DECOHERENCE OBSERVABLE AND DEPHASING ON THE HONEST TYPE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Total interference observable, identical formula to the original
    file:  obs = p₁ + p₂ + 2·coh_re. With trace-1 enforced this is
            `1 + 2·coh_re`, but we keep the explicit form to match the
    original API. -/
def totalObs (ρ : DensityMatrix2Honest) : ℝ :=
  ρ.p₁ + ρ.p₂ + 2 * ρ.coh_re

/-- With trace-1 in the type, the observable simplifies to
    `1 + 2·coh_re`. -/
theorem totalObs_eq_one_plus_two_coh (ρ : DensityMatrix2Honest) :
    totalObs ρ = 1 + 2 * ρ.coh_re := by
  unfold totalObs
  have := ρ.htrace
  linarith

/-- **Dephasing on the honest type.** Multiplying the coherence by
    `γ ∈ [0, 1]` preserves trace-1 (populations untouched) and
    PSD (`(γ·c)² ≤ c² ≤ p₁·p₂`). -/
def dephase (γ : ℝ) (hγ_nn : 0 ≤ γ) (hγ_le_one : γ ≤ 1)
    (ρ : DensityMatrix2Honest) : DensityMatrix2Honest where
  p₁ := ρ.p₁
  p₂ := ρ.p₂
  coh_re := γ * ρ.coh_re
  coh_im := γ * ρ.coh_im
  hp₁_nn := ρ.hp₁_nn
  hp₂_nn := ρ.hp₂_nn
  htrace := ρ.htrace
  hPSD := by
    -- (γ·c_re)² + (γ·c_im)² = γ² · (c_re² + c_im²) ≤ 1 · (c_re² + c_im²)
    -- ≤ p₁ · p₂.
    have hsum :
        (γ * ρ.coh_re) ^ 2 + (γ * ρ.coh_im) ^ 2 =
          γ ^ 2 * (ρ.coh_re ^ 2 + ρ.coh_im ^ 2) := by ring
    rw [hsum]
    have hγsq_nn : 0 ≤ γ ^ 2 := sq_nonneg _
    have hγsq_le_one : γ ^ 2 ≤ 1 := by
      have h1 : γ * γ ≤ 1 * 1 :=
        mul_le_mul hγ_le_one hγ_le_one hγ_nn (by norm_num)
      have hsq : γ ^ 2 = γ * γ := sq (a := γ) ▸ rfl
      calc γ ^ 2 = γ * γ := by ring
        _ ≤ 1 * 1 := h1
        _ = 1 := by norm_num
    have hcsum_nn : 0 ≤ ρ.coh_re ^ 2 + ρ.coh_im ^ 2 := by positivity
    have hPSD := ρ.hPSD
    -- γ² · (c_re² + c_im²) ≤ 1 · (c_re² + c_im²) ≤ p₁ · p₂
    have step1 : γ ^ 2 * (ρ.coh_re ^ 2 + ρ.coh_im ^ 2) ≤
        1 * (ρ.coh_re ^ 2 + ρ.coh_im ^ 2) :=
      mul_le_mul_of_nonneg_right hγsq_le_one hcsum_nn
    have step2 : (1 : ℝ) * (ρ.coh_re ^ 2 + ρ.coh_im ^ 2) ≤ ρ.p₁ * ρ.p₂ := by
      rw [one_mul]; exact hPSD
    linarith

/-- Dephased observable formula — matches the original file. -/
theorem dephased_obs (γ : ℝ) (hγ_nn : 0 ≤ γ) (hγ_le_one : γ ≤ 1)
    (ρ : DensityMatrix2Honest) :
    totalObs (dephase γ hγ_nn hγ_le_one ρ) =
      ρ.p₁ + ρ.p₂ + 2 * γ * ρ.coh_re := by
  unfold totalObs dephase
  ring

/-- **Full dephasing (`γ = 0`) gives the classical observable**, equal
    to the trace `p₁ + p₂ = 1`. -/
theorem full_dephasing_classical (ρ : DensityMatrix2Honest) :
    totalObs (dephase 0 le_rfl (by norm_num) ρ) = ρ.p₁ + ρ.p₂ := by
  rw [dephased_obs]; ring

/-- **Full dephasing on the honest type yields exactly `1`** (trace),
    using the trace-1 field. -/
theorem full_dephasing_yields_one (ρ : DensityMatrix2Honest) :
    totalObs (dephase 0 le_rfl (by norm_num) ρ) = 1 := by
  rw [full_dephasing_classical]; exact ρ.htrace

/-- **No dephasing (`γ = 1`) preserves the full quantum observable.** -/
theorem no_dephasing_quantum (ρ : DensityMatrix2Honest) :
    totalObs (dephase 1 (by norm_num) le_rfl ρ) = totalObs ρ := by
  unfold totalObs dephase
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: PHYSICALLY MEANINGFUL CONSEQUENCES OF THE FIX
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    With trace-1 + PSD enforced, both populations are bounded in
    `[0, 1]` and the coherence magnitude is bounded above (in
    particular `|c|² ≤ 1/4`). These are basic 2-state probability
    facts that the original type CANNOT prove because it does not
    encode the constraints.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Each population is at most 1.** -/
theorem p₁_le_one (ρ : DensityMatrix2Honest) : ρ.p₁ ≤ 1 := by
  have ht := ρ.htrace
  have hp2 := ρ.hp₂_nn
  linarith

theorem p₂_le_one (ρ : DensityMatrix2Honest) : ρ.p₂ ≤ 1 := by
  have ht := ρ.htrace
  have hp1 := ρ.hp₁_nn
  linarith

/-- **Coherence magnitude is bounded by `1/4`.** Standard fact:
    `p₁·p₂ ≤ ((p₁+p₂)/2)² = 1/4` by AM-GM, and PSD gives
    `coh_re² + coh_im² ≤ p₁·p₂`. Hence `|c|² ≤ 1/4`. -/
theorem coherence_squared_le_quarter (ρ : DensityMatrix2Honest) :
    ρ.coh_re ^ 2 + ρ.coh_im ^ 2 ≤ 1 / 4 := by
  have hPSD := ρ.hPSD
  have ht := ρ.htrace
  have hp1 := ρ.hp₁_nn
  have hp2 := ρ.hp₂_nn
  -- AM-GM in elementary form: (p₁ - p₂)² ≥ 0  ⟹  p₁·p₂ ≤ ((p₁+p₂)/2)²
  have hAMGM : ρ.p₁ * ρ.p₂ ≤ ((ρ.p₁ + ρ.p₂) / 2) ^ 2 := by
    nlinarith [sq_nonneg (ρ.p₁ - ρ.p₂)]
  have hsq : ((ρ.p₁ + ρ.p₂) / 2) ^ 2 = 1 / 4 := by
    rw [ht]; norm_num
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: BRIDGE TO THE ORIGINAL `DensityMatrix2`
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The forgetful map `toLoose` extracts the data and discards the
    `htrace` and `hPSD` fields. Composed with `pathological_rejected`
    this gives a precise statement: the image of `toLoose` is a STRICT
    subset of `DensityMatrix2`. The original type is too permissive.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Forgetful map**: every honest density matrix gives a (loose)
    `DensityMatrix2`. The reverse direction is FALSE — the corrupt
    term `⟨0, 0, 5, 0, …⟩` lives in the loose type but no honest term
    maps to it (`pathological_rejected`). -/
def toLoose (ρ : DensityMatrix2Honest) : DensityMatrix2 where
  p₁ := ρ.p₁
  p₂ := ρ.p₂
  coh_re := ρ.coh_re
  coh_im := ρ.coh_im
  p₁_nonneg := ρ.hp₁_nn
  p₂_nonneg := ρ.hp₂_nn

/-- The forgetful map preserves `totalObs`. -/
theorem toLoose_totalObs (ρ : DensityMatrix2Honest) :
    DensityMatrix.totalObs (toLoose ρ) = totalObs ρ := by
  unfold DensityMatrix.totalObs totalObs toLoose
  rfl

/-- **The corrupt term lives in `DensityMatrix2`** (no obstruction to
    constructing it there). This formalizes "the original type
    accepts non-density-matrices." -/
def looseCorrupt : DensityMatrix2 :=
  ⟨0, 0, 5, 0, le_refl 0, le_refl 0⟩

/-- **No honest density matrix maps to the corrupt loose term.**
    Together with the existence of `looseCorrupt`, this proves that
    the image of `toLoose` is a proper subset of `DensityMatrix2`. -/
theorem corrupt_not_in_image :
    ¬ ∃ ρ : DensityMatrix2Honest, toLoose ρ = looseCorrupt := by
  rintro ⟨ρ, h⟩
  have hp1 : ρ.p₁ = 0 := by
    have := congrArg DensityMatrix2.p₁ h
    simpa [toLoose, looseCorrupt] using this
  have hp2 : ρ.p₂ = 0 := by
    have := congrArg DensityMatrix2.p₂ h
    simpa [toLoose, looseCorrupt] using this
  have hcre : ρ.coh_re = 5 := by
    have := congrArg DensityMatrix2.coh_re h
    simpa [toLoose, looseCorrupt] using this
  have hcim : ρ.coh_im = 0 := by
    have := congrArg DensityMatrix2.coh_im h
    simpa [toLoose, looseCorrupt] using this
  exact pathological_rejected ⟨ρ, hp1, hp2, hcre, hcim⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: MASTER STATEMENT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER THEOREM (HONEST DENSITY-MATRIX FIX).**

    Bundling the structural properties this file proves about the
    corrected density-matrix type:

    (1) The corrupt term `⟨0, 0, 5, 0, …⟩` is REJECTED by the type
        (`pathological_rejected`).
    (2) PSD alone already rejects it (`pathological_rejected_by_PSD_alone`),
        so trace-1 and PSD are independently doing real work.
    (3) Normalized amplitudes give a genuine pure-state density matrix
        (`fromAmplitudes`).
    (4) Pure states saturate PSD: det = 0 (`fromAmplitudes_pure_det_zero`).
    (5) Dephasing with `γ ∈ [0, 1]` is a well-defined endomorphism of
        the honest type (`dephase`), preserves trace, and at γ = 0
        yields the classical observable equal to 1
        (`full_dephasing_yields_one`).
    (6) Populations are bounded in `[0, 1]` and `|c|² ≤ 1/4`
        (`p₁_le_one`, `p₂_le_one`, `coherence_squared_le_quarter`) —
        elementary facts the loose type cannot establish.
    (7) The honest type is a STRICT subtype of `DensityMatrix2`
        (`toLoose` exists, but `corrupt_not_in_image` shows it is not
        surjective; the loose type contains `looseCorrupt`).
-/
theorem honest_density_matrix_master :
    -- (1) Corrupt term rejected by the honest type
    (¬ ∃ ρ : DensityMatrix2Honest,
        ρ.p₁ = 0 ∧ ρ.p₂ = 0 ∧ ρ.coh_re = 5 ∧ ρ.coh_im = 0)
    -- (2) Pure-state construction works
    ∧ (∀ z₁ z₂ : ℂ,
        z₁.re ^ 2 + z₁.im ^ 2 + (z₂.re ^ 2 + z₂.im ^ 2) = 1 →
          ∃ ρ : DensityMatrix2Honest,
            ρ.coh_re ^ 2 + ρ.coh_im ^ 2 = ρ.p₁ * ρ.p₂)
    -- (3) Full dephasing yields the classical trace = 1
    ∧ (∀ ρ : DensityMatrix2Honest,
        totalObs (dephase 0 le_rfl (by norm_num) ρ) = 1)
    -- (4) Coherence bounded by 1/4 universally
    ∧ (∀ ρ : DensityMatrix2Honest, ρ.coh_re ^ 2 + ρ.coh_im ^ 2 ≤ 1 / 4)
    -- (5) Honest is a strict subtype of loose
    ∧ (¬ ∃ ρ : DensityMatrix2Honest, toLoose ρ = looseCorrupt) := by
  refine ⟨pathological_rejected, ?_, full_dephasing_yields_one,
          coherence_squared_le_quarter, corrupt_not_in_image⟩
  intro z₁ z₂ hnorm
  exact ⟨fromAmplitudes z₁ z₂ hnorm, fromAmplitudes_pure_det_zero z₁ z₂ hnorm⟩

end UnifiedTheory.LayerB.DensityMatrixHonest
