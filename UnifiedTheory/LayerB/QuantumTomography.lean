/-
  LayerB/QuantumTomography.lean
  ──────────────────────────────

  **Quantum state tomography uniqueness** — every density matrix is
  uniquely determined by its Born-rule probabilities on an
  informationally-complete POVM (IC-POVM).

  ──────────────────────────────────────────────────────────────────
  WHAT IS DEFINED / PROVEN (no `sorry`, no custom `axiom`):

    1. `InformationallyCompletePOVM n k` :  a `POVM n k` whose effects
       span the real vector space of `n × n` Hermitian matrices.
       (Spanning is required only for *Hermitian* targets, which is the
       physically relevant case — density matrices are Hermitian.)

    2. `tomography_uniqueness` :  if two density matrices ρ, σ give
       the *same* Born-rule probability on every effect of an IC-POVM,
       then `ρ.M = σ.M`.  Proven by linearity + the Hilbert–Schmidt
       inner-product identity `Tr(H · H) = 0 ↔ H = 0` for Hermitian H.

    3. `pauliPlusX, pauliMinusX, …, pauliPlusZ, pauliMinusZ` :  the six
       qubit Pauli effects `E_± := (I ± P)/6` for `P ∈ {X, Y, Z}`.
       Each is Hermitian and PSD; the six sum to the `2 × 2` identity.

    4. `pauliICPOVM_qubit : POVM 2 6` :  the bundled 6-element Pauli
       POVM on a single qubit.

    5. `pauliICPOVM_qubit_spans_hermitian` :  every `2 × 2` Hermitian
       matrix `H = ⟨⟨a, b⟩, ⟨b*, d⟩⟩` (with `a, d` real) is a real
       linear combination of the six Pauli effects.  The coefficients
       are *explicit*: each is a small rational of the entries of H.

    6. `pauliICPOVM_qubit_isIC` :  the bundled
       `InformationallyCompletePOVM 2 6` for qubits.

    7. `qubit_tomography_uniqueness` :  the headline specialisation —
       a qubit density matrix is uniquely determined by its Born-rule
       probabilities on the six Pauli effects.

  ──────────────────────────────────────────────────────────────────
  SCOPING:

  The general tomography theorem is structural — it relies only on
  real-linear spanning + the Hilbert–Schmidt orthogonality
  `Tr(H * H) = 0 ↔ H = 0` for Hermitian H, which we get from
  `Matrix.trace_conjTranspose_mul_self_eq_zero_iff`.

  The qubit construction is the longest part — six explicit `2 × 2`
  matrices with entry-by-entry PSD verification and an explicit
  decomposition of a generic `2 × 2` Hermitian into Pauli coefficients
  (the standard Bloch-sphere parameterisation, restricted to the
  POVM effects).
-/

import UnifiedTheory.LayerB.NaimarkDilation

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.QuantumTomography

open Matrix Complex
open scoped BigOperators ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.NaimarkDilation

/-! ## 1. Informationally-complete POVMs -/

/-- An **informationally-complete POVM (IC-POVM)** on `ℂ^n`: a `POVM n k`
    whose effects span the real vector space of `n × n` Hermitian
    matrices.

    The spanning condition is required only for *Hermitian* targets,
    which is the physically relevant case — density matrices and
    their differences are Hermitian. -/
structure InformationallyCompletePOVM (n k : ℕ) extends POVM n k where
  /-- The effects span (as real linear combinations) every Hermitian
      matrix on `ℂ^n`. -/
  span_hermitian :
    ∀ H : Matrix (Fin n) (Fin n) ℂ, H.IsHermitian →
      ∃ c : Fin k → ℝ, H = ∑ i, (c i : ℂ) • E i

/-! ## 2. Hilbert–Schmidt orthogonality for Hermitians

We need: for a Hermitian matrix `H`, `Tr(H * H) = 0 ↔ H = 0`.  This is
exactly `Matrix.trace_conjTranspose_mul_self_eq_zero_iff` once we
substitute `H = Hᴴ` on the left. -/

/-- **Hilbert–Schmidt positivity for Hermitians.**  For a Hermitian
    matrix `H`, the (complex) trace `Tr(H * H)` is zero iff `H = 0`. -/
theorem trace_sq_eq_zero_iff_zero_of_hermitian
    {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.IsHermitian) :
    Matrix.trace (H * H) = 0 ↔ H = 0 := by
  -- `Tr(H * H) = Tr(Hᴴ * H)` since `Hᴴ = H` for Hermitian `H`.
  have h1 : H * H = H.conjTranspose * H := by rw [hH.eq]
  rw [h1]
  exact trace_conjTranspose_mul_self_eq_zero_iff

/-! ## 3. Trace of `H · K` is real for Hermitian `H, K`

For Hermitian matrices `H, K`, the trace `Tr(H * K)` is real (its
imaginary part vanishes).  Useful for matching real-part-only Born
probabilities to full complex traces. -/

/-- **Trace of a product of two Hermitians is real.** -/
theorem trace_mul_hermitian_hermitian_im_zero
    {n : ℕ}
    {H K : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    (Matrix.trace (H * K)).im = 0 := by
  -- `(Tr(HK))* = Tr((HK)ᴴ) = Tr(Kᴴ Hᴴ) = Tr(KH) = Tr(HK)` by cyclicity.
  have h_conj : star (Matrix.trace (H * K)) = Matrix.trace (H * K) := by
    rw [← Matrix.trace_conjTranspose]
    rw [Matrix.conjTranspose_mul, hH.eq, hK.eq]
    exact Matrix.trace_mul_comm K H
  -- A complex number equal to its star is real.
  have := congrArg Complex.im h_conj
  rw [Complex.star_def, Complex.conj_im] at this
  linarith

/-! ## 4. Tomography uniqueness — the headline theorem -/

/-- **Tomography uniqueness.**  Given an informationally-complete POVM
    `P` on `ℂ^n` and two density matrices `ρ, σ`, if the Born-rule
    probability of every effect agrees on both states, then
    `ρ.M = σ.M`.

    Proof.  Set `H := ρ.M - σ.M`.  Hermiticity of `H` is immediate.
    For each effect `E_i`, the trace `Tr(H · E_i) = Tr(ρ.M · E_i) - Tr(σ.M · E_i)`
    has real part zero (Born-rule hypothesis) and imaginary part zero
    (both factors are Hermitian).  Hence `Tr(H · E_i) = 0` as a
    complex number.  By IC-spanning, every Hermitian matrix `K` is a
    real linear combination `K = Σ c_i · E_i`, so `Tr(H · K) = 0` for
    every Hermitian `K`.  Taking `K = H` gives `Tr(H · H) = 0`, hence
    `H = 0` by `trace_sq_eq_zero_iff_zero_of_hermitian`. -/
theorem tomography_uniqueness {n k : ℕ}
    (P : InformationallyCompletePOVM n k)
    (ρ σ : ComplexDensityMatrix n)
    (h_match : ∀ i, P.toPOVM.bornProb ρ i = P.toPOVM.bornProb σ i) :
    ρ.M = σ.M := by
  -- Step 1: difference is Hermitian.
  set H : Matrix (Fin n) (Fin n) ℂ := ρ.M - σ.M with hH_def
  have hH_herm : H.IsHermitian := ρ.hHerm.sub σ.hHerm
  -- Step 2: for each i, Tr(H · E i) = 0 as a complex number.
  have h_trace_E : ∀ i, Matrix.trace (H * P.E i) = 0 := by
    intro i
    have hE_herm : (P.E i).IsHermitian := P.isHerm i
    -- Real part is zero by Born-rule hypothesis.
    have h_re : (Matrix.trace (H * P.E i)).re = 0 := by
      rw [hH_def, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
      have h_left  := h_match i
      unfold POVM.bornProb at h_left
      linarith
    -- Imaginary part is zero since H, E_i are Hermitian.
    have h_im : (Matrix.trace (H * P.E i)).im = 0 :=
      trace_mul_hermitian_hermitian_im_zero hH_herm hE_herm
    -- Complex number with both parts zero is zero.
    apply Complex.ext
    · exact h_re
    · exact h_im
  -- Step 3: extend to every Hermitian K via spanning, then take K = H.
  have h_trace_K : ∀ K : Matrix (Fin n) (Fin n) ℂ, K.IsHermitian →
      Matrix.trace (H * K) = 0 := by
    intro K hK_herm
    obtain ⟨c, hKeq⟩ := P.span_hermitian K hK_herm
    rw [hKeq]
    -- Tr (H * ∑ i, c i • E i) = ∑ i, c i * Tr(H * E i) = 0.
    rw [Matrix.mul_sum, Matrix.trace_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [Matrix.mul_smul, Matrix.trace_smul, h_trace_E i]
    simp
  -- Step 4: take K = H ⟹ Tr(H * H) = 0 ⟹ H = 0.
  have h_sq : Matrix.trace (H * H) = 0 := h_trace_K H hH_herm
  have h_zero : H = 0 := (trace_sq_eq_zero_iff_zero_of_hermitian hH_herm).mp h_sq
  -- Conclude ρ.M = σ.M from ρ.M - σ.M = 0.
  have : ρ.M - σ.M = 0 := h_zero
  exact sub_eq_zero.mp this

/-! ## 5. The qubit Pauli IC-POVM

We now construct the explicit 6-element Pauli IC-POVM on a single qubit
(`n = 2`).  The six effects are

  E_{±X} := (I ± σ_X) / 6,
  E_{±Y} := (I ± σ_Y) / 6,
  E_{±Z} := (I ± σ_Z) / 6,

with `σ_X, σ_Y, σ_Z` the standard Pauli matrices and `I` the `2 × 2`
identity.  They sum to `I` (each opposite pair contributes `(2 I)/6 = I/3`,
and three pairs give `I`).  Each is PSD because `(I ± P)/2` is a rank-1
projector for any self-adjoint involution `P` (and a positive scalar
times a projector is PSD).

Spanning:  every `2 × 2` Hermitian `H = aI + b σ_X + c σ_Y + d σ_Z`
(with `a, b, c, d ∈ ℝ`) decomposes as

  H = 3a · (E_{+X} + E_{-X})   [   = 3a · I/3 = a I    ]
    + 3b · (E_{+X} − E_{-X})   [   = 3b · σ_X /3 = b σ_X ]
    + 3c · (E_{+Y} − E_{-Y})
    + 3d · (E_{+Z} − E_{-Z}).

This redundantly uses only `(E_{+X} ± E_{-X})` and friends but
expresses every Hermitian as a real linear combination of the six
effects.
-/

section QubitPauli

/-- The 2×2 identity matrix as a `Matrix (Fin 2) (Fin 2) ℂ`. -/
noncomputable def matI : Matrix (Fin 2) (Fin 2) ℂ := 1

/-- Pauli X matrix. -/
noncomputable def matX : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- Pauli Y matrix. -/
noncomputable def matY : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -Complex.I; Complex.I, 0]

/-- Pauli Z matrix. -/
noncomputable def matZ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

/-! ### Hermiticity of the Pauli matrices -/

theorem matI_isHerm : matI.IsHermitian := by
  change matI.conjTranspose = matI
  unfold matI
  exact Matrix.conjTranspose_one

theorem matX_isHerm : matX.IsHermitian := by
  change matX.conjTranspose = matX
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matX, Matrix.conjTranspose, Matrix.of_apply, star, Complex.ext_iff]

theorem matY_isHerm : matY.IsHermitian := by
  change matY.conjTranspose = matY
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matY, Matrix.conjTranspose, Matrix.of_apply, star, Complex.ext_iff,
      Complex.I_re, Complex.I_im]

theorem matZ_isHerm : matZ.IsHermitian := by
  change matZ.conjTranspose = matZ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matZ, Matrix.conjTranspose, Matrix.of_apply, star, Complex.ext_iff]

/-! ### The six Pauli effects.

Each is `(I ± P)/6` for `P ∈ {X, Y, Z}`. -/

/-- Effect `(I + σ_X)/6`. -/
noncomputable def E_pX : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 : ℂ) / 6) • (matI + matX)

/-- Effect `(I − σ_X)/6`. -/
noncomputable def E_mX : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 : ℂ) / 6) • (matI - matX)

/-- Effect `(I + σ_Y)/6`. -/
noncomputable def E_pY : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 : ℂ) / 6) • (matI + matY)

/-- Effect `(I − σ_Y)/6`. -/
noncomputable def E_mY : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 : ℂ) / 6) • (matI - matY)

/-- Effect `(I + σ_Z)/6`. -/
noncomputable def E_pZ : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 : ℂ) / 6) • (matI + matZ)

/-- Effect `(I − σ_Z)/6`. -/
noncomputable def E_mZ : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 : ℂ) / 6) • (matI - matZ)

/-- Indexing the six Pauli effects by `Fin 6`.  We use the order
    `0 = +X, 1 = -X, 2 = +Y, 3 = -Y, 4 = +Z, 5 = -Z`. -/
noncomputable def pauliEffect : Fin 6 → Matrix (Fin 2) (Fin 2) ℂ
  | ⟨0, _⟩ => E_pX
  | ⟨1, _⟩ => E_mX
  | ⟨2, _⟩ => E_pY
  | ⟨3, _⟩ => E_mY
  | ⟨4, _⟩ => E_pZ
  | ⟨5, _⟩ => E_mZ
  | ⟨_+6, h⟩ => absurd h (by omega)

/-! ### PSD verification

We verify PSD by direct computation: for each effect we exhibit a
column-vector Kraus operator whose `Kᴴ * K` is the effect.

For `(I + P)/6` with `P` a Pauli, `(I + P)/2` is a rank-1 projector;
multiplying by `1/3` keeps it PSD.  We instead use the cleaner route:
`(I + P)/6` is a real-nonneg scalar times a PSD matrix.

The PSD of `(I + σ_X)/2` etc. comes from the matrix being equal to
the outer product of a unit vector with itself, which is automatically
PSD via `posSemidef_conjTranspose_mul_self`.
-/

/-- A `1 × 2` matrix encoding the row vector `(1/√2, 1/√2)`. -/
noncomputable def vec_pX_row : Matrix (Fin 1) (Fin 2) ℂ :=
  fun _ j => if j = 0 then ((Real.sqrt 2)⁻¹ : ℂ) else ((Real.sqrt 2)⁻¹ : ℂ)

/-- Two `1 × 2` row vectors are easy to manipulate; we won't actually
    pursue the Kraus route for PSD here (it gets very heavy
    arithmetically).  Instead we prove PSD by reducing to scalar
    multiples of explicit PSD matrices and using `Matrix.PosSemidef.smul`
    plus the rank-1 outer-product fact via `posSemidef_conjTranspose_mul_self`. -/
example : True := trivial

/-- The complex scalar `1/6` is self-conjugate (it is real). -/
private theorem star_one_sixth : star ((1 : ℂ) / 6) = (1 : ℂ) / 6 := by
  apply Complex.ext <;> simp [Complex.star_def]

/-- The complex scalar `1/3` is self-conjugate (it is real). -/
private theorem star_one_third : star ((1 : ℂ) / 3) = (1 : ℂ) / 3 := by
  apply Complex.ext <;> simp [Complex.star_def]

/-- Hermiticity of every Pauli effect (used as a building block for PSD). -/
theorem E_pX_isHerm : E_pX.IsHermitian := by
  change E_pX.conjTranspose = E_pX
  unfold E_pX
  have h_sum : (matI + matX).IsHermitian := matI_isHerm.add matX_isHerm
  rw [Matrix.conjTranspose_smul, h_sum.eq, star_one_sixth]

theorem E_mX_isHerm : E_mX.IsHermitian := by
  change E_mX.conjTranspose = E_mX
  unfold E_mX
  have h_sum : (matI - matX).IsHermitian := matI_isHerm.sub matX_isHerm
  rw [Matrix.conjTranspose_smul, h_sum.eq, star_one_sixth]

theorem E_pY_isHerm : E_pY.IsHermitian := by
  change E_pY.conjTranspose = E_pY
  unfold E_pY
  have h_sum : (matI + matY).IsHermitian := matI_isHerm.add matY_isHerm
  rw [Matrix.conjTranspose_smul, h_sum.eq, star_one_sixth]

theorem E_mY_isHerm : E_mY.IsHermitian := by
  change E_mY.conjTranspose = E_mY
  unfold E_mY
  have h_sum : (matI - matY).IsHermitian := matI_isHerm.sub matY_isHerm
  rw [Matrix.conjTranspose_smul, h_sum.eq, star_one_sixth]

theorem E_pZ_isHerm : E_pZ.IsHermitian := by
  change E_pZ.conjTranspose = E_pZ
  unfold E_pZ
  have h_sum : (matI + matZ).IsHermitian := matI_isHerm.add matZ_isHerm
  rw [Matrix.conjTranspose_smul, h_sum.eq, star_one_sixth]

theorem E_mZ_isHerm : E_mZ.IsHermitian := by
  change E_mZ.conjTranspose = E_mZ
  unfold E_mZ
  have h_sum : (matI - matZ).IsHermitian := matI_isHerm.sub matZ_isHerm
  rw [Matrix.conjTranspose_smul, h_sum.eq, star_one_sixth]

/-! ### PSD via explicit Kraus operators.

For each effect `(I + P)/6 = (1/3) * (I + P)/2 = (1/3) |v⟩⟨v|`, with
`|v⟩` the unit `+1`-eigenvector of `P`.  We define `K := (1/√3) · v†`
(a `1 × 2` row), so `Kᴴ * K = (1/3) · v · v† = (I + P)/6`.  Then PSD
follows from `posSemidef_conjTranspose_mul_self`.

Concretely:
  • `+X` eigenvector:  `v_pX = (1, 1)/√2`
  • `-X` eigenvector:  `v_mX = (1, -1)/√2`
  • `+Y` eigenvector:  `v_pY = (1, i)/√2`
  • `-Y` eigenvector:  `v_mY = (1, -i)/√2`
  • `+Z` eigenvector:  `v_pZ = (1, 0)`
  • `-Z` eigenvector:  `v_mZ = (0, 1)`

For brevity we package each Kraus operator as a `Matrix (Fin 1) (Fin 2) ℂ`.
-/

/-- Real scalar `1/√6`. -/
noncomputable def r6 : ℝ := (Real.sqrt 6)⁻¹

/-- Real scalar `1/√3`. -/
noncomputable def r3 : ℝ := (Real.sqrt 3)⁻¹

/-- Kraus row vector `(1/√6) · (1, 1)` for the `+X` effect. -/
noncomputable def K_pX : Matrix (Fin 1) (Fin 2) ℂ :=
  !![(r6 : ℂ), (r6 : ℂ)]

/-- Kraus row vector `(1/√6) · (1, -1)` for the `-X` effect. -/
noncomputable def K_mX : Matrix (Fin 1) (Fin 2) ℂ :=
  !![(r6 : ℂ), -(r6 : ℂ)]

/-- Kraus row vector `(1/√6) · (1, -i)` for the `+Y` effect.
    (Convention: the +Y eigenvector is `(1, i)/√2`; its conjugate
    transpose row is `(1, -i)/√2`.) -/
noncomputable def K_pY : Matrix (Fin 1) (Fin 2) ℂ :=
  !![(r6 : ℂ), -(r6 : ℂ) * Complex.I]

/-- Kraus row vector `(1/√6) · (1, i)` for the `-Y` effect. -/
noncomputable def K_mY : Matrix (Fin 1) (Fin 2) ℂ :=
  !![(r6 : ℂ), (r6 : ℂ) * Complex.I]

/-- Kraus row vector `(1/√3) · (1, 0)` for the `+Z` effect. -/
noncomputable def K_pZ : Matrix (Fin 1) (Fin 2) ℂ :=
  !![(r3 : ℂ), 0]

/-- Kraus row vector `(1/√3) · (0, 1)` for the `-Z` effect. -/
noncomputable def K_mZ : Matrix (Fin 1) (Fin 2) ℂ :=
  !![0, (r3 : ℂ)]

/-! ### Helpers: real-valued reciprocals and squares -/

theorem r6_sq : r6 * r6 = (1 : ℝ) / 6 := by
  unfold r6
  have h6 : (0 : ℝ) ≤ 6 := by norm_num
  have h_sq : Real.sqrt 6 * Real.sqrt 6 = 6 := Real.mul_self_sqrt h6
  have h_ne : Real.sqrt 6 ≠ 0 := by
    intro h; rw [h, zero_mul] at h_sq; linarith
  rw [← mul_inv]
  rw [show Real.sqrt 6 * Real.sqrt 6 = 6 from h_sq]
  norm_num

theorem r3_sq : r3 * r3 = (1 : ℝ) / 3 := by
  unfold r3
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  have h_sq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt h3
  have h_ne : Real.sqrt 3 ≠ 0 := by
    intro h; rw [h, zero_mul] at h_sq; linarith
  rw [← mul_inv]
  rw [show Real.sqrt 3 * Real.sqrt 3 = 3 from h_sq]
  norm_num

theorem r6_sq_complex : (r6 : ℂ) * (r6 : ℂ) = (1 : ℂ) / 6 := by
  have h := r6_sq
  have h_cast : ((r6 * r6 : ℝ) : ℂ) = (((1 : ℝ) / 6) : ℂ) := by
    exact_mod_cast h
  rw [Complex.ofReal_mul] at h_cast
  rw [h_cast]
  push_cast
  ring

theorem r3_sq_complex : (r3 : ℂ) * (r3 : ℂ) = (1 : ℂ) / 3 := by
  have h := r3_sq
  have h_cast : ((r3 * r3 : ℝ) : ℂ) = (((1 : ℝ) / 3) : ℂ) := by
    exact_mod_cast h
  rw [Complex.ofReal_mul] at h_cast
  rw [h_cast]
  push_cast
  ring

/-! ### Verifying each Kraus square equals the corresponding effect

We compute each entry of `Kᴴ * K` directly using `Matrix.mul_apply` +
`Fin.sum_univ_two`, then close with `sqrt6_sq_complex` / `sqrt3_sq_complex`. -/

/-- The (i, j) entry of `Kᴴ * K` for K a `1 × n` matrix is
    `star (K 0 i) * K 0 j`. -/
private lemma conjT_mul_self_apply
    {n : ℕ} (K : Matrix (Fin 1) (Fin n) ℂ) (i j : Fin n) :
    (K.conjTranspose * K) i j = star (K 0 i) * K 0 j := by
  rw [Matrix.mul_apply]
  simp [Matrix.conjTranspose]

private lemma star_r6 : star ((r6 : ℝ) : ℂ) = ((r6 : ℝ) : ℂ) :=
  Complex.conj_ofReal _

private lemma star_r3 : star ((r3 : ℝ) : ℂ) = ((r3 : ℝ) : ℂ) :=
  Complex.conj_ofReal _

theorem K_pX_kraus_eq : K_pX.conjTranspose * K_pX = E_pX := by
  ext i j
  rw [conjT_mul_self_apply]
  unfold E_pX matI matX K_pX
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply,
        Matrix.one_apply, star_r6]) <;>
    (first
      | (rw [r6_sq_complex]; ring)
      | ring
      | rfl)

theorem K_mX_kraus_eq : K_mX.conjTranspose * K_mX = E_mX := by
  ext i j
  rw [conjT_mul_self_apply]
  unfold E_mX matI matX K_mX
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply,
        Matrix.one_apply, star_r6]) <;>
    (first
      | (rw [show -((r6 : ℂ)) * -((r6 : ℂ)) = (r6 : ℂ) * (r6 : ℂ) by ring,
             r6_sq_complex]; ring)
      | (rw [show -((r6 : ℂ)) * ((r6 : ℂ)) = -((r6 : ℂ) * (r6 : ℂ)) by ring,
             r6_sq_complex]; ring)
      | (rw [show ((r6 : ℂ)) * -((r6 : ℂ)) = -((r6 : ℂ) * (r6 : ℂ)) by ring,
             r6_sq_complex]; ring)
      | (rw [r6_sq_complex]; ring)
      | ring
      | rfl)

/-- Helper: `Complex.I` squared. -/
private theorem complex_I_sq : Complex.I * Complex.I = -1 := Complex.I_mul_I

theorem K_pY_kraus_eq : K_pY.conjTranspose * K_pY = E_pY := by
  ext i j
  rw [conjT_mul_self_apply]
  unfold E_pY matI matY K_pY
  fin_cases i <;> fin_cases j
  · -- (0,0)
    simp [Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, star_r6,
      Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
    have h6 := r6_sq_complex
    linear_combination h6
  · -- (0,1): r6 * (r6 * I) = (1/6) * I
    simp [Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, star_r6,
      Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
    have h6 := r6_sq_complex
    linear_combination Complex.I * h6
  · -- (1,0): r6 * I * r6 = (1/6) * I
    simp [Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, star_r6,
      Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
    have h6 := r6_sq_complex
    linear_combination Complex.I * h6
  · -- (1,1): -(r6 * I * (r6 * I)) = 1/6
    simp [Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, star_r6,
      Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
    have h6 := r6_sq_complex
    have hI := complex_I_sq
    have h_step : -((r6 : ℂ) * Complex.I * ((r6 : ℂ) * Complex.I))
                = -((r6 : ℂ) * (r6 : ℂ)) * (Complex.I * Complex.I) := by ring
    rw [h_step, h6, hI]
    ring

theorem K_mY_kraus_eq : K_mY.conjTranspose * K_mY = E_mY := by
  ext i j
  rw [conjT_mul_self_apply]
  unfold E_mY matI matY K_mY
  fin_cases i <;> fin_cases j
  · simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply, star_r6,
      Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
    have h6 := r6_sq_complex
    linear_combination h6
  · simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply, star_r6,
      Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
    have h6 := r6_sq_complex
    linear_combination Complex.I * h6
  · simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply, star_r6,
      Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
    have h6 := r6_sq_complex
    linear_combination Complex.I * h6
  · simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply, star_r6,
      Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
    have h6 := r6_sq_complex
    have hI := complex_I_sq
    have h_step : -((r6 : ℂ) * Complex.I * ((r6 : ℂ) * Complex.I))
                = -((r6 : ℂ) * (r6 : ℂ)) * (Complex.I * Complex.I) := by ring
    rw [h_step, h6, hI]
    ring

theorem K_pZ_kraus_eq : K_pZ.conjTranspose * K_pZ = E_pZ := by
  ext i j
  rw [conjT_mul_self_apply]
  unfold E_pZ matI matZ K_pZ
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply,
        Matrix.one_apply, star_r3]) <;>
    (first
      | (rw [r3_sq_complex]; ring)
      | ring
      | rfl)

theorem K_mZ_kraus_eq : K_mZ.conjTranspose * K_mZ = E_mZ := by
  ext i j
  rw [conjT_mul_self_apply]
  unfold E_mZ matI matZ K_mZ
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply,
        Matrix.one_apply, star_r3]) <;>
    (first
      | (rw [r3_sq_complex]; ring)
      | ring
      | rfl)

/-! ### Each effect is PSD -/

theorem E_pX_isPSD : E_pX.PosSemidef := by
  rw [← K_pX_kraus_eq]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem E_mX_isPSD : E_mX.PosSemidef := by
  rw [← K_mX_kraus_eq]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem E_pY_isPSD : E_pY.PosSemidef := by
  rw [← K_pY_kraus_eq]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem E_mY_isPSD : E_mY.PosSemidef := by
  rw [← K_mY_kraus_eq]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem E_pZ_isPSD : E_pZ.PosSemidef := by
  rw [← K_pZ_kraus_eq]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem E_mZ_isPSD : E_mZ.PosSemidef := by
  rw [← K_mZ_kraus_eq]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-! ### `pauliEffect` is PSD at every index -/

theorem pauliEffect_isPSD : ∀ i, (pauliEffect i).PosSemidef := by
  intro i
  match i with
  | ⟨0, _⟩ => exact E_pX_isPSD
  | ⟨1, _⟩ => exact E_mX_isPSD
  | ⟨2, _⟩ => exact E_pY_isPSD
  | ⟨3, _⟩ => exact E_mY_isPSD
  | ⟨4, _⟩ => exact E_pZ_isPSD
  | ⟨5, _⟩ => exact E_mZ_isPSD

/-! ### Completeness: the six effects sum to the identity -/

theorem pauliEffect_complete :
    (∑ i, pauliEffect i) = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Fin.sum_univ_six]
  show pauliEffect 0 + pauliEffect 1 + pauliEffect 2 + pauliEffect 3
      + pauliEffect 4 + pauliEffect 5 = (1 : Matrix (Fin 2) (Fin 2) ℂ)
  show E_pX + E_mX + E_pY + E_mY + E_pZ + E_mZ = (1 : Matrix (Fin 2) (Fin 2) ℂ)
  unfold E_pX E_mX E_pY E_mY E_pZ E_mZ matI matX matY matZ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
      Matrix.one_apply] <;>
    ring

/-! ### The bundled qubit Pauli POVM -/

/-- The bundled 6-element Pauli POVM on a single qubit. -/
noncomputable def pauliICPOVM_qubit : POVM 2 6 where
  E := pauliEffect
  isPSD := pauliEffect_isPSD
  complete := pauliEffect_complete

/-! ### Spanning the Hermitian space.

A `2 × 2` Hermitian matrix has the form
`H = ⟨⟨a, b + i b'⟩, ⟨b − i b', d⟩⟩` with `a, d, b, b' ∈ ℝ`.
Equivalently `H = ((a+d)/2) I + b σ_X + (-b') σ_Y + ((a-d)/2) σ_Z`.

We decompose `H` in the six-effect basis as
  H = 3·((a+d)/2)·(E_{+X}+E_{-X})/3·... — actually we use the simpler
identity `I = 3(E_{+X} + E_{-X})`, `σ_X = 3(E_{+X} − E_{-X})`,
`σ_Y = 3(E_{+Y} − E_{-Y})`, `σ_Z = 3(E_{+Z} − E_{-Z})`.  Substituting:

  H = ((a+d)/2) I + b σ_X + (−b') σ_Y + ((a−d)/2) σ_Z
    = ((a+d)/2)·3·(E_{+X} + E_{-X})/1 + … but actually
    note (E_{+X} + E_{-X}) + (E_{+Y} + E_{-Y}) + (E_{+Z} + E_{-Z}) = I,
    not 3I.  Let's use a cleaner basis:
    I = (E_{+X} + E_{-X}) + (E_{+Y} + E_{-Y}) + (E_{+Z} + E_{-Z}).

  We use the recipe (one of many valid expansions):
    H = α_+X · E_{+X} + α_-X · E_{-X} + α_+Y · E_{+Y} + α_-Y · E_{-Y}
         + α_+Z · E_{+Z} + α_-Z · E_{-Z}
  with explicit coefficients chosen below.

  Concrete recipe (clean choice):
    H = ((a+d)/2)·I + b·σ_X + (−b')·σ_Y + ((a−d)/2)·σ_Z
    Replace I with `3 (E_{+X} + E_{-X})`,
            σ_X with `3 (E_{+X} − E_{-X})`,
            σ_Y with `3 (E_{+Y} − E_{-Y})`,
            σ_Z with `3 (E_{+Z} − E_{-Z})`.
    Coefficients:
      c_{+X} = 3·((a+d)/2) + 3 b,
      c_{-X} = 3·((a+d)/2) − 3 b,
      c_{+Y} = +3·(−b') = −3 b',
      c_{-Y} = −3·(−b') = +3 b',
      c_{+Z} = +3·((a−d)/2),
      c_{-Z} = −3·((a−d)/2).
-/

/-- Decomposition coefficients of a `2 × 2` Hermitian `H` in the six
    Pauli effects, expressed as a `Fin 6 → ℝ` function. -/
noncomputable def pauliDecompCoeffs
    (H : Matrix (Fin 2) (Fin 2) ℂ) : Fin 6 → ℝ
  | ⟨0, _⟩ => 3 * (((H 0 0).re + (H 1 1).re) / 2) + 3 * (H 0 1).re
  | ⟨1, _⟩ => 3 * (((H 0 0).re + (H 1 1).re) / 2) - 3 * (H 0 1).re
  | ⟨2, _⟩ => -3 * (H 0 1).im
  | ⟨3, _⟩ =>  3 * (H 0 1).im
  | ⟨4, _⟩ => 3 * (((H 0 0).re - (H 1 1).re) / 2)
  | ⟨5, _⟩ => -3 * (((H 0 0).re - (H 1 1).re) / 2)
  | ⟨_+6, h⟩ => absurd h (by omega)

/-! ### The span identity.

Substituting the coefficients gives an entrywise identity that we
verify by `fin_cases` + `simp [...]` + `ring`.  We work directly with
`H`'s entries `H i j` and use the Hermitian assumption to rewrite
`H 1 0 = star (H 0 1)`. -/

/-- **The 2×2 Hermitian spanning identity for the qubit Pauli POVM.** -/
theorem pauliEffect_span_hermitian
    (H : Matrix (Fin 2) (Fin 2) ℂ) (hH : H.IsHermitian) :
    H = ∑ i, (pauliDecompCoeffs H i : ℂ) • pauliEffect i := by
  -- Expand the sum.
  have h_sum :
      (∑ i, (pauliDecompCoeffs H i : ℂ) • pauliEffect i)
        = (pauliDecompCoeffs H 0 : ℂ) • E_pX
          + (pauliDecompCoeffs H 1 : ℂ) • E_mX
          + (pauliDecompCoeffs H 2 : ℂ) • E_pY
          + (pauliDecompCoeffs H 3 : ℂ) • E_mY
          + (pauliDecompCoeffs H 4 : ℂ) • E_pZ
          + (pauliDecompCoeffs H 5 : ℂ) • E_mZ := by
    rw [Fin.sum_univ_six]
    rfl
  rw [h_sum]
  -- Hermiticity tells us H 1 0 = star (H 0 1).
  have h_off : H 1 0 = star (H 0 1) := by
    have := hH.apply 0 1
    -- hH.apply 0 1 : star (H 1 0) = H 0 1
    -- ⟹ H 1 0 = star (H 0 1)
    have h_eq : star (star (H 1 0)) = star (H 0 1) := by
      rw [this]
    rwa [star_star] at h_eq
  -- Hermiticity also forces (H 0 0).im = 0 and (H 1 1).im = 0.
  have h_diag00_real : (H 0 0).im = 0 := by
    have := hH.apply 0 0
    -- star (H 0 0) = H 0 0  ⟹  H 0 0 is real
    have h_im : (star (H 0 0)).im = (H 0 0).im := by rw [this]
    rw [Complex.star_def, Complex.conj_im] at h_im
    linarith
  have h_diag11_real : (H 1 1).im = 0 := by
    have := hH.apply 1 1
    have h_im : (star (H 1 1)).im = (H 1 1).im := by rw [this]
    rw [Complex.star_def, Complex.conj_im] at h_im
    linarith
  -- Now go entrywise.
  ext i j
  fin_cases i <;> fin_cases j
  · -- (0, 0) entry.
    change H 0 0 = _
    unfold pauliDecompCoeffs E_pX E_mX E_pY E_mY E_pZ E_mZ matI matX matY matZ
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply]
    apply Complex.ext
    · simp; push_cast; ring
    · simp [h_diag00_real]
  · -- (0, 1) entry.
    change H 0 1 = _
    unfold pauliDecompCoeffs E_pX E_mX E_pY E_mY E_pZ E_mZ matI matX matY matZ
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply]
    apply Complex.ext
    · simp; push_cast; ring
    · simp; push_cast; ring
  · -- (1, 0) entry.  LHS = H 1 0 = star (H 0 1).
    change H 1 0 = _
    rw [h_off]
    unfold pauliDecompCoeffs E_pX E_mX E_pY E_mY E_pZ E_mZ matI matX matY matZ
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply]
    apply Complex.ext
    · simp [Complex.star_def, Complex.conj_re]; push_cast; ring
    · simp [Complex.star_def, Complex.conj_im]; push_cast; ring
  · -- (1, 1) entry.
    change H 1 1 = _
    unfold pauliDecompCoeffs E_pX E_mX E_pY E_mY E_pZ E_mZ matI matX matY matZ
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply]
    apply Complex.ext
    · simp; ring
    · simp [h_diag11_real]

/-! ### The bundled IC-POVM -/

/-- **The qubit Pauli POVM is informationally complete.** -/
noncomputable def pauliICPOVM_qubit_isIC : InformationallyCompletePOVM 2 6 where
  toPOVM := pauliICPOVM_qubit
  span_hermitian H hH := ⟨pauliDecompCoeffs H, pauliEffect_span_hermitian H hH⟩

/-! ### Headline qubit specialisation -/

/-- **Qubit tomography uniqueness.**  A qubit density matrix is uniquely
    determined by its Born-rule probabilities on the six Pauli
    effects `(I ± σ_{X,Y,Z}) / 6`. -/
theorem qubit_tomography_uniqueness
    (ρ σ : ComplexDensityMatrix 2)
    (h_match : ∀ i, pauliICPOVM_qubit.bornProb ρ i
                  = pauliICPOVM_qubit.bornProb σ i) :
    ρ.M = σ.M :=
  tomography_uniqueness pauliICPOVM_qubit_isIC ρ σ h_match

end QubitPauli

/-! ## 6. Axiom audit. -/

#print axioms tomography_uniqueness
#print axioms pauliICPOVM_qubit
#print axioms pauliICPOVM_qubit_isIC
#print axioms qubit_tomography_uniqueness

end UnifiedTheory.LayerB.QuantumTomography
