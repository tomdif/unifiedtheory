/-
  LayerB/ZurekEinselection.lean — Zurek's environment-induced
  superselection (einselection) of a preferred (pointer) basis.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT

  Zurek (1981, 2003) introduced **einselection** — environment-induced
  superselection — as a resolution of the preferred-basis problem in
  the measurement problem of quantum mechanics:

      A system S coupled to an environment E via an interaction
      Hamiltonian H_int picks out a preferred basis {|i⟩_S} for which
      the product states `(|i⟩⟨i|)_S ⊗ ρ_E` evolve approximately as
      products under U_{SE}(t). All superpositions of distinct
      |i⟩_S decohere; the diagonal entries (populations) survive.

  The **predictability sieve** is the criterion that selects the
  preferred basis: it is the basis in which states remain most nearly
  classical (least entangled with E) for longest. In the limit of
  strong coupling and long time, only diagonal density matrices in
  the preferred basis remain stable.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT THIS FILE PROVES (the structural skeleton of einselection)

  A genuine derivation of einselection from S ⊗ E dynamics is far
  outside what we can build with our current PartialTrace + Lindblad
  infrastructure — it would require the full Stinespring dilation
  picture, Hamiltonian dynamics, and an asymptotic ergodic argument
  on the system-environment manifold.

  What we CAN, and do, build here is the **structural endpoint** of
  the einselection picture: the **diagonal dephasing channel**
  `D : ComplexDensityMatrix n → ComplexDensityMatrix n` that kills
  every off-diagonal entry, viewed as the limiting / fixed-point form
  of the system's reduced density matrix after the einselection
  process has run to completion.

  The theorems we prove on this channel are exactly the structural
  content of einselection at the level of states (Zurek 2003, eq. 2.4
  and the surrounding discussion):

  (1) `diagonalDephasing` is a well-typed channel on
      `ComplexDensityMatrix n`: it preserves Hermiticity, trace 1, and
      the trace-PSD field. This is the "CPTP at the state level"
      statement for the einselected limit.

  (2) `dephasing_idempotent`: `D(D(ρ)) = D(ρ)`. The einselected limit
      is a true projector — applying it again does nothing. This is
      the absorbing-set property of einselection.

  (3) `dephasing_fixed_points`: `D(ρ) = ρ ↔ ∀ i ≠ j, ρ.M i j = 0`.
      The fixed points of einselection are EXACTLY the diagonal
      density matrices in the preferred basis. This is the
      preferred-basis statement: the einselected set is the diagonal
      manifold.

  (4) `dephasing_kills_offdiagonal`: every off-diagonal entry of `D ρ`
      is zero. The off-diagonal coherences (the witnesses to
      superposition between |i⟩ and |j⟩) are EXACTLY what
      einselection kills.

  (5) `dephasing_preserves_diagonal`: the diagonal entries
      (populations) are preserved. Einselection is a CLASSICAL ↔
      QUANTUM filter — populations survive, coherences die.

  (6) `pointerStates`: the `n` rank-1 diagonal projectors |i⟩⟨i| are
      defined as the einselected pointer basis (via the delta
      distribution on `Fin n`).

  (7) `pointer_states_einselected`: each pointer state is a fixed
      point of `D`. The pointer basis IS the einselected basis.

  (8) `pointer_states_pairwise_distinguishable`: two distinct pointer
      states differ in their diagonal entries. The einselected basis
      is faithfully labelled by classical outcomes.

  (9) `einselection_limit`: bundles the above into a single
      Zurek-style statement: the long-time / strong-coupling limit of
      dephasing converges (in one step) to a diagonal density matrix,
      which is a fixed point of further dephasing.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

  – We model einselection by its **structural endpoint** (the
    diagonal-projection channel) rather than by deriving it from
    coupled S ⊗ E Hamiltonian dynamics. The dynamical derivation is
    a separate research project (Hu-Paz-Zhang master equation,
    spin-bath models, etc.).

  – "Long-time limit" is collapsed to "one application of `D`": for
    the diagonal-projection channel the dynamical fixed point is
    reached in one step (idempotence). Real einselection has an
    exponential approach with timescale `τ_d` set by H_int; that
    timescale is captured in `LindbladDecoherence.decoherenceTime`,
    which dovetails with this file.

  – No system-environment tensor product is constructed here. The
    `PartialTrace.lean` API would let us write
    `ρ_S = Tr_E (U |0⟩⟨0|_S ⊗ ρ_E U†)`, but proving that this
    converges to the diagonal of ρ_S in the preferred basis requires
    spectral / ergodicity analysis we do not formalize.

  – No `sorry`, no custom `axiom`. The structural einselection
    statements (1)–(9) all close at the state level.
-/

import UnifiedTheory.LayerB.RobertsonSchrodinger
import UnifiedTheory.LayerB.DiagonalDensityMatrix
import UnifiedTheory.LayerB.ClassicalEntropy

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.ZurekEinselection

open Matrix Complex
open scoped BigOperators ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalEntropy.ProbabilityVector

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE DIAGONAL DEPHASING CHANNEL
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The diagonal dephasing channel `D : ρ ↦ diag(ρ_{11}, ..., ρ_{nn})`
    is the structural endpoint of einselection: it kills all
    off-diagonal entries and keeps populations. It is the limiting
    form of `dephasingChannel γ` as `γ → 0`, generalised from n=2 to
    arbitrary n.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

variable {n : ℕ}

/-- The raw diagonal-projection matrix: keeps diagonal entries,
    zeros everything off-diagonal. -/
noncomputable def diagProjMatrix (M : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => M i i)

@[simp]
theorem diagProjMatrix_apply_eq (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    diagProjMatrix M i i = M i i := by
  simp [diagProjMatrix, Matrix.diagonal_apply_eq]

theorem diagProjMatrix_apply_ne (M : Matrix (Fin n) (Fin n) ℂ)
    {i j : Fin n} (h : i ≠ j) :
    diagProjMatrix M i j = 0 := by
  simp [diagProjMatrix, Matrix.diagonal_apply_ne _ h]

/-- The raw matrix is Hermitian whenever `M` is: each diagonal entry
    of a Hermitian matrix is real, so the diagonal-projection is the
    diagonal-of-reals matrix, which is its own conjugate transpose. -/
theorem diagProjMatrix_isHermitian
    {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) :
    (diagProjMatrix M).IsHermitian := by
  ext i j
  by_cases hij : i = j
  · subst hij
    -- Diagonal: star (M i i) = M i i because M is Hermitian
    change star ((diagProjMatrix M) i i) = (diagProjMatrix M) i i
    rw [diagProjMatrix_apply_eq]
    have := congrFun (congrFun hM i) i
    -- hM at (i,i): star (M i i) = M i i
    simpa [Matrix.conjTranspose_apply] using this
  · -- Off-diagonal: both sides are 0
    change star ((diagProjMatrix M) j i) = (diagProjMatrix M) i j
    rw [diagProjMatrix_apply_ne M (Ne.symm hij),
        diagProjMatrix_apply_ne M hij, star_zero]

/-- Trace of the diagonal projection equals the trace of the original. -/
theorem diagProjMatrix_trace (M : Matrix (Fin n) (Fin n) ℂ) :
    (diagProjMatrix M).trace = M.trace := by
  rw [Matrix.trace, Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  simp [Matrix.diag_apply, diagProjMatrix_apply_eq]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: TRACE-PSD PRESERVATION

    The diagonal entries of a `ComplexDensityMatrix n` are
    non-negative reals (they are populations: M_{ii} = p_i ≥ 0,
    p_i ∈ ℝ). We show this, then prove the trace-PSD field for the
    diagonal-projection by routing through `DiagonalDensityMatrix`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The diagonal entries of a `ComplexDensityMatrix` are real. -/
theorem diag_im_zero (ρ : ComplexDensityMatrix n) (i : Fin n) :
    (ρ.M i i).im = 0 := by
  -- Hermitian implies diagonal is real
  have h := congrFun (congrFun ρ.hHerm i) i
  -- h : (Mᴴ) i i = M i i, i.e., star (M i i) = M i i
  -- For a complex z, star z = z iff z.im = 0
  have h2 : star (ρ.M i i) = ρ.M i i := by
    simpa [Matrix.conjTranspose_apply] using h
  -- star z = conj z, and conj z = z iff z.im = 0
  have h3 : (starRingEnd ℂ) (ρ.M i i) = ρ.M i i := h2
  -- conj z = z ↔ z = (z.re : ℂ)
  rw [Complex.ext_iff] at h3
  -- h3 : ((conj z).re = z.re ∧ (conj z).im = z.im)
  -- conj.re = z.re, conj.im = -z.im
  simp [Complex.conj_re, Complex.conj_im] at h3
  -- h3 : -z.im = z.im
  linarith [h3]

/-- The diagonal entries of a `ComplexDensityMatrix` have non-negative
    real part. This is the population non-negativity `p_i ≥ 0`.

    Strategy: choose `X` to be the matrix with `X k k = 1` only when
    `k = i` (everything else zero). Then `X† X = X` (since `X` is a
    Hermitian rank-1 diagonal projector), and `Tr(ρ · X† · X) = ρ.M i i`.
    The trace-PSD field of `ρ` then gives `0 ≤ (ρ.M i i).re`. -/
theorem diag_re_nonneg (ρ : ComplexDensityMatrix n) (i : Fin n) :
    0 ≤ (ρ.M i i).re := by
  classical
  -- X = rank-1 diagonal projector onto |i⟩
  let X : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of (fun a b => if a = i ∧ b = i then (1 : ℂ) else 0)
  -- Compute X† = X (X is real and symmetric)
  have hXt : X.conjTranspose = X := by
    ext a b
    change star (X b a) = X a b
    simp only [X, Matrix.of_apply]
    by_cases hab : a = i ∧ b = i
    · rw [if_pos hab, if_pos ⟨hab.2, hab.1⟩, star_one]
    · rw [if_neg hab, if_neg (fun h => hab ⟨h.2, h.1⟩), star_zero]
  -- Compute X · X = X
  have hXX : X * X = X := by
    ext a b
    rw [Matrix.mul_apply]
    -- The product entry: ∑ k, X(a,k) * X(k,b)
    -- = ∑ k, (if a=i ∧ k=i then 1 else 0) * (if k=i ∧ b=i then 1 else 0)
    -- The k-th term is nonzero iff a=i ∧ k=i ∧ b=i, i.e., k=i and (a=i∧b=i).
    show (∑ k, X a k * X k b) = X a b
    have h_term : ∀ k, X a k * X k b
                  = if a = i ∧ k = i ∧ b = i then (1 : ℂ) else 0 := by
      intro k
      simp only [X, Matrix.of_apply]
      by_cases hak : a = i ∧ k = i
      · by_cases hkb : k = i ∧ b = i
        · rw [if_pos hak, if_pos hkb, mul_one, if_pos ⟨hak.1, hak.2, hkb.2⟩]
        · rw [if_pos hak, if_neg hkb, mul_zero, if_neg]
          intro habkb; exact hkb ⟨habkb.2.1, habkb.2.2⟩
      · rw [if_neg hak, zero_mul, if_neg]
        intro habkb; exact hak ⟨habkb.1, habkb.2.1⟩
    simp_rw [h_term]
    -- Now sum the indicator: ∑ k, (if a=i ∧ k=i ∧ b=i then 1 else 0)
    by_cases hab : a = i ∧ b = i
    · -- Only k = i contributes
      rw [Finset.sum_eq_single i]
      · rw [if_pos ⟨hab.1, rfl, hab.2⟩]
        simp only [X, Matrix.of_apply, if_pos hab]
      · intro k _ hk
        rw [if_neg]
        intro h; exact hk h.2.1
      · intro h; exact absurd (Finset.mem_univ _) h
    · -- No term contributes
      have h_zero : ∀ k ∈ (Finset.univ : Finset (Fin n)),
                  (if a = i ∧ k = i ∧ b = i then (1 : ℂ) else 0) = 0 := by
        intro k _
        rw [if_neg]
        intro h; exact hab ⟨h.1, h.2.2⟩
      rw [Finset.sum_congr rfl h_zero, Finset.sum_const_zero]
      simp only [X, Matrix.of_apply, if_neg hab]
  -- Now X† · X = X · X = X (from hXt and hXX)
  have hXtX : X.conjTranspose * X = X := by rw [hXt, hXX]
  -- Tr(ρ · X) = ρ.M i i
  have h_tr_rhoX : Matrix.trace (ρ.M * X) = ρ.M i i := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply]
    -- The diagonal: (ρ.M * X) a a = ∑ k, ρ.M a k * X k a
    -- X k a = if k = i ∧ a = i then 1 else 0, nonzero only when k = i ∧ a = i
    have h_per : ∀ a, (ρ.M * X) a a = if a = i then ρ.M a i else 0 := by
      intro a
      rw [Matrix.mul_apply]
      simp only [X, Matrix.of_apply]
      by_cases ha : a = i
      · rw [if_pos ha]
        rw [Finset.sum_eq_single i]
        · rw [if_pos ⟨rfl, ha⟩, mul_one]
        · intro k _ hk
          rw [if_neg, mul_zero]
          intro h; exact hk h.1
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [if_neg ha]
        apply Finset.sum_eq_zero
        intro k _
        rw [if_neg, mul_zero]
        intro h; exact ha h.2
    -- Now sum: ∑ a, (if a = i then ρ.M a i else 0) = ρ.M i i
    have h_per_i : ∀ a, (ρ.M * X) a a = if a = i then ρ.M i i else 0 := by
      intro a
      rw [h_per a]
      by_cases ha : a = i
      · rw [if_pos ha, if_pos ha, ha]
      · rw [if_neg ha, if_neg ha]
    simp_rw [h_per_i]
    rw [Finset.sum_ite_eq' Finset.univ i (fun _ => ρ.M i i)]
    simp
  -- Tr(ρ · X† · X) = Tr(ρ · X) = ρ.M i i
  have h_tr : Matrix.trace (ρ.M * X.conjTranspose * X) = ρ.M i i := by
    rw [Matrix.mul_assoc, hXtX, h_tr_rhoX]
  -- Apply the trace-PSD field
  have h_psd := ρ.hTracePSD X
  rw [h_tr] at h_psd
  exact h_psd

/-! Build the diagonal-as-`ProbabilityVector`. -/

/-- The diagonal (real parts) of a `ComplexDensityMatrix` form a
    probability vector on `Fin n`. -/
noncomputable def diagProbVec (ρ : ComplexDensityMatrix n) :
    ProbabilityVector (Fin n) where
  p i := (ρ.M i i).re
  nonneg i := diag_re_nonneg ρ i
  sum_one := by
    -- ∑ (ρ.M i i).re = (∑ ρ.M i i).re = trace.re = 1.re = 1
    rw [← Complex.re_sum]
    have h_tr : ∑ i, ρ.M i i = ρ.M.trace := by
      rw [Matrix.trace]
      simp [Matrix.diag_apply]
    rw [h_tr, ρ.hTrace, Complex.one_re]

/-- The diagonal-projection matrix equals the matrix of the
    `diagonalDensityMatrix` built from `diagProbVec`. The two
    constructions of "the diagonal density matrix from the
    populations of ρ" agree. -/
theorem diagProjMatrix_eq_diagonalDensityMatrix (ρ : ComplexDensityMatrix n) :
    diagProjMatrix ρ.M
      = (UnifiedTheory.LayerB.DiagonalDensityMatrix.diagonalDensityMatrix
          (diagProbVec ρ)).M := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [diagProjMatrix_apply_eq]
    rw [UnifiedTheory.LayerB.DiagonalDensityMatrix.diagonalDensityMatrix_apply_eq]
    -- LHS: ρ.M i i (a ℂ), RHS: ((diagProbVec ρ).p i : ℂ) = ((ρ.M i i).re : ℂ)
    -- These are equal iff (ρ.M i i).im = 0, which is diag_im_zero
    apply Complex.ext
    · simp [diagProbVec]
    · simp [diagProbVec, diag_im_zero ρ i]
  · rw [diagProjMatrix_apply_ne _ hij,
        UnifiedTheory.LayerB.DiagonalDensityMatrix.diagonalDensityMatrix_apply_ne
          _ hij]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: THE EINSELECTION CHANNEL `diagonalDephasing`
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The diagonal dephasing channel** `D : ρ ↦ diag(ρ_{11}, ..., ρ_{nn})`.

    This is the structural endpoint of einselection: a CPTP map whose
    action on a density matrix replaces it with the diagonal density
    matrix carrying the same populations. Off-diagonal coherences are
    erased entirely. -/
noncomputable def diagonalDephasing (n : ℕ) (ρ : ComplexDensityMatrix n) :
    ComplexDensityMatrix n :=
  UnifiedTheory.LayerB.DiagonalDensityMatrix.diagonalDensityMatrix
    (diagProbVec ρ)

/-- The underlying matrix of `diagonalDephasing` agrees with the raw
    diagonal-projection matrix. -/
theorem diagonalDephasing_M (ρ : ComplexDensityMatrix n) :
    (diagonalDephasing n ρ).M = diagProjMatrix ρ.M := by
  unfold diagonalDephasing
  rw [← diagProjMatrix_eq_diagonalDensityMatrix]

/-- Diagonal entries (populations) are preserved. -/
theorem diagonalDephasing_diag (ρ : ComplexDensityMatrix n) (i : Fin n) :
    (diagonalDephasing n ρ).M i i = ((ρ.M i i).re : ℂ) := by
  unfold diagonalDephasing
  rw [UnifiedTheory.LayerB.DiagonalDensityMatrix.diagonalDensityMatrix_apply_eq]
  rfl

/-- Off-diagonal entries (coherences) are zero. -/
theorem diagonalDephasing_offdiag (ρ : ComplexDensityMatrix n)
    {i j : Fin n} (h : i ≠ j) :
    (diagonalDephasing n ρ).M i j = 0 := by
  unfold diagonalDephasing
  exact UnifiedTheory.LayerB.DiagonalDensityMatrix.diagonalDensityMatrix_apply_ne
    _ h

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: IDEMPOTENCE (`D ∘ D = D`)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The diagonal-of-diagonal equals the diagonal: `D ∘ D = D` at the
    matrix level. -/
theorem diagProjMatrix_idempotent (M : Matrix (Fin n) (Fin n) ℂ) :
    diagProjMatrix (diagProjMatrix M) = diagProjMatrix M := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [diagProjMatrix_apply_eq, diagProjMatrix_apply_eq]
  · rw [diagProjMatrix_apply_ne _ hij, diagProjMatrix_apply_ne _ hij]

/-- **EINSELECTION IS A TRUE PROJECTOR**: applying the channel twice
    is the same as applying it once. The set of einselected states is
    therefore absorbing: once you're diagonal, you stay diagonal under
    further einselection. -/
theorem dephasing_idempotent (ρ : ComplexDensityMatrix n) :
    (diagonalDephasing n (diagonalDephasing n ρ)).M
      = (diagonalDephasing n ρ).M := by
  rw [diagonalDephasing_M, diagonalDephasing_M, diagProjMatrix_idempotent]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: FIXED-POINT CHARACTERISATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The Zurek einselection theorem at the level of states: the fixed
    points of `D` are EXACTLY the diagonal density matrices in the
    preferred basis. This is the preferred-basis characterisation of
    einselection.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **EINSELECTION FIXED-POINT CHARACTERISATION (Zurek)**: the fixed
    points of the diagonal-dephasing channel are exactly the diagonal
    density matrices. A state ρ is einselected iff every off-diagonal
    entry vanishes. -/
theorem dephasing_fixed_points (ρ : ComplexDensityMatrix n) :
    (diagonalDephasing n ρ).M = ρ.M ↔ ∀ i j, i ≠ j → ρ.M i j = 0 := by
  constructor
  · -- If D ρ = ρ then every off-diagonal entry is zero
    intro hfix i j hij
    -- (D ρ).M i j = 0 by diagonalDephasing_offdiag
    -- (D ρ).M i j = ρ.M i j by hfix
    have h1 : (diagonalDephasing n ρ).M i j = 0 :=
      diagonalDephasing_offdiag ρ hij
    rw [hfix] at h1
    exact h1
  · -- If every off-diagonal is zero, then D ρ = ρ
    intro hdiag
    ext i j
    by_cases hij : i = j
    · -- Diagonal: need (D ρ).M i i = ρ.M i i, i.e., ((ρ.M i i).re : ℂ) = ρ.M i i
      subst hij
      rw [diagonalDephasing_diag]
      -- Need ((ρ.M i i).re : ℂ) = ρ.M i i, i.e., im = 0
      apply Complex.ext
      · simp
      · simp [diag_im_zero ρ i]
    · -- Off-diagonal: both sides 0
      rw [diagonalDephasing_offdiag ρ hij, hdiag i j hij]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: POINTER STATES — THE EINSELECTED BASIS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The pointer states are the n rank-1 diagonal projectors |i⟩⟨i|.
    Each is a fixed point of `D`, and the set is the einselected
    basis predicted by Zurek 1981.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The `i`-th **pointer state**: the rank-1 diagonal density matrix
    with a single 1 at position `(i, i)`. Built from the delta
    distribution on `Fin n`. Requires `n > 0`. -/
noncomputable def pointerStates (n : ℕ) [NeZero n] (i : Fin n) :
    ComplexDensityMatrix n :=
  UnifiedTheory.LayerB.DiagonalDensityMatrix.diagonalDensityMatrix
    (delta (Fin n) i)

/-- The diagonal entries of `pointerStates i`: 1 at `i`, 0 elsewhere. -/
theorem pointerStates_diag {n : ℕ} [NeZero n] (i j : Fin n) :
    (pointerStates n i).M j j = (if j = i then 1 else 0 : ℂ) := by
  unfold pointerStates
  rw [UnifiedTheory.LayerB.DiagonalDensityMatrix.diagonalDensityMatrix_apply_eq]
  -- (delta (Fin n) i).p j = if j = i then 1 else 0 : ℝ; cast to ℂ
  show (((delta (Fin n) i).p j : ℝ) : ℂ) = (if j = i then 1 else 0 : ℂ)
  by_cases h : j = i
  · rw [if_pos h]
    show ((delta (Fin n) i).p j : ℂ) = 1
    have : (delta (Fin n) i).p j = 1 := by
      unfold delta; simp [h]
    rw [this]; simp
  · rw [if_neg h]
    show ((delta (Fin n) i).p j : ℂ) = 0
    have : (delta (Fin n) i).p j = 0 := by
      unfold delta; simp [h]
    rw [this]; simp

/-- The off-diagonal entries of `pointerStates i` are zero. -/
theorem pointerStates_offdiag {n : ℕ} [NeZero n] (i : Fin n)
    {j k : Fin n} (h : j ≠ k) :
    (pointerStates n i).M j k = 0 :=
  UnifiedTheory.LayerB.DiagonalDensityMatrix.diagonalDensityMatrix_apply_ne
    _ h

/-- **POINTER STATES ARE EINSELECTED**: each pointer state is a fixed
    point of the diagonal-dephasing channel. The pointer basis IS the
    einselected preferred basis. -/
theorem pointer_states_einselected {n : ℕ} [NeZero n] (i : Fin n) :
    (diagonalDephasing n (pointerStates n i)).M = (pointerStates n i).M := by
  rw [dephasing_fixed_points]
  intro j k hjk
  exact pointerStates_offdiag i hjk

/-- **POINTER STATES ARE DISTINGUISHABLE**: two distinct pointer
    states differ in their diagonal entries (and so are not the same
    density matrix). Combined with `pointer_states_einselected`, this
    gives an einselected basis of `n` classically-labelled outcomes,
    one per element of `Fin n`. -/
theorem pointer_states_pairwise_distinguishable
    {n : ℕ} [NeZero n] {i j : Fin n} (h : i ≠ j) :
    (pointerStates n i).M ≠ (pointerStates n j).M := by
  intro h_eq
  -- Look at the (i, i) entry: pointerStates n i has it = 1, pointerStates n j has it = 0
  have h1 : (pointerStates n i).M i i = 1 := by
    rw [pointerStates_diag]; simp
  have h2 : (pointerStates n j).M i i = 0 := by
    rw [pointerStates_diag]
    rw [if_neg (fun heq => h heq)]
  rw [h_eq] at h1
  rw [h2] at h1
  exact absurd h1 (by norm_num)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: PRESERVATION OF DIAGONAL ENTRIES (POPULATIONS)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **POPULATIONS SURVIVE**: the diagonal entries (populations) of ρ
    are preserved (in real part) by einselection. The im-part is
    pinned to 0 by Hermiticity, so the diagonal is literally
    preserved as a real number. -/
theorem dephasing_preserves_diagonal (ρ : ComplexDensityMatrix n) (i : Fin n) :
    (diagonalDephasing n ρ).M i i = ρ.M i i := by
  rw [diagonalDephasing_diag]
  apply Complex.ext
  · simp
  · simp [diag_im_zero ρ i]

/-- **COHERENCES DIE**: every off-diagonal entry of `D ρ` is zero.
    Einselection erases all superposition witnesses between distinct
    pointer-basis states. -/
theorem dephasing_kills_offdiagonal (ρ : ComplexDensityMatrix n)
    {i j : Fin n} (h : i ≠ j) :
    (diagonalDephasing n ρ).M i j = 0 :=
  diagonalDephasing_offdiag ρ h

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: THE EINSELECTION LIMIT BUNDLE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **ZUREK EINSELECTION (structural form)**: in the long-time /
    strong-coupling limit modelled by the diagonal-dephasing channel,
    every state of the system converges (in one step) to a diagonal
    density matrix, which is then a fixed point of further dephasing.

    Concretely:
      (1) `(D ρ).M i j = 0` for `i ≠ j` — off-diagonal coherences die.
      (2) `(D ρ).M i i = ρ.M i i` — populations are preserved.
      (3) `D (D ρ) = D ρ` — the limit is a true projector
          (idempotent).
      (4) `D ρ = ρ` iff ρ is already diagonal — the fixed points of
          einselection are exactly the einselected (diagonal)
          density matrices. -/
theorem einselection_limit (ρ : ComplexDensityMatrix n) :
    -- (1) Off-diagonal coherences die
    (∀ i j : Fin n, i ≠ j → (diagonalDephasing n ρ).M i j = 0)
    -- (2) Populations preserved
    ∧ (∀ i : Fin n, (diagonalDephasing n ρ).M i i = ρ.M i i)
    -- (3) The limit is idempotent
    ∧ (diagonalDephasing n (diagonalDephasing n ρ)).M
        = (diagonalDephasing n ρ).M
    -- (4) Fixed point ↔ already diagonal
    ∧ ((diagonalDephasing n ρ).M = ρ.M ↔ ∀ i j, i ≠ j → ρ.M i j = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij; exact diagonalDephasing_offdiag ρ hij
  · intro i; exact dephasing_preserves_diagonal ρ i
  · exact dephasing_idempotent ρ
  · exact dephasing_fixed_points ρ

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: MASTER BUNDLE — EINSELECTION + POINTER BASIS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER THEOREM (ZUREK EINSELECTION, STRUCTURAL FORM).**

    Bundles the einselection picture at the level of states (Zurek
    1981, 2003):

    (A) `diagonalDephasing` is a well-typed channel on
        `ComplexDensityMatrix n` — Hermiticity, trace 1, and PSD
        (via the trace-PSD field) are preserved.

    (B) The channel is **idempotent**: einselection is a true
        projector.

    (C) The **fixed points** of einselection are exactly the diagonal
        density matrices (the einselected / preferred basis).

    (D) The `n` **pointer states** |i⟩⟨i| are each fixed points of
        einselection, and they are pairwise distinguishable (form a
        genuine n-element basis of classical outcomes).

    (E) **Populations survive** and **coherences die** — the
        signature behaviour of decoherence in the preferred basis. -/
theorem einselection_master :
    -- (A) The channel is well-typed (proved by construction in
    --     `diagonalDephasing`; we re-export trace and Hermiticity).
    (∀ {n : ℕ} (ρ : ComplexDensityMatrix n),
        (diagonalDephasing n ρ).M.IsHermitian)
    ∧ (∀ {n : ℕ} (ρ : ComplexDensityMatrix n),
        (diagonalDephasing n ρ).M.trace = 1)
    -- (B) Idempotence
    ∧ (∀ {n : ℕ} (ρ : ComplexDensityMatrix n),
        (diagonalDephasing n (diagonalDephasing n ρ)).M
          = (diagonalDephasing n ρ).M)
    -- (C) Fixed-point characterisation
    ∧ (∀ {n : ℕ} (ρ : ComplexDensityMatrix n),
        (diagonalDephasing n ρ).M = ρ.M ↔ ∀ i j, i ≠ j → ρ.M i j = 0)
    -- (D) Pointer states are einselected and pairwise distinguishable
    ∧ (∀ {n : ℕ} [NeZero n] (i : Fin n),
        (diagonalDephasing n (pointerStates n i)).M = (pointerStates n i).M)
    ∧ (∀ {n : ℕ} [NeZero n] {i j : Fin n}, i ≠ j →
        (pointerStates n i).M ≠ (pointerStates n j).M)
    -- (E) Populations survive, coherences die
    ∧ (∀ {n : ℕ} (ρ : ComplexDensityMatrix n) (i : Fin n),
        (diagonalDephasing n ρ).M i i = ρ.M i i)
    ∧ (∀ {n : ℕ} (ρ : ComplexDensityMatrix n) {i j : Fin n}, i ≠ j →
        (diagonalDephasing n ρ).M i j = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n ρ; exact (diagonalDephasing n ρ).hHerm
  · intro n ρ; exact (diagonalDephasing n ρ).hTrace
  · intro n ρ; exact dephasing_idempotent ρ
  · intro n ρ; exact dephasing_fixed_points ρ
  · intro n _ i; exact pointer_states_einselected i
  · intro n _ i j h; exact pointer_states_pairwise_distinguishable h
  · intro n ρ i; exact dephasing_preserves_diagonal ρ i
  · intro n ρ i j h; exact dephasing_kills_offdiagonal ρ h

end UnifiedTheory.LayerB.ZurekEinselection
