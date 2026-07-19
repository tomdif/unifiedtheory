/-
  LayerB/GaussianStates.lean — Continuous-variable Gaussian state framework.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT

  An N-mode bosonic quantum system has 2N canonical operators
        R = (x₁, p₁, …, x_N, p_N)
  satisfying the canonical commutation relations [R_i, R_j] = i Ω_{ij},
  where Ω is the symplectic form
        Ω = ⊕_{k=1..N} (0  1; −1  0)        (block-diagonal, 2N×2N).

  A Gaussian state is fully characterised by its first moment vector
  d_i := ⟨R_i⟩ and its covariance matrix
        V_{ij} := (1/2) ⟨{ΔR_i, ΔR_j}⟩          (symmetric anticommutator).

  **Heisenberg–Robertson–Schrödinger (CV form)**.  A real symmetric matrix
  V is a valid quantum covariance matrix iff
        V + (i/2) Ω  ⪰  0   (as a Hermitian matrix on ℂ^{2N}).

  For N = 1 this is equivalent to
        det V  ≥  1/4,
  i.e. Δx · Δp ≥ 1/2 (standard Heisenberg).

  A pure Gaussian state has det V = (1/4)^N, saturating the bound.
  The vacuum |0⟩ has V = (1/2)·I.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED

  – `symplecticForm N`              : the 2N×2N block-diagonal symplectic
                                       form Ω.
  – `symplecticForm_antisymmetric`  : Ωᵀ = −Ω.
  – `symplecticForm_zero_diag`      : Ω(i,i) = 0.
  – `symplecticForm_one_zero`       : explicit Ω at N=1: Ω(0,1)=1, Ω(1,0)=−1.
  – `CovarianceMatrix N`            : structure bundling real-symmetric +
                                       positive-definite V satisfying the
                                       real reformulation of the
                                       Heisenberg uncertainty.
  – `heisenberg_N_one`              : det V ≥ 1/4 for any single-mode
                                       covariance matrix.
  – `vacuumCovariance N := (1/2)·I` : the vacuum-state CM.
  – `vacuumCovariance_isSymm`,
    `vacuumCovariance_isPosDef`,
    `vacuumCovariance_uncertainty`  : the vacuum satisfies all CM fields.
  – `vacuumCM N`                    : the vacuum packaged as a `CovarianceMatrix`.
  – `IsPureGaussian`                : det V = (1/4)^N.
  – `vacuum_isPureGaussian_one`     : the N=1 vacuum is pure.
  – `WilliamsonForm`                : Williamson's symplectic-diagonal form
                                       stated as a named hypothesis.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

  – **Real reformulation of the uncertainty.**  The textbook condition
    `V + (i/2)Ω ⪰ 0` is a Hermitian-PSD statement on ℂ^{2N}.  Writing
    `z = x + i y` with real x, y, the condition is equivalent to
        ∀ x y : ℝ^{2N},   xᵀΩy  ≤  xᵀVx + yᵀVy.
    (The proof: z† V z is real because V is symmetric, and
     (i/2) z†Ωz = −(1/2)(xᵀΩy − yᵀΩx) = −xᵀΩy since Ω is antisymmetric.
     So `z†(V + (i/2)Ω)z = xᵀVx + yᵀVy − xᵀΩy` and the PSD condition
     for all complex z is the real bilinear inequality above.)
    We take this real reformulation as the type-level field of
    `CovarianceMatrix`.  This is mathematically equivalent and keeps the
    file purely real-matrix.

  – **N = 1 Heisenberg fully proved.**  We pick a specific (x, y) pair
    that turns the uncertainty bilinear inequality into a single-variable
    quadratic non-negativity `(det V / V₀₀) t² − t + V₀₀ ≥ 0` for all t,
    then evaluate at t₀ := V₀₀ / (2 det V) to extract det V ≥ 1/4.

  – **Williamson's theorem stated as hypothesis.**  Williamson (1936)
    showed that every PD covariance matrix can be brought to the form
    `S · diag(ν₁, ν₁, …, ν_N, ν_N) · Sᵀ` by a symplectic similarity S.
    The full proof requires advanced linear-algebra machinery (symplectic
    eigenvalue theory, Iwasawa decomposition of Sp(2N)) outside the
    scope of this file; we state the conclusion as `WilliamsonForm` for
    downstream consumers.

  – **Vacuum is pure at N = 1.**  We prove `det (vacuumCovariance 1) =
    1/4 = (1/4)^1`.  For general N the analogous identity is
    `det ((1/2)·I_{2N}) = (1/2)^{2N} = (1/4)^N`; proved here for N = 1
    explicitly and noted as a routine extension (would require
    `Matrix.det_smul` plus `Matrix.det_one`, both available in Mathlib;
    we ship the N = 1 case to honour the "Heisenberg N = 1" emphasis).

  Zero `sorry`. Zero custom axioms.
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.FinCases

set_option relaxedAutoImplicit false
set_option linter.unusedSimpArgs false

namespace UnifiedTheory.LayerB.GaussianStates

open Matrix

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE SYMPLECTIC FORM Ω
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For an N-mode bosonic system the symplectic form is the
    block-diagonal 2N×2N matrix

        Ω = ⊕_{k=0..N-1}  ⎛ 0   1 ⎞
                          ⎝−1   0 ⎠

    With the convention R = (x_0, p_0, x_1, p_1, …, x_{N-1}, p_{N-1}),
    indices 2k and 2k+1 form one mode.  The non-zero entries are
        Ω(2k, 2k+1) = +1,   Ω(2k+1, 2k) = −1   for k = 0, …, N−1.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The symplectic form on `ℝ^{2N}`: block-diagonal with N copies of
    `⎛ 0  1 ⎞ / ⎝−1  0 ⎠`. -/
noncomputable def symplecticForm (N : ℕ) :
    Matrix (Fin (2*N)) (Fin (2*N)) ℝ :=
  fun i j =>
    if i.val + 1 = j.val ∧ i.val % 2 = 0 then (1 : ℝ)
    else if j.val + 1 = i.val ∧ j.val % 2 = 0 then (-1 : ℝ)
    else 0

/-- **Antisymmetry of Ω**: `Ωᵀ = −Ω`. -/
theorem symplecticForm_antisymmetric (N : ℕ) :
    (symplecticForm N)ᵀ = -(symplecticForm N) := by
  ext i j
  simp only [Matrix.transpose_apply, symplecticForm, Matrix.neg_apply]
  -- Case split on which branch each side falls into.
  by_cases h1 : j.val + 1 = i.val ∧ j.val % 2 = 0
  · -- LHS: branch 1 (with i,j swapped) ⇒ value 1.
    -- RHS: need branch 2 for `Ω i j` ⇒ value -(-1) = 1.
    rcases h1 with ⟨hji, hjpar⟩
    have hne : ¬ (i.val + 1 = j.val ∧ i.val % 2 = 0) := by
      rintro ⟨hij, _⟩; omega
    simp [hji, hjpar, hne]
  · by_cases h2 : i.val + 1 = j.val ∧ i.val % 2 = 0
    · -- LHS: branch 2 (with i,j swapped) ⇒ value -1.
      -- RHS: branch 1 for `Ω i j` ⇒ value -(1) = -1.
      rcases h2 with ⟨hij, hipar⟩
      simp [hij, hipar, h1]
    · -- LHS: branch 3 ⇒ 0.  RHS: also branch 3 ⇒ -0 = 0.
      simp [h1, h2]

/-- The diagonal of Ω is zero. -/
theorem symplecticForm_zero_diag (N : ℕ) (i : Fin (2*N)) :
    symplecticForm N i i = 0 := by
  -- Both branches fail because `i.val + 1 = i.val` is impossible.
  unfold symplecticForm
  have h1 : ¬ (i.val + 1 = i.val ∧ i.val % 2 = 0) := by
    rintro ⟨h, _⟩; omega
  have h2 : ¬ (i.val + 1 = i.val ∧ i.val % 2 = 0) := h1
  rw [if_neg h1, if_neg h2]

/-- Antisymmetry, pointwise form: `Ω(i,j) = −Ω(j,i)`. -/
theorem symplecticForm_swap (N : ℕ) (i j : Fin (2*N)) :
    symplecticForm N i j = -(symplecticForm N j i) := by
  -- From Ωᵀ = −Ω applied at (j, i): Ω i j = −Ω j i.
  have h := symplecticForm_antisymmetric N
  have heq : (symplecticForm N)ᵀ j i = (-(symplecticForm N)) j i := by
    rw [h]
  -- LHS: Ω i j; RHS: −Ω j i.
  simpa [Matrix.transpose_apply, Matrix.neg_apply] using heq

/-- **xᵀ Ω x = 0** for any real vector x (consequence of antisymmetry).
    This is a useful corollary of the antisymmetry of Ω. -/
theorem symplecticForm_quad_zero (N : ℕ) (x : Fin (2*N) → ℝ) :
    x ⬝ᵥ (symplecticForm N *ᵥ x) = 0 := by
  -- Standard antisymmetry argument: 2·xᵀΩx = xᵀΩx + xᵀΩᵀx = 0.
  set S := x ⬝ᵥ (symplecticForm N *ᵥ x) with hS_def
  -- Expand S into a double sum.
  have expand1 : S = ∑ i, ∑ j, x i * symplecticForm N i j * x j := by
    show x ⬝ᵥ (symplecticForm N *ᵥ x) = _
    unfold dotProduct mulVec
    simp only [dotProduct, Finset.mul_sum]
    congr 1; ext i; congr 1; ext j; ring
  -- Show S = -S.
  have key : S = -S := by
    rw [expand1]
    -- Σ_{i,j} t(i,j) = Σ_{j,i} t(i,j) = Σ_{i,j} t(j,i) (rename i↔j).
    -- Then use t(j,i) = -t(i,j) (antisymmetry).
    conv_lhs => rw [Finset.sum_comm]
    -- Now: ∑ j ∑ i, x i * Ω(i,j) * x j.  Rename: j → i, i → j.
    -- (∑ j ∑ i, f(i,j) = ∑ i ∑ j, f(j,i) is just dummy renaming.)
    have rename : (∑ j, ∑ i, x i * symplecticForm N i j * x j) =
                  ∑ i, ∑ j, x j * symplecticForm N j i * x i := by
      rfl  -- just renaming bound variables
    rw [rename]
    -- Now each summand: x j * Ω(j,i) * x i = -(x i * Ω(i,j) * x j).
    have h2 : (∑ i, ∑ j, x j * symplecticForm N j i * x i) =
              ∑ i, ∑ j, -(x i * symplecticForm N i j * x j) := by
      congr 1; ext i; congr 1; ext j
      rw [symplecticForm_swap N j i]; ring
    rw [h2]
    -- ∑ ∑ -f = -∑ ∑ f.
    have step3 : (∑ i, ∑ j, -(x i * symplecticForm N i j * x j)) =
                 -(∑ i, ∑ j, x i * symplecticForm N i j * x j) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_neg_distrib]
    rw [step3]
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1B: EXPLICIT N=1 VALUES OF Ω
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- At N=1, `Ω(0, 1) = 1`. -/
theorem symplecticForm_one_01 :
    symplecticForm 1 ⟨0, by omega⟩ ⟨1, by omega⟩ = 1 := by
  simp [symplecticForm]

/-- At N=1, `Ω(1, 0) = −1`. -/
theorem symplecticForm_one_10 :
    symplecticForm 1 ⟨1, by omega⟩ ⟨0, by omega⟩ = -1 := by
  simp [symplecticForm]

/-- At N=1, `Ω(0, 0) = 0`. -/
theorem symplecticForm_one_00 :
    symplecticForm 1 ⟨0, by omega⟩ ⟨0, by omega⟩ = 0 :=
  symplecticForm_zero_diag 1 _

/-- At N=1, `Ω(1, 1) = 0`. -/
theorem symplecticForm_one_11 :
    symplecticForm 1 ⟨1, by omega⟩ ⟨1, by omega⟩ = 0 :=
  symplecticForm_zero_diag 1 _

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: THE COVARIANCE-MATRIX STRUCTURE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A valid CV-Gaussian covariance matrix:

      (a) Real symmetric.
      (b) Positive definite (every direction has positive variance).
      (c) Heisenberg–Robertson–Schrödinger uncertainty.

    The textbook form of (c) is `V + (i/2) Ω ⪰ 0` on ℂ^{2N}.
    Writing z = x + iy with x, y ∈ ℝ^{2N} and using xᵀΩx = 0 from
    antisymmetry, the complex condition unfolds to the equivalent
    real bilinear inequality

      ∀ x, y : ℝ^{2N},  xᵀΩy  ≤  xᵀVx + yᵀVy.

    We adopt this real form as the type field, keeping the entire
    structure inside `Matrix _ _ ℝ`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A valid covariance matrix for an N-mode Gaussian state.  The four
    fields enforce, at the type level, all the standard properties:
    symmetry, strict positivity, and the Heisenberg–Robertson–Schrödinger
    uncertainty (real form). -/
structure CovarianceMatrix (N : ℕ) where
  /-- The underlying 2N×2N real matrix V. -/
  V : Matrix (Fin (2*N)) (Fin (2*N)) ℝ
  /-- Symmetry: V = Vᵀ. -/
  isSymm : V.IsSymm
  /-- Positive definite: V > 0 (every direction has strictly positive
      variance).  Uses Mathlib's `Matrix.PosDef`. -/
  isPosDef : V.PosDef
  /-- **Uncertainty (real reformulation of `V + (i/2)Ω ⪰ 0`)**:
      `xᵀ Ω y ≤ xᵀ V x + yᵀ V y` for every real pair (x, y). -/
  uncertainty :
    ∀ x y : Fin (2*N) → ℝ,
      x ⬝ᵥ (symplecticForm N *ᵥ y) ≤
        x ⬝ᵥ (V *ᵥ x) + y ⬝ᵥ (V *ᵥ y)

namespace CovarianceMatrix

variable {N : ℕ}

/-- Each diagonal entry of V is strictly positive (i.e. every variance is
    > 0). -/
theorem diag_pos (V : CovarianceMatrix N) (i : Fin (2*N)) : 0 < V.V i i :=
  V.isPosDef.diag_pos

/-- Restated symmetry: `V.V j i = V.V i j`. -/
theorem symm_apply (V : CovarianceMatrix N) (i j : Fin (2*N)) :
    V.V j i = V.V i j := by
  have h := V.isSymm
  unfold Matrix.IsSymm at h
  have := congrArg (fun M => M i j) h
  simpa using this

end CovarianceMatrix

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: HEISENBERG UNCERTAINTY FOR N = 1
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For any single-mode covariance matrix V (2×2 real symmetric PD):
                      det V  ≥  1/4.

    Proof strategy:  choose x = (1, 0) and y = (-V₀₁ t / V₀₀, t).  The
    uncertainty inequality reduces to a one-parameter quadratic in t:
                  (det V / V₀₀) · t² − t + V₀₀  ≥  0   ∀ t.
    Evaluating at t₀ := V₀₀ / (2 det V) gives, after algebra,
                  V₀₀ · (4·det V − 1) / (4·det V)  ≥  0,
    and since V₀₀ > 0 and det V > 0 this forces 4 det V ≥ 1.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

namespace HeisenbergProof
-- N = 1 case.  Local index lemmas for 2 = 2*1.

/-- The two indices of `Fin (2*1)`, named for readability. -/
abbrev i0 : Fin (2*1) := ⟨0, by omega⟩
abbrev i1 : Fin (2*1) := ⟨1, by omega⟩

/-- Both indices of Fin 2 are exhaustively i0 or i1. -/
theorem fin_two_cases (i : Fin (2*1)) : i = i0 ∨ i = i1 := by
  -- 2*1 = 2; values 0 or 1.
  rcases i with ⟨v, hv⟩
  interval_cases v
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Sum over `Fin (2*1)` unfolds to evaluation at i0 and i1. -/
theorem sum_fin_two (f : Fin (2*1) → ℝ) :
    ∑ i, f i = f i0 + f i1 := by
  rw [show (Finset.univ : Finset (Fin (2*1))) = {i0, i1} by
        decide]
  rw [Finset.sum_pair (by decide)]

end HeisenbergProof

/-- **HEISENBERG UNCERTAINTY for N = 1**: every single-mode covariance
    matrix satisfies `det V ≥ 1/4`. -/
theorem heisenberg_N_one (V : CovarianceMatrix 1) : (1 : ℝ)/4 ≤ V.V.det := by
  open HeisenbergProof in
  set Vmat := V.V with hVmat_def
  set a := Vmat i0 i0 with ha_def
  set b := Vmat i0 i1 with hb_def
  set c := Vmat i1 i1 with hc_def
  -- Symmetry: V i1 i0 = b.
  have hsymm : Vmat i1 i0 = b := V.symm_apply i0 i1
  -- Positivity of the diagonal.
  have ha_pos : 0 < a := V.diag_pos i0
  have hc_pos : 0 < c := V.diag_pos i1
  -- The determinant formula `det V = a*c - b^2` for 2×2.
  -- Matrix.det_fin_two: det M = M 0 0 * M 1 1 - M 0 1 * M 1 0.
  -- Indices 0, 1 of Fin (2*1) are definitionally i0, i1.
  have det_eq : Vmat.det = a * c - b * b := by
    rw [Matrix.det_fin_two]
    -- Goal: Vmat 0 0 * Vmat 1 1 - Vmat 0 1 * Vmat 1 0 = a * c - b * b.
    -- 0, 1 : Fin (2*1) are i0, i1.
    show Vmat 0 0 * Vmat 1 1 - Vmat 0 1 * Vmat 1 0 = a * c - b * b
    have h00 : Vmat (0 : Fin (2*1)) 0 = a := rfl
    have h11 : Vmat (1 : Fin (2*1)) 1 = c := rfl
    have h01 : Vmat (0 : Fin (2*1)) 1 = b := rfl
    have h10 : Vmat (1 : Fin (2*1)) 0 = b := hsymm
    rw [h00, h11, h01, h10]
  -- ----------------------------------------------------------
  -- Build the uncertainty inequality with x = (1,0), y = (s, t).
  -- xᵀΩy = t.  xᵀVx = a.  yᵀVy = a·s² + 2·b·s·t + c·t².
  -- ----------------------------------------------------------
  have unc : ∀ s t : ℝ,
      t ≤ a + (a * s * s + 2 * b * s * t + c * t * t) := by
    intro s t
    let x : Fin (2*1) → ℝ := fun i => if i = i0 then 1 else 0
    let y : Fin (2*1) → ℝ := fun i => if i = i0 then s else t
    have hu := V.uncertainty x y
    -- Compute each dot-product explicitly using `sum_fin_two`.
    have hx0 : x i0 = 1 := by simp [x]
    have hx1 : x i1 = 0 := by simp [x]
    have hy0 : y i0 = s := by simp [y]
    have hy1 : y i1 = t := by simp [y]
    have hΩ00 : symplecticForm 1 i0 i0 = 0 := symplecticForm_one_00
    have hΩ01 : symplecticForm 1 i0 i1 = 1 := symplecticForm_one_01
    have hΩ10 : symplecticForm 1 i1 i0 = -1 := symplecticForm_one_10
    have hΩ11 : symplecticForm 1 i1 i1 = 0 := symplecticForm_one_11
    -- LHS: x ⬝ (Ω y) = t.
    have lhs_eq : x ⬝ᵥ (symplecticForm 1 *ᵥ y) = t := by
      show ∑ i, x i * ∑ j, symplecticForm 1 i j * y j = t
      rw [sum_fin_two]
      rw [sum_fin_two (fun j => symplecticForm 1 i0 j * y j)]
      rw [sum_fin_two (fun j => symplecticForm 1 i1 j * y j)]
      rw [hx0, hx1, hy0, hy1, hΩ00, hΩ01, hΩ10, hΩ11]
      ring
    -- xᵀ V x = a.
    have xVx_eq : x ⬝ᵥ (Vmat *ᵥ x) = a := by
      show ∑ i, x i * ∑ j, Vmat i j * x j = a
      rw [sum_fin_two]
      rw [sum_fin_two (fun j => Vmat i0 j * x j)]
      rw [sum_fin_two (fun j => Vmat i1 j * x j)]
      rw [hx0, hx1]
      show 1 * (Vmat i0 i0 * 1 + Vmat i0 i1 * 0) + 0 *
            (Vmat i1 i0 * 1 + Vmat i1 i1 * 0) = a
      rw [← ha_def]
      ring
    -- yᵀ V y = a s² + 2 b s t + c t².
    have yVy_eq : y ⬝ᵥ (Vmat *ᵥ y) = a * s * s + 2 * b * s * t + c * t * t := by
      show ∑ i, y i * ∑ j, Vmat i j * y j = a * s * s + 2 * b * s * t + c * t * t
      rw [sum_fin_two]
      rw [sum_fin_two (fun j => Vmat i0 j * y j)]
      rw [sum_fin_two (fun j => Vmat i1 j * y j)]
      rw [hy0, hy1]
      show s * (Vmat i0 i0 * s + Vmat i0 i1 * t)
            + t * (Vmat i1 i0 * s + Vmat i1 i1 * t)
            = a * s * s + 2 * b * s * t + c * t * t
      rw [← ha_def, ← hb_def, ← hc_def, hsymm]
      ring
    rw [lhs_eq, xVx_eq, yVy_eq] at hu
    linarith
  -- ----------------------------------------------------------
  -- Specialise to s = -b·t/a, giving t ≤ a + (det V / a) · t².
  -- ----------------------------------------------------------
  have unc_t : ∀ t : ℝ, t ≤ a + ((a * c - b * b) / a) * t * t := by
    intro t
    have hs := unc (-(b * t / a)) t
    -- Simplify the RHS in hs.
    have ha_ne : a ≠ 0 := ne_of_gt ha_pos
    have expand : a * (-(b * t / a)) * (-(b * t / a))
                  + 2 * b * (-(b * t / a)) * t
                  + c * t * t
                  = ((a * c - b * b) / a) * t * t := by
      field_simp
      ring
    linarith [hs, expand]
  -- ----------------------------------------------------------
  -- Now: for `det V ≤ 0`, the inequality at large t fails.  But we
  -- only need to handle det V > 0 (use evaluating at t₀ = a/(2·det V)).
  -- First derive `det V > 0` from positive definiteness.
  -- ----------------------------------------------------------
  -- We split by sign of det V.
  -- Case 1: det V ≤ 0. Then `unc_t` at t = a + 1 gives a contradiction
  -- (LHS grows linearly, RHS is bounded above by `a`).
  by_contra hlt
  push_neg at hlt   -- hlt : V.V.det < 1/4
  rw [det_eq] at hlt
  set D := a * c - b * b with hD
  -- We have D < 1/4. Goal: derive ⊥ from `unc_t`.
  -- Pick T such that the quadratic `D/a · T² − T + a` is negative.
  -- If D > 0: pick T = a/(2D). Value = a·(4D − 1)/(4D) < 0 since 4D < 1.
  -- If D ≤ 0: pick T very large; D/a · T² − T + a → -∞ when D ≤ 0 (RHS ≤ a),
  -- contradicting T ≤ a for T > a.
  by_cases hDpos : 0 < D
  · -- Case D > 0 and D < 1/4.
    have hD_ne : D ≠ 0 := ne_of_gt hDpos
    have h4D_ne : (4 : ℝ) * D ≠ 0 := by positivity
    set T := a / (2 * D)
    have := unc_t T
    -- Compute (D/a) * T^2 - T + a.
    -- = (D/a) * a²/(4 D²) - a/(2D) + a
    -- = a/(4D) - a/(2D) + a = -a/(4D) + a = a(1 - 1/(4D)) = a(4D-1)/(4D).
    have rhs_calc : D / a * T * T = a / (4 * D) := by
      simp [T]; field_simp; ring
    have ineq : T ≤ a + a / (4 * D) := by
      have h := this
      rw [rhs_calc] at h
      exact h
    -- T = a/(2D).  So a/(2D) ≤ a + a/(4D), i.e. a/(4D) ≤ a, i.e. 1 ≤ 4D
    -- (using a > 0).  This contradicts 4D < 1.
    have : a / (2 * D) - a / (4 * D) ≤ a := by linarith
    have step : a / (4 * D) ≤ a := by
      have : a / (2 * D) - a / (4 * D) = a / (4 * D) := by
        field_simp; ring
      linarith
    -- step says a/(4D) ≤ a. With a > 0, that gives 1/(4D) ≤ 1, i.e. 4D ≥ 1.
    have h4D_pos : 0 < 4 * D := by positivity
    have h1leq : (1 : ℝ) ≤ 4 * D := by
      have hdiv : a / (4 * D) ≤ a := step
      have ha2 : a ≤ a * (4 * D) := (div_le_iff₀ h4D_pos).mp hdiv
      -- Cancel a > 0 from a ≤ a · (4D).
      nlinarith
    linarith
  · -- Case D ≤ 0.  Take T large enough.
    push_neg at hDpos  -- D ≤ 0
    -- For T > 0, RHS = D/a · T² + a ≤ a (since D/a · T² ≤ 0).
    -- So T ≤ a for all T > 0, contradiction at T = a + 1.
    have := unc_t (a + 1)
    -- D/a ≤ 0 and (a+1)^2 ≥ 0, so D/a * (a+1)^2 ≤ 0.
    have hDa_nonpos : D / a ≤ 0 := div_nonpos_of_nonpos_of_nonneg hDpos ha_pos.le
    have hT2_nn : (0:ℝ) ≤ (a + 1) * (a + 1) := by positivity
    have hprod_nonpos : D / a * (a + 1) * (a + 1) ≤ 0 := by
      have : D / a * ((a + 1) * (a + 1)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hDa_nonpos hT2_nn
      linarith [this, show D / a * (a + 1) * (a + 1) = D / a * ((a + 1) * (a + 1))
                       from by ring]
    linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: PURE GAUSSIAN STATES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A **pure Gaussian state** saturates the uncertainty principle:
    `det V = (1/4)^N`.  For N = 1 this is `det V = 1/4`, the boundary
    case of Heisenberg. -/
def IsPureGaussian {N : ℕ} (V : CovarianceMatrix N) : Prop :=
  V.V.det = (1/4 : ℝ)^N

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: THE VACUUM STATE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The vacuum |0⟩ has covariance matrix V_vac = (1/2)·I.  This is the
    minimum-uncertainty Gaussian state (pure, with all variances equal
    to 1/2 in the natural ℏ = 1 unit convention).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The vacuum-state covariance matrix: V = (1/2)·I_{2N}. -/
noncomputable def vacuumCovariance (N : ℕ) :
    Matrix (Fin (2*N)) (Fin (2*N)) ℝ :=
  (1/2 : ℝ) • (1 : Matrix (Fin (2*N)) (Fin (2*N)) ℝ)

/-- The vacuum CM is symmetric. -/
theorem vacuumCovariance_isSymm (N : ℕ) :
    (vacuumCovariance N).IsSymm := by
  unfold Matrix.IsSymm vacuumCovariance
  rw [Matrix.transpose_smul, Matrix.transpose_one]

/-- The vacuum CM is positive definite. -/
theorem vacuumCovariance_isPosDef (N : ℕ) :
    (vacuumCovariance N).PosDef := by
  unfold vacuumCovariance
  exact Matrix.PosDef.one.smul (by norm_num : (0 : ℝ) < 1/2)

/-! Within-pair swap σ : Fin (2N) → Fin (2N) (used in the vacuum
    uncertainty proof).  σ swaps each `2k` with `2k+1`.  It is an
    involution, hence a bijection.  Moreover `(Ω y)_i = ε(i) · y(σ i)`
    where ε(i) is the parity sign (+1 if i even, -1 if i odd).  These
    facts make `Σ_i (Ω y)_i² = Σ_j y_j²` immediate. -/

/-- The pair-swap σ on `Fin (2N)`: maps `2k ↔ 2k+1`. -/
noncomputable def pairSwap (N : ℕ) (i : Fin (2*N)) : Fin (2*N) :=
  if h : i.val % 2 = 0 then
    ⟨i.val + 1, by
      have h1 : i.val + 1 < 2*N := by
        have := i.isLt
        -- i even and i < 2N ⇒ i ≤ 2N − 2 ⇒ i+1 < 2N.
        omega
      exact h1⟩
  else
    ⟨i.val - 1, by
      have h1 : i.val - 1 < 2*N := by
        have := i.isLt
        omega
      exact h1⟩

/-- `pairSwap` is an involution. -/
theorem pairSwap_involutive (N : ℕ) :
    Function.Involutive (pairSwap N) := by
  intro i
  apply Fin.ext
  -- Goal: (pairSwap N (pairSwap N i)).val = i.val.
  by_cases h : i.val % 2 = 0
  · -- i even ⇒ pairSwap i has value i+1, which is odd. So pairSwap maps it to i+1-1 = i.
    have h2 : (i.val + 1) % 2 = 1 := by omega
    have h2' : (i.val + 1) % 2 ≠ 0 := by omega
    simp only [pairSwap, dif_pos h, dif_neg h2']
    omega
  · -- i odd ⇒ pairSwap i has value i-1, which is even.
    have hmod : i.val % 2 = 1 := by omega
    have hpos : 1 ≤ i.val := by omega
    have h2 : (i.val - 1) % 2 = 0 := by omega
    simp only [pairSwap, dif_neg h, dif_pos h2]
    omega

/-- `pairSwap` is a bijection. -/
theorem pairSwap_bijective (N : ℕ) : Function.Bijective (pairSwap N) :=
  (pairSwap_involutive N).bijective

/-- Action of Ω on a vector entrywise:  `(Ω y)_i = ε(i) · y(σ i)`
    where `ε(i) = 1` if i is even and `−1` if i is odd. -/
theorem mulVec_symplectic_eq (N : ℕ) (y : Fin (2*N) → ℝ) (i : Fin (2*N)) :
    (symplecticForm N *ᵥ y) i =
      (if i.val % 2 = 0 then (1 : ℝ) else -1) * y (pairSwap N i) := by
  -- Σ_j Ω(i,j) y_j; only j = pairSwap N i contributes.
  show ∑ j, symplecticForm N i j * y j =
        (if i.val % 2 = 0 then (1 : ℝ) else -1) * y (pairSwap N i)
  by_cases h : i.val % 2 = 0
  · -- i even: pairSwap i = ⟨i+1, _⟩.
    -- Ω(i, j) is nonzero only when j = i+1: Ω(i, i+1) = 1 (branch 1).
    have hps : pairSwap N i = ⟨i.val + 1, by
        have := i.isLt; omega⟩ := by
      unfold pairSwap; simp [h]
    rw [hps]
    rw [if_pos h]
    rw [Finset.sum_eq_single (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin (2*N))]
    · -- main term: Ω(i, i+1) = 1.
      have hΩ : symplecticForm N i ⟨i.val + 1, by have := i.isLt; omega⟩ = 1 := by
        unfold symplecticForm
        have hyes : i.val + 1 = (⟨i.val + 1, by have := i.isLt; omega⟩
                                  : Fin (2*N)).val ∧ i.val % 2 = 0 :=
          ⟨rfl, h⟩
        rw [if_pos hyes]
      rw [hΩ]
    · -- All other j contribute 0.
      intro j _ hjne
      have hjne_val : j.val ≠ i.val + 1 := by
        intro heq; apply hjne; apply Fin.ext; exact heq
      have hΩ0 : symplecticForm N i j = 0 := by
        unfold symplecticForm
        rcases (Decidable.em (i.val + 1 = j.val ∧ i.val % 2 = 0)) with hb1 | hb1
        · exfalso; exact hjne_val hb1.1.symm
        · rcases (Decidable.em (j.val + 1 = i.val ∧ j.val % 2 = 0)) with hb2 | hb2
          · -- Branch 2: j+1 = i, j even ⇒ i odd. But i even. Contradiction.
            exfalso; omega
          · rw [if_neg hb1, if_neg hb2]
      rw [hΩ0]; ring
    · intro hni
      exfalso; exact hni (Finset.mem_univ _)
  · -- i odd: pairSwap i = ⟨i-1, _⟩.
    have hmod : i.val % 2 = 1 := by omega
    have hpos : 1 ≤ i.val := by omega
    have hps : pairSwap N i = ⟨i.val - 1, by
        have := i.isLt; omega⟩ := by
      unfold pairSwap; simp [h]
    rw [hps]
    rw [if_neg h]
    rw [Finset.sum_eq_single (⟨i.val - 1, by have := i.isLt; omega⟩ : Fin (2*N))]
    · -- main term: Ω(i, i-1) = -1 (branch 2: j+1 = i, j = i-1 even).
      have hΩ : symplecticForm N i ⟨i.val - 1, by have := i.isLt; omega⟩ = -1 := by
        unfold symplecticForm
        have hb1 : ¬ (i.val + 1 = i.val - 1 ∧ i.val % 2 = 0) := by
          rintro ⟨h1, _⟩; omega
        have hb2 : i.val - 1 + 1 = i.val ∧ (i.val - 1) % 2 = 0 := by
          refine ⟨?_, ?_⟩ <;> omega
        -- (⟨i-1, _⟩ : Fin (2*N)).val is definitionally i-1, so the `if` reduces.
        rw [if_neg hb1, if_pos hb2]
      rw [hΩ]
    · intro j _ hjne
      have hjne_val : j.val ≠ i.val - 1 := by
        intro heq; apply hjne; apply Fin.ext; exact heq
      have hΩ0 : symplecticForm N i j = 0 := by
        unfold symplecticForm
        rcases (Decidable.em (i.val + 1 = j.val ∧ i.val % 2 = 0)) with hb1 | hb1
        · -- i+1 = j ∧ i even.  But i odd, contradiction.
          exfalso; omega
        · rcases (Decidable.em (j.val + 1 = i.val ∧ j.val % 2 = 0)) with hb2 | hb2
          · -- j+1 = i ⇒ j = i-1, contradicting hjne.
            exfalso; exact hjne_val (by omega)
          · rw [if_neg hb1, if_neg hb2]
      rw [hΩ0]; ring
    · intro hni
      exfalso; exact hni (Finset.mem_univ _)

/-- The squared norm of `Ω y` equals the squared norm of `y`. -/
theorem mulVec_symplectic_sq_eq (N : ℕ) (y : Fin (2*N) → ℝ) :
    ∑ i, (symplecticForm N *ᵥ y) i * (symplecticForm N *ᵥ y) i =
      ∑ j, y j * y j := by
  -- Per entry: (Ωy)_i² = (ε(i))²·y(σi)² = y(σi)².  Sum and reindex by σ.
  have hpoint : ∀ i, (symplecticForm N *ᵥ y) i * (symplecticForm N *ᵥ y) i =
                       y (pairSwap N i) * y (pairSwap N i) := by
    intro i
    rw [mulVec_symplectic_eq]
    by_cases h : i.val % 2 = 0
    · rw [if_pos h]; ring
    · rw [if_neg h]; ring
  -- Reindex by σ (a bijection).
  calc ∑ i, (symplecticForm N *ᵥ y) i * (symplecticForm N *ᵥ y) i
      = ∑ i, y (pairSwap N i) * y (pairSwap N i) :=
        Finset.sum_congr rfl (fun i _ => hpoint i)
    _ = ∑ j, y j * y j := by
        -- Σ_i f(σ i) = Σ_j f(j) since σ is a bijection.
        let σ : Fin (2*N) ≃ Fin (2*N) :=
          ⟨pairSwap N, pairSwap N, pairSwap_involutive N, pairSwap_involutive N⟩
        exact Finset.sum_equiv σ (by simp) (by intros; rfl)

/-- The vacuum CM satisfies the uncertainty bilinear inequality.

    For V = (1/2)·I:  xᵀVx = (1/2)Σx_i², yᵀVy = (1/2)Σy_i².
    AM-GM per entry:  x_i·(Ωy)_i ≤ (1/2)(x_i² + (Ωy)_i²).
    Then Σ_i (Ωy)_i² = Σ_j y_j² because Ω is orthogonal (it acts as a
    signed pair-swap). -/
theorem vacuumCovariance_uncertainty (N : ℕ) :
    ∀ x y : Fin (2*N) → ℝ,
      x ⬝ᵥ (symplecticForm N *ᵥ y) ≤
        x ⬝ᵥ (vacuumCovariance N *ᵥ x) + y ⬝ᵥ (vacuumCovariance N *ᵥ y) := by
  intro x y
  -- Compute the diagonal quadratic forms.
  have xVx : x ⬝ᵥ (vacuumCovariance N *ᵥ x) = (1/2) * ∑ i, x i * x i := by
    show ∑ i, x i * ((vacuumCovariance N *ᵥ x) i) = (1/2) * ∑ i, x i * x i
    have : ∀ i, (vacuumCovariance N *ᵥ x) i = (1/2) * x i := by
      intro i
      show ∑ j, vacuumCovariance N i j * x j = (1/2) * x i
      unfold vacuumCovariance
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intros j _ hji; simp [Ne.symm hji]
      · intro hni; exfalso; exact hni (Finset.mem_univ _)
    simp_rw [this]
    rw [Finset.mul_sum]
    congr 1; ext i; ring
  have yVy : y ⬝ᵥ (vacuumCovariance N *ᵥ y) = (1/2) * ∑ i, y i * y i := by
    show ∑ i, y i * ((vacuumCovariance N *ᵥ y) i) = (1/2) * ∑ i, y i * y i
    have : ∀ i, (vacuumCovariance N *ᵥ y) i = (1/2) * y i := by
      intro i
      show ∑ j, vacuumCovariance N i j * y j = (1/2) * y i
      unfold vacuumCovariance
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intros j _ hji; simp [Ne.symm hji]
      · intro hni; exfalso; exact hni (Finset.mem_univ _)
    simp_rw [this]
    rw [Finset.mul_sum]
    congr 1; ext i; ring
  rw [xVx, yVy]
  -- AM-GM per entry: x_i · (Ωy)_i ≤ (1/2)(x_i² + (Ωy)_i²).
  have step1 : x ⬝ᵥ (symplecticForm N *ᵥ y) ≤
              (1/2) * ∑ i, (x i * x i + (symplecticForm N *ᵥ y) i *
                            (symplecticForm N *ᵥ y) i) := by
    have h : ∀ i, x i * (symplecticForm N *ᵥ y) i ≤
                  (1/2) * (x i * x i + (symplecticForm N *ᵥ y) i *
                                       (symplecticForm N *ᵥ y) i) := by
      intro i
      nlinarith [sq_nonneg (x i - (symplecticForm N *ᵥ y) i)]
    calc x ⬝ᵥ (symplecticForm N *ᵥ y)
        = ∑ i, x i * (symplecticForm N *ᵥ y) i := rfl
      _ ≤ ∑ i, (1/2) *
              (x i * x i + (symplecticForm N *ᵥ y) i *
                            (symplecticForm N *ᵥ y) i) :=
            Finset.sum_le_sum (fun i _ => h i)
      _ = (1/2) * ∑ i, (x i * x i + (symplecticForm N *ᵥ y) i *
                                    (symplecticForm N *ᵥ y) i) := by
            rw [← Finset.mul_sum]
  -- Use Ω-orthogonality: Σ (Ωy)_i² = Σ y_j².
  have Ωy_sq := mulVec_symplectic_sq_eq N y
  -- Combine.
  have rhs_eq : (1/2) * ∑ i, (x i * x i + (symplecticForm N *ᵥ y) i *
                                          (symplecticForm N *ᵥ y) i) =
                (1/2) * ∑ i, x i * x i + (1/2) * ∑ i, y i * y i := by
    rw [Finset.sum_add_distrib, mul_add, Ωy_sq]
  linarith

/-- The vacuum CM packaged as a `CovarianceMatrix`. -/
noncomputable def vacuumCM (N : ℕ) : CovarianceMatrix N where
  V := vacuumCovariance N
  isSymm := vacuumCovariance_isSymm N
  isPosDef := vacuumCovariance_isPosDef N
  uncertainty := vacuumCovariance_uncertainty N

/-- For N = 1, `det ((1/2)·I_{2}) = 1/4 = (1/4)^1`.  This is the
    saturated form of Heisenberg. -/
theorem vacuum_isPureGaussian_one :
    IsPureGaussian (vacuumCM 1) := by
  show (vacuumCM 1).V.det = (1/4 : ℝ)^1
  show (vacuumCovariance 1).det = (1/4 : ℝ)^1
  unfold vacuumCovariance
  rw [Matrix.det_smul, Matrix.det_one, mul_one]
  -- Now: (1/2)^(card (Fin (2*1))) = (1/4)^1.
  -- card (Fin (2*1)) = 2*1 = 2.
  simp [Fintype.card_fin]
  norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: WILLIAMSON FORM (hypothesis-level)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Williamson's theorem (1936): every positive-definite real symmetric
    2N×2N matrix V can be brought, via a symplectic similarity, to a
    diagonal form
        V = S · D · Sᵀ,   D = diag(ν₁, ν₁, ν₂, ν₂, …, ν_N, ν_N),
    where S ∈ Sp(2N, ℝ) (symplectic: Sᵀ Ω S = Ω) and the **symplectic
    eigenvalues** ν_k > 0 are uniquely determined by V (the moduli of
    the eigenvalues of i Ω V).  In the framework where Ω carries an
    extra factor of 2, the Heisenberg uncertainty is equivalent to
    every ν_k ≥ 1/2.

    The full proof requires the symplectic eigenvalue decomposition
    (Iwasawa or polar decomposition of Sp(2N)) which is not currently
    in Mathlib.  We state the conclusion as a named property which
    downstream consumers can assume.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A symplectic matrix: `Sᵀ Ω S = Ω`. -/
def IsSymplectic {N : ℕ} (S : Matrix (Fin (2*N)) (Fin (2*N)) ℝ) : Prop :=
  Sᵀ * symplecticForm N * S = symplecticForm N

/-- The **Williamson normal form** as a Prop on a covariance matrix.
    Says there exist a symplectic matrix S and N positive symplectic
    eigenvalues ν such that
        V = S · diag(ν₁, ν₁, …, ν_N, ν_N) · Sᵀ.
    Heisenberg uncertainty is then equivalent to ν_k ≥ 1/2 for all k. -/
def WilliamsonForm {N : ℕ} (V : CovarianceMatrix N) : Prop :=
  ∃ (S : Matrix (Fin (2*N)) (Fin (2*N)) ℝ)
    (ν : Fin N → ℝ),
    IsSymplectic S ∧
    (∀ k, 0 < ν k) ∧
    V.V = S * (Matrix.diagonal (fun i : Fin (2*N) =>
              ν ⟨i.val / 2, by omega⟩)) * Sᵀ

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: MASTER SUMMARY THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Master bundle** of Gaussian-states facts proved in this file.

    1. The symplectic form Ω is antisymmetric.
    2. Single-mode Heisenberg: every covariance matrix at N=1 satisfies
       det V ≥ 1/4.
    3. The vacuum state V = (1/2)·I is a valid covariance matrix.
    4. The vacuum at N=1 is a pure Gaussian state, saturating Heisenberg. -/
theorem gaussian_states_master :
    (∀ N : ℕ, (symplecticForm N)ᵀ = -(symplecticForm N)) ∧
    (∀ V : CovarianceMatrix 1, (1 : ℝ)/4 ≤ V.V.det) ∧
    (∀ N : ℕ, (vacuumCovariance N).IsSymm ∧
              (vacuumCovariance N).PosDef) ∧
    IsPureGaussian (vacuumCM 1) :=
  ⟨symplecticForm_antisymmetric,
   heisenberg_N_one,
   fun N => ⟨vacuumCovariance_isSymm N, vacuumCovariance_isPosDef N⟩,
   vacuum_isPureGaussian_one⟩

end UnifiedTheory.LayerB.GaussianStates
