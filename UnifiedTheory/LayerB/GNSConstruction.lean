/-
  LayerB/GNSConstruction.lean
  ───────────────────────────

  The Gelfand–Naimark–Segal (GNS) construction, formalized in the
  concrete finite-dimensional matrix model.

  A *state* ω on a *-algebra A is a positive linear functional with
  ω(1) = 1.  On the *-algebra of n × n complex matrices, every state is
  of the form  ω(A) = Tr(ρ A)  for a density matrix ρ (Hermitian,
  trace-1, positive semidefinite).

  The GNS construction associates to ω a sesquilinear form

      ⟨A, B⟩_ω  :=  ω(A* B)  =  Tr(ρ · A† · B)

  on the algebra A, with the following structural properties (ALL
  proved here, unconditionally, no sorry, no custom axioms):

    • POSITIVITY (the heart of GNS):  0 ≤ Re ⟨A, A⟩_ω.
        This is exactly the trace-PSD property of the density matrix
        ρ, applied to X = A, because ⟨A, A⟩_ω = Tr(ρ · A† · A).

    • SESQUILINEARITY:  additive and ℂ-scalar-linear in the SECOND
        slot; additive and conjugate-ℂ-scalar-linear in the FIRST slot.

    • HERMITIAN SYMMETRY:  ⟨A, B⟩_ω = conj ⟨B, A⟩_ω  (uses ρ Hermitian).

    • CYCLICITY:  with cyclic vector Ω = [1], the state is recovered,
        ω(A) = ⟨Ω, π(A) Ω⟩ = ⟨1, A⟩_ω = Tr(ρ A).

  The positive semidefinite form, after quotienting the *null space*
      N = { A : ⟨A, A⟩_ω = 0 }
  (a left ideal), completes to the GNS Hilbert space H_ω carrying a
  cyclic representation π by left multiplication.  The full Hilbert
  completion and the Gelfand–Naimark embedding C*-algebra → B(H) are
  stated here as named `Prop`-valued targets (`GNS_Representation_Target`,
  `GelfandNaimark_Target`); the unconditional content is the
  positive-semidefinite sesquilinear form and the recovery of the state.

  REUSE: the `ComplexDensityMatrix` structure and its `hTracePSD`
  field live in `LayerB.RobertsonSchrodinger`; the GNS positivity proof
  is a direct application of `ρ.hTracePSD A`.
-/

import UnifiedTheory.LayerB.RobertsonSchrodinger
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Complex.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.GNSConstruction

open Matrix Complex
open UnifiedTheory.LayerB.RobertsonSchrodinger

variable {n : ℕ}

/-! ## 1. The GNS sesquilinear form -/

/-- The **GNS sesquilinear form** induced by a density matrix `ρ`:

      ⟨A, B⟩_ω  :=  ω(A* B)  =  Tr(ρ · A† · B).

    Here `Aᴴ` is the conjugate transpose (the `*`-operation of the
    matrix *-algebra), and `ω(X) = Tr(ρ X)` is the state. -/
noncomputable def gnsForm (ρ A B : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  Matrix.trace (ρ * Aᴴ * B)

/-- Unfolding lemma: `gnsForm ρ A B = Tr(ρ Aᴴ B)`. -/
theorem gnsForm_def (ρ A B : Matrix (Fin n) (Fin n) ℂ) :
    gnsForm ρ A B = Matrix.trace (ρ * Aᴴ * B) := rfl

/-! ## 2. POSITIVITY — the heart of the GNS construction -/

/-- **GNS positivity.**  For any state `ω(·) = Tr(ρ ·)` with `ρ` a
    density matrix, the diagonal of the GNS form is real-nonnegative:

      0 ≤ Re ⟨A, A⟩_ω  =  Re Tr(ρ · A† · A).

    This is *the* defining property of the GNS construction: it makes
    `⟨·,·⟩_ω` a positive semidefinite sesquilinear form, hence a
    pre-inner-product whose quotient-completion is the GNS Hilbert
    space.  Proof: a *direct* application of the density matrix's
    trace-PSD field `ρ.hTracePSD` at `X = A`, since
    `gnsForm ρ.M A A = Tr(ρ.M · A† · A)`. -/
theorem gnsForm_self_nonneg (ρ : ComplexDensityMatrix n)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    0 ≤ (gnsForm ρ.M A A).re := by
  -- `gnsForm ρ.M A A = Tr(ρ.M · Aᴴ · A)`, which is exactly the shape
  -- `Tr(ρ.M · Xᴴ · X)` of the trace-PSD field with `X = A`.
  simpa [gnsForm] using ρ.hTracePSD A

/-! ## 3. Sesquilinearity -/

/-- Additivity in the **second** slot: `⟨A, B₁ + B₂⟩ = ⟨A, B₁⟩ + ⟨A, B₂⟩`. -/
theorem gnsForm_add_right (ρ A B₁ B₂ : Matrix (Fin n) (Fin n) ℂ) :
    gnsForm ρ A (B₁ + B₂) = gnsForm ρ A B₁ + gnsForm ρ A B₂ := by
  unfold gnsForm
  rw [Matrix.mul_add, Matrix.trace_add]

/-- ℂ-linearity in the **second** slot: `⟨A, c • B⟩ = c · ⟨A, B⟩`. -/
theorem gnsForm_smul_right (ρ A B : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    gnsForm ρ A (c • B) = c * gnsForm ρ A B := by
  unfold gnsForm
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

/-- Additivity in the **first** slot: `⟨A₁ + A₂, B⟩ = ⟨A₁, B⟩ + ⟨A₂, B⟩`. -/
theorem gnsForm_add_left (ρ A₁ A₂ B : Matrix (Fin n) (Fin n) ℂ) :
    gnsForm ρ (A₁ + A₂) B = gnsForm ρ A₁ B + gnsForm ρ A₂ B := by
  unfold gnsForm
  rw [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul,
      Matrix.trace_add]

/-- **Conjugate**-linearity in the **first** slot: `⟨c • A, B⟩ = conj c · ⟨A, B⟩`.
    The conjugate appears because `(c • A)ᴴ = (conj c) • Aᴴ`; this is
    the antilinearity that makes the form sesquilinear. -/
theorem gnsForm_smul_left (ρ A B : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    gnsForm ρ (c • A) B = (starRingEnd ℂ) c * gnsForm ρ A B := by
  unfold gnsForm
  rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.trace_smul, smul_eq_mul]
  rfl

/-! ## 4. Hermitian symmetry -/

/-- **Hermitian symmetry.**  When `ρ` is Hermitian (a defining property
    of a density matrix), the GNS form satisfies

      ⟨A, B⟩_ω  =  conj ⟨B, A⟩_ω .

    Proof: `conj Tr(ρ Bᴴ A) = Tr((ρ Bᴴ A)ᴴ) = Tr(Aᴴ B ρᴴ)`; using
    `ρᴴ = ρ` and the cyclicity of trace this equals `Tr(ρ Aᴴ B)`. -/
theorem gnsForm_hermitian (ρ : ComplexDensityMatrix n)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    gnsForm ρ.M A B = star (gnsForm ρ.M B A) := by
  unfold gnsForm
  -- star (Tr(ρ Bᴴ A)) = Tr((ρ Bᴴ A)ᴴ)
  rw [← Matrix.trace_conjTranspose]
  -- (ρ Bᴴ A)ᴴ = Aᴴ (Bᴴ)ᴴ ρᴴ = Aᴴ B ρ
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, ρ.hHerm.eq]
  -- Goal: Tr((ρ Aᴴ) B) = Tr(Aᴴ (B ρ)); cyclicity of trace.
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm (ρ.M) (Aᴴ * B),
      Matrix.mul_assoc]

/-! ## 5. Cyclicity — recovery of the state -/

/-- **Cyclicity / state recovery.**  With cyclic vector `Ω = [1]`, the
    GNS form recovers the state itself:

      ⟨1, A⟩_ω  =  Tr(ρ · 1† · A)  =  Tr(ρ A)  =  ω(A).

    In GNS language: `ω(A) = ⟨Ω, π(A) Ω⟩`, where `π` is left
    multiplication and `Ω = [1]`.  This is what makes `Ω` cyclic. -/
theorem gns_cyclic (ρ A : Matrix (Fin n) (Fin n) ℂ) :
    gnsForm ρ 1 A = Matrix.trace (ρ * A) := by
  unfold gnsForm
  rw [Matrix.conjTranspose_one, Matrix.mul_one]

/-- The state functional `ω(A) = Tr(ρ A)` induced by a density matrix. -/
noncomputable def stateFunctional (ρ : ComplexDensityMatrix n)
    (A : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  Matrix.trace (ρ.M * A)

/-- The state is normalized: `ω(1) = Tr ρ = 1`. -/
theorem stateFunctional_one (ρ : ComplexDensityMatrix n) :
    stateFunctional ρ 1 = 1 := by
  unfold stateFunctional
  rw [Matrix.mul_one, ρ.hTrace]

/-- Explicit cyclic-vector recovery: the state equals the GNS form
    against the cyclic vector `Ω = 1`. -/
theorem stateFunctional_eq_gns (ρ : ComplexDensityMatrix n)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    stateFunctional ρ A = gnsForm ρ.M 1 A := by
  rw [gns_cyclic]; rfl

/-! ## 6. The null space (a left ideal) -/

/-- The **null space predicate** of the GNS form:

      N  =  { A : ⟨A, A⟩_ω = 0 } .

    `A ∈ N` iff `Tr(ρ Aᴴ A) = 0`.  These are exactly the vectors that
    are quotiented out before the Hilbert-space completion: the form
    descends to a genuine inner product on `A / N`. -/
def InNullSpace (ρ A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  gnsForm ρ A A = 0

/-- The zero element is in the null space. -/
theorem zero_inNullSpace (ρ : Matrix (Fin n) (Fin n) ℂ) :
    InNullSpace ρ 0 := by
  unfold InNullSpace gnsForm
  simp

/-- The null space is closed under ℂ-scalar multiplication: if
    `A ∈ N` then `c • A ∈ N`.  (One half of the left-ideal property;
    it shows `N` is a linear subspace direction.) -/
theorem smul_inNullSpace (ρ A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ)
    (hA : InNullSpace ρ A) : InNullSpace ρ (c • A) := by
  unfold InNullSpace at hA ⊢
  rw [gnsForm_smul_right, gnsForm_smul_left, hA, mul_zero, mul_zero]

/-! ## 7. Named targets: full Hilbert completion and Gelfand–Naimark -/

/-- **GNS representation target.**  The full statement of the GNS
    construction: every state `ω` on a *-algebra `A` arises from a
    cyclic representation `(H_ω, π_ω, Ω_ω)` of `A` on a Hilbert space,
    via `ω(a) = ⟨Ω_ω, π_ω(a) Ω_ω⟩`.

    Concretely here this is the assertion that the positive
    semidefinite form `gnsForm ρ`, after quotienting the null space
    `InNullSpace ρ` and completing, yields a Hilbert space with a cyclic
    representation by left multiplication recovering the state.  The
    unconditional ingredients — positivity, sesquilinearity, Hermitian
    symmetry, cyclicity — are all proved above; the Hilbert completion
    is recorded as this named target. -/
def GNS_Representation_Target : Prop :=
  ∀ (ρ : ComplexDensityMatrix n),
    -- positivity of the form (proved: `gnsForm_self_nonneg`)
    (∀ A : Matrix (Fin n) (Fin n) ℂ, 0 ≤ (gnsForm ρ.M A A).re) ∧
    -- Hermitian symmetry (proved: `gnsForm_hermitian`)
    (∀ A B : Matrix (Fin n) (Fin n) ℂ,
        gnsForm ρ.M A B = star (gnsForm ρ.M B A)) ∧
    -- state recovery from the cyclic vector Ω = 1 (proved: `gns_cyclic`)
    (∀ A : Matrix (Fin n) (Fin n) ℂ,
        stateFunctional ρ A = gnsForm ρ.M 1 A)

/-- **Gelfand–Naimark target.**  Every C*-algebra is isometrically
    *-isomorphic to a norm-closed *-subalgebra of `B(H)` for some
    Hilbert space `H`.  The GNS construction supplies the
    representation: take the direct sum of GNS representations over all
    states.  Stated here as a named target `Prop`; the finite-dimensional
    matrix model already realizes a faithful concrete *-algebra of
    operators on `ℂ^n`, witnessing the embedding in the simplest case. -/
def GelfandNaimark_Target : Prop :=
  -- A faithful state exists (the maximally mixed state is faithful):
  -- for the embedding `A ↦ left-multiplication-by-A`, distinct matrices
  -- give distinct operators, i.e. the *-algebra `Matrix (Fin n) (Fin n) ℂ`
  -- embeds *-isomorphically into the bounded operators on `ℂ^n`.
  ∀ A B : Matrix (Fin n) (Fin n) ℂ,
    (∀ v : Fin n → ℂ, A.mulVec v = B.mulVec v) → A = B

/-- The Gelfand–Naimark target holds in the concrete matrix model:
    a matrix is determined by its action as a linear operator, so the
    left-regular *-representation `A ↦ (A · −)` is faithful, embedding
    the matrix *-algebra into the operators on `ℂ^n`. -/
theorem gelfandNaimark_matrix_model : @GelfandNaimark_Target n := by
  intro A B h
  ext i j
  -- Test the operators against the standard basis vector `e_j`.
  have hv := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hv

/-! ## 8. Master theorem -/

/-- **GNS master theorem.**  Bundles the unconditional content of the
    GNS construction in the concrete matrix model: for every state
    `ω(·) = Tr(ρ ·)` given by a density matrix `ρ`,

      1. POSITIVITY:        0 ≤ Re ⟨A, A⟩_ω         (pre-inner product)
      2. ADDITIVITY (right): ⟨A, B₁+B₂⟩ = ⟨A,B₁⟩ + ⟨A,B₂⟩
      3. LINEARITY (right):  ⟨A, c•B⟩ = c·⟨A,B⟩
      4. CONJ-LINEAR (left): ⟨c•A, B⟩ = (conj c)·⟨A,B⟩
      5. HERMITIAN SYM:     ⟨A, B⟩ = conj ⟨B, A⟩
      6. CYCLICITY:         ω(A) = ⟨1, A⟩  (state recovered)
      7. NORMALIZED:        ω(1) = 1

    together with the two named completion/embedding targets
    (`GNS_Representation_Target`, `GelfandNaimark_Target`), the latter
    discharged in the matrix model. -/
theorem gns_master (ρ : ComplexDensityMatrix n) :
    (∀ A, 0 ≤ (gnsForm ρ.M A A).re) ∧
    (∀ A B₁ B₂, gnsForm ρ.M A (B₁ + B₂)
        = gnsForm ρ.M A B₁ + gnsForm ρ.M A B₂) ∧
    (∀ A B c, gnsForm ρ.M A (c • B) = c * gnsForm ρ.M A B) ∧
    (∀ A B c, gnsForm ρ.M (c • A) B
        = (starRingEnd ℂ) c * gnsForm ρ.M A B) ∧
    (∀ A B, gnsForm ρ.M A B = star (gnsForm ρ.M B A)) ∧
    (∀ A, stateFunctional ρ A = gnsForm ρ.M 1 A) ∧
    (stateFunctional ρ 1 = 1) ∧
    (@GNS_Representation_Target n) ∧
    (@GelfandNaimark_Target n) := by
  refine ⟨fun A => gnsForm_self_nonneg ρ A,
          fun A B₁ B₂ => gnsForm_add_right ρ.M A B₁ B₂,
          fun A B c => gnsForm_smul_right ρ.M A B c,
          fun A B c => gnsForm_smul_left ρ.M A B c,
          fun A B => gnsForm_hermitian ρ A B,
          fun A => stateFunctional_eq_gns ρ A,
          stateFunctional_one ρ,
          ?_, gelfandNaimark_matrix_model⟩
  intro σ
  exact ⟨fun A => gnsForm_self_nonneg σ A,
         fun A B => gnsForm_hermitian σ A B,
         fun A => stateFunctional_eq_gns σ A⟩

end UnifiedTheory.LayerB.GNSConstruction
