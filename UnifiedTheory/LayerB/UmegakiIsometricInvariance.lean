/-
  LayerB/UmegakiIsometricInvariance.lean
  ───────────────────────────────────────

  **Isometric invariance of Umegaki relative entropy.**

  For an isometry `V` (i.e. `V† V = I`) and density matrices `ρ, σ`,
  the Umegaki quantum relative entropy is preserved under
  conjugation by `V`:

        S(V ρ V†  ‖  V σ V†)  =  S(ρ ‖ σ).

  This is the analytic fact that gates the
  `KrausMeasurementDPIBridge_Target` in
  `StinespringMeasurementDPI.lean`.

  ──────────────────────────────────────────────────────────────────
  WHAT IS PROVEN HERE (no `sorry`, no custom `axiom`):

    1. `square_isometry_mem_unitaryGroup`
       For a SQUARE matrix `V : Matrix (Fin n) (Fin n) ℂ`,
       `IsIsometry V` implies `V ∈ Matrix.unitaryGroup …`.
       (A square isometry is automatically a unitary —
       `mem_unitaryGroup_iff'`.)

    2. `squareIsometryToUnitary` and `squareIsometryConjugate`
       Helper constructors packaging `V ρ V†` as a
       `ComplexDensityMatrix n` when `V` is a SQUARE isometry,
       built on top of `unitaryConjugate` from
       `UnitaryInvariance.lean`.

    3. `umegakiRelativeEntropy_square_isometric_invariant`
       (UNCONDITIONAL — square case)
       For any square isometry `V : Matrix (Fin n) (Fin n) ℂ`
       (`V† V = I`) and `ρ σ : ComplexDensityMatrix n`,
       the Umegaki relative entropy of the conjugated density
       matrices equals `S(ρ ‖ σ)`.  Built directly on top of
       `umegakiRelativeEntropy_unitary_invariant` from
       `UnitaryInvariance.lean`, by reducing the square isometry
       to a unitary.

    4. `isometricConjMatrix_*`
       For a RECTANGULAR isometry `V : Matrix (Fin m) (Fin n) ℂ`,
       the matrix `V ρ V†` satisfies:
         (a) Hermitian (`isometricConjMatrix_isHermitian`),
         (b) trace 1   (`isometricConjMatrix_trace`),
         (c) PSD       (`isometricConjMatrix_posSemidef`),
         (d) trace-PSD (`isometricConjMatrix_tracePSD`).
       All four are unconditional.

    5. `umegakiRelativeEntropy_isometric_invariant_Target`
       (RECTANGULAR — NAMED GATE)
       The general isometric-invariance statement for
       (possibly rectangular) isometries
       `V : Matrix (Fin m) (Fin n) ℂ`.  Exposed as a clean
       `Prop`-gate, in parallel with
       `KrausMeasurementDPIBridge_Target`.

    6. `umegakiRelativeEntropy_isometric_invariant_square` —
       the square slice of the gate is closed unconditionally.

  No `sorry`, no custom `axiom`.

  ──────────────────────────────────────────────────────────────────
  WHY THE RECTANGULAR CASE IS A GATE.

  The unitary-invariance proof in `UnitaryInvariance.lean` exploits
  the fact that conjugation by a *unitary* `U` is a unital
  `*-algebra automorphism` of `Matrix (Fin n) (Fin n) ℂ`, and
  invokes `StarAlgHomClass.map_cfc` to interchange it with the CFC.

  For a strictly RECTANGULAR isometry `V : Matrix (Fin m) (Fin n) ℂ`
  with `m > n`, the map `X ↦ V X V†` from
  `Matrix (Fin n) (Fin n) ℂ` to `Matrix (Fin m) (Fin m) ℂ` is a
  `*-algebra homomorphism` that is multiplicative and star-preserving
  (using `V† V = I`) but NOT unital — it sends the identity to the
  projection `V V†`, not the identity of the larger algebra.  The
  unital `map_cfc` machinery therefore does not apply directly.

  Two routes close the rectangular case:

  ROUTE A (unitary extension).
    Extend `V` to a full unitary `U` on `Fin m` using Mathlib's
    `Orthonormal.exists_orthonormalBasis_extension`.  Then
        V ρ V†  =  U · (ρ ⊕ 0) · U†,
    and unitary-invariance of `S(·‖·)` reduces to the case of a
    block-diagonal padding, which is handled by spectral analysis
    (the nonzero spectrum of `V ρ V†` equals that of `ρ`).

  ROUTE B (non-unital map_cfc).
    Use `NonUnitalStarAlgHomClass.map_cfcₙ` (which DOES apply to
    `X ↦ V X V†`) and convert between the unital and non-unital
    CFC.  Mathlib's `Real.log` already satisfies `log 0 = 0`, so
    the non-unital CFC of `Real.log` is well-defined.

  Both routes add ~200–400 lines of CFC plumbing.  The named gate
  here is the clean substitute, in line with this file's
  zero-sorry / zero-custom-axiom standing constraint.
-/

import UnifiedTheory.LayerB.UmegakiRelativeEntropy
import UnifiedTheory.LayerB.OperatorMonotoneLog
import UnifiedTheory.LayerB.UnitaryInvariance
import UnifiedTheory.LayerB.StinespringDilation
import Mathlib.LinearAlgebra.UnitaryGroup

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.UmegakiIsometricInvariance

open Matrix Complex
open scoped BigOperators ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.SpectralFC
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.UmegakiRelativeEntropy
open UnifiedTheory.LayerB.UnitaryInvariance
open UnifiedTheory.LayerB.StinespringDilation

/-! ## 1. Square isometry ⇒ unitary -/

variable {n : ℕ}

/-- **A square isometry is a unitary.**

    For `V : Matrix (Fin n) (Fin n) ℂ`, the isometry condition
    `V† V = I` is exactly `mem_unitaryGroup_iff'`.  In particular,
    membership in `Matrix.unitaryGroup (Fin n) ℂ` follows. -/
theorem square_isometry_mem_unitaryGroup
    {V : Matrix (Fin n) (Fin n) ℂ} (hV : IsIsometry V) :
    V ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  -- `IsIsometry V` unfolds to `V.conjTranspose * V = 1`, which
  -- equals `star V * V = 1` since for matrices `star = conjTranspose`.
  have h_star : star V * V = (1 : Matrix (Fin n) (Fin n) ℂ) := by
    change V.conjTranspose * V = 1
    exact hV
  exact Matrix.mem_unitaryGroup_iff'.mpr h_star

/-- Package a square isometry as a `Matrix.unitaryGroup` element. -/
noncomputable def squareIsometryToUnitary
    {V : Matrix (Fin n) (Fin n) ℂ} (hV : IsIsometry V) :
    Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨V, square_isometry_mem_unitaryGroup hV⟩

@[simp]
theorem squareIsometryToUnitary_val
    {V : Matrix (Fin n) (Fin n) ℂ} (hV : IsIsometry V) :
    (squareIsometryToUnitary hV).val = V := rfl

/-! ## 2. The conjugated state as a `ComplexDensityMatrix` (square case) -/

/-- For a square isometry `V`, the conjugate `V ρ V†` is itself a
    `ComplexDensityMatrix n`, identical to `unitaryConjugate`. -/
noncomputable def squareIsometryConjugate
    {V : Matrix (Fin n) (Fin n) ℂ} (hV : IsIsometry V)
    (ρ : ComplexDensityMatrix n) :
    ComplexDensityMatrix n :=
  unitaryConjugate (squareIsometryToUnitary hV) ρ

@[simp]
theorem squareIsometryConjugate_M
    {V : Matrix (Fin n) (Fin n) ℂ} (hV : IsIsometry V)
    (ρ : ComplexDensityMatrix n) :
    (squareIsometryConjugate hV ρ).M = V * ρ.M * V.conjTranspose := by
  -- `unitaryConjugate U ρ` is `U.val * ρ.M * star U.val`.
  -- Here `U.val = V` and `star V = V.conjTranspose` (definitionally
  -- on matrices).
  change V * ρ.M * star V = V * ρ.M * V.conjTranspose
  rfl

/-! ## 3. Isometric invariance of Umegaki relative entropy — SQUARE CASE -/

/-- **Isometric invariance of Umegaki relative entropy (square case).**

    For a SQUARE isometry `V : Matrix (Fin n) (Fin n) ℂ`
    (`V† V = I`, equivalently `V ∈ Matrix.unitaryGroup`), and
    density matrices `ρ, σ : ComplexDensityMatrix n`,

        S(V ρ V†  ‖  V σ V†)  =  S(ρ ‖ σ).

    Proof: A square isometry is a unitary, so this is
    `umegakiRelativeEntropy_unitary_invariant` applied to
    `U := ⟨V, square_isometry_mem_unitaryGroup hV⟩`. -/
theorem umegakiRelativeEntropy_square_isometric_invariant
    {V : Matrix (Fin n) (Fin n) ℂ} (hV : IsIsometry V)
    (ρ σ : ComplexDensityMatrix n) :
    umegakiRelativeEntropy
        (squareIsometryConjugate hV ρ) (squareIsometryConjugate hV σ)
      = umegakiRelativeEntropy ρ σ :=
  umegakiRelativeEntropy_unitary_invariant (squareIsometryToUnitary hV) ρ σ

/-! ## 4. The (rectangular) conjugated state as a `ComplexDensityMatrix`-data

For a generic rectangular isometry `V : Matrix (Fin m) (Fin n) ℂ`
with `V† V = I`, the matrix `V * ρ.M * V†` is Hermitian, trace 1,
and PSD on `Fin m`.  This is the same content as
`stinespringConjMatrix` in `StinespringMeasurementDPI.lean` (which
specialises to `Fin m = Fin n × Fin k`), but here without the
specific Stinespring index shape. -/

section RectangularIsometryDensity

variable {m : ℕ}

/-- The conjugated matrix `V * ρ * V†` for an isometry
    `V : Matrix (Fin m) (Fin n) ℂ`. -/
noncomputable def isometricConjMatrix
    (V : Matrix (Fin m) (Fin n) ℂ) (ρ : ComplexDensityMatrix n) :
    Matrix (Fin m) (Fin m) ℂ :=
  V * ρ.M * V.conjTranspose

/-- `V ρ V†` is Hermitian. -/
theorem isometricConjMatrix_isHermitian
    (V : Matrix (Fin m) (Fin n) ℂ) (ρ : ComplexDensityMatrix n) :
    (isometricConjMatrix V ρ).IsHermitian := by
  unfold isometricConjMatrix
  change (V * ρ.M * V.conjTranspose).conjTranspose = V * ρ.M * V.conjTranspose
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  rw [Matrix.conjTranspose_conjTranspose, ρ.hHerm.eq]
  rw [Matrix.mul_assoc]

/-- `V ρ V†` has trace 1 when `V` is an isometry. -/
theorem isometricConjMatrix_trace
    (V : Matrix (Fin m) (Fin n) ℂ) (hV : IsIsometry V)
    (ρ : ComplexDensityMatrix n) :
    Matrix.trace (isometricConjMatrix V ρ) = 1 := by
  unfold isometricConjMatrix
  calc Matrix.trace (V * ρ.M * V.conjTranspose)
      = Matrix.trace (V.conjTranspose * (V * ρ.M)) := by
        rw [show V * ρ.M * V.conjTranspose = (V * ρ.M) * V.conjTranspose from rfl]
        exact Matrix.trace_mul_comm (V * ρ.M) V.conjTranspose
    _ = Matrix.trace (V.conjTranspose * V * ρ.M) := by rw [← Matrix.mul_assoc]
    _ = Matrix.trace ((1 : Matrix (Fin n) (Fin n) ℂ) * ρ.M) := by
        unfold IsIsometry at hV; rw [hV]
    _ = Matrix.trace ρ.M := by rw [Matrix.one_mul]
    _ = 1 := ρ.hTrace

/-- `V ρ V†` is PSD. -/
theorem isometricConjMatrix_posSemidef
    (V : Matrix (Fin m) (Fin n) ℂ) (ρ : ComplexDensityMatrix n) :
    (isometricConjMatrix V ρ).PosSemidef := by
  unfold isometricConjMatrix
  exact (posSemidef_of_ComplexDensityMatrix ρ).mul_mul_conjTranspose_same V

/-- `V ρ V†` satisfies the trace-PSD field. -/
theorem isometricConjMatrix_tracePSD
    (V : Matrix (Fin m) (Fin n) ℂ) (ρ : ComplexDensityMatrix n) :
    ∀ X : Matrix (Fin m) (Fin m) ℂ,
      0 ≤ (Matrix.trace (isometricConjMatrix V ρ * X.conjTranspose * X)).re := by
  intro X
  have hcyc : Matrix.trace (isometricConjMatrix V ρ * X.conjTranspose * X)
            = Matrix.trace (X * isometricConjMatrix V ρ * X.conjTranspose) := by
    rw [show isometricConjMatrix V ρ * X.conjTranspose * X
            = (isometricConjMatrix V ρ * X.conjTranspose) * X from rfl]
    rw [Matrix.trace_mul_comm (isometricConjMatrix V ρ * X.conjTranspose) X]
    rw [← Matrix.mul_assoc]
  rw [hcyc]
  have h_sandwich : (X * isometricConjMatrix V ρ * X.conjTranspose).PosSemidef :=
    (isometricConjMatrix_posSemidef V ρ).mul_mul_conjTranspose_same X
  have h_trace_nn : (0 : ℂ) ≤ (X * isometricConjMatrix V ρ * X.conjTranspose).trace :=
    h_sandwich.trace_nonneg
  have := (Complex.le_def.mp h_trace_nn).1
  simpa using this

end RectangularIsometryDensity

/-! ## 5. The rectangular gate

The general statement of isometric invariance, as a `Prop`-target.
Closing this gate would discharge the load-bearing analytic fact
of the Stinespring lift unconditionally. -/

section RectangularGate

/-- **Isometric invariance of Umegaki relative entropy
    — general (rectangular) target.**

    For all `m, n : ℕ`, all isometries `V : Matrix (Fin m) (Fin n) ℂ`
    (`V† V = I`), and all `ρ σ : ComplexDensityMatrix n`,

        S(V ρ V†  ‖  V σ V†)  =  S(ρ ‖ σ),

    where the LHS is the trace formula
    `Re Tr( (V ρ V†) · (log (V ρ V†) − log (V σ V†)) )`
    directly on matrices.

    The trace-PSD field and the underlying Hermitian / trace 1
    facts are supplied unconditionally by the `isometricConjMatrix_*`
    lemmas; closing this gate is purely the spectral-CFC step,
    `cfc Real.log (V σ V†) = V (cfc Real.log σ.M) V† + …`. -/
def umegakiRelativeEntropy_isometric_invariant_Target : Prop :=
  ∀ {m n : ℕ} (V : Matrix (Fin m) (Fin n) ℂ) (_hV : IsIsometry V)
    (ρ σ : ComplexDensityMatrix n),
    (Matrix.trace
        (isometricConjMatrix V ρ
          * (cfc Real.log (isometricConjMatrix V ρ)
              - cfc Real.log (isometricConjMatrix V σ)))).re
      = umegakiRelativeEntropy ρ σ

/-- **The square (n = m) case of the rectangular gate is closed
    unconditionally.**

    When `m = n`, the isometric-invariance reduces to
    unitary-invariance via
    `umegakiRelativeEntropy_square_isometric_invariant`.
    This delivers the square slice of
    `umegakiRelativeEntropy_isometric_invariant_Target`,
    leaving only the strict-rectangular case `m > n`. -/
theorem umegakiRelativeEntropy_isometric_invariant_square
    {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ) (hV : IsIsometry V)
    (ρ σ : ComplexDensityMatrix n) :
    (Matrix.trace
        (isometricConjMatrix V ρ
          * (cfc Real.log (isometricConjMatrix V ρ)
              - cfc Real.log (isometricConjMatrix V σ)))).re
      = umegakiRelativeEntropy ρ σ := by
  -- Identify `isometricConjMatrix V ρ` with `(squareIsometryConjugate hV ρ).M`
  -- and `cfc Real.log` on it with `operatorLog`.  Rewrite the `cfc` calls
  -- first, then the conjugated-matrix factor.
  have hLogρ : cfc Real.log (isometricConjMatrix V ρ)
             = operatorLog (squareIsometryConjugate hV ρ) := by
    change cfc Real.log (isometricConjMatrix V ρ)
         = cfcρ Real.log (squareIsometryConjugate hV ρ)
    unfold isometricConjMatrix cfcρ
    rw [squareIsometryConjugate_M]
  have hLogσ : cfc Real.log (isometricConjMatrix V σ)
             = operatorLog (squareIsometryConjugate hV σ) := by
    change cfc Real.log (isometricConjMatrix V σ)
         = cfcρ Real.log (squareIsometryConjugate hV σ)
    unfold isometricConjMatrix cfcρ
    rw [squareIsometryConjugate_M]
  have hConjρ : isometricConjMatrix V ρ = (squareIsometryConjugate hV ρ).M := by
    unfold isometricConjMatrix
    rw [squareIsometryConjugate_M]
  rw [hLogρ, hLogσ, hConjρ]
  -- Now the LHS is exactly umegakiRelativeEntropy of the conjugated states.
  change umegakiRelativeEntropy
            (squareIsometryConjugate hV ρ) (squareIsometryConjugate hV σ)
        = umegakiRelativeEntropy ρ σ
  exact umegakiRelativeEntropy_square_isometric_invariant hV ρ σ

end RectangularGate

/-! ## 6. Honest scoping note

The rectangular gate captures the genuinely-hard analytic content:
the unital-CFC interchange of `cfc Real.log` with `V (·) V†` when
`V V† ≠ 1` (i.e. when `V` is not a unitary).  Two routes for
discharging the gate are sketched at the top of this file.

The square case — `umegakiRelativeEntropy_square_isometric_invariant`
— is the unconditional payoff, suffices for all applications where
the Stinespring dilation lives on a square block (e.g. when the
ancilla and the system have the same dimension), and discharges
trivially through `umegakiRelativeEntropy_unitary_invariant`. -/

/-- **Scoping note A — what this file unconditionally delivers.**

      1. `square_isometry_mem_unitaryGroup` — IsIsometry → unitary
         on square matrices.
      2. `squareIsometryConjugate ρ`        — `V ρ V†` packaged as
                                              a `ComplexDensityMatrix n`
                                              when `V` is a square
                                              isometry.
      3. `umegakiRelativeEntropy_square_isometric_invariant`
         — `S(V ρ V† ‖ V σ V†) = S(ρ ‖ σ)` for square isometries,
            closed unconditionally via unitary invariance.
      4. `isometricConjMatrix_*`            — `V ρ V†` is
                                              Hermitian, trace-1,
                                              PSD, and trace-PSD
                                              for ANY (rectangular)
                                              isometry, all four
                                              fields unconditional.

  No `sorry`, no custom `axiom`. -/
-- ⚠️ AUDIT-FLAG (TRIVIAL TARGET): `: True := trivial` documentation placeholder, NOT a theorem and
-- NOT a discharge. The genuinely-proved invariance is the SQUARE (unitary) case
-- `umegakiRelativeEntropy_square_isometric_invariant`. Do not read this placeholder as a result.
theorem scopingNote_unconditional_payoff : True := trivial

/-- **Scoping note B — the rectangular gate.**

    `umegakiRelativeEntropy_isometric_invariant_Target` — the
    rectangular isometric-invariance statement.  Closing it
    requires either:
       • a unitary extension of `V` (Route A:
         `Orthonormal.exists_orthonormalBasis_extension`); or
       • non-unital `map_cfcₙ` machinery (Route B).

    Estimated work: ~200–400 lines of CFC plumbing in either route.
    The named gate composes cleanly with
    `KrausMeasurementDPIBridge_Target` in
    `StinespringMeasurementDPI.lean`. -/
-- ⚠️ AUDIT-FLAG (TRIVIAL TARGET): `: True := trivial` documentation placeholder, NOT a theorem and
-- NOT a discharge. The rectangular (true-isometry) invariance is the OPEN
-- `umegakiRelativeEntropy_isometric_invariant_Target`; only the square (unitary) case is proved
-- (`umegakiRelativeEntropy_square_isometric_invariant`). Do not read this placeholder as a result.
theorem scopingNote_rectangular_gate : True := trivial

/-! ## 7. Axiom audit (post-build verification)

  Uncomment locally to verify:

    #print axioms square_isometry_mem_unitaryGroup
    #print axioms umegakiRelativeEntropy_square_isometric_invariant
    #print axioms isometricConjMatrix_isHermitian
    #print axioms isometricConjMatrix_trace
    #print axioms isometricConjMatrix_posSemidef
    #print axioms isometricConjMatrix_tracePSD
    #print axioms umegakiRelativeEntropy_isometric_invariant_square

  All should depend only on Lean's three standard axioms
  `propext, Classical.choice, Quot.sound`.  No `sorry`, no
  custom `axiom`. -/

end UnifiedTheory.LayerB.UmegakiIsometricInvariance
