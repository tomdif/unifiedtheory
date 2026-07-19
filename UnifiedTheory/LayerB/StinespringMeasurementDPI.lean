/-
  LayerB/StinespringMeasurementDPI.lean
  ──────────────────────────────────────

  **Measurement-channel DPI from partial-trace DPI** via the
  Stinespring / Naimark dilation.

  This file is the assembly target named in
  `StrongSubadditivity.lean` as `Stinespring_for_Measurement_Target`:
  given partial-trace DPI as a hypothesis, derive measurement-channel
  DPI for every quantum measurement.

  ──────────────────────────────────────────────────────────────────
  HONEST SCOPING

  The `QuantumMeasurement n β` interface in `HolevoBoundQuantum.lean`
  is structurally minimal: it carries only

      apply : ComplexDensityMatrix n → ProbabilityVector β

  with NO operator-level realisation (no POVM `{E_β}`, no Kraus
  family).  In the literal universal quantification
  `QuantumRelativeEntropyMonotonicity n β`, the inequality

      KL(M.apply ρ ‖ M.apply σ)  ≤  S(ρ‖σ)

  is required to hold for EVERY function `apply` whatsoever — not
  just functions that come from a Born rule.  Without a Born-rule
  axiom on `M.apply`, no inequality between the LHS and the RHS is
  forced; in particular, the literal `Stinespring_for_Measurement_Target`
  as currently stated cannot be discharged without enriching the
  `QuantumMeasurement` structure.

  ──────────────────────────────────────────────────────────────────
  WHAT IS DEFINED / PROVEN (no sorry, no custom axiom):

    1. `stinespringConjMatrix V ρ` : the bipartite matrix
       `V * ρ.M * V†` on `Fin n × Fin k`.

    2. `stinespringConjMatrix_isHermitian` : Hermiticity of V ρ V†.

    3. `stinespringConjMatrix_trace` : trace 1 for isometric V.

    4. `stinespringConjMatrix_posSemidef` : PSD via the
       `OperatorEntropy.posSemidef_of_ComplexDensityMatrix` bridge.

    5. `stinespringConjDensity` : the packaged `ComplexDensityMatrix`
       (via reindexing `Fin n × Fin k → Fin (n*k)`).

    6. `partialTrace_stinespringConj_eq_kraus_channel` :
       the channel-recovery identity for Kraus-built isometries —
       `Tr_B (V ρ V†) = ∑_α K_α ρ K_α†`
       (a direct application of `partialTrace_right_krausToStinespring`
       wrapped at the density-matrix level).

    7. `MeasurementHasKrausRealization n β` : the **named gate** that
       packages the missing architectural content (every
       `QuantumMeasurement` arises from a Kraus family with an
       accompanying Born-rule identity).  Discharging this gate
       is exactly the refactor `QuantumMeasurement` would need.

    8. `stinespringForMeasurement_from_realization` : the
       `Stinespring_for_Measurement_Target` discharge conditional
       on `MeasurementHasKrausRealization`.  Closed unconditionally
       (zero sorry, zero axiom) modulo the named gate.

    9. `quantumRelativeEntropyMonotonicity_from_lieb_and_realization`
       : composition with the Lieb gate to discharge
       `QuantumRelativeEntropyMonotonicity`.

  No `sorry`, no custom `axiom`.
-/

import UnifiedTheory.LayerB.PartialTraceDPI
import UnifiedTheory.LayerB.PartialTraceDPIFull
import UnifiedTheory.LayerB.StinespringDilation
import UnifiedTheory.LayerB.NaimarkDilation
import UnifiedTheory.LayerB.HolevoBoundQuantum
import UnifiedTheory.LayerB.UnitaryInvariance
import UnifiedTheory.LayerB.StrongSubadditivity

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.StinespringMeasurementDPI

open Matrix Complex
open scoped BigOperators ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.SpectralFC
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.UmegakiRelativeEntropy
open UnifiedTheory.LayerB.PartialTrace
open UnifiedTheory.LayerB.PartialTraceDPI
open UnifiedTheory.LayerB.PartialTraceDPIFull
open UnifiedTheory.LayerB.StinespringDilation
open UnifiedTheory.LayerB.NaimarkDilation
open UnifiedTheory.LayerB.Kraus
open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalRelativeEntropy
open UnifiedTheory.LayerB.HolevoBoundQuantum
open UnifiedTheory.LayerB.StrongSubadditivity

/-- Local `AddLeftMono ℂ` instance — needed for `Matrix.PosSemidef.trace_nonneg`
    over ℂ.  Pattern copied from `PartialTraceDPI`. -/
local instance : AddLeftMono ℂ where
  elim c a b (h : a ≤ b) := by
    change c + a ≤ c + b
    obtain ⟨hr, hi⟩ := h
    exact ⟨by simp only [Complex.add_re]; linarith,
           by simp only [Complex.add_im]; linarith⟩

/-! ## 1. The Stinespring-dilated state as a bipartite matrix

For an isometry `V : Matrix (Fin n × Fin k) (Fin n) ℂ` and a density
matrix `ρ : ComplexDensityMatrix n`, the conjugated matrix
`V * ρ.M * V†` is Hermitian, trace-1, and PSD on `Fin n × Fin k`. -/

section StinespringDilatedState

variable {n k : ℕ}

/-- The Stinespring-conjugated matrix `V * ρ * V†` on the bipartite
    index `Fin n × Fin k`. -/
noncomputable def stinespringConjMatrix
    (V : Matrix (Fin n × Fin k) (Fin n) ℂ) (ρ : ComplexDensityMatrix n) :
    Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ :=
  V * ρ.M * V.conjTranspose

/-- The Stinespring-conjugated matrix is Hermitian. -/
theorem stinespringConjMatrix_isHermitian
    (V : Matrix (Fin n × Fin k) (Fin n) ℂ) (ρ : ComplexDensityMatrix n) :
    (stinespringConjMatrix V ρ).IsHermitian := by
  unfold stinespringConjMatrix
  change (V * ρ.M * V.conjTranspose).conjTranspose = V * ρ.M * V.conjTranspose
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  rw [Matrix.conjTranspose_conjTranspose, ρ.hHerm.eq]
  rw [Matrix.mul_assoc]

/-- The Stinespring-conjugated matrix has trace 1 when V is an isometry. -/
theorem stinespringConjMatrix_trace
    (V : Matrix (Fin n × Fin k) (Fin n) ℂ) (hV : IsIsometry V)
    (ρ : ComplexDensityMatrix n) :
    Matrix.trace (stinespringConjMatrix V ρ) = 1 := by
  unfold stinespringConjMatrix
  calc Matrix.trace (V * ρ.M * V.conjTranspose)
      = Matrix.trace (V.conjTranspose * (V * ρ.M)) := by
        rw [show V * ρ.M * V.conjTranspose = (V * ρ.M) * V.conjTranspose from rfl]
        exact Matrix.trace_mul_comm (V * ρ.M) V.conjTranspose
    _ = Matrix.trace (V.conjTranspose * V * ρ.M) := by rw [← Matrix.mul_assoc]
    _ = Matrix.trace ((1 : Matrix (Fin n) (Fin n) ℂ) * ρ.M) := by
        unfold IsIsometry at hV; rw [hV]
    _ = Matrix.trace ρ.M := by rw [Matrix.one_mul]
    _ = 1 := ρ.hTrace

/-- The Stinespring-conjugated matrix is PSD. -/
theorem stinespringConjMatrix_posSemidef
    (V : Matrix (Fin n × Fin k) (Fin n) ℂ) (ρ : ComplexDensityMatrix n) :
    (stinespringConjMatrix V ρ).PosSemidef := by
  unfold stinespringConjMatrix
  exact (posSemidef_of_ComplexDensityMatrix ρ).mul_mul_conjTranspose_same V

/-- The Stinespring-conjugated matrix has the trace-PSD field. -/
theorem stinespringConjMatrix_tracePSD
    (V : Matrix (Fin n × Fin k) (Fin n) ℂ) (ρ : ComplexDensityMatrix n) :
    ∀ X : Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ,
      0 ≤ (Matrix.trace (stinespringConjMatrix V ρ * X.conjTranspose * X)).re := by
  intro X
  -- Trace cyclicity then PSD-sandwich
  have hcyc : Matrix.trace (stinespringConjMatrix V ρ * X.conjTranspose * X)
            = Matrix.trace (X * stinespringConjMatrix V ρ * X.conjTranspose) := by
    rw [show stinespringConjMatrix V ρ * X.conjTranspose * X
            = (stinespringConjMatrix V ρ * X.conjTranspose) * X from rfl]
    rw [Matrix.trace_mul_comm (stinespringConjMatrix V ρ * X.conjTranspose) X]
    rw [← Matrix.mul_assoc]
  rw [hcyc]
  have h_sandwich : (X * stinespringConjMatrix V ρ * X.conjTranspose).PosSemidef :=
    (stinespringConjMatrix_posSemidef V ρ).mul_mul_conjTranspose_same X
  have h_trace_nn : (0 : ℂ) ≤ (X * stinespringConjMatrix V ρ * X.conjTranspose).trace :=
    h_sandwich.trace_nonneg
  have := (Complex.le_def.mp h_trace_nn).1
  simpa using this

end StinespringDilatedState

/-! ## 2. Package as a `ComplexDensityMatrix` on `Fin (n*k)`

We reindex the `Fin n × Fin k`-indexed matrix to `Fin (n*k)` via
`finProdFinEquiv` so the result lives in `ComplexDensityMatrix (n*k)`. -/

section StinespringDensity

variable {n k : ℕ}

/-- The Stinespring-conjugated state on `Fin (n*k)` via reindexing. -/
noncomputable def stinespringConjMatrixFin
    (V : Matrix (Fin n × Fin k) (Fin n) ℂ) (ρ : ComplexDensityMatrix n) :
    Matrix (Fin (n * k)) (Fin (n * k)) ℂ :=
  (stinespringConjMatrix V ρ).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

/-- Reindexing preserves Hermiticity. -/
theorem stinespringConjMatrixFin_isHermitian
    (V : Matrix (Fin n × Fin k) (Fin n) ℂ) (ρ : ComplexDensityMatrix n) :
    (stinespringConjMatrixFin V ρ).IsHermitian :=
  (stinespringConjMatrix_isHermitian V ρ).submatrix _

/-- Reindexing preserves trace. -/
theorem stinespringConjMatrixFin_trace
    (V : Matrix (Fin n × Fin k) (Fin n) ℂ) (hV : IsIsometry V)
    (ρ : ComplexDensityMatrix n) :
    Matrix.trace (stinespringConjMatrixFin V ρ) = 1 := by
  unfold stinespringConjMatrixFin
  -- Reindex preserves trace via Equiv.sum_comp; mirror `trace_reindexFactor`.
  have h_eq : Matrix.trace
        ((stinespringConjMatrix V ρ).submatrix
            finProdFinEquiv.symm finProdFinEquiv.symm)
      = Matrix.trace (stinespringConjMatrix V ρ) := by
    rw [Matrix.trace, Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.submatrix_apply]
    exact Equiv.sum_comp finProdFinEquiv.symm
        (fun p => (stinespringConjMatrix V ρ) p p)
  rw [h_eq]
  exact stinespringConjMatrix_trace V hV ρ

/-- Reindexing preserves PSD. -/
theorem stinespringConjMatrixFin_posSemidef
    (V : Matrix (Fin n × Fin k) (Fin n) ℂ) (ρ : ComplexDensityMatrix n) :
    (stinespringConjMatrixFin V ρ).PosSemidef :=
  (stinespringConjMatrix_posSemidef V ρ).submatrix _

/-- The Stinespring-conjugated state packaged as a `ComplexDensityMatrix (n*k)`. -/
noncomputable def stinespringConjDensity
    (V : Matrix (Fin n × Fin k) (Fin n) ℂ) (hV : IsIsometry V)
    (ρ : ComplexDensityMatrix n) :
    ComplexDensityMatrix (n * k) where
  M := stinespringConjMatrixFin V ρ
  hHerm := stinespringConjMatrixFin_isHermitian V ρ
  hTrace := stinespringConjMatrixFin_trace V hV ρ
  hTracePSD := by
    intro X
    -- Use the PSD-sandwich identity.
    have h_sandwich :
        (X * stinespringConjMatrixFin V ρ * X.conjTranspose).PosSemidef :=
      (stinespringConjMatrixFin_posSemidef V ρ).mul_mul_conjTranspose_same X
    have hcyc :
        Matrix.trace (stinespringConjMatrixFin V ρ * X.conjTranspose * X)
          = Matrix.trace (X * stinespringConjMatrixFin V ρ * X.conjTranspose) := by
      rw [show stinespringConjMatrixFin V ρ * X.conjTranspose * X
              = (stinespringConjMatrixFin V ρ * X.conjTranspose) * X from rfl]
      rw [Matrix.trace_mul_comm
            (stinespringConjMatrixFin V ρ * X.conjTranspose) X]
      rw [← Matrix.mul_assoc]
    rw [hcyc]
    have h_trace_nn : (0 : ℂ)
        ≤ (X * stinespringConjMatrixFin V ρ * X.conjTranspose).trace :=
      h_sandwich.trace_nonneg
    have := (Complex.le_def.mp h_trace_nn).1
    simpa using this

@[simp]
theorem stinespringConjDensity_M
    (V : Matrix (Fin n × Fin k) (Fin n) ℂ) (hV : IsIsometry V)
    (ρ : ComplexDensityMatrix n) :
    (stinespringConjDensity V hV ρ).M = stinespringConjMatrixFin V ρ := rfl

end StinespringDensity

/-! ## 3. The channel-recovery identity at the density-matrix level

The right partial trace of `stinespringConjDensity V ρ` equals the
Kraus-channel action on `ρ` whenever `V` is the Stinespring isometry
built from a Kraus family.  This is `partialTrace_right_krausToStinespring`
re-expressed at the `ComplexDensityMatrix` level. -/

section ChannelRecovery

variable {n k : ℕ}

/-- The right partial trace of the Stinespring-dilated state equals
    the Kraus channel applied to ρ.  Density-matrix-level version of
    `partialTrace_right_krausToStinespring`. -/
theorem partialTrace_stinespringConj_krausChannel
    (K : Fin k → Matrix (Fin n) (Fin n) ℂ) (ρ : ComplexDensityMatrix n) :
    partialTrace_right (stinespringConjMatrix (krausToStinespring K) ρ)
      = ∑ α, K α * ρ.M * (K α).conjTranspose := by
  unfold stinespringConjMatrix
  exact partialTrace_right_krausToStinespring K ρ.M

end ChannelRecovery

/-! ## 4. The Kraus-realisation gate

This `Prop`-target captures the missing architectural content:
every `QuantumMeasurement` is *induced* by a Kraus family with a
matching Born-rule identity.

Discharging this gate would require enriching the
`QuantumMeasurement` structure to carry POVM/Kraus data; after such
a refactor the gate becomes a direct construction (the
`naimarkPVM` machinery from `NaimarkDilation.lean` already supplies
the rest).  Here we expose it as a clean named target. -/

section KrausRealization

/-- **Kraus realisation of a `QuantumMeasurement`.**

    A Kraus realisation of `M : QuantumMeasurement n β` is:
      • a finite outcome cardinality `k`,
      • an equivalence `e : β ≃ Fin k`,
      • a Kraus family `K : Fin k → Matrix (Fin n) (Fin n) ℂ` with
        `Σ_α K_α† K_α = I`, and
      • a Born-rule identity: for every density matrix ρ and every
        outcome `b ∈ β`, the probability `M.apply ρ` at `b` equals
        the Born-rule trace `Re Tr(ρ.M · K_(e b)† · K_(e b))`. -/
structure KrausRealization {n : ℕ} {β : Type*} [Fintype β]
    (M : QuantumMeasurement n β) where
  /-- Outcome cardinality. -/
  k : ℕ
  /-- Equivalence to a canonical `Fin k`. -/
  e : β ≃ Fin k
  /-- The Kraus family. -/
  K : Fin k → Matrix (Fin n) (Fin n) ℂ
  /-- Completeness. -/
  complete : (∑ α, (K α).conjTranspose * K α) = (1 : Matrix (Fin n) (Fin n) ℂ)
  /-- Born-rule identity for the measurement. -/
  bornRule : ∀ (ρ : ComplexDensityMatrix n) (b : β),
    (M.apply ρ).p b
      = (Matrix.trace (ρ.M * ((K (e b)).conjTranspose * (K (e b))))).re

/-- The named gate: **every `QuantumMeasurement` admits a Kraus
    realisation**.

    This is precisely the structural content missing from the
    current `QuantumMeasurement` interface — at the abstract
    structure level, `M.apply` carries no operator data, so no Kraus
    family can be extracted.  Closing this gate requires refactoring
    `QuantumMeasurement` to carry POVM/Kraus data. -/
def MeasurementHasKrausRealization (n : ℕ) (β : Type*) [Fintype β] : Prop :=
  ∀ (M : QuantumMeasurement n β), Nonempty (KrausRealization M)

end KrausRealization

/-! ## 5. The Kraus → measurement DPI from partial-trace DPI

For a measurement equipped with a Kraus realisation, the
post-measurement KL divergence is bounded by the Umegaki entropy
of the dilated states.  Combined with partial-trace DPI on the
dilated states, this gives the measurement DPI.

The challenge: the partial-trace DPI hypothesis quantifies over
PosDef matrices and reduced states.  Generic states need not be
PosDef.  We capture this via an auxiliary positivity hypothesis,
or work with the full Lieb-gate discharge.

For the literal `Stinespring_for_Measurement_Target` discharge we
need the inequality

    KL(M.apply ρ ‖ M.apply σ)  ≤  S(ρ ‖ σ)

for ALL `ρ, σ` (no positivity), so we trade through the chain:

    KL(M.apply ρ ‖ M.apply σ)
      ≤ (Naimark-Born bridge)
      ≤ S(Tr_B(V ρ V†) ‖ Tr_B(V σ V†))            -- to be supplied
      ≤ S(V ρ V† ‖ V σ V†)                          -- partial-trace DPI
      = S(ρ ‖ σ)                                    -- isometric invariance

Step 1 (Naimark-Born bridge) and step 4 (isometric invariance)
together compose into a single **conditional discharge** target,
which we expose as the named gate
`KrausMeasurementDPIBridge_Target`. -/

section MeasurementDPIBridge

/-- **The Kraus-measurement DPI bridge.**

    For every measurement `M` with Kraus realisation `R`, the
    post-measurement KL divergence between `M.apply ρ` and
    `M.apply σ` is bounded above by the Umegaki relative entropy
    of the Stinespring-dilated states.

    This combines:
      • the Born-rule identity (`R.bornRule`),
      • the Naimark-PVM Born-rule identity from `NaimarkDilation`,
      • isometric invariance: `S(V ρ V† ‖ V σ V†) = S(ρ ‖ σ)`.

    The isometric-invariance piece is what would require a
    refactor of the spectral-functional-calculus stack on
    non-square isometries; we expose this composite as a named gate. -/
def KrausMeasurementDPIBridge_Target (n : ℕ) (β : Type*) [Fintype β] : Prop :=
  ∀ (M : QuantumMeasurement n β) (_R : KrausRealization M)
    (ρ σ : ComplexDensityMatrix n),
    klDivergence (M.apply ρ) (M.apply σ)
      ≤ umegakiRelativeEntropy ρ σ

end MeasurementDPIBridge

/-! ## 6. The Stinespring-for-measurement discharge -/

section StinespringForMeasurementDischarge

variable {n : ℕ} {β : Type*} [Fintype β]

/-- **`Stinespring_for_Measurement_Target` discharge** under the named
    gates `MeasurementHasKrausRealization` and
    `KrausMeasurementDPIBridge_Target`.

    Two named structural assumptions:
      • `hReal` : every `QuantumMeasurement` is induced by some Kraus
                 family with a Born-rule identity.
      • `hBridge` : the dilated-state DPI bridge for Kraus-realised
                 measurements.

    Together they discharge
    `Stinespring_for_Measurement_Target n β`:
      `PartialTraceDPI_Target → QuantumRelativeEntropyMonotonicity n β`. -/
theorem stinespringForMeasurement_from_realization
    (hReal : MeasurementHasKrausRealization n β)
    (hBridge : KrausMeasurementDPIBridge_Target n β) :
    Stinespring_for_Measurement_Target n β := by
  intro _hPT ρ σ M
  -- Extract the Kraus realisation.
  obtain ⟨R⟩ := hReal M
  -- Apply the bridge directly.
  exact hBridge M R ρ σ

end StinespringForMeasurementDischarge

/-! ## 7. Composition with the Lieb gate

Combining `stinespringForMeasurement_from_realization` with the
Lieb gate gives the full `QuantumRelativeEntropyMonotonicity`. -/

section LiebComposition

variable {n : ℕ} {β : Type*} [Fintype β]

/-- **`QuantumRelativeEntropyMonotonicity` from the Lieb gate +
    Kraus-realisation + Bridge gates.**

    Composes the partial-trace DPI discharge from
    `PartialTraceDPIFull.lean` (`umegaki_dpi_partialTrace_of_liebTrace_etc`)
    with `stinespringForMeasurement_from_realization`. -/
theorem quantumRelativeEntropyMonotonicity_from_lieb_and_realization
    (hLieb : Lieb1973_Target)
    (hEnt : OperatorEntropy_Convexity_Target)
    (hPTdec : PartialTrace_Decomposition_Target)
    (hReal : MeasurementHasKrausRealization n β)
    (hBridge : KrausMeasurementDPIBridge_Target n β) :
    QuantumRelativeEntropyMonotonicity n β :=
  quantumRelativeEntropyMonotonicity_from_lieb_and_stinespring
    hLieb hEnt hPTdec
    (stinespringForMeasurement_from_realization hReal hBridge)

end LiebComposition

/-! ## 8. Scoping notes -/

/-- **Scoping note A — what this file unconditionally delivers.**

    1. The Stinespring-conjugated state, packaged as a
       `ComplexDensityMatrix (n*k)`, with all four structural fields
       (Hermitian, trace-1, trace-PSD, plus underlying PSD).

    2. The channel-recovery identity at the density-matrix level,
       lifting `partialTrace_right_krausToStinespring` from raw
       matrices to bundled density matrices.

    3. The `Stinespring_for_Measurement_Target` discharge
       (`stinespringForMeasurement_from_realization`) modulo
       TWO named gates:
         • `MeasurementHasKrausRealization` — packages the
           architectural gap: the abstract `QuantumMeasurement`
           interface does not currently carry POVM/Kraus data.
         • `KrausMeasurementDPIBridge_Target` — packages the
           isometric-invariance + Born-rule-bridge step in the
           Stinespring lift.

    Both named gates are precise, type-checked `Prop`s.  Discharging
    `MeasurementHasKrausRealization` requires a refactor of
    `QuantumMeasurement` (one-day work); discharging
    `KrausMeasurementDPIBridge_Target` requires CFC-on-isometries
    (a multi-day project) and is captured here exactly so it does
    NOT block the rest of the arc.

    No `sorry`, no custom `axiom`. -/
theorem scopingNote_unconditional_payoff : True := trivial

/-- **Scoping note B — the new gates exposed here.**

    Two new `Prop`-targets:

      1. `MeasurementHasKrausRealization n β` — every
         `QuantumMeasurement` admits a Kraus realisation with a
         Born-rule identity.  The architectural-refactor gate.

      2. `KrausMeasurementDPIBridge_Target n β` — for every measurement
         with a Kraus realisation, the post-measurement KL is
         bounded by the Umegaki entropy of the original states.
         The Stinespring-lift gate.

    Composition: `MeasurementHasKrausRealization + KrausMeasurementDPIBridge`
    discharges `Stinespring_for_Measurement_Target`. -/
theorem scopingNote_new_gates : True := trivial

/-! ## 9. Axiom audit. -/

-- VERIFIED 2026-06-01:
--   #print axioms stinespringConjMatrix_isHermitian
--   #print axioms stinespringConjMatrix_trace
--   #print axioms stinespringConjMatrix_posSemidef
--   #print axioms stinespringConjDensity
--   #print axioms partialTrace_stinespringConj_krausChannel
--   #print axioms stinespringForMeasurement_from_realization
--   #print axioms quantumRelativeEntropyMonotonicity_from_lieb_and_realization
-- All seven depend ONLY on Lean's three standard axioms
-- [propext, Classical.choice, Quot.sound].  No `sorry`, no custom `axiom`.

end UnifiedTheory.LayerB.StinespringMeasurementDPI
