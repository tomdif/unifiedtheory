/-
# Gleason's Theorem (1957)

Every countably-additive probability measure on the projection lattice of a
Hilbert space of dimension `≥ 3` is given by the Born rule
`μ(P) = Tr(ρ P)` for a unique density operator `ρ`.

## What is closed unconditionally

The **easy (Born) direction**: every density matrix `ρ` induces a valid
projection measure `μ_ρ(P) = Re Tr(ρ P)` — additive (in full, not just on
orthogonal projections), normalized (`μ_ρ(I) = Tr ρ = 1`), and non-negative
on projections (the load-bearing step, using the trace-PSD field of
`ComplexDensityMatrix`).

## Named targets (honest scoping of the deep mathematics)

* `Gleason_Target` — the HARD direction: in dimension `≥ 3` every projection
  measure is Born.  The genuine content of Gleason's theorem; its proof
  requires the frame-function regularity argument (continuity on the sphere
  + the 3-dim "no non-continuous frame function" lemma).
* `Gleason_Fails_Dim2` — the dimension restriction is sharp: in dimension 2
  there are non-Born frame functions.
* `Gleason_implies_KS_Target` — Gleason rules out `{0,1}`-valued measures,
  hence implies Kochen–Specker.

All theorems depend only on `propext`, `Classical.choice`, `Quot.sound`.
Zero `sorry`, zero custom `axiom`.
-/

import UnifiedTheory.LayerB.RobertsonSchrodinger

namespace UnifiedTheory.LayerB.GleasonTheorem

open Matrix
open UnifiedTheory.LayerB.RobertsonSchrodinger
open scoped BigOperators

variable {n : ℕ}

/-- A matrix is a projection when it is Hermitian and idempotent. -/
def IsProjection (P : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  P.IsHermitian ∧ P * P = P

/-- A (finitely-additive) measure on projections of `ℂ^n`. -/
structure ProjectionMeasure (n : ℕ) where
  /-- The measure assigns a real number to each matrix (used on projections). -/
  μ : Matrix (Fin n) (Fin n) ℂ → ℝ
  /-- Non-negative on projections. -/
  nonneg : ∀ P, IsProjection P → 0 ≤ μ P
  /-- Normalized: the whole space has measure 1. -/
  normalized : μ 1 = 1
  /-- Additive on orthogonal projections. -/
  additive : ∀ P Q, IsProjection P → IsProjection Q → P * Q = 0 →
    μ (P + Q) = μ P + μ Q

/-- The Born measure of a density matrix: `μ_ρ(P) = Re Tr(ρ P)`. -/
noncomputable def bornMeasure (ρ : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ → ℝ :=
  fun P => (Matrix.trace (ρ * P)).re

/-- The Born measure is additive on ALL pairs (stronger than orthogonal-only). -/
theorem bornMeasure_additive (ρ P Q : Matrix (Fin n) (Fin n) ℂ) :
    bornMeasure ρ (P + Q) = bornMeasure ρ P + bornMeasure ρ Q := by
  unfold bornMeasure
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]

/-- The Born measure is linear under scaling. -/
theorem bornMeasure_smul (c : ℝ) (ρ P : Matrix (Fin n) (Fin n) ℂ) :
    bornMeasure ρ ((c : ℂ) • P) = c * bornMeasure ρ P := by
  unfold bornMeasure
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.mul_re]
  simp

/-- The Born measure of the identity equals `Tr ρ`; for a density matrix this is 1. -/
theorem bornMeasure_normalized (ρ : ComplexDensityMatrix n) :
    bornMeasure ρ.M 1 = 1 := by
  unfold bornMeasure
  rw [Matrix.mul_one, ρ.hTrace]
  simp

/-- **Load-bearing step.** The Born measure is non-negative on projections.

For a projection `P = P† · P` (since `P` is Hermitian and idempotent), so
`ρ · P = ρ · P† · P`, and the trace-PSD field of the density matrix gives
`Re Tr(ρ · P† · P) ≥ 0`. -/
theorem bornMeasure_nonneg (ρ : ComplexDensityMatrix n)
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsProjection P) :
    0 ≤ bornMeasure ρ.M P := by
  obtain ⟨hHerm, hIdem⟩ := hP
  unfold bornMeasure
  -- Rewrite P = P† * P : Hermitian gives P† = P, idempotent gives P*P = P.
  have hPP : ρ.M * P = ρ.M * P.conjTranspose * P := by
    rw [hHerm.eq, Matrix.mul_assoc, hIdem]
  rw [hPP]
  exact ρ.hTracePSD P

/-- The Born measure of a density matrix is a valid `ProjectionMeasure`
    — the easy direction of Gleason's theorem. -/
noncomputable def bornMeasure_is_projectionMeasure (ρ : ComplexDensityMatrix n) :
    ProjectionMeasure n where
  μ := bornMeasure ρ.M
  nonneg := bornMeasure_nonneg ρ
  normalized := bornMeasure_normalized ρ
  additive := fun P Q _ _ _ => bornMeasure_additive ρ.M P Q

/-- **Gleason's theorem (hard direction, named target).**
    In dimension `≥ 3`, every projection measure is Born. -/
def Gleason_Target : Prop :=
  ∀ {n : ℕ}, 3 ≤ n → ∀ (m : ProjectionMeasure n),
    ∃ ρ : ComplexDensityMatrix n,
      ∀ P, IsProjection P → m.μ P = bornMeasure ρ.M P

/-- **Sharpness of the dimension hypothesis (named target).**
    In dimension 2 there exist non-Born projection measures. -/
def Gleason_Fails_Dim2 : Prop :=
  ∃ (m : ProjectionMeasure 2),
    ¬ ∃ ρ : ComplexDensityMatrix 2,
      ∀ P, IsProjection P → m.μ P = bornMeasure ρ.M P

/-- **Gleason ⟹ Kochen–Specker (named target).**
    In dimension `≥ 3` there is no `{0,1}`-valued projection measure. -/
def Gleason_implies_KS_Target : Prop :=
  ∀ {n : ℕ}, 3 ≤ n → ∀ (m : ProjectionMeasure n),
    ¬ ∀ P, IsProjection P → (m.μ P = 0 ∨ m.μ P = 1)

/-- Master theorem: the unconditional Born direction together with the three
    named targets that capture the deep content of Gleason's theorem. -/
theorem gleason_master :
    (∀ (ρ : ComplexDensityMatrix n) (P Q : Matrix (Fin n) (Fin n) ℂ),
      bornMeasure ρ.M (P + Q) = bornMeasure ρ.M P + bornMeasure ρ.M Q) ∧
    (∀ (ρ : ComplexDensityMatrix n), bornMeasure ρ.M 1 = 1) ∧
    (∀ (ρ : ComplexDensityMatrix n) (P : Matrix (Fin n) (Fin n) ℂ),
      IsProjection P → 0 ≤ bornMeasure ρ.M P) := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun ρ P Q => bornMeasure_additive ρ.M P Q
  · exact bornMeasure_normalized
  · exact bornMeasure_nonneg

end UnifiedTheory.LayerB.GleasonTheorem
