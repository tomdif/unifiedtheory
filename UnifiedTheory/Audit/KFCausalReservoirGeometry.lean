/-
  Supporting finite algebra and estimates for reservoir preparation.
  The graph enumeration, half-line spectral transform, and escape limit
  are analytic/executable suppliers, not formalized by this module.
-/
import UnifiedTheory.Audit.KFCausalPatchGeometry
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalReservoirGeometry
noncomputable section
open scoped BigOperators Matrix
open Filter Topology

/-- A channel isometry retains the complete input, including its phases. -/
theorem isometry_recovery {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (T : Matrix A B ℂ) (hT : Tᴴ * T = 1) (v : B → ℂ) :
    Tᴴ *ᵥ (T *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, hT, Matrix.one_mulVec]

/-- In particular there is no unwanted vector invisible to every channel. -/
theorem isometry_no_dark {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (T : Matrix A B ℂ) (hT : Tᴴ * T = 1) (v : B → ℂ) (hz : T *ᵥ v = 0) :
    v = 0 := by
  have h := isometry_recovery T hT v
  rw [hz, Matrix.mulVec_zero] at h
  exact h.symm

/-- The same identity preserves overlaps between all input columns. -/
theorem isometry_preserves_gram {A B J : Type*} [Fintype A] [Fintype B]
    [DecidableEq B] (T : Matrix A B ℂ) (hT : Tᴴ * T = 1)
    (X Y : Matrix B J ℂ) : (T * X)ᴴ * (T * Y) = Xᴴ * Y := by
  rw [Matrix.conjTranspose_mul]
  calc
    (Xᴴ * Tᴴ) * (T * Y) = Xᴴ * ((Tᴴ * T) * Y) := by
      simp only [Matrix.mul_assoc]
    _ = Xᴴ * Y := by rw [hT, Matrix.one_mul]

/-- An energy-resolved move has the stated commutator, entry by entry. -/
theorem energy_filter_commutator {X : Type*} [Fintype X] [DecidableEq X]
    (d : X → ℂ) (M : Matrix X X ℂ) (r : ℂ)
    (hdrop : ∀ i j, M i j ≠ 0 → d i = d j - r) :
    Matrix.diagonal d * M - M * Matrix.diagonal d = (-r) • M := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.smul_apply, smul_eq_mul]
  by_cases h : M i j = 0
  · simp [h]
  · rw [hdrop i j h]
    ring

/-- Equal and opposite graph/bath energy shifts conserve their sum. -/
theorem exchange_energy_conservation {X : Type*} [Fintype X]
    (A B M : Matrix X X ℂ) (r : ℂ)
    (hA : A * M - M * A = (-r) • M)
    (hB : B * M - M * B = r • M) :
    (A + B) * M - M * (A + B) = 0 := by
  calc
    _ = (A * M - M * A) + (B * M - M * B) := by
      rw [add_mul, mul_add]
      abel
    _ = 0 := by rw [hA, hB, ← add_smul]; simp

/-- A positive-drop filter vanishes on a column whose possible moves
all preserve the potential. Graph recognition supplies the plateau. -/
theorem plateau_column_vanishes {X : Type*} (d : X → ℝ)
    (M : Matrix X X ℂ) (j : X) (r : ℝ) (hr : 0 < r)
    (hdrop : ∀ i, M i j ≠ 0 → d i = d j - r)
    (hflat : ∀ i, M i j ≠ 0 → d i = d j) : ∀ i, M i j = 0 := by
  intro i
  by_contra h
  have hd := hdrop i h
  have hf := hflat i h
  linarith

/-- A return-amplitude truncation estimate gives a whole-window bound. -/
theorem amplitude_error_bound (finite infinite u delta : ℝ)
    (hi : |infinite| ≤ u) (he : |finite - infinite| ≤ delta) :
    |finite| ≤ u + delta := by
  calc
    |finite| = |(finite - infinite) + infinite| := by congr 1; ring
    _ ≤ |finite - infinite| + |infinite| := abs_add_le _ _
    _ ≤ u + delta := by linarith

/-- Applies to the real boundary return amplitude after removing gap phase. -/
theorem probability_retention_bound (p0 amplitude u : ℝ)
    (hp : 0 ≤ p0) (ha : |amplitude| ≤ u) :
    p0 * amplitude ^ 2 ≤ p0 * u ^ 2 := by
  apply mul_le_mul_of_nonneg_left _ hp
  have h := abs_le.mp ha
  nlinarith [sq_nonneg (u - amplitude), sq_nonneg (u + amplitude)]

/-- The analytic finite-chain tail is < 1/1000 for R=128 and kappa*T=20. -/
theorem toy_retention_certificate : ((1 : ℝ) / 11 + 1 / 1000) ^ 2 < 1 / 100 := by
  norm_num

/-- Decay of the supplied return amplitude yields class preparation.
This asserts no stationary limit for the full reservoir wavepacket. -/
theorem asymptotic_class_preparation (a : ℝ → ℝ) (p0 : ℝ)
    (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun t => 1 - p0 * a t ^ 2) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub ((ha.pow 2).const_mul p0)
  simpa using h

#print axioms isometry_recovery
#print axioms isometry_no_dark
#print axioms isometry_preserves_gram
#print axioms energy_filter_commutator
#print axioms exchange_energy_conservation
#print axioms plateau_column_vanishes
#print axioms amplitude_error_bound
#print axioms probability_retention_bound
#print axioms toy_retention_certificate
#print axioms asymptotic_class_preparation

end
end UnifiedTheory.Audit.KFCausalReservoirGeometry
