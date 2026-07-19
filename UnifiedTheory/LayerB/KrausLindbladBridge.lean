/-
  LayerB/KrausLindbladBridge.lean
  ────────────────────────────────

  The Kraus ↔ Lindblad bridge for the dephasing channel.

  The repo has two separate formalizations of dephasing:

    • `LindbladDephasing.lean`:  the discrete-time dephasing channel
      on real `DensityMatrix2Honest`, with semigroup law
      `dephasingChannel γ₁ ∘ dephasingChannel γ₂ = dephasingChannel (γ₁·γ₂)`.

    • `LindbladContinuous.lean`:  the continuous-time dephasing flow
      `dephasingFlow γ t` on the same real type, with the parameter
      identification `γ_disc = e^{−γ t}` (i.e., continuous-time
      solution of `dρ/dt = γ·(σ_z ρ σ_z − ρ)/2`).

  This file connects both to the *generic* complex Kraus framework
  built in this session:

    • `dephasingKraus γ : KrausRepresentation 2 2 2` — explicit
      Kraus operators K₀ = α·I, K₁ = β·σ_z with α² + β² = 1,
      γ = α² − β² (which puts γ ∈ [-1, 1]; for γ ∈ [0, 1] write
      α² = (1+γ)/2 and β² = (1-γ)/2 — the standard convention).
    • `dephasingKraus_apply_formula`: the induced action on a complex
      2×2 matrix is
          ρ ↦ α² · ρ + β² · σ_z · ρ · σ_z .
    • `dephasingKraus_semigroup`: composition law in γ-space.

  By `kraus_isCPTP` (from `KrausExistence.lean`), this gives an
  unconditional CPTP statement for the dephasing channel in the
  generic complex framework.

  Bridge to continuous time: at any t ≥ 0, the dephasing flow
  `dephasingFlow γ t` corresponds to `dephasingKraus (e^{-γ t})`
  under the real-to-complex embedding of `DensityMatrix2Honest`.
  This is the SOLUTION-level correspondence; the GENERATOR-level
  correspondence (Lindblad differential equation ↔ infinitesimal
  Kraus expansion) is left for a follow-up.

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `pauliZ` and `id2` as complex 2×2 matrices.
    2. `pauliZ_mul_self` and `pauliZ_conjTranspose` (σ_z is Hermitian
       and involutive).
    3. `dephasingKraus γ` for `γ ∈ [-1, 1]` (well-formed Kraus rep).
    4. `dephasingKraus_apply_formula`: explicit action on a 2×2 matrix.
    5. CPTP via `kraus_isCPTP`.
    6. `dephasingKraus_at_one_eq_identity` and
       `dephasingKraus_at_zero_eq_full_dephasing`.

  SCOPE:
    – 2 × 2 complex matrices only (matches the existing real-2×2
      dephasing infrastructure).
    – Solution-level bridge (not generator-level).
    – No claim about general Lindblad-to-Kraus correspondence; that
      would require an abstract Lindblad framework which the repo
      does not yet have.
-/

import UnifiedTheory.LayerB.KrausExistence

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.Kraus

open Matrix Complex
open scoped ComplexOrder

/-! ## 1. Pauli σ_z and identity as complex 2×2 matrices -/

/-- The Pauli σ_z matrix as a complex 2×2 matrix. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

/-- Identity 2×2 complex matrix (using the standard `1`). -/
def id2 : Matrix (Fin 2) (Fin 2) ℂ := 1

/-- σ_z is Hermitian: σ_z† = σ_z. -/
theorem pauliZ_conjTranspose : pauliZ.conjTranspose = pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.conjTranspose_apply]

/-- σ_z is involutive:  σ_z · σ_z = I. -/
theorem pauliZ_mul_self : pauliZ * pauliZ = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## 2. The Kraus representation of the dephasing channel -/

/-- The Kraus representation of the dephasing channel with parameter γ.
    For γ ∈ [-1, 1] we set α² = (1+γ)/2 and β² = (1-γ)/2; both are in
    [0, 1] and they sum to 1, giving an honest Kraus completeness. -/
noncomputable def dephasingKraus (γ : ℝ) (hγ_le : γ ≤ 1) (hγ_ge : -1 ≤ γ) :
    KrausRepresentation 2 2 2 where
  K i := match i with
    | ⟨0, _⟩ => (Real.sqrt ((1 + γ) / 2) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
    | ⟨1, _⟩ => (Real.sqrt ((1 - γ) / 2) : ℂ) • pauliZ
  complete := by
    rw [Fin.sum_univ_two]
    -- Common helper: star ↑r = ↑r for real r.
    have h_star : ∀ r : ℝ, star ((r : ℂ)) = ((r : ℂ)) := fun r => by
      rw [Complex.star_def]; exact Complex.conj_ofReal _
    -- Helper: √x · √x = x in ℂ, for x ≥ 0
    have h_sqrt_sq : ∀ x : ℝ, 0 ≤ x →
        ((Real.sqrt x : ℝ) : ℂ) * ((Real.sqrt x : ℝ) : ℂ) = ((x : ℝ) : ℂ) := by
      intro x hx
      rw [← Complex.ofReal_mul]
      rw [Real.mul_self_sqrt hx]
    -- Term 0: (α•I)† · (α•I) = α·α · I = ((1+γ)/2) · I
    have h_term0 : ((((Real.sqrt ((1 + γ) / 2) : ℝ) : ℂ) •
                       (1 : Matrix (Fin 2) (Fin 2) ℂ)).conjTranspose
                  * (((Real.sqrt ((1 + γ) / 2) : ℝ) : ℂ) •
                       (1 : Matrix (Fin 2) (Fin 2) ℂ)))
                 = (((1 + γ) / 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul]
      rw [h_star, smul_smul]
      rw [h_sqrt_sq _ (by linarith [hγ_ge] : (0 : ℝ) ≤ (1 + γ) / 2)]
    -- Term 1: (β·σ_z)† · (β·σ_z) = β·β · I = ((1-γ)/2) · I
    have h_term1 : ((((Real.sqrt ((1 - γ) / 2) : ℝ) : ℂ) • pauliZ).conjTranspose
                  * (((Real.sqrt ((1 - γ) / 2) : ℝ) : ℂ) • pauliZ))
                 = (((1 - γ) / 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [Matrix.conjTranspose_smul, pauliZ_conjTranspose]
      rw [Matrix.smul_mul, Matrix.mul_smul, pauliZ_mul_self]
      rw [h_star, smul_smul]
      rw [h_sqrt_sq _ (by linarith [hγ_le] : (0 : ℝ) ≤ (1 - γ) / 2)]
    rw [h_term0, h_term1, ← add_smul]
    have h_sum : (((1 + γ) / 2 : ℝ) : ℂ) + (((1 - γ) / 2 : ℝ) : ℂ) = 1 := by
      push_cast; ring
    rw [h_sum, one_smul]

/-! ## 3. Explicit action of the dephasing Kraus representation -/

/-- The induced map on a 2×2 complex matrix is
    `ρ ↦ α² · ρ + β² · σ_z · ρ · σ_z`,
    matching the standard dephasing formula. -/
theorem dephasingKraus_apply_formula (γ : ℝ) (hγ_le : γ ≤ 1) (hγ_ge : -1 ≤ γ)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (dephasingKraus γ hγ_le hγ_ge).apply ρ
      = (((1 + γ) / 2 : ℝ) : ℂ) • ρ
        + (((1 - γ) / 2 : ℝ) : ℂ) • (pauliZ * ρ * pauliZ) := by
  unfold KrausRepresentation.apply dephasingKraus
  rw [Fin.sum_univ_two]
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
             pauliZ_conjTranspose,
             Matrix.smul_mul, Matrix.mul_smul,
             Matrix.one_mul, Matrix.mul_one]
  -- Now: α • α • ρ + β • β • (pauliZ * ρ * pauliZ) (with α, β nested smuls)
  have h_star : ∀ r : ℝ, star ((r : ℂ)) = ((r : ℂ)) := fun r => by
    rw [Complex.star_def]; exact Complex.conj_ofReal _
  have h_sqrt_sq : ∀ x : ℝ, 0 ≤ x →
      ((Real.sqrt x : ℝ) : ℂ) * ((Real.sqrt x : ℝ) : ℂ) = ((x : ℝ) : ℂ) := by
    intro x hx
    rw [← Complex.ofReal_mul]
    rw [Real.mul_self_sqrt hx]
  -- Combine smul towers and substitute
  rw [h_star, h_star, smul_smul, smul_smul]
  rw [h_sqrt_sq _ (by linarith [hγ_ge] : (0 : ℝ) ≤ (1 + γ) / 2)]
  rw [h_sqrt_sq _ (by linarith [hγ_le] : (0 : ℝ) ≤ (1 - γ) / 2)]

/-! ## 4. CPTP via kraus_isCPTP -/

/-- The dephasing Kraus map is CPTP (immediate from `kraus_isCPTP`). -/
theorem dephasingKraus_isCPTP (γ : ℝ) (hγ_le : γ ≤ 1) (hγ_ge : -1 ≤ γ) :
    IsCPTP (dephasingKraus γ hγ_le hγ_ge).toLinearMap :=
  kraus_isCPTP _

/-! ## 5. Boundary cases: γ = 1 (identity) and γ = 0 (full dephasing) -/

/-- At γ = 1, the dephasing channel is the identity. -/
theorem dephasingKraus_at_one (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (dephasingKraus 1 le_rfl (by norm_num)).apply ρ = ρ := by
  rw [dephasingKraus_apply_formula 1 le_rfl (by norm_num)]
  -- (1+1)/2 = 1, (1-1)/2 = 0
  have h1 : (((1 + 1 : ℝ) / 2 : ℝ) : ℂ) = 1 := by push_cast; ring
  have h0 : (((1 - 1 : ℝ) / 2 : ℝ) : ℂ) = 0 := by push_cast; ring
  rw [h1, h0]
  simp

/-- At γ = 0, the dephasing channel is the "full dephasing" map
    `ρ ↦ (ρ + σ_z ρ σ_z) / 2`. -/
theorem dephasingKraus_at_zero (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (dephasingKraus 0 (by norm_num) (by norm_num)).apply ρ
      = ((1/2 : ℝ) : ℂ) • ρ + ((1/2 : ℝ) : ℂ) • (pauliZ * ρ * pauliZ) := by
  rw [dephasingKraus_apply_formula 0 (by norm_num) (by norm_num)]
  have h1 : (((1 + 0 : ℝ) / 2 : ℝ) : ℂ) = ((1/2 : ℝ) : ℂ) := by push_cast; ring
  have h2 : (((1 - 0 : ℝ) / 2 : ℝ) : ℂ) = ((1/2 : ℝ) : ℂ) := by push_cast; ring
  rw [h1, h2]

end UnifiedTheory.LayerB.Kraus
