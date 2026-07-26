/-
  LayerA/AdjointRunningDeterminant.lean — The single-plaquette adjoint running
  determinant: the connection-DEPENDENT part of the adjoint fermion measure.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  THE RUNNING HALF.

  `AdjointMasslessMeasure` located the massless mode as the exact zero of the
  adjoint measure operator `Ad_W − 1` — the Cartan direction with eigenvalue `1`.
  The RUNNING lives in the NONZERO eigenvalues: on the root direction `E_{ij}`
  (`i ≠ j`) the adjoint action of a diagonal holonomy `W = diag λ` has eigenvalue
  `λᵢ / λⱼ`, so the connection-dependent part of the one-loop adjoint determinant is

        det(1 − Ad_W)|_roots  =  ∏_{i≠j} (1 − λᵢ/λⱼ).

  This is a nonconstant function of the holonomy — the adjoint fermion measure is
  NOT a `W`-independent constant that would decouple; it RUNS.

  WHAT IS PROVED (zero sorry, zero custom axioms):
   • `diag_conj_eij` — `Ad` of a diagonal holonomy acts diagonally on the matrix
     units: `diag d · E_{ij} · diag e = (dᵢ eⱼ) • E_{ij}`.  With `e = λ⁻¹` this is
     the root eigenvalue `λᵢ/λⱼ`.
   • `su2Hol_mul_inv` — `diag(a, a⁻¹)` and `diag(a⁻¹, a)` are inverse: the SU(2)
     holonomy and its inverse.
   • `su2_root_eigenvalue_12` / `_21` — the two SU(2) root directions have adjoint
     eigenvalues `a²` and `a⁻²` (the triplet's off-Cartan spectrum).
   • `su2RunDet_runs` — the SU(2) (weak-triplet) running determinant
     `(1−a²)(1−a⁻²)` is NONCONSTANT in the holonomy: it is `0` at the trivial
     holonomy `a = 1` and `−9/4` at `a = 2`.  The adjoint mode runs.

  SCOPE (honest — the residual to a literal SM β-coefficient).  This computes the
  connection-DEPENDENCE of the discrete adjoint determinant (that it runs) and the
  triplet's root spectrum.  It does NOT fix the SIGN and MAGNITUDE of the β-
  function coefficient: that needs the fermionic measure entering with the
  opposite determinant power to the bosons (Grassmann integration) and the
  continuum limit turning the single-plaquette determinant into a literal RGE
  contribution — the refinement wall (R3).  So: unconditional that the adjoint
  measure runs and its off-Cartan spectrum; conditional (R3 + Grassmann power) the
  β-magnitude.  The octet (SU(3), 6 roots) is the direct analogue — see
  `scripts/adjoint_running_det.py` for its explicit nonconstant value.
-/
import Mathlib

set_option autoImplicit false

namespace UnifiedTheory.LayerA.AdjointRunningDeterminant

open Matrix

/-- Matrix unit `E_{ij}`: `1` at `(i,j)`, `0` elsewhere. The root direction of the
adjoint representation for `i ≠ j`. -/
def eij {n : ℕ} (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  fun r c => if r = i ∧ c = j then 1 else 0

/-- **Adjoint action of a diagonal holonomy on a matrix unit.**  Conjugation by
diagonals scales `E_{ij}` by `dᵢ eⱼ`.  With `e = λ⁻¹` (so `diag e = (diag λ)⁻¹`)
this is the root eigenvalue `λᵢ/λⱼ` of `Ad_W`. -/
theorem diag_conj_eij {n : ℕ} (d e : Fin n → ℝ) (i j : Fin n) :
    diagonal d * eij i j * diagonal e = (d i * e j) • eij i j := by
  ext k l
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
  show d k * eij i j k l * e l = d i * e j * eij i j k l
  unfold eij
  by_cases h : k = i ∧ l = j
  · obtain ⟨hk, hl⟩ := h; subst hk; subst hl; simp
  · simp only [h, if_false, mul_zero, zero_mul]

/-- The SU(2) holonomy `diag(a, a⁻¹)` and `diag(a⁻¹, a)` are inverse. -/
theorem su2Hol_mul_inv (a : ℝ) (ha : a ≠ 0) :
    diagonal ![a, a⁻¹] * diagonal ![a⁻¹, a] = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [Matrix.diagonal_mul_diagonal]
  rw [show (fun i => ![a, a⁻¹] i * ![a⁻¹, a] i) = (fun _ => (1:ℝ)) from ?_, ← Matrix.diagonal_one]
  funext i; fin_cases i <;> simp [mul_inv_cancel₀ ha, inv_mul_cancel₀ ha]

/-- **The first SU(2) root eigenvalue is `a²`.**  `Ad_{diag(a,a⁻¹)}` scales `E₁₂`
by `a²`. -/
theorem su2_root_eigenvalue_12 (a : ℝ) :
    diagonal ![a, a⁻¹] * eij 0 1 * diagonal ![a⁻¹, a] = (a ^ 2) • eij (0 : Fin 2) 1 := by
  rw [diag_conj_eij]
  congr 1
  simp [pow_two]

/-- **The second SU(2) root eigenvalue is `a⁻²`.**  `Ad_{diag(a,a⁻¹)}` scales `E₂₁`
by `a⁻²`. -/
theorem su2_root_eigenvalue_21 (a : ℝ) :
    diagonal ![a, a⁻¹] * eij 1 0 * diagonal ![a⁻¹, a] = ((a ^ 2)⁻¹) • eij (1 : Fin 2) 0 := by
  rw [diag_conj_eij]
  congr 1
  rw [show (![a, a⁻¹] : Fin 2 → ℝ) 1 = a⁻¹ from rfl, show (![a⁻¹, a] : Fin 2 → ℝ) 0 = a⁻¹ from rfl]
  rw [← mul_inv, ← pow_two]

/-- The SU(2) (weak-triplet) adjoint running determinant off the Cartan:
`∏_{roots}(1 − eigenvalue) = (1 − a²)(1 − a⁻²)`. -/
noncomputable def su2RunDet (a : ℝ) : ℝ := (1 - a ^ 2) * (1 - (a ^ 2)⁻¹)

/-- **The adjoint mode RUNS.**  The SU(2) running determinant is NONCONSTANT in the
holonomy — `0` at the trivial holonomy `a = 1`, `−9/4` at `a = 2` — so the adjoint
fermion measure is connection-dependent and does not decouple. -/
theorem su2RunDet_runs : su2RunDet 1 = 0 ∧ su2RunDet 2 = -9/4 ∧ su2RunDet 2 ≠ su2RunDet 1 := by
  refine ⟨by norm_num [su2RunDet], by norm_num [su2RunDet], ?_⟩
  rw [show su2RunDet 1 = 0 from by norm_num [su2RunDet],
      show su2RunDet 2 = -9/4 from by norm_num [su2RunDet]]
  norm_num

#print axioms diag_conj_eij
#print axioms su2_root_eigenvalue_12
#print axioms su2_root_eigenvalue_21
#print axioms su2RunDet_runs

end UnifiedTheory.LayerA.AdjointRunningDeterminant
