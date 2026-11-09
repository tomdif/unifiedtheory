/-
  Constructive finite-time elimination of a fast constraint penalty.
  The correction is obtained by solving D E = F J - J K. Its residual
  is computed, not assumed small. The exponential-flow theorem below
  discharges the differential-equation and norm hypotheses for bounded
  skew-adjoint generators on real Hilbert spaces (including realified
  quantum systems). Uniformity in particle cutoff/volume is separate.
-/
import UnifiedTheory.Audit.KFCausalDynamicalClosure
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalFastPenaltyDynamics
noncomputable section

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The finite correction need not itself be an isometry. The final bound
compares the original encoding, so no normalization is hidden here. -/
def dressed (J correction : E →L[ℝ] F) (Λ : ℝ) : E →L[ℝ] F :=
  J - Λ⁻¹ • correction

theorem correction_from_partial_inverse
    (D S L P : F →L[ℝ] F) (K : E →L[ℝ] E) (J : E →L[ℝ] F)
    (hL : D.comp L = 1 - P) (hK : P.comp (S.comp J) = J.comp K) :
    D.comp (L.comp (S.comp J)) = S.comp J - J.comp K := by
  rw [← ContinuousLinearMap.comp_assoc, hL]
  simp [ContinuousLinearMap.sub_comp, hK]
  ext x
  rfl

/-- First-order dressing cancels the entire bare leakage exactly. -/
theorem dressed_residual_identity
    (D S : F →L[ℝ] F) (K : E →L[ℝ] E) (J correction : E →L[ℝ] F)
    (hzero : D.comp J = 0)
    (hsolve : D.comp correction = S.comp J - J.comp K)
    (Λ : ℝ) (hΛ : Λ ≠ 0) :
    (Λ • D + S).comp (dressed J correction Λ) -
      (dressed J correction Λ).comp K =
        Λ⁻¹ • (correction.comp K - S.comp correction) := by
  simp only [dressed, ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.sub_comp, hzero, hsolve, smul_sub, smul_add, smul_zero,
    smul_smul, inv_mul_cancel₀ hΛ, one_smul]
  abel

theorem dressed_distance (J correction : E →L[ℝ] F) (Λ : ℝ) (hΛ : 0 < Λ) :
    ‖J - dressed J correction Λ‖ = ‖correction‖ / Λ := by
  simp [dressed, norm_smul, Real.norm_eq_abs, abs_of_pos hΛ, div_eq_inv_mul]

theorem dressed_residual_norm
    (D S : F →L[ℝ] F) (K : E →L[ℝ] E) (J correction : E →L[ℝ] F)
    (hzero : D.comp J = 0)
    (hsolve : D.comp correction = S.comp J - J.comp K)
    (Λ : ℝ) (hΛ : 0 < Λ) :
    ‖(Λ • D + S).comp (dressed J correction Λ) -
      (dressed J correction Λ).comp K‖ =
        ‖correction.comp K - S.comp correction‖ / Λ := by
  rw [dressed_residual_identity D S K J correction hzero hsolve Λ hΛ.ne']
  simp [norm_smul, Real.norm_eq_abs, abs_of_pos hΛ, div_eq_inv_mul]

theorem dressed_residual_bound
    (D S : F →L[ℝ] F) (K : E →L[ℝ] E) (J correction : E →L[ℝ] F)
    (hzero : D.comp J = 0)
    (hsolve : D.comp correction = S.comp J - J.comp K)
    (Λ : ℝ) (hΛ : 0 < Λ) :
    ‖(Λ • D + S).comp (dressed J correction Λ) -
      (dressed J correction Λ).comp K‖ ≤
        (‖correction‖ * ‖K‖ + ‖S.comp correction‖) / Λ := by
  rw [dressed_residual_identity D S K J correction hzero hsolve Λ hΛ.ne',
    norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hΛ]
  have h := (norm_sub_le (correction.comp K) (S.comp correction)).trans
    (add_le_add (ContinuousLinearMap.opNorm_comp_le correction K) (le_refl _))
  simpa [div_eq_inv_mul] using mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hΛ.le)

private theorem change_encoding
    (U : F →L[ℝ] F) (V : E →L[ℝ] E) (J J₀ : E →L[ℝ] F)
    (η error : ℝ) (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1)
    (hJ : ‖J₀ - J‖ ≤ η) (herror : ‖U.comp J - J.comp V‖ ≤ error) :
    ‖U.comp J₀ - J₀.comp V‖ ≤ error + 2 * η := by
  have hη : 0 ≤ η := (norm_nonneg _).trans hJ
  have hid : U.comp J₀ - J₀.comp V =
      U.comp (J₀-J) + (U.comp J - J.comp V) + (J-J₀).comp V := by
    ext x
    simp
  have hl : ‖U.comp (J₀-J)‖ ≤ η := by
    calc
      _ ≤ ‖U‖ * ‖J₀-J‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * η := mul_le_mul hU hJ (norm_nonneg _) (by norm_num)
      _ = η := one_mul _
  have hr : ‖(J-J₀).comp V‖ ≤ η := by
    calc
      _ ≤ ‖J-J₀‖ * ‖V‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ η * 1 := mul_le_mul (by simpa [norm_sub_rev] using hJ) hV (norm_nonneg _) hη
      _ = η := mul_one _
  rw [hid]
  have h₁ := norm_add_le (U.comp (J₀-J)) (U.comp J - J.comp V)
  have h₂ := norm_add_le
    (U.comp (J₀-J) + (U.comp J - J.comp V)) ((J-J₀).comp V)
  linarith

/-- A bound for the bare encoded evolution. It uses only S on the correction
range, avoiding an unnecessary full-space norm of the slow Hamiltonian. -/
theorem penalty_flow_error_le
    (D S : F →L[ℝ] F) (K : E →L[ℝ] E) (J correction : E →L[ℝ] F)
    (hzero : D.comp J = 0)
    (hsolve : D.comp correction = S.comp J - J.comp K)
    (Λ : ℝ) (hΛ : 0 < Λ)
    (U : ℝ → F →L[ℝ] F) (V : ℝ → E →L[ℝ] E)
    (hU0 : U 0 = 1) (hV0 : V 0 = 1)
    (hUd : ∀ s, HasDerivAt U ((U s).comp (Λ • D + S)) s)
    (hVd : ∀ s, HasDerivAt V (K.comp (V s)) s)
    (hU : ∀ s, 0 ≤ s → ‖U s‖ ≤ 1)
    (hV : ∀ s, 0 ≤ s → ‖V s‖ ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖(U t).comp J - J.comp (V t)‖ ≤
      (t * ‖correction.comp K - S.comp correction‖ + 2 * ‖correction‖) / Λ := by
  have hd := KFCausalDynamicalClosure.continuous_time_error_le
    (Λ • D + S) K (dressed J correction Λ) U V hU0 hV0 hUd hVd hU hV
    _ (dressed_residual_norm D S K J correction hzero hsolve Λ hΛ).le t ht
  have he := change_encoding (U t) (V t) (dressed J correction Λ) J
    _ _ (hU t ht) (hV t ht) (dressed_distance J correction Λ hΛ).le hd
  convert he using 1
  ring

section Hilbert
variable {H G : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G] [Nontrivial G]

theorem skew_exp_norm (A : H →L[ℝ] H) (hA : A ∈ skewAdjoint (H →L[ℝ] H)) (t : ℝ) :
    ‖NormedSpace.exp (t • A)‖ = 1 := by
  letI : NormedAlgebra ℚ (H →L[ℝ] H) := .restrictScalars ℚ ℝ _
  exact CStarRing.norm_of_mem_unitary
    (NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem t hA))

/-- Fully specified bounded exponential flows: no evolution or contraction
axioms are supplied. For quantum use, realify the generators -iH. -/
theorem penalty_exponential_error_le
    (D S : H →L[ℝ] H) (K : G →L[ℝ] G) (J correction : G →L[ℝ] H)
    (hD : D ∈ skewAdjoint (H →L[ℝ] H))
    (hS : S ∈ skewAdjoint (H →L[ℝ] H))
    (hK : K ∈ skewAdjoint (G →L[ℝ] G))
    (hzero : D.comp J = 0)
    (hsolve : D.comp correction = S.comp J - J.comp K)
    (Λ : ℝ) (hΛ : 0 < Λ) (t : ℝ) (ht : 0 ≤ t) :
    ‖(NormedSpace.exp (t • (Λ • D + S))).comp J -
        J.comp (NormedSpace.exp (t • K))‖ ≤
      (t * ‖correction.comp K - S.comp correction‖ + 2 * ‖correction‖) / Λ := by
  have hA := (skewAdjoint (H →L[ℝ] H)).add_mem (skewAdjoint.smul_mem Λ hD) hS
  exact penalty_flow_error_le D S K J correction hzero hsolve Λ hΛ
    (fun s => NormedSpace.exp (s • (Λ • D + S)))
    (fun s => NormedSpace.exp (s • K))
    (by simp) (by simp)
    (fun s => hasDerivAt_exp_smul_const (Λ • D + S) s)
    (fun s => hasDerivAt_exp_smul_const' K s)
    (fun s _ => (skew_exp_norm _ hA s).le)
    (fun s _ => (skew_exp_norm _ hK s).le) t ht

end Hilbert

#print axioms correction_from_partial_inverse
#print axioms dressed_residual_identity
#print axioms dressed_distance
#print axioms dressed_residual_norm
#print axioms dressed_residual_bound
#print axioms penalty_flow_error_le
#print axioms penalty_exponential_error_le

end
end UnifiedTheory.Audit.KFCausalFastPenaltyDynamics
