/-
  Quantitative obligations for deriving dynamics on a physical sector.

  The encoding J maps effective states into microscopic states. Small
  compressed matrix elements alone do not control dynamics: the full
  intertwining residual U J - J V must be small, including leakage.
  These theorems propagate that residual and transfer generator brackets.
  They do not supply a microscopic Hamiltonian or Einstein generators.
-/
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalDynamicalClosure
noncomputable section
open Filter Topology

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [Nontrivial E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F]

omit [Nontrivial E] in
/-- Exact telescoping step for two evolutions on different state spaces. -/
theorem evolution_defect_succ
    (U : F →L[ℂ] F) (V : E →L[ℂ] E) (J : E →L[ℂ] F) (k : ℕ) :
    (U^(k+1)).comp J - J.comp (V^(k+1)) =
      U.comp ((U^k).comp J - J.comp (V^k)) +
        (U.comp J - J.comp V).comp (V^k) := by
  ext x
  simp [pow_succ']

/-- Unitary evolutions are a special case of these contraction hypotheses.
The estimate is uniform over all input states, not only a fixed test vector. -/
theorem evolution_error_le
    (U : F →L[ℂ] F) (V : E →L[ℂ] E) (J : E →L[ℂ] F)
    (ε : ℝ) (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1)
    (hstep : ‖U.comp J - J.comp V‖ ≤ ε) (k : ℕ) :
    ‖(U^k).comp J - J.comp (V^k)‖ ≤ k * ε := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans hstep
  induction k with
  | zero =>
      simp only [pow_zero, Nat.cast_zero, zero_mul, norm_le_zero_iff]
      ext x
      simp
  | succ k ih =>
      rw [evolution_defect_succ]
      have hvk : ‖V^k‖ ≤ 1 :=
        (norm_pow_le V k).trans (pow_le_one₀ (norm_nonneg V) hV)
      calc
        _ ≤ ‖U.comp ((U^k).comp J - J.comp (V^k))‖ +
            ‖(U.comp J - J.comp V).comp (V^k)‖ := norm_add_le _ _
        _ ≤ ‖U‖ * ‖(U^k).comp J - J.comp (V^k)‖ +
            ‖U.comp J - J.comp V‖ * ‖V^k‖ :=
          add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
            (ContinuousLinearMap.opNorm_comp_le _ _)
        _ ≤ 1 * (k * ε) + ε * 1 := add_le_add
          (mul_le_mul hU ih (norm_nonneg _) (by norm_num))
          (mul_le_mul hstep hvk (norm_nonneg _) hε)
        _ = (k+1 : ℕ) * ε := by push_cast; ring

/-- In particular, encoded states remain close to the evolved effective states. -/
theorem evolved_state_error_le
    (U : F →L[ℂ] F) (V : E →L[ℂ] E) (J : E →L[ℂ] F)
    (ε : ℝ) (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1)
    (hstep : ‖U.comp J - J.comp V‖ ≤ ε) (k : ℕ) (ψ : E) :
    ‖(U^k) (J ψ) - J ((V^k) ψ)‖ ≤ (k * ε) * ‖ψ‖ := by
  calc
    _ ≤ ‖(U^k).comp J - J.comp (V^k)‖ * ‖ψ‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (evolution_error_le U V J ε hU hV hstep k) (norm_nonneg ψ)

/-- Refinement needs accumulated error to vanish; one-step convergence alone
does not suffice when the number of physical time steps grows. -/
theorem evolution_converges_of_accumulated_error
    (U : ℕ → F →L[ℂ] F) (V : ℕ → E →L[ℂ] E) (J : ℕ → E →L[ℂ] F)
    (ε : ℕ → ℝ) (steps : ℕ → ℕ)
    (hU : ∀ r, ‖U r‖ ≤ 1) (hV : ∀ r, ‖V r‖ ≤ 1)
    (hstep : ∀ r, ‖(U r).comp (J r) - (J r).comp (V r)‖ ≤ ε r)
    (hlimit : Tendsto (fun r => (steps r : ℝ) * ε r) atTop (𝓝 0)) :
    Tendsto (fun r => ‖((U r)^(steps r)).comp (J r) -
      (J r).comp ((V r)^(steps r))‖) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => norm_nonneg _) _ hlimit
  intro r
  exact evolution_error_le (U r) (V r) (J r) (ε r) (hU r) (hV r) (hstep r) _

/-- An O(δ²) one-step error gives an O(δ) error uniformly on every fixed
physical time interval. The microscopic and effective steps are supplied. -/
theorem finite_time_error_le
    (U : F →L[ℂ] F) (V : E →L[ℂ] E) (J : E →L[ℂ] F)
    (δ T : ℝ) (hδ : 0 ≤ δ) (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1)
    (hstep : ‖U.comp J - J.comp V‖ ≤ δ^2)
    (k : ℕ) (htime : (k : ℝ) * δ ≤ T) :
    ‖(U^k).comp J - J.comp (V^k)‖ ≤ T * δ := by
  calc
    _ ≤ k * δ^2 := evolution_error_le U V J (δ^2) hU hV hstep k
    _ = ((k : ℝ) * δ) * δ := by ring
    _ ≤ T * δ := mul_le_mul_of_nonneg_right htime hδ

omit [Nontrivial E] in
/-- A nearby dressed encoding transfers an evolution estimate back to the
bare encoding with twice the encoding error, uniformly for contractions. -/
theorem encoding_change_error_le
    (U : F →L[ℂ] F) (V : E →L[ℂ] E) (J J₀ : E →L[ℂ] F)
    (η error : ℝ) (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1)
    (hJ : ‖J₀ - J‖ ≤ η) (herror : ‖U.comp J - J.comp V‖ ≤ error) :
    ‖U.comp J₀ - J₀.comp V‖ ≤ error + 2 * η := by
  have hη : 0 ≤ η := (norm_nonneg _).trans hJ
  have he : U.comp J₀ - J₀.comp V =
      U.comp (J₀-J) + (U.comp J - J.comp V) + (J-J₀).comp V := by
    ext x
    simp
  have hleft : ‖U.comp (J₀-J)‖ ≤ η := by
    calc
      _ ≤ ‖U‖ * ‖J₀-J‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * η := mul_le_mul hU hJ (norm_nonneg _) (by norm_num)
      _ = η := one_mul _
  have hright : ‖(J-J₀).comp V‖ ≤ η := by
    calc
      _ ≤ ‖J-J₀‖ * ‖V‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ η * 1 := mul_le_mul (by simpa [norm_sub_rev] using hJ) hV (norm_nonneg _) hη
      _ = η := mul_one _
  rw [he]
  have h₁ := norm_add_le (U.comp (J₀-J)) (U.comp J - J.comp V)
  have h₂ := norm_add_le (U.comp (J₀-J) + (U.comp J - J.comp V)) ((J-J₀).comp V)
  linarith

omit [Nontrivial E] in
/-- The full residual, including components outside the encoded sector,
controls composition and hence the off-shell generator algebra. -/
theorem bracket_defect_identity
    (A B : F →L[ℂ] F) (a b : E →L[ℂ] E) (J : E →L[ℂ] F) :
    (A * B - B * A).comp J - J.comp (a * b - b * a) =
      A.comp (B.comp J - J.comp b) - B.comp (A.comp J - J.comp a) +
        (A.comp J - J.comp a).comp b - (B.comp J - J.comp b).comp a := by
  ext x
  simp
  abel

omit [Nontrivial E] in
theorem bracket_error_le
    (A B : F →L[ℂ] F) (a b : E →L[ℂ] E) (J : E →L[ℂ] F)
    (εA εB : ℝ) (hA : ‖A.comp J - J.comp a‖ ≤ εA)
    (hB : ‖B.comp J - J.comp b‖ ≤ εB) :
    ‖(A * B - B * A).comp J - J.comp (a * b - b * a)‖ ≤
      (‖A‖ + ‖a‖) * εB + (‖B‖ + ‖b‖) * εA := by
  rw [bracket_defect_identity]
  have h₁ := ContinuousLinearMap.opNorm_comp_le A (B.comp J - J.comp b)
  have h₂ := ContinuousLinearMap.opNorm_comp_le B (A.comp J - J.comp a)
  have h₃ := ContinuousLinearMap.opNorm_comp_le (A.comp J - J.comp a) b
  have h₄ := ContinuousLinearMap.opNorm_comp_le (B.comp J - J.comp b) a
  have e₁ := mul_le_mul_of_nonneg_left hB (norm_nonneg A)
  have e₂ := mul_le_mul_of_nonneg_left hA (norm_nonneg B)
  have e₃ := mul_le_mul_of_nonneg_right hA (norm_nonneg b)
  have e₄ := mul_le_mul_of_nonneg_right hB (norm_nonneg a)
  have t₁ := norm_sub_le (A.comp (B.comp J - J.comp b))
    (B.comp (A.comp J - J.comp a))
  have t₂ := norm_add_le
    (A.comp (B.comp J - J.comp b) - B.comp (A.comp J - J.comp a))
    ((A.comp J - J.comp a).comp b)
  have t₃ := norm_sub_le
    (A.comp (B.comp J - J.comp b) - B.comp (A.comp J - J.comp a) +
      (A.comp J - J.comp a).comp b) ((B.comp J - J.comp b).comp a)
  nlinarith

omit [Nontrivial E] in
/-- If C annihilates the bare encoding, changing its penalty coefficient
does not change the full generator residual. A dressed encoding or a separate
oscillatory estimate is needed when the slow term leaks out of that kernel. -/
theorem penalty_does_not_reduce_bare_residual
    (C S : F →L[ℂ] F) (K : E →L[ℂ] E) (J : E →L[ℂ] F)
    (hkernel : C.comp J = 0) (penalty : ℂ) :
    (penalty • C + S).comp J - J.comp K = S.comp J - J.comp K := by
  have hz : ∀ x, C (J x) = 0 := fun x => by
    simpa using congrArg (fun f : E →L[ℂ] F => f x) hkernel
  ext x
  simp [hz]

section ContinuousTime

variable {ER FR : Type*}
variable [NormedAddCommGroup ER] [NormedSpace ℝ ER]
variable [NormedAddCommGroup FR] [NormedSpace ℝ FR]

/-- A generator residual controls the entire continuous evolution. Complex
quantum evolutions can be regarded as real-linear flows with generators -iH.
No inverse spectral gap or norm of the microscopic generator enters this bound.
The flow equations and contraction bounds remain explicit hypotheses. -/
theorem continuous_time_error_le
    (A : FR →L[ℝ] FR) (B : ER →L[ℝ] ER) (J : ER →L[ℝ] FR)
    (U : ℝ → FR →L[ℝ] FR) (V : ℝ → ER →L[ℝ] ER)
    (hU0 : U 0 = 1) (hV0 : V 0 = 1)
    (hUd : ∀ s, HasDerivAt U ((U s).comp A) s)
    (hVd : ∀ s, HasDerivAt V (B.comp (V s)) s)
    (hU : ∀ s, 0 ≤ s → ‖U s‖ ≤ 1)
    (hV : ∀ s, 0 ≤ s → ‖V s‖ ≤ 1)
    (ε : ℝ) (hres : ‖A.comp J - J.comp B‖ ≤ ε)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖(U t).comp J - J.comp (V t)‖ ≤ t * ε := by
  let f := fun s => (U (t-s)).comp (J.comp (V s))
  let d := fun s => (U (t-s)).comp ((J.comp B - A.comp J).comp (V s))
  have hd : ∀ s, HasDerivAt f (d s) s := by
    intro s
    have hleft := (hUd (t-s)).scomp s ((hasDerivAt_id s).const_sub t)
    have hright := (hasDerivAt_const s J).clm_comp (hVd s)
    convert hleft.clm_comp hright using 1
    ext x
    simp [d, sub_eq_add_neg, add_comm]
  have hε : 0 ≤ ε := (norm_nonneg _).trans hres
  have hb : ∀ s ∈ Set.Ico 0 t, ‖d s‖ ≤ ε := by
    intro s hs
    have hu := hU (t-s) (by linarith [hs.2])
    have hv := hV s hs.1
    have hr : ‖J.comp B - A.comp J‖ ≤ ε := by simpa [norm_sub_rev] using hres
    have hinner : ‖(J.comp B - A.comp J).comp (V s)‖ ≤ ε := by
      calc
        _ ≤ ‖J.comp B - A.comp J‖ * ‖V s‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ε * 1 := mul_le_mul hr hv (norm_nonneg _) hε
        _ = ε := mul_one _
    calc
      ‖d s‖ ≤ ‖U (t-s)‖ * ‖(J.comp B - A.comp J).comp (V s)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ε := mul_le_mul hu hinner (norm_nonneg _) (by norm_num)
      _ = ε := one_mul _
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s _ => (hd s).hasDerivWithinAt) hb t (show t ∈ Set.Icc 0 t from ⟨ht, le_rfl⟩)
  have hend : f t - f 0 = J.comp (V t) - (U t).comp J := by
    ext x
    simp [f, hU0, hV0]
  rw [hend, norm_sub_rev] at h
  simpa [mul_comm] using h

end ContinuousTime

#print axioms evolution_error_le
#print axioms evolved_state_error_le
#print axioms evolution_converges_of_accumulated_error
#print axioms finite_time_error_le
#print axioms encoding_change_error_le
#print axioms bracket_error_le
#print axioms penalty_does_not_reduce_bare_residual
#print axioms continuous_time_error_le

end
end UnifiedTheory.Audit.KFCausalDynamicalClosure
