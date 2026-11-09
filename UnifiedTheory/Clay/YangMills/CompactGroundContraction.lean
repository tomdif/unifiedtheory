/- Compactness converts an eigenvalue-ratio estimate into a norm contraction
on the full vacuum-orthogonal subspace. The restricted operator's norm is
proved to be attained when nonzero; no orthogonal operator-norm bound is
assumed. -/
import UnifiedTheory.Clay.YangMills.PositiveKernelGroundState

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.CompactGroundContraction
noncomputable section
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- A ground eigenvector of a symmetric operator has an invariant orthogonal complement. -/
theorem orthogonal_invariant (T : H →L[ℂ] H) (hT : T.IsPositive) (Ω : H)
    (lam : ℝ) (hΩ : T Ω = lam • Ω) (v : H) (hv : inner ℂ Ω v = 0) :
    inner ℂ Ω (T v) = 0 := by
  have hs : inner ℂ (T Ω) v = inner ℂ Ω (T v) := hT.isSymmetric Ω v
  rw [← hs, hΩ, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, hv, mul_zero]

/-- A ratio bound on the actual nonzero orthogonal eigenvectors controls every orthogonal vector. -/
theorem norm_contraction (T : H →L[ℂ] H) (hT : T.IsPositive)
    (hcompact : IsCompactOperator T) (Ω : H) (lam q : ℝ)
    (hlam : 0 < lam) (hq : 0 ≤ q) (hΩ : T Ω = lam • Ω)
    (hratio : ∀ (rho : ℝ) (v : H), 0 < rho → v ≠ 0 → inner ℂ Ω v = 0 →
      T v = rho • v → rho / lam ≤ q)
    (v : H) (hv : inner ℂ Ω v = 0) : ‖T v‖ ≤ (lam * q) * ‖v‖ := by
  let V : Submodule ℂ H := (ℂ ∙ Ω)ᗮ
  have hV (w : H) (hw : w ∈ V) : T w ∈ V := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    exact orthogonal_invariant T hT Ω lam hΩ w
      (Submodule.mem_orthogonal_singleton_iff_inner_right.mp hw)
  let L : V →ₗ[ℂ] V := T.toLinearMap.restrict hV
  have hbound (w : V) : ‖L w‖ ≤ ‖T‖ * ‖w‖ := T.le_opNorm w
  let R : V →L[ℂ] V := L.mkContinuous ‖T‖ hbound
  have hRpos : R.IsPositive := by
    constructor
    · intro x y
      exact hT.isSymmetric (x : H) (y : H)
    · intro x
      exact hT.re_inner_nonneg_left (x : H)
  have hRcompact : IsCompactOperator R := hcompact.restrict' hV
  have hRnorm : ‖R‖ ≤ lam * q := by
    by_cases hz : R = 0
    · rw [hz]
      have hz0 : ‖(0 : V →L[ℂ] V)‖ = 0 := ContinuousLinearMap.opNorm_zero
      rw [hz0]
      exact mul_nonneg hlam.le hq
    obtain ⟨hRposnorm, w, hwnorm, hweig⟩ :=
      PositiveKernelGroundState.positive_compact_top_eigenvector R hRpos hRcompact hz
    have hwne : (w : H) ≠ 0 := by
      intro hw
      have hzero : w = 0 := Subtype.ext hw
      rw [hzero, norm_zero] at hwnorm
      norm_num at hwnorm
    have hworth : inner ℂ Ω (w : H) = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.property
    have hwe : T (w : H) = ‖R‖ • (w : H) := by
      have h := congrArg (fun z : V => (z : H)) hweig
      exact h
    simpa only [mul_comm q lam] using
      (div_le_iff₀ hlam).mp (hratio ‖R‖ w hRposnorm hwne hworth hwe)
  let w : V := ⟨v, Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hv⟩
  have h := R.le_opNorm w
  exact h.trans (mul_le_mul_of_nonneg_right hRnorm (norm_nonneg w))

end
end UnifiedTheory.Clay.YangMills.CompactGroundContraction
