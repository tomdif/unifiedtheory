/- A resolvent constructed from a densely embedded Hilbert form space.
No spectral theorem or pre-existing unbounded Hamiltonian is assumed. -/
import Mathlib.Analysis.InnerProductSpace.LinearPMap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalFormResolvent
noncomputable section

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def resolvent (J : E →L[ℂ] H) : H →L[ℂ] H := J.comp J.adjoint

theorem resolvent_symmetric (J : E →L[ℂ] H) (x y : H) :
    inner ℂ (resolvent J x) y = inner ℂ x (resolvent J y) := by
  change inner ℂ (J (J.adjoint x)) y = inner ℂ x (J (J.adjoint y))
  rw [← J.adjoint_inner_right, J.adjoint_inner_left]

theorem resolvent_adjoint (J : E →L[ℂ] H) :
    (resolvent J).adjoint = resolvent J := by
  simp [resolvent, ContinuousLinearMap.adjoint_comp]

theorem resolvent_inner (J : E →L[ℂ] H) (x : H) :
    inner ℂ x (resolvent J x) = (‖J.adjoint x‖^2 : ℝ) := by
  rw [resolvent, ContinuousLinearMap.comp_apply, ← J.adjoint_inner_left]
  simpa only [Complex.ofReal_pow] using (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (J.adjoint x))

theorem adjoint_injective (J : E →L[ℂ] H) (hd : DenseRange J) :
    Function.Injective J.adjoint := by
  apply LinearMap.ker_eq_bot.mp
  rw [← J.orthogonal_range]
  apply Submodule.topologicalClosure_eq_top_iff.mp
  exact Submodule.dense_iff_topologicalClosure_eq_top.mp hd

theorem resolvent_injective (J : E →L[ℂ] H) (hi : Function.Injective J)
    (hd : DenseRange J) : Function.Injective (resolvent J) :=
  hi.comp (adjoint_injective J hd)

theorem resolvent_dense (J : E →L[ℂ] H) (hi : Function.Injective J)
    (hd : DenseRange J) : DenseRange (resolvent J) := by
  change Dense ((resolvent J).range : Set H)
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  rw [ContinuousLinearMap.orthogonal_range, resolvent_adjoint]
  exact LinearMap.ker_eq_bot.mpr (resolvent_injective J hi hd)

theorem resolvent_norm_le_one (J : E →L[ℂ] H) (hc : ‖J‖ ≤ 1) :
    ‖resolvent J‖ ≤ 1 := by
  calc
    ‖resolvent J‖ ≤ ‖J‖ * ‖J.adjoint‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖J‖ * ‖J‖ := by rw [ContinuousLinearMap.adjoint, LinearIsometryEquiv.norm_map]
    _ ≤ 1 := by nlinarith [norm_nonneg J]

theorem resolvent_positive (J : E →L[ℂ] H) (x : H) :
    0 ≤ (inner ℂ x (resolvent J x)).re := by
  rw [resolvent_inner]
  exact sq_nonneg _

#print axioms resolvent_symmetric
#print axioms resolvent_injective
#print axioms resolvent_dense
#print axioms resolvent_norm_le_one
#print axioms resolvent_positive

end
end UnifiedTheory.Audit.KFCausalFormResolvent
