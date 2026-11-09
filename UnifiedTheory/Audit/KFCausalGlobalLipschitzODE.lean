/- Global integral curves for a C1 globally Lipschitz vector field, using
Picard-Lindelof on a uniform time interval and the verified continuation
lemma. This supplies existence rather than assuming a solution. -/
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalGlobalLipschitzODE
noncomputable section
open Set Metric
open scoped Manifold NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem uniform_local (f : E → E) (K : ℝ≥0) (hf : LipschitzWith K f) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : E, ∃ γ : ℝ → E, γ 0 = x ∧
      ∀ t ∈ Ioo (-δ) δ, HasDerivAt γ (f (γ t)) t := by
  let δ : ℝ := 1/((K:ℝ)+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ,hδ,?_⟩
  intro x
  let a : ℝ≥0 := ‖f x‖₊+1
  let L : ℝ≥0 := (K+1)*a
  have hb (y : E) (hy : y ∈ closedBall x (a:ℝ)) : ‖f y‖ ≤ L := by
    calc
      _ ≤ ‖f y-f x‖+‖f x‖ := norm_le_norm_sub_add _ _
      _ ≤ (K:ℝ)*‖y-x‖+‖f x‖ := add_le_add (hf.norm_sub_le y x) le_rfl
      _ ≤ (K:ℝ)*(a:ℝ)+(a:ℝ) := add_le_add
        (mul_le_mul_of_nonneg_left (mem_closedBall_iff_norm.mp hy) K.coe_nonneg)
        (by change ‖f x‖ ≤ ‖f x‖+1; linarith)
      _ = (L:ℝ) := by dsimp [L]; ring
  have hp : IsPicardLindelof (fun _ : ℝ => f)
      (tmin := -δ) (tmax := δ) ⟨0,by constructor <;> linarith only [hδ]⟩ x a 0 L K := by
    apply IsPicardLindelof.of_time_independent hb hf.lipschitzOnWith
    change (L:ℝ)*max (δ-0) (0-(-δ)) ≤ (a:ℝ)-0
    simp only [sub_zero,sub_neg_eq_add,zero_add,max_self]
    dsimp [L,δ]
    have hk : (K:ℝ)+1 ≠ 0 := by positivity
    field_simp
    exact le_rfl
  obtain ⟨γ,hγ0,hγ⟩ := hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨γ,hγ0,fun t ht => (hγ t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)⟩

theorem exists_global (f : E → E) (hc : ContDiff ℝ 1 f) (K : ℝ≥0) (hf : LipschitzWith K f)
    (x : E) : ∃ γ : ℝ → E, γ 0 = x ∧ ∀ t : ℝ, HasDerivAt γ (f (γ t)) t := by
  obtain ⟨δ,hδ,hlocal⟩ := uniform_local f K hf
  have hv : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent 1
      (fun y : E => (⟨y,f y⟩ : TangentBundle 𝓘(ℝ,E) E)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hc
  have hloc (y : E) : ∃ γ : ℝ → E, γ 0 = y ∧
      IsMIntegralCurveOn (I := 𝓘(ℝ,E)) γ f (Ioo (-δ) δ) := by
    obtain ⟨γ,hγ0,hγ⟩ := hlocal y
    refine ⟨γ,hγ0,?_⟩
    intro t ht
    rw [hasMFDerivWithinAt_iff_hasFDerivWithinAt]
    exact (hγ t ht).hasDerivWithinAt
  obtain ⟨γ,hγ0,hγ⟩ := exists_isMIntegralCurve_of_isMIntegralCurveOn hv hδ hloc x
  refine ⟨γ,hγ0,?_⟩
  intro t
  rw [hasDerivAt_iff_hasFDerivAt,← hasMFDerivAt_iff_hasFDerivAt]
  exact hγ t

#print axioms uniform_local
#print axioms exists_global

end
end UnifiedTheory.Audit.KFCausalGlobalLipschitzODE
