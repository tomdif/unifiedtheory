/- A bounded physical action that commutes with the circle, and has a
bounded action on the original form space, acts on the actual averaged
form space. The output intertwining identity passes to L2 sections. -/
import UnifiedTheory.Audit.KFCausalAveragedFormProjection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalAveragedFormAction
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit
open UnifiedTheory.Audit.KFCausalAveragedFormSpace
open UnifiedTheory.Audit.KFCausalAveragedFormProjection

variable {H E K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (U : StrongUnitaryGroup H) (T : ℝ) (J : E →L[ℂ] H)
  (D : H →L[ℂ] H) (F : E →L[ℂ] E)
  (hF : ∀ v, J (F v) = D (J v))
  (hD : ∀ (θ : ℝ) v, D (U.action θ v) = U.action θ (D v))

def ambientAction : Ambient (H := H) (E := E) →L[ℂ] Ambient (H := H) (E := E) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H (Lp E 2 angleMeasure)).symm.toContinuousLinearMap.comp
    ((D.prodMap (F.compLpL 2 angleMeasure)).comp
      (WithLp.prodContinuousLinearEquiv 2 ℂ H (Lp E 2 angleMeasure)).toContinuousLinearMap)

include hF hD in
theorem ambient_mem (u : FormSpace U T J) : ambientAction D F u.val ∈ formGraph U T J := by
  change J.compLp (F.compLp (sectionMap U T J u)) - orbit U T (D (embedding U T J u)) = 0
  apply sub_eq_zero.mpr
  apply Lp.ext
  filter_upwards [J.coeFn_compLp (F.compLp (sectionMap U T J u)),
    F.coeFn_compLp (sectionMap U T J u), compatibility_ae U T J u,
    orbitState_coe U T (D (embedding U T J u))] with θ hJ hFs hu ho
  rw [hJ,hFs,hF,hu,hD]
  exact ho.symm

def formAction : FormSpace U T J →L[ℂ] FormSpace U T J where
  toFun u := ⟨ambientAction D F u.val,ambient_mem U T J D F hF hD u⟩
  map_add' u v := by
    apply Subtype.ext
    exact (ambientAction D F).map_add u.val v.val
  map_smul' c u := by
    apply Subtype.ext
    exact (ambientAction D F).map_smul c u.val
  cont := ((ambientAction D F).continuous.comp continuous_subtype_val).subtype_mk _

theorem formAction_embedding (u : FormSpace U T J) :
    embedding U T J (formAction U T J D F hF hD u) = D (embedding U T J u) := rfl

theorem formAction_section (u : FormSpace U T J) :
    sectionMap U T J (formAction U T J D F hF hD u) = F.compLp (sectionMap U T J u) := rfl

theorem formAction_norm (hDn : ∀ x, ‖D x‖ ≤ ‖x‖) (hFn : ∀ v, ‖F v‖ ≤ 2*‖v‖)
    (u : FormSpace U T J) : ‖formAction U T J D F hF hD u‖ ≤ 2*‖u‖ := by
  have hFop : ‖F‖ ≤ 2 := ContinuousLinearMap.opNorm_le_bound _ (by norm_num) hFn
  have hFs : ‖F.compLp (sectionMap U T J u)‖ ≤ 2*‖sectionMap U T J u‖ :=
    (F.norm_compLp_le _).trans (mul_le_mul_of_nonneg_right hFop (norm_nonneg _))
  have hd := pow_le_pow_left₀ (norm_nonneg _) (hDn (embedding U T J u)) 2
  have hf := pow_le_pow_left₀ (norm_nonneg _) hFs 2
  have h1 := norm_identity U T J (formAction U T J D F hF hD u)
  have h0 := norm_identity U T J u
  simp only [formAction_embedding,formAction_section] at h1
  nlinarith [sq_nonneg ‖embedding U T J u‖,norm_nonneg u,
    norm_nonneg (formAction U T J D F hF hD u)]

theorem formAction_output (A : E →L[ℂ] K) (R : K →L[ℂ] K)
    (hA : ∀ v, A (F v) = R (A v)) (u : FormSpace U T J) :
    averagedOutput U T J A (formAction U T J D F hF hD u) =
      R.compLp (averagedOutput U T J A u) := by
  change A.compLp (F.compLp (sectionMap U T J u)) = R.compLp (A.compLp (sectionMap U T J u))
  apply Lp.ext
  filter_upwards [A.coeFn_compLp (F.compLp (sectionMap U T J u)),
    F.coeFn_compLp (sectionMap U T J u), R.coeFn_compLp (A.compLp (sectionMap U T J u)),
    A.coeFn_compLp (sectionMap U T J u)] with θ ha hf hr hb
  rw [ha,hf,hr,hb,hA]

include hF hD in
theorem formAction_domain (f : H) (hf : f ∈ domain U T J) : D f ∈ domain U T J := by
  obtain ⟨u,rfl⟩ := hf
  exact ⟨formAction U T J D F hF hD u,rfl⟩

#print axioms ambient_mem
#print axioms formAction_embedding
#print axioms formAction_section
#print axioms formAction_norm
#print axioms formAction_output
#print axioms formAction_domain

end
end UnifiedTheory.Audit.KFCausalAveragedFormAction
