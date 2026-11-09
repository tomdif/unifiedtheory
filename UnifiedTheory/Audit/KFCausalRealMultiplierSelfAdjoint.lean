/- Self-adjointness of the actual signed maximal multiplication operator.
The adjoint domain is derived using the positive absolute multiplier and
the real sign unitary, with no self-adjointness certificate as an input. -/
import UnifiedTheory.Audit.KFCausalUnitaryRealMultiplier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalRealMultiplierSelfAdjoint
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalRealSignMultiplier
open UnifiedTheory.Audit.KFCausalUnitaryPositiveMultiplier
open UnifiedTheory.Audit.KFCausalUnitaryRealMultiplier
open UnifiedTheory.Audit.KFCausalPositiveMultiplierEnergy

variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [MeasurableSpace X] {μ : Measure X}

theorem realPullback_symmetric (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ) (w : X → ℝ) (hm : Measurable w) :
    (realPullback Ω w hm).IsFormalAdjoint (realPullback Ω w hm) := by
  intro f g
  rw [← Ω.inner_map_map (realPullback Ω w hm f) (g:H),
    ← Ω.inner_map_map (f:H) (realPullback Ω w hm g),L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [realPullback_coe Ω w hm f,realPullback_coe Ω w hm g] with x hf hg
  rw [hf,hg]
  change inner ℂ ((w x:ℂ) • (Ω (f:H)) x) ((Ω (g:H)) x) =
    inner ℂ ((Ω (f:H)) x) ((w x:ℂ) • (Ω (g:H)) x)
  rw [inner_smul_left,inner_smul_right,Complex.conj_ofReal]

variable [CompleteSpace H]

theorem realPullback_dense (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ) (w : X → ℝ) (hm : Measurable w) :
    Dense ((realPullback Ω w hm).domain : Set H) :=
  pullback_dense Ω (fun x => |w x|) (continuous_abs.measurable.comp hm) (fun x => abs_nonneg (w x))

theorem realPullback_adjoint_domain_subset (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (w : X → ℝ) (hm : Measurable w) :
    (realPullback Ω w hm).adjoint.domain ≤ (realPullback Ω w hm).domain := by
  intro f hf
  let A := positivePullback Ω (fun x => |w x|) (continuous_abs.measurable.comp hm) (fun x => abs_nonneg (w x))
  let h := (realPullback Ω w hm).adjoint ⟨f,hf⟩
  have hp : ∀ y : A.domain, inner ℂ h (y:H)=inner ℂ (signAction Ω w hm f) (A y) := by
    intro y
    have hi := LinearPMap.adjoint_isFormalAdjoint (realPullback_dense Ω w hm) ⟨f,hf⟩ y
    change inner ℂ h (y:H)=inner ℂ f (realPullback Ω w hm y) at hi
    rw [realPullback_apply] at hi
    exact hi.trans (signAction_symmetric Ω w hm f (A y)).symm
  have ha := LinearPMap.mem_adjoint_domain_of_exists (T := A) (signAction Ω w hm f) ⟨h,hp⟩
  have he := LinearPMap.adjoint_apply_eq
    (pullback_dense Ω (fun x => |w x|) (continuous_abs.measurable.comp hm) (fun x => abs_nonneg (w x)))
    ⟨signAction Ω w hm f,ha⟩ hp
  have hg := A.adjoint.mem_graph ⟨signAction Ω w hm f,ha⟩
  rw [he] at hg
  have hsa : A.adjoint=A := LinearPMap.isSelfAdjoint_def.mp
    (pullback_selfAdjoint Ω (fun x => |w x|) (continuous_abs.measurable.comp hm) (fun x => abs_nonneg (w x)))
  change (signAction Ω w hm f,h) ∈ A.adjoint.graph at hg
  rw [hsa] at hg
  have hr := (pullback_graph_iff Ω (fun x => |w x|) (continuous_abs.measurable.comp hm)
    (fun x => abs_nonneg (w x)) _ _).mp hg
  rw [signAction_coordinates] at hr
  apply LinearPMap.mem_domain_of_mem_graph (y := h)
  apply (realPullback_graph Ω w hm f h).mpr
  filter_upwards [hr,signUnitary_coe w hm (Ω f)] with x hx hs
  rw [hx,hs,← mul_assoc,← Complex.ofReal_mul,mul_comm (|w x|),realSign_abs]

theorem realPullback_selfAdjoint (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (w : X → ℝ) (hm : Measurable w) : IsSelfAdjoint (realPullback Ω w hm) := by
  have hf : realPullback Ω w hm ≤ (realPullback Ω w hm).adjoint :=
    (realPullback_symmetric Ω w hm).le_adjoint (realPullback_dense Ω w hm)
  exact LinearPMap.isSelfAdjoint_def.mpr
    (LinearPMap.eq_of_le_of_domain_eq hf
      (le_antisymm hf.1 (realPullback_adjoint_domain_subset Ω w hm))).symm

theorem realPullback_closed (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ) (w : X → ℝ) (hm : Measurable w) :
    (realPullback Ω w hm).IsClosed := (realPullback_selfAdjoint Ω w hm).isClosed

omit [CompleteSpace H] in
theorem realPullback_norm_square (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ) (w : X → ℝ) (hm : Measurable w)
    (f : (realPullback Ω w hm).domain) :
    ‖realPullback Ω w hm f‖^2=∫ x, (w x)^2*‖(Ω (f:H)) x‖^2 ∂μ := by
  rw [← Ω.norm_map (realPullback Ω w hm f),l2_norm_square]
  apply integral_congr_ae
  filter_upwards [realPullback_coe Ω w hm f] with x hx
  rw [hx]
  simp only [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]

#print axioms realPullback_symmetric
#print axioms realPullback_dense
#print axioms realPullback_adjoint_domain_subset
#print axioms realPullback_selfAdjoint
#print axioms realPullback_closed
#print axioms realPullback_norm_square

end
end UnifiedTheory.Audit.KFCausalRealMultiplierSelfAdjoint
