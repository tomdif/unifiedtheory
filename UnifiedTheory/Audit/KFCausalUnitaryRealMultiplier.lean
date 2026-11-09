/- Maximal real multiplication transported through a proved unitary.
Its signed action is constructed from the positive absolute multiplier
and a bounded sign unitary, retaining the exact weighted L2 domain. -/
import UnifiedTheory.Audit.KFCausalRealSignMultiplier
import UnifiedTheory.Audit.KFCausalUnitaryPositiveMultiplier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalUnitaryRealMultiplier
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalRealSignMultiplier
open UnifiedTheory.Audit.KFCausalUnitaryPositiveMultiplier

variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [MeasurableSpace X] {μ : Measure X}

def signAction (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ) (w : X → ℝ) (hm : Measurable w) : H ≃ₗᵢ[ℂ] H :=
  Ω.trans ((signUnitary w hm).trans Ω.symm)

theorem signAction_coordinates (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ) (w : X → ℝ) (hm : Measurable w)
    (f : H) : Ω (signAction Ω w hm f)=signUnitary w hm (Ω f) :=
  Ω.apply_symm_apply _

theorem signAction_symmetric (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ) (w : X → ℝ) (hm : Measurable w)
    (f g : H) : inner ℂ (signAction Ω w hm f) g=inner ℂ f (signAction Ω w hm g) := by
  rw [← Ω.inner_map_map (signAction Ω w hm f) g,← Ω.inner_map_map f (signAction Ω w hm g),
    signAction_coordinates,signAction_coordinates]
  exact signUnitary_symmetric w hm _ _

def realPullback (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ) (w : X → ℝ) (hm : Measurable w) : H →ₗ.[ℂ] H :=
  (signAction Ω w hm).toLinearEquiv.toLinearMap.compPMap
    (positivePullback Ω (fun x => |w x|) (continuous_abs.measurable.comp hm) (fun x => abs_nonneg (w x)))

theorem realPullback_apply (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ) (w : X → ℝ) (hm : Measurable w)
    (f : (realPullback Ω w hm).domain) :
    realPullback Ω w hm f = signAction Ω w hm
      (positivePullback Ω (fun x => |w x|) (continuous_abs.measurable.comp hm) (fun x => abs_nonneg (w x)) f) := rfl

theorem realPullback_domain (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ) (w : X → ℝ) (hm : Measurable w) (f : H) :
    f ∈ (realPullback Ω w hm).domain ↔ MemLp (fun x => (w x:ℂ)*(Ω f) x) 2 μ := by
  change f ∈ (positivePullback Ω (fun x => |w x|) (continuous_abs.measurable.comp hm) (fun x => abs_nonneg (w x))).domain ↔ _
  rw [pullback_domain_iff]
  exact absolute_weight_memLp_iff w hm (Ω f)

theorem realPullback_coe (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ) (w : X → ℝ) (hm : Measurable w)
    (f : (realPullback Ω w hm).domain) :
    Ω (realPullback Ω w hm f) =ᵐ[μ] fun x => (w x:ℂ)*(Ω (f:H)) x := by
  rw [realPullback_apply,signAction_coordinates]
  have hA := (pullback_graph_iff Ω (fun x => |w x|) (continuous_abs.measurable.comp hm) (fun x => abs_nonneg (w x)) _ _).mp
    ((positivePullback Ω (fun x => |w x|) (continuous_abs.measurable.comp hm) (fun x => abs_nonneg (w x))).mem_graph f)
  filter_upwards [signUnitary_coe w hm
    (Ω (positivePullback Ω (fun x => |w x|) (continuous_abs.measurable.comp hm) (fun x => abs_nonneg (w x)) f)),hA] with x hx ha
  rw [hx,ha,← mul_assoc,← Complex.ofReal_mul,realSign_abs]

theorem realPullback_graph (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ) (w : X → ℝ) (hm : Measurable w)
    (f g : H) : (f,g) ∈ (realPullback Ω w hm).graph ↔
      Ω g =ᵐ[μ] fun x => (w x:ℂ)*(Ω f) x := by
  constructor
  · intro h
    obtain ⟨u,hu,hg⟩ := (LinearPMap.mem_graph_iff _).mp h
    simpa only [hu,hg] using realPullback_coe Ω w hm u
  · intro hg
    have hf := (realPullback_domain Ω w hm f).mpr ((Lp.memLp (Ω g)).ae_eq hg)
    have he : realPullback Ω w hm ⟨f,hf⟩=g := by
      apply Ω.injective
      apply Lp.ext
      exact (realPullback_coe Ω w hm ⟨f,hf⟩).trans hg.symm
    simpa only [he] using (realPullback Ω w hm).mem_graph ⟨f,hf⟩

#print axioms signAction_coordinates
#print axioms signAction_symmetric
#print axioms realPullback_apply
#print axioms realPullback_domain
#print axioms realPullback_coe
#print axioms realPullback_graph

end
end UnifiedTheory.Audit.KFCausalUnitaryRealMultiplier
