/- A full natural graph representative identifies a self-adjoint operator
with the maximal real multiplier. This uses adjoint maximality; it does not
assume equality of domains or introduce a preferred smooth core. -/
import UnifiedTheory.Audit.KFCausalRealMultiplierSelfAdjoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalSelfAdjointMultiplierIdentification
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalUnitaryRealMultiplier

variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [MeasurableSpace X] {μ : Measure X}

theorem selfAdjoint_eq_realPullback (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ) (w : X → ℝ) (hm : Measurable w)
    (hrep : ∀ f g : H, (f,g) ∈ A.graph → Ω g =ᵐ[μ] fun x => (w x:ℂ)*(Ω f) x) :
    A = realPullback Ω w hm := by
  have hle : A ≤ realPullback Ω w hm := by
    apply LinearPMap.le_graph_iff.mp
    rintro ⟨f,g⟩ hfg
    exact (realPullback_graph Ω w hm f g).mpr (hrep f g hfg)
  have hf : A.IsFormalAdjoint (realPullback Ω w hm) := by
    intro f g
    rw [← Ω.inner_map_map (A f) (g:H),← Ω.inner_map_map (f:H) (realPullback Ω w hm g),
      L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hrep f (A f) (A.mem_graph f),realPullback_coe Ω w hm g] with x ha hb
    rw [ha,hb]
    change inner ℂ ((w x:ℂ) • (Ω (f:H)) x) ((Ω (g:H)) x) =
      inner ℂ ((Ω (f:H)) x) ((w x:ℂ) • (Ω (g:H)) x)
    rw [inner_smul_left,inner_smul_right,Complex.conj_ofReal]
  have hr := hf.le_adjoint hA.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hA] at hr
  exact le_antisymm hle hr

#print axioms selfAdjoint_eq_realPullback

end
end UnifiedTheory.Audit.KFCausalSelfAdjointMultiplierIdentification
