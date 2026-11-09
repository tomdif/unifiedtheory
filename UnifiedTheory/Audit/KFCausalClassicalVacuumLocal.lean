/- Local existence and uniqueness for the derived full canonical vacuum
vector field, for every initial time and phase point. -/
import UnifiedTheory.Audit.KFCausalCanonicalPhaseODE

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClassicalVacuumLocal
noncomputable section
open Set Filter
open scoped Topology Manifold
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth
open UnifiedTheory.Audit.KFCausalCanonicalPhaseODE

theorem exists_local (ε κ : ℝ) (hε : 0 ≤ ε) (x : TimePhase) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ γ : ℝ → TimePhase, γ 0 = x ∧
      ∀ t ∈ Ioo (-δ) δ, HasDerivAt γ (field ε κ (γ t)) t := by
  obtain ⟨δ,hδ,a,r,L,K,_,hp⟩ := IsPicardLindelof.of_contDiffAt_one
    ((field_contDiff ε κ hε).contDiffAt (x := x)) (0:ℝ)
  obtain ⟨γ,hγ0,hγ⟩ := hp.exists_eq_forall_mem_Icc_hasDerivWithinAt (Metric.mem_closedBall_self r.coe_nonneg)
  refine ⟨δ,hδ,γ,hγ0,?_⟩
  intro t ht
  have hm : t ∈ Icc (0-δ) (0+δ) := by simpa using Ioo_subset_Icc_self ht
  exact (hγ t hm).hasDerivAt (Icc_mem_nhds (by simpa using ht.1) (by simpa using ht.2))

theorem local_uniqueness (ε κ : ℝ) (hε : 0 ≤ ε) (γ η : ℝ → TimePhase) (t₀ : ℝ)
    (hγ : ∀ᶠ t in 𝓝 t₀, HasDerivAt γ (field ε κ (γ t)) t)
    (hη : ∀ᶠ t in 𝓝 t₀, HasDerivAt η (field ε κ (η t)) t) (he : γ t₀ = η t₀) :
    γ =ᶠ[𝓝 t₀] η := by
  have hv : ContMDiff 𝓘(ℝ,TimePhase) (𝓘(ℝ,TimePhase)).tangent 1
      (fun x : TimePhase => (⟨x,field ε κ x⟩ : TangentBundle 𝓘(ℝ,TimePhase) TimePhase)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr (field_contDiff ε κ hε)
  have hg : IsMIntegralCurveAt (I := 𝓘(ℝ,TimePhase)) γ (field ε κ) t₀ := by
    filter_upwards [hγ] with t ht
    rw [hasMFDerivAt_iff_hasFDerivAt]
    exact ht
  have hh : IsMIntegralCurveAt (I := 𝓘(ℝ,TimePhase)) η (field ε κ) t₀ := by
    filter_upwards [hη] with t ht
    rw [hasMFDerivAt_iff_hasFDerivAt]
    exact ht
  exact isMIntegralCurveAt_eventuallyEq_of_contMDiffAt
    BoundarylessManifold.isInteriorPoint hv.contMDiffAt hg hh he

#print axioms exists_local
#print axioms local_uniqueness

end
end UnifiedTheory.Audit.KFCausalClassicalVacuumLocal
