/- The full matter canonical field is derived from the smooth Hamiltonian.
Every initial point has a locally unique solution. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterSmooth
import UnifiedTheory.Audit.KFCausalCanonicalPhaseODE

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClassicalMatterODE
noncomputable section
open Set Filter
open scoped Topology Manifold
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth (TimePhase)
open UnifiedTheory.Audit.KFCausalCanonicalPhaseODE (poisson stateInclusion dual_poisson_zero)
open UnifiedTheory.Audit.KFCausalClassicalMatterSmooth

def stateDifferential (ε m g κ : ℝ) (x : TimePhase) : Phase →L[ℝ] ℝ :=
  (fderiv ℝ (fullHamiltonian ε m g κ) x).comp stateInclusion

def field (ε m g κ : ℝ) (x : TimePhase) : TimePhase := (1,poisson (stateDifferential ε m g κ x))

theorem field_contDiff (ε m g κ : ℝ) (hε : 0 ≤ ε) : ContDiff ℝ 1 (field ε m g κ) := by
  have hd := (fullHamiltonian_contDiff ε m g κ hε 2).fderiv_right (m := 1) (by norm_num)
  have hs : ContDiff ℝ 1 (stateDifferential ε m g κ) := hd.clm_comp contDiff_const
  exact contDiff_const.prodMk (poisson.contDiff.comp hs)

theorem hamiltonian_field (ε m g κ : ℝ) (x : TimePhase) :
    fderiv ℝ (fullHamiltonian ε m g κ) x (field ε m g κ x) =
      fderiv ℝ (fullHamiltonian ε m g κ) x (1,0) := by
  let l := fderiv ℝ (fullHamiltonian ε m g κ) x
  change l (1,poisson (l.comp stateInclusion)) = l (1,0)
  rw [show (1,poisson (l.comp stateInclusion)) =
    (1,0)+stateInclusion (poisson (l.comp stateInclusion)) by simp [stateInclusion], map_add]
  have h : l (stateInclusion (poisson (l.comp stateInclusion))) = 0 :=
    dual_poisson_zero (l.comp stateInclusion)
  rw [h, add_zero]

theorem field_vacuum (ε κ : ℝ) :
    field ε 0 0 κ = KFCausalCanonicalPhaseODE.field ε κ := by
  funext x
  simp only [field,stateDifferential,fullHamiltonian_vacuum,
    KFCausalCanonicalPhaseODE.field,KFCausalCanonicalPhaseODE.stateDifferential]

theorem exists_local (ε m g κ : ℝ) (hε : 0 ≤ ε) (x : TimePhase) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ γ : ℝ → TimePhase, γ 0 = x ∧
      ∀ t ∈ Ioo (-δ) δ, HasDerivAt γ (field ε m g κ (γ t)) t := by
  obtain ⟨δ,hδ,a,r,L,K,_,hp⟩ := IsPicardLindelof.of_contDiffAt_one
    ((field_contDiff ε m g κ hε).contDiffAt (x := x)) (0:ℝ)
  obtain ⟨γ,hγ0,hγ⟩ := hp.exists_eq_forall_mem_Icc_hasDerivWithinAt (Metric.mem_closedBall_self r.coe_nonneg)
  refine ⟨δ,hδ,γ,hγ0,?_⟩
  intro t ht
  have hm : t ∈ Icc (0-δ) (0+δ) := by simpa using Ioo_subset_Icc_self ht
  exact (hγ t hm).hasDerivAt (Icc_mem_nhds (by simpa using ht.1) (by simpa using ht.2))

theorem local_uniqueness (ε m g κ : ℝ) (hε : 0 ≤ ε) (γ η : ℝ → TimePhase) (t₀ : ℝ)
    (hγ : ∀ᶠ t in 𝓝 t₀, HasDerivAt γ (field ε m g κ (γ t)) t)
    (hη : ∀ᶠ t in 𝓝 t₀, HasDerivAt η (field ε m g κ (η t)) t) (he : γ t₀ = η t₀) :
    γ =ᶠ[𝓝 t₀] η := by
  have hv : ContMDiff 𝓘(ℝ,TimePhase) (𝓘(ℝ,TimePhase)).tangent 1
      (fun x : TimePhase => (⟨x,field ε m g κ x⟩ : TangentBundle 𝓘(ℝ,TimePhase) TimePhase)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr (field_contDiff ε m g κ hε)
  have hg : IsMIntegralCurveAt (I := 𝓘(ℝ,TimePhase)) γ (field ε m g κ) t₀ := by
    filter_upwards [hγ] with t ht
    rw [hasMFDerivAt_iff_hasFDerivAt]
    exact ht
  have hh : IsMIntegralCurveAt (I := 𝓘(ℝ,TimePhase)) η (field ε m g κ) t₀ := by
    filter_upwards [hη] with t ht
    rw [hasMFDerivAt_iff_hasFDerivAt]
    exact ht
  exact isMIntegralCurveAt_eventuallyEq_of_contMDiffAt
    BoundarylessManifold.isInteriorPoint hv.contMDiffAt hg hh he

#print axioms field_contDiff
#print axioms hamiltonian_field
#print axioms field_vacuum
#print axioms exists_local
#print axioms local_uniqueness

end
end UnifiedTheory.Audit.KFCausalClassicalMatterODE
