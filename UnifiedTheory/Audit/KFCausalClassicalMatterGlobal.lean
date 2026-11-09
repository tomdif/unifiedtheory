/- Global existence and uniqueness for the actual full classical matter ODE.
A compact cutoff constructs a curve on each finite window. The uniform bound
keeps that cutoff identically one; uniqueness glues these exact solutions. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterUniformBound
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalClassicalMatterGlobal
noncomputable section
open Set
open scoped Manifold NNReal
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalMatterSmooth
open UnifiedTheory.Audit.KFCausalClassicalMatterODE
open UnifiedTheory.Audit.KFCausalClassicalMatterDamping
open UnifiedTheory.Audit.KFCausalClassicalMatterUniformBound

open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth (TimePhase)

theorem exists_window (ε m g κ : ℝ) (hε : 0 < ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 < κ)
    (x₀ : TimePhase) (T : ℝ) (hT : 0 ≤ T) :
    ∃ γ : ℝ → TimePhase, γ 0 = x₀ ∧
      ∀ t ∈ Icc (-T) T, HasDerivAt γ (field ε m g κ (γ t)) t := by
  obtain ⟨B,hB,hbound⟩ := finite_window_bound ε m g κ hε hm hg hκ x₀ T hT
  let χ : ContDiffBump (0 : TimePhase) := ⟨B+1,B+2,by linarith,by linarith⟩
  have hc : ContDiff ℝ 1 (fun x => χ x • (field ε m g κ x).2) :=
    χ.contDiff.smul (field_contDiff ε m g κ hε.le).snd
  have hs : HasCompactSupport (fun x => χ x • (field ε m g κ x).2) := χ.hasCompactSupport.smul_right
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hc (by norm_num)
  have hl : LipschitzWith (max 0 K) (fun x => dampedField ε m g κ (χ x) x) :=
    (LipschitzWith.const (1:ℝ)).prodMk hK
  obtain ⟨γ,h₀,hγ⟩ := KFCausalGlobalLipschitzODE.exists_global
    (fun x => dampedField ε m g κ (χ x) x) (dampedField_contDiff ε m g κ hε.le χ χ.contDiff) _ hl x₀
  have hb := hbound (fun t => χ (γ t)) γ h₀ (fun _ _ => ⟨χ.nonneg,χ.le_one⟩)
    (fun t _ => hγ t)
  refine ⟨γ,h₀,?_⟩
  intro t ht
  have hχ : χ (γ t) = 1 := χ.one_of_mem_closedBall (by
    rw [mem_closedBall_zero_iff]
    exact (hb t ht).trans (by change B ≤ B+1; linarith))
  simpa only [hχ,dampedField_one] using hγ t

theorem exists_global (ε m g κ : ℝ) (hε : 0 < ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 < κ) (x₀ : TimePhase) :
    ∃ γ : ℝ → TimePhase, γ 0 = x₀ ∧ ∀ t, HasDerivAt γ (field ε m g κ (γ t)) t := by
  have hv : ContMDiff 𝓘(ℝ,TimePhase) (𝓘(ℝ,TimePhase)).tangent 1
      (fun x : TimePhase => (⟨x,field ε m g κ x⟩ : TangentBundle 𝓘(ℝ,TimePhase) TimePhase)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr (field_contDiff ε m g κ hε.le)
  have hw (a : ℝ) : ∃ γ : ℝ → TimePhase, γ 0 = x₀ ∧
      IsMIntegralCurveOn (I := 𝓘(ℝ,TimePhase)) γ (field ε m g κ) (Ioo (-a) a) := by
    obtain ⟨γ,h₀,hγ⟩ := exists_window ε m g κ hε hm hg hκ x₀ |a| (abs_nonneg a)
    refine ⟨γ,h₀,?_⟩
    intro t ht
    rw [hasMFDerivWithinAt_iff_hasFDerivWithinAt]
    exact (hγ t ⟨by linarith [ht.1,le_abs_self a],by linarith [ht.2,le_abs_self a]⟩).hasDerivWithinAt
  obtain ⟨γ,h₀,hγ⟩ := (exists_isMIntegralCurve_iff_exists_isMIntegralCurveOn_Ioo hv x₀).mpr hw
  refine ⟨γ,h₀,?_⟩
  intro t
  rw [hasDerivAt_iff_hasFDerivAt,← hasMFDerivAt_iff_hasFDerivAt]
  exact hγ t

theorem global_unique (ε m g κ : ℝ) (hε : 0 ≤ ε) (γ η : ℝ → TimePhase)
    (hγ : ∀ t, HasDerivAt γ (field ε m g κ (γ t)) t)
    (hη : ∀ t, HasDerivAt η (field ε m g κ (η t)) t) (h₀ : γ 0 = η 0) : γ = η := by
  have hv : ContMDiff 𝓘(ℝ,TimePhase) (𝓘(ℝ,TimePhase)).tangent 1
      (fun x : TimePhase => (⟨x,field ε m g κ x⟩ : TangentBundle 𝓘(ℝ,TimePhase) TimePhase)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr (field_contDiff ε m g κ hε)
  have hγ' : IsMIntegralCurve (I := 𝓘(ℝ,TimePhase)) γ (field ε m g κ) := by
    intro t
    rw [hasMFDerivAt_iff_hasFDerivAt]
    exact (hγ t).hasFDerivAt
  have hη' : IsMIntegralCurve (I := 𝓘(ℝ,TimePhase)) η (field ε m g κ) := by
    intro t
    rw [hasMFDerivAt_iff_hasFDerivAt]
    exact (hη t).hasFDerivAt
  exact isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hv hγ' hη' h₀

theorem exists_unique_global (ε m g κ : ℝ) (hε : 0 < ε) (hm : 0 ≤ m) (hg : 0 ≤ g)
    (hκ : 0 < κ) (x₀ : TimePhase) :
    ∃! γ : ℝ → TimePhase, γ 0 = x₀ ∧ ∀ t, HasDerivAt γ (field ε m g κ (γ t)) t := by
  obtain ⟨γ,h₀,hγ⟩ := exists_global ε m g κ hε hm hg hκ x₀
  refine ⟨γ,⟨h₀,hγ⟩,?_⟩
  intro η hη
  exact global_unique ε m g κ hε.le η γ hη.2 hγ (hη.1.trans h₀.symm)

#print axioms exists_window
#print axioms exists_global
#print axioms global_unique
#print axioms exists_unique_global

end
end UnifiedTheory.Audit.KFCausalClassicalMatterGlobal
