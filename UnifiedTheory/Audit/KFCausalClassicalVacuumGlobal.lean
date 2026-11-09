/- Global existence and uniqueness for the actual full classical vacuum ODE.
A compact cutoff constructs a curve on each finite window. The uniform bound
keeps that cutoff identically one; uniqueness glues these exact solutions. -/
import UnifiedTheory.Audit.KFCausalClassicalVacuumUniformBound
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalClassicalVacuumGlobal
noncomputable section
open Set
open scoped Manifold NNReal
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth
open UnifiedTheory.Audit.KFCausalCanonicalPhaseODE
open UnifiedTheory.Audit.KFCausalClassicalVacuumDamping
open UnifiedTheory.Audit.KFCausalClassicalVacuumUniformBound

theorem exists_window (ε κ : ℝ) (hε : 0 < ε) (hκ : 0 < κ)
    (x₀ : TimePhase) (T : ℝ) (hT : 0 ≤ T) :
    ∃ γ : ℝ → TimePhase, γ 0 = x₀ ∧
      ∀ t ∈ Icc (-T) T, HasDerivAt γ (field ε κ (γ t)) t := by
  obtain ⟨B,hB,hbound⟩ := finite_window_bound ε κ hε hκ x₀ T hT
  let χ : ContDiffBump (0 : TimePhase) := ⟨B+1,B+2,by linarith,by linarith⟩
  have hc : ContDiff ℝ 1 (fun x => χ x • (field ε κ x).2) :=
    χ.contDiff.smul (field_contDiff ε κ hε.le).snd
  have hs : HasCompactSupport (fun x => χ x • (field ε κ x).2) := χ.hasCompactSupport.smul_right
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hc (by norm_num)
  have hl : LipschitzWith (max 0 K) (fun x => dampedField ε κ (χ x) x) :=
    (LipschitzWith.const (1:ℝ)).prodMk hK
  obtain ⟨γ,h₀,hγ⟩ := KFCausalGlobalLipschitzODE.exists_global
    (fun x => dampedField ε κ (χ x) x) (dampedField_contDiff ε κ hε.le χ χ.contDiff) _ hl x₀
  have hb := hbound (fun t => χ (γ t)) γ h₀ (fun _ _ => ⟨χ.nonneg,χ.le_one⟩)
    (fun t _ => hγ t)
  refine ⟨γ,h₀,?_⟩
  intro t ht
  have hχ : χ (γ t) = 1 := χ.one_of_mem_closedBall (by
    rw [mem_closedBall_zero_iff]
    exact (hb t ht).trans (by change B ≤ B+1; linarith))
  simpa only [hχ,dampedField_one] using hγ t

theorem exists_global (ε κ : ℝ) (hε : 0 < ε) (hκ : 0 < κ) (x₀ : TimePhase) :
    ∃ γ : ℝ → TimePhase, γ 0 = x₀ ∧ ∀ t, HasDerivAt γ (field ε κ (γ t)) t := by
  have hv : ContMDiff 𝓘(ℝ,TimePhase) (𝓘(ℝ,TimePhase)).tangent 1
      (fun x : TimePhase => (⟨x,field ε κ x⟩ : TangentBundle 𝓘(ℝ,TimePhase) TimePhase)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr (field_contDiff ε κ hε.le)
  have hw (a : ℝ) : ∃ γ : ℝ → TimePhase, γ 0 = x₀ ∧
      IsMIntegralCurveOn (I := 𝓘(ℝ,TimePhase)) γ (field ε κ) (Ioo (-a) a) := by
    obtain ⟨γ,h₀,hγ⟩ := exists_window ε κ hε hκ x₀ |a| (abs_nonneg a)
    refine ⟨γ,h₀,?_⟩
    intro t ht
    rw [hasMFDerivWithinAt_iff_hasFDerivWithinAt]
    exact (hγ t ⟨by linarith [ht.1,le_abs_self a],by linarith [ht.2,le_abs_self a]⟩).hasDerivWithinAt
  obtain ⟨γ,h₀,hγ⟩ := (exists_isMIntegralCurve_iff_exists_isMIntegralCurveOn_Ioo hv x₀).mpr hw
  refine ⟨γ,h₀,?_⟩
  intro t
  rw [hasDerivAt_iff_hasFDerivAt,← hasMFDerivAt_iff_hasFDerivAt]
  exact hγ t

theorem global_unique (ε κ : ℝ) (hε : 0 ≤ ε) (γ η : ℝ → TimePhase)
    (hγ : ∀ t, HasDerivAt γ (field ε κ (γ t)) t)
    (hη : ∀ t, HasDerivAt η (field ε κ (η t)) t) (h₀ : γ 0 = η 0) : γ = η := by
  have hv : ContMDiff 𝓘(ℝ,TimePhase) (𝓘(ℝ,TimePhase)).tangent 1
      (fun x : TimePhase => (⟨x,field ε κ x⟩ : TangentBundle 𝓘(ℝ,TimePhase) TimePhase)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr (field_contDiff ε κ hε)
  have hγ' : IsMIntegralCurve (I := 𝓘(ℝ,TimePhase)) γ (field ε κ) := by
    intro t
    rw [hasMFDerivAt_iff_hasFDerivAt]
    exact (hγ t).hasFDerivAt
  have hη' : IsMIntegralCurve (I := 𝓘(ℝ,TimePhase)) η (field ε κ) := by
    intro t
    rw [hasMFDerivAt_iff_hasFDerivAt]
    exact (hη t).hasFDerivAt
  exact isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hv hγ' hη' h₀

#print axioms exists_window
#print axioms exists_global
#print axioms global_unique

end
end UnifiedTheory.Audit.KFCausalClassicalVacuumGlobal
