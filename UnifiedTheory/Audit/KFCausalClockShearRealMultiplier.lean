/- Real bounded clock multipliers preserve the full shear momentum graph.
Their mixed shear expectations are real; this is an actual domain statement. -/
import UnifiedTheory.Audit.KFCausalTransverseShearGraphCommutation
import UnifiedTheory.Audit.KFCausalSelfAdjointCoreWeakGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockShearRealMultiplier
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum
open UnifiedTheory.Audit.KFCausalTransverseShearClockCommutation (clock_multiplier)
open UnifiedTheory.Audit.KFCausalSelfAdjointCoreWeakGraph (graph_iff_weak)

theorem clock_graph (Q : Hilbert →L[ℂ] Hilbert) (w : ℝ → ℂ)
    (hq : ∀ f : Hilbert, Q f =ᵐ[volume] fun x => w x.1*f x)
    (h : ℝ) (hne : h ≠ 0) (f j : Hilbert) (hfj : (f,j) ∈ (shearMomentum h).graph) :
    (Q f,Q j) ∈ (shearMomentum h).graph :=
  KFCausalStrongUnitaryProductDerivative.graph_of_commutes shearGroup h hne Q
    (clock_multiplier Q w hq) f j hfj

theorem real_symmetric (Q : Hilbert →L[ℂ] Hilbert) (w : ℝ → ℝ)
    (hq : ∀ f : Hilbert, Q f =ᵐ[volume] fun x => (w x.1:ℂ)*f x) (f g : Hilbert) :
    inner ℂ (Q f) g = inner ℂ f (Q g) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hq f,hq g] with x hf hg
  rw [hf,hg]
  change inner ℂ ((w x.1:ℂ) • f x) (g x) = inner ℂ (f x) ((w x.1:ℂ) • g x)
  rw [inner_smul_left,inner_smul_right]
  simp only [Complex.conj_ofReal]

theorem real_shear_pairing (Q : Hilbert →L[ℂ] Hilbert) (w : ℝ → ℝ)
    (hq : ∀ f : Hilbert, Q f =ᵐ[volume] fun x => (w x.1:ℂ)*f x)
    (h : ℝ) (hne : h ≠ 0) (f j : Hilbert) (hfj : (f,j) ∈ (shearMomentum h).graph) :
    (inner ℂ f (Q j)).im = 0 := by
  have hQ := clock_graph Q (fun s => (w s:ℂ)) hq h hne f j hfj
  have he := (graph_iff_weak _ (shear_selfAdjoint h hne) (Q f) (Q j)).mp hQ f j hfj
  rw [← real_symmetric Q w hq j f] at he
  have hi := congrArg Complex.im he
  have hs : (inner ℂ (Q j) f).im = -(inner ℂ f (Q j)).im :=
    inner_im_symm (𝕜 := ℂ) (Q j) f
  linarith

theorem defect_shear_pairing (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
    (f j : Hilbert) (hfj : (f,j) ∈ (shearMomentum h).graph) :
    (inner ℂ f (KFCausalClockFloorDefectOperator.defectOperator ε hε j)).im = 0 :=
  real_shear_pairing _ (KFCausalClockFloorCanonicalDefect.defect ε)
    (KFCausalClockFloorDefectOperator.defectOperator_coe ε hε) h hne f j hfj

#print axioms clock_graph
#print axioms real_symmetric
#print axioms real_shear_pairing
#print axioms defect_shear_pairing
end
end UnifiedTheory.Audit.KFCausalClockShearRealMultiplier
