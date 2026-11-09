/- The transverse Fourier symbol characterizes the entire natural momentum
graph, in both directions. The reverse implication follows from actual
self-adjointness, without a smooth-state or product-domain restriction. -/
import UnifiedTheory.Audit.KFCausalChargeDualMomentum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalChargeDualMomentumDomain
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalChargeTransverseSplit
open UnifiedTheory.Audit.KFCausalChargeDualMomentum
open UnifiedTheory.Audit.KFCausalDirectionalTranslationMomentum
open UnifiedTheory.Audit.KFCausalUnitaryRealMultiplier
open UnifiedTheory.Audit.KFCausalRealMultiplierSelfAdjoint

theorem dualSymbol_measurable (h : ℝ) (v : Joint 2 4) : Measurable (dualSymbol h v) := by
  unfold dualSymbol
  fun_prop

theorem spectralMomentum_eq_dual (h : ℝ) (hne : h ≠ 0) (v : Joint 2 4)
    (hv : v (.inr 0) = 0) :
    spectralMomentum h v = realPullback dualMixed (dualSymbol h v) (dualSymbol_measurable h v) := by
  let A := spectralMomentum h v
  let B := realPullback dualMixed (dualSymbol h v) (dualSymbol_measurable h v)
  have hle : A ≤ B := by
    apply LinearPMap.le_graph_iff.mp
    rintro ⟨f,g⟩ hfg
    exact (realPullback_graph dualMixed (dualSymbol h v) _ f g).mpr
      (dualMomentum_graph_coe h hne v hv f g hfg)
  have hsa : IsSelfAdjoint A :=
    realPullback_selfAdjoint _ _ _
  have hsym : A.IsFormalAdjoint B := by
    intro f g
    have he : A f = B ⟨f,hle.1 f.property⟩ := hle.2 rfl
    rw [he]
    exact realPullback_symmetric dualMixed (dualSymbol h v) _ ⟨f,hle.1 f.property⟩ g
  have hrev := hsym.le_adjoint hsa.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hsa] at hrev
  exact le_antisymm hle hrev

theorem dualMomentum_graph_iff (h : ℝ) (hne : h ≠ 0) (v : Joint 2 4)
    (hv : v (.inr 0) = 0) (f g : JointHilbert 2 4) :
    (f,g) ∈ (spectralMomentum h v).graph ↔
      dualMixed g =ᵐ[volume] fun x => (dualSymbol h v x : ℂ)*(dualMixed f) x := by
  rw [spectralMomentum_eq_dual h hne v hv]
  exact realPullback_graph _ _ _ _ _

theorem dualMomentum_domain_iff (h : ℝ) (hne : h ≠ 0) (v : Joint 2 4)
    (hv : v (.inr 0) = 0) (f : JointHilbert 2 4) :
    f ∈ (spectralMomentum h v).domain ↔
      MemLp (fun x => (dualSymbol h v x : ℂ)*(dualMixed f) x) 2 := by
  rw [spectralMomentum_eq_dual h hne v hv]
  exact realPullback_domain _ _ _ _

#print axioms dualSymbol_measurable
#print axioms spectralMomentum_eq_dual
#print axioms dualMomentum_graph_iff
#print axioms dualMomentum_domain_iff
end
end UnifiedTheory.Audit.KFCausalChargeDualMomentumDomain
