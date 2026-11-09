/- The two original antisymmetric physical momenta are exactly their
maximal charge-coordinate multiplication operators, in both directions. -/
import UnifiedTheory.Audit.KFCausalAntisymmetricMomentumCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalAntisymmetricMomentumGraphEquivalence
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalPhysicalTransverseMomentum (transverseMomentum transverseMomentum_selfAdjoint)
open KFCausalAntisymmetricMomentumCoordinates (antiDirection antiSymbol antisymmetric_graph_coe)
open KFCausalUnitaryRealMultiplier (realPullback realPullback_graph realPullback_domain)
open KFCausalRealMultiplierSelfAdjoint (realPullback_symmetric)

theorem antiSymbol_measurable (h : ℝ) (i : Fin 2) : Measurable (antiSymbol h i) := by
  unfold antiSymbol
  fun_prop

theorem antisymmetric_eq_multiplier (h : ℝ) (hh : h ≠ 0) (i : Fin 2) :
    transverseMomentum h (antiDirection i) =
      realPullback chargeCoordinates (antiSymbol h i) (antiSymbol_measurable h i) := by
  let A := transverseMomentum h (antiDirection i)
  let B := realPullback chargeCoordinates (antiSymbol h i) (antiSymbol_measurable h i)
  have hle : A ≤ B := by
    apply LinearPMap.le_graph_iff.mp
    rintro ⟨f,g⟩ hfg
    exact (realPullback_graph chargeCoordinates (antiSymbol h i) _ f g).mpr
      (antisymmetric_graph_coe h hh i f g hfg)
  have hsa : IsSelfAdjoint A := transverseMomentum_selfAdjoint h (antiDirection i)
  have hsym : A.IsFormalAdjoint B := by
    intro f g
    have he : A f=B ⟨f,hle.1 f.property⟩ := hle.2 rfl
    rw [he]
    exact realPullback_symmetric chargeCoordinates (antiSymbol h i) _ ⟨f,hle.1 f.property⟩ g
  have hrev := hsym.le_adjoint hsa.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hsa] at hrev
  exact le_antisymm hle hrev

theorem antisymmetric_graph_iff (h : ℝ) (hh : h ≠ 0) (i : Fin 2) (f g : Hilbert) :
    (f,g) ∈ (transverseMomentum h (antiDirection i)).graph ↔
      chargeCoordinates g =ᵐ[volume] fun x => (antiSymbol h i x:ℂ)*(chargeCoordinates f) x := by
  rw [antisymmetric_eq_multiplier h hh i]
  exact realPullback_graph _ _ _ f g

theorem antisymmetric_domain_iff (h : ℝ) (hh : h ≠ 0) (i : Fin 2) (f : Hilbert) :
    f ∈ (transverseMomentum h (antiDirection i)).domain ↔
      MemLp (fun x => (antiSymbol h i x:ℂ)*(chargeCoordinates f) x) 2 := by
  rw [antisymmetric_eq_multiplier h hh i]
  exact realPullback_domain _ _ _ f

#print axioms antiSymbol_measurable
#print axioms antisymmetric_eq_multiplier
#print axioms antisymmetric_graph_iff
#print axioms antisymmetric_domain_iff
end
end UnifiedTheory.Audit.KFCausalAntisymmetricMomentumGraphEquivalence
