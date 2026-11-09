/- The adjoint of the original radial test is the same test with opposite
neutral-position frequency. This follows from its actual L2 multiplier. -/
import UnifiedTheory.Audit.KFCausalUnitaryMultiplierPairing
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialCutoff

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalNeutralPositionRadialAdjoint
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCutoff
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (scalar)

theorem symbol_conj (h δ v : ℝ) (x : Joint 2 4) :
    starRingEnd ℂ (symbol h δ (-v) x) = symbol h δ v x := by
  simp only [symbol,scalar,map_mul,Complex.conj_ofReal,← Complex.exp_conj,
    Complex.conj_I,Complex.ofReal_neg,map_neg,neg_mul,mul_neg,neg_neg]

theorem action_dual (h δ v : ℝ) (hδ : 0 < δ) (f g : Hilbert) :
    inner ℂ f (action h δ v hδ g) = inner ℂ (action h δ (-v) hδ f) g :=
  KFCausalUnitaryMultiplierPairing.inner_dual chargeCoordinates
    (action h δ v hδ) (action h δ (-v) hδ) (symbol h δ v) (symbol h δ (-v))
    (action_coe h δ v hδ) (action_coe h δ (-v) hδ) (symbol_conj h δ v) f g

theorem action_adjoint (h δ v : ℝ) (hδ : 0 < δ) :
    (action h δ v hδ).adjoint = action h δ (-v) hδ :=
  ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    (fun f g => (action_dual h δ v hδ f g).symm)).symm

#print axioms symbol_conj
#print axioms action_dual
#print axioms action_adjoint

end
end UnifiedTheory.Audit.KFCausalNeutralPositionRadialAdjoint
