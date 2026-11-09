/- The signed physical field is a maximal self-adjoint multiplication
operator. Its domain is derived from weighted L2, not supplied as an
assumption; the previously constructed field-square domain is stronger. -/
import UnifiedTheory.Audit.KFCausalRealMultiplierSelfAdjoint
import UnifiedTheory.Audit.KFCausalTransverseFieldSquare

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalPhysicalField
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalUnitaryRealMultiplier
open UnifiedTheory.Audit.KFCausalRealMultiplierSelfAdjoint
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare

def physicalField (l : Transverse →L[ℝ] ℝ) : Hilbert →ₗ.[ℂ] Hilbert :=
  realPullback (LinearIsometryEquiv.refl ℂ Hilbert) (fun z : Configuration => l z.2)
    (l.continuous.comp continuous_snd).measurable

theorem physicalField_selfAdjoint (l : Transverse →L[ℝ] ℝ) : IsSelfAdjoint (physicalField l) :=
  realPullback_selfAdjoint _ _ _

theorem physicalField_closed (l : Transverse →L[ℝ] ℝ) : (physicalField l).IsClosed :=
  (physicalField_selfAdjoint l).isClosed

theorem physicalField_dense (l : Transverse →L[ℝ] ℝ) : Dense ((physicalField l).domain : Set Hilbert) :=
  (physicalField_selfAdjoint l).dense_domain

theorem physicalField_graph (l : Transverse →L[ℝ] ℝ) (f g : Hilbert) :
    (f,g) ∈ (physicalField l).graph ↔ g =ᵐ[volume] fun z : Configuration => (l z.2:ℂ)*f z :=
  realPullback_graph (LinearIsometryEquiv.refl ℂ Hilbert) _ _ f g

theorem physicalField_domain (l : Transverse →L[ℝ] ℝ) (f : Hilbert) :
    f ∈ (physicalField l).domain ↔ MemLp (fun z : Configuration => (l z.2:ℂ)*f z) 2 :=
  realPullback_domain (LinearIsometryEquiv.refl ℂ Hilbert) _ _ f

theorem fieldSquare_domain_le_physicalField (l : Transverse →L[ℝ] ℝ) :
    (fieldSquare l).domain ≤ (physicalField l).domain := by
  intro f hf
  exact (physicalField_domain l f).mpr (fieldSquare_linear_energy l f hf)

#print axioms physicalField_selfAdjoint
#print axioms physicalField_closed
#print axioms physicalField_dense
#print axioms physicalField_graph
#print axioms physicalField_domain
#print axioms fieldSquare_domain_le_physicalField

end
end UnifiedTheory.Audit.KFCausalPhysicalField
