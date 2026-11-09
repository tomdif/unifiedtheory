/- Maximal self-adjoint transverse momenta in physical configuration
coordinates. Their spectral coordinates are the ordinary physical Fourier
coordinates, not the coupled longitudinal straightening coordinates. -/
import UnifiedTheory.Audit.KFCausalRealMultiplierSelfAdjoint
import UnifiedTheory.Audit.KFCausalEuclideanConfiguration

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalPhysicalTransverseMomentum
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalUnitaryRealMultiplier
open UnifiedTheory.Audit.KFCausalRealMultiplierSelfAdjoint

def transverseVector (v : Transverse) : Space := WithLp.toLp 2 (Fin.cons 0 v)

theorem split_transverse_add (v : Transverse) (t : ℝ) (x : Space) :
    split (x+t • transverseVector v)=((split x).1,(split x).2+t • v) := by
  rw [split_apply,split_apply]
  ext i
  · simp [transverseVector]
  · simp [transverseVector]

def transverseSymbol (hbar : ℝ) (v : Transverse) (k : Space) : ℝ :=
  2*Real.pi*hbar*inner ℝ k (transverseVector v)

theorem transverseSymbol_continuous (hbar : ℝ) (v : Transverse) :
    Continuous (transverseSymbol hbar v) := by unfold transverseSymbol; fun_prop

def transverseMomentum (hbar : ℝ) (v : Transverse) : Hilbert →ₗ.[ℂ] Hilbert :=
  realPullback fourierCoordinates (transverseSymbol hbar v)
    (transverseSymbol_continuous hbar v).measurable

theorem transverseMomentum_selfAdjoint (hbar : ℝ) (v : Transverse) :
    IsSelfAdjoint (transverseMomentum hbar v) := realPullback_selfAdjoint _ _ _

theorem transverseMomentum_closed (hbar : ℝ) (v : Transverse) :
    (transverseMomentum hbar v).IsClosed := (transverseMomentum_selfAdjoint hbar v).isClosed

theorem transverseMomentum_dense (hbar : ℝ) (v : Transverse) :
    Dense ((transverseMomentum hbar v).domain : Set Hilbert) :=
  (transverseMomentum_selfAdjoint hbar v).dense_domain

theorem transverseMomentum_graph (hbar : ℝ) (v : Transverse) (f g : Hilbert) :
    (f,g) ∈ (transverseMomentum hbar v).graph ↔
      fourierCoordinates g =ᵐ[volume] fun k => (transverseSymbol hbar v k:ℂ)*(fourierCoordinates f) k :=
  realPullback_graph _ _ _ f g

theorem transverseMomentum_domain (hbar : ℝ) (v : Transverse) (f : Hilbert) :
    f ∈ (transverseMomentum hbar v).domain ↔
      MemLp (fun k => (transverseSymbol hbar v k:ℂ)*(fourierCoordinates f) k) 2 :=
  realPullback_domain _ _ _ f

theorem transverseMomentum_energy (hbar : ℝ) (v : Transverse)
    (f : (transverseMomentum hbar v).domain) :
    ‖transverseMomentum hbar v f‖^2 =
      ∫ k, (transverseSymbol hbar v k)^2*‖(fourierCoordinates (f:Hilbert)) k‖^2 :=
  realPullback_norm_square _ _ _ f

#print axioms split_transverse_add
#print axioms transverseSymbol_continuous
#print axioms transverseMomentum_selfAdjoint
#print axioms transverseMomentum_closed
#print axioms transverseMomentum_dense
#print axioms transverseMomentum_graph
#print axioms transverseMomentum_domain
#print axioms transverseMomentum_energy

end
end UnifiedTheory.Audit.KFCausalPhysicalTransverseMomentum
