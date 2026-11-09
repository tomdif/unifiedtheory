/- Schwartz transverse packets have the actual derivative energy needed
by the coupled tail-repair estimate, after the Euclidean coordinate lift. -/
import UnifiedTheory.Audit.KFCausalEuclideanClockSplit
import UnifiedTheory.Audit.KFCausalTransverseDerivativeScaling
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalSchwartzTransversePacket
noncomputable section
open MeasureTheory
open scoped LineDeriv
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalTransverseDerivativeScaling

def transverseLinearEquiv : Transverse ≃L[ℝ] TailSpace :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 5 => ℝ)).symm

def unflattenSchwartz (ψ : SchwartzMap TailSpace ℂ) : SchwartzMap Transverse ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ transverseLinearEquiv ψ

theorem unflattenSchwartz_coe (ψ : SchwartzMap TailSpace ℂ) :
    (unflattenSchwartz ψ : Transverse → ℂ) = ψ ∘ transverseCoordinates := rfl

def directionalSchwartz (ψ : SchwartzMap TailSpace ℂ) : SchwartzMap Transverse ℂ :=
  ∂_{direction} (unflattenSchwartz ψ)

theorem directionalSchwartz_apply (ψ : SchwartzMap TailSpace ℂ) (x : Transverse) :
    directionalSchwartz ψ x = directionalDerivative (ψ ∘ transverseCoordinates) x := by
  rw [directionalSchwartz,SchwartzMap.lineDerivOp_apply]
  rfl

theorem packet_directional_memLp (ψ : SchwartzMap TailSpace ℂ) :
    MemLp (directionalDerivative (ψ ∘ transverseCoordinates)) 2 := by
  have he : (directionalSchwartz ψ : Transverse → ℂ) = directionalDerivative (ψ ∘ transverseCoordinates) :=
    funext (directionalSchwartz_apply ψ)
  rw [← he]
  exact (directionalSchwartz ψ).memLp 2 volume

theorem packet_directional_energy (ψ : SchwartzMap TailSpace ℂ) :
    Integrable (fun x => ‖directionalDerivative (ψ ∘ transverseCoordinates) x‖^2) :=
  (memLp_two_iff_integrable_sq_norm (packet_directional_memLp ψ).aestronglyMeasurable).mp
    (packet_directional_memLp ψ)

#print axioms unflattenSchwartz_coe
#print axioms directionalSchwartz_apply
#print axioms packet_directional_memLp
#print axioms packet_directional_energy

end
end UnifiedTheory.Audit.KFCausalSchwartzTransversePacket
