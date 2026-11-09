/- The generic completed square is the actual displaced state's analytic
packet, including its neutral shear. Its centre and phase frequencies are
identified with the physical phase coordinates before any limit is taken. -/
import UnifiedTheory.Audit.KFCausalClockFloorCenteredGaussian
import UnifiedTheory.Audit.KFCausalDisplacedPhysicalPhase

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedCentering
noncomputable section
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Block Joint)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (scale scale_square)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (Grouped complexScale complexScale_square)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds (position coherentPacket)
open UnifiedTheory.Audit.KFCausalClassicalChargePhase (physicalTail)
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow (momentumScale)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth)

private theorem u_apply (h : ℝ) (q : Joint 2 4) (i : Fin 2) :
    uParameter h q i = -((momentumScale h)⁻¹*q (.inl i)) := rfl
private theorem v_apply (h : ℝ) (k : Joint 2 4) (i : Fin 2) :
    vParameter h k i = momentumScale h*k (.inl i) := rfl
private theorem r_apply (h : ℝ) (k : Joint 2 4) (i : Fin 4) : rParameter h k i = k (.inr i) := rfl
private theorem w_apply (h : ℝ) (q : Joint 2 4) (i : Fin 4) : wParameter h q i = q (.inr i) := rfl

def center (v : Block 2) (w : Block 4) : Fin 5 → ℝ :=
  ![-scale*(v 0+w 1),scale*(v 0-w 1),-scale*(v 1+w 2),scale*(v 1-w 2),-w 3]

def frequencies (u : Block 2) (r : Block 4) : Fin 5 → ℝ :=
  ![2*Real.pi*scale*(u 0+r 1),2*Real.pi*scale*(r 1-u 0),
    2*Real.pi*scale*(u 1+r 2),2*Real.pi*scale*(r 2-u 1),2*Real.pi*r 3]

theorem center_physical (h : ℝ) (q k : Joint 2 4) :
    center (vParameter h k) (wParameter h q) = physicalTail (KFCausalDisplacedPhysicalPhase.phase h q k).1 := by
  funext i
  fin_cases i <;> simp [center,physicalTail,KFCausalPairedModeCoordinates.backward,
    KFCausalDisplacedPhysicalPhase.phase,v_apply,w_apply] <;> ring_nf
  all_goals simp

theorem frequencies_physical (h : ℝ) (hh : h ≠ 0) (q k : Joint 2 4) :
    frequencies (uParameter h q) (rParameter h k) =
      fun i => physicalTail (KFCausalDisplacedPhysicalPhase.phase h q k).2 i/h := by
  funext i
  fin_cases i <;> simp [frequencies,physicalTail,KFCausalPairedModeCoordinates.backward,
    KFCausalDisplacedPhysicalPhase.phase,u_apply,r_apply,momentumScale]
  all_goals field_simp [hh] <;> ring

theorem coefficients_eq (α β : ℝ) (u v : Block 2) (r w : Block 4) :
    coefficients α β u v r w = KFCausalClockFloorCenteredGaussian.source α β (center v w) (frequencies u r) := by
  funext i
  fin_cases i <;> simp [coefficients,KFCausalClockFloorCenteredGaussian.source,
    KFCausalClockFloorCenteredGaussian.weight,center,frequencies] <;> ring

theorem constant_eq (α β : ℝ) (u v : Block 2) (w : Block 4) :
    constant α β u v w = KFCausalFourierTranslation.phase u v *
      KFCausalClockFloorCenteredGaussian.amplitude α β (center v w) := by
  unfold constant KFCausalClockFloorCenteredGaussian.amplitude
  congr 2
  congr 1
  simp [KFCausalClockFloorCenteredGaussian.realQuadratic,
    KFCausalClockFloorCenteredGaussian.weight,center,Fin.sum_univ_succ]
  have hs : (scale:ℂ)^2 = (1/2:ℂ) := by
    rw [← Complex.ofReal_pow,scale_square]
    norm_num
  ring_nf
  rw [hs]
  ring

theorem quadratic_position (α β : ℝ) (z : ℂ) (x : Grouped) :
    KFCausalClockFloorCenteredGaussian.quadratic α β (position z x) =
      KFCausalClockFloorShearBounds.quadratic α β z x.1 x.2 := by
  simp [KFCausalClockFloorCenteredGaussian.quadratic,KFCausalClockFloorCenteredGaussian.weight,
    position,KFCausalClockFloorCoherentBounds.neutral,KFCausalClockFloorShearBounds.quadratic,
    KFCausalClockFloorShearBounds.squared,Fin.sum_univ_succ]
  ring_nf
  rw [complexScale_square]
  ring

theorem packet_eq (α β : ℝ) (u v : Block 2) (r w : Block 4) (z : ℂ) (x : Grouped) :
    constant α β u v w * coherentPacket α β (coefficients α β u v r w) z x =
      KFCausalFourierTranslation.phase u v *
        KFCausalClockFloorCenteredGaussian.packet α β (center v w) (frequencies u r) (position z x) := by
  rw [constant_eq,coefficients_eq,← KFCausalClockFloorCenteredGaussian.source_identity,
    quadratic_position]
  unfold coherentPacket KFCausalClockFloorCoherentBounds.source KFCausalClockFloorShearBounds.packet
  ring

theorem packet_norm (α β : ℝ) (u v : Block 2) (r w : Block 4) (z : ℂ) (x : Grouped) :
    ‖constant α β u v w * coherentPacket α β (coefficients α β u v r w) z x‖ =
      ‖KFCausalClockFloorCenteredGaussian.packet α β (center v w) (frequencies u r) (position z x)‖ := by
  rw [packet_eq,norm_mul,KFCausalFourierTranslation.phase_norm,one_mul]

theorem displaced_packet_norm (h : ℝ) (hh : h ≠ 0) (q k : Joint 2 4) (z : ℂ) (x : Grouped) :
    ‖amplitude h q k * coherentPacket (groundWidth h) (neutralWidth h) (source h q k) z x‖ =
      ‖KFCausalClockFloorCenteredGaussian.packet (groundWidth h) (neutralWidth h)
        (physicalTail (KFCausalDisplacedPhysicalPhase.phase h q k).1)
        (fun i => physicalTail (KFCausalDisplacedPhysicalPhase.phase h q k).2 i/h) (position z x)‖ := by
  rw [amplitude,source,packet_norm,center_physical,frequencies_physical h hh]

#print axioms center_physical
#print axioms frequencies_physical
#print axioms coefficients_eq
#print axioms constant_eq
#print axioms quadratic_position
#print axioms packet_eq
#print axioms packet_norm
#print axioms displaced_packet_norm

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedCentering
