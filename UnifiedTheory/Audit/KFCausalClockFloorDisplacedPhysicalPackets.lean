/- Real physical packets with their exact displaced centres and canonical
momenta. These identities retain the amplitude/source cancellation before
computing the clock and transverse momentum energies. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedFieldSymbols

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedPhysicalPackets
noncomputable section
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalClassicalChargePhase (physicalTail)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources (source amplitude)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedCentering
open UnifiedTheory.Audit.KFCausalClockFloorCoherentMoments (sourcedPacket)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSources (linearSource)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (physicalGaussian)
open UnifiedTheory.Audit.KFCausalClockFloorCenteredGaussian (weight realQuadratic packet)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedRescaling (scale scale_groundWidth scale_neutralWidth)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedPhaseLimit (rescaledPosition)
open UnifiedTheory.Audit.KFCausalClockFloorCenteredEstimates (energy)
open UnifiedTheory.Audit.KFCausalClockFloorRecenteredMajorant (gaussianEnvelope)

def positionCenter (h : ℝ) (q k : Joint 2 4) : Transverse :=
  physicalTail (KFCausalDisplacedPhysicalPhase.phase h q k).1
def phaseMomentum (h : ℝ) (q k : Joint 2 4) : Transverse :=
  physicalTail (KFCausalDisplacedPhysicalPhase.phase h q k).2

theorem source_physical (h : ℝ) (hh : h ≠ 0) (q k : Joint 2 4) :
    source h q k = KFCausalClockFloorCenteredGaussian.source (groundWidth h) (neutralWidth h)
      (positionCenter h q k) (fun i => phaseMomentum h q k i/h) := by
  rw [source,coefficients_eq,center_physical,frequencies_physical h hh]
  rfl

theorem physicalGaussian_quadratic (α β : ℝ) (X : Transverse) :
    physicalGaussian α β X = Complex.exp (-KFCausalClockFloorCenteredGaussian.quadratic α β (fun i => (X i:ℂ))) := by
  rw [KFCausalClockFloorCenteredDensityLimit.quadratic_real]
  unfold physicalGaussian
  congr 2
  simp [realQuadratic,weight,Fin.sum_univ_succ]
  ring

theorem sourcedPacket_centered (α β : ℝ) (Q R X : Transverse) :
    KFCausalClockFloorCenteredGaussian.amplitude α β Q *
      sourcedPacket α β (KFCausalClockFloorCenteredGaussian.source α β Q R) X =
        packet α β Q R (fun i => (X i:ℂ)) := by
  rw [sourcedPacket,physicalGaussian_quadratic,← mul_assoc]
  exact KFCausalClockFloorCenteredGaussian.source_identity α β Q R _

theorem displacedPacket_norm (h : ℝ) (hh : h ≠ 0) (q k : Joint 2 4) (X : Transverse) :
    ‖amplitude h q k*sourcedPacket (groundWidth h) (neutralWidth h) (source h q k) X‖ =
      ‖packet (groundWidth h) (neutralWidth h) (positionCenter h q k)
        (fun i => phaseMomentum h q k i/h) (fun i => (X i:ℂ))‖ := by
  rw [source_physical h hh]
  unfold positionCenter
  rw [amplitude,constant_eq,center_physical,mul_assoc,
    sourcedPacket_centered,norm_mul,KFCausalFourierTranslation.phase_norm,one_mul]

theorem weight_scale (h : ℝ) (hh : h ≠ 0) (i : Fin 5) :
    (scale h)^2*weight (groundWidth h) (neutralWidth h) i = weight (groundWidth 1) (neutralWidth 1) i := by
  fin_cases i
  all_goals first | exact scale_groundWidth h hh | exact scale_neutralWidth h hh

theorem realQuadratic_scale (h : ℝ) (hh : h ≠ 0) (ξ : Transverse) :
    (scale h)^2*realQuadratic (groundWidth h) (neutralWidth h) ξ = energy ξ := by
  unfold realQuadratic energy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_assoc,weight_scale h hh]

theorem displacedPacket_recenter_square (h : ℝ) (hh : h ≠ 0) (q k : Joint 2 4) (ξ : Transverse) :
    ‖amplitude h q k*sourcedPacket (groundWidth h) (neutralWidth h) (source h q k)
      (rescaledPosition h (positionCenter h q k) ξ)‖^2 = gaussianEnvelope 2 ξ := by
  rw [displacedPacket_norm h hh]
  change ‖packet (groundWidth h) (neutralWidth h) (positionCenter h q k) _
    (fun i => ((positionCenter h q k i+scale h*ξ i:ℝ):ℂ))‖^2 = _
  rw [KFCausalClockFloorCenteredGaussian.packet_real_recenter,
    neg_mul,realQuadratic_scale h hh,← Real.exp_nat_mul]
  unfold gaussianEnvelope
  congr 1
  norm_num only [Nat.cast_ofNat]
  ring

#print axioms source_physical
#print axioms physicalGaussian_quadratic
#print axioms sourcedPacket_centered
#print axioms displacedPacket_norm
#print axioms weight_scale
#print axioms realQuadratic_scale
#print axioms displacedPacket_recenter_square

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedPhysicalPackets
