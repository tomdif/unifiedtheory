/- A physical-coordinate realization of every mixed-coordinate displacement.
The first block uses translated modulations; the spectator block uses
modulated translations. This order accounts for the Fourier phase exactly. -/
import UnifiedTheory.Audit.KFCausalFourierPhasePackets
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedStates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalDisplacedPairedCoordinates
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalPhysicalMixedCoordinates
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow
open UnifiedTheory.Audit.KFCausalChargeDisplacementCovariance
open UnifiedTheory.Audit.KFCausalFourierTranslation (phase shift_preserves_volume)
open UnifiedTheory.Audit.KFCausalFourierPhasePackets

theorem split_add (x y : Joint 2 4) : split 2 4 (x+y) = split 2 4 x+split 2 4 y := rfl

theorem phase_split (k x : Joint 2 4) :
    phase k x = phase (split 2 4 k).1 (split 2 4 x).1 * phase (split 2 4 k).2 (split 2 4 x).2 := by
  rw [phase,inner_split]
  simp only [phase,AddChar.map_add_eq_mul,Circle.coe_mul]

theorem pairedState_charge_coe (f : Block 2 → ℂ) (g : Block 4 → ℂ)
    (hf1 : Integrable f) (hf2 : MemLp f 2) (hg : MemLp g 2) :
    chargeCoordinates (pairedState (hf2.toLp f) (hg.toLp g)) =ᵐ[volume]
      fun x => (𝓕 f) (split 2 4 x).1*g (split 2 4 x).2 := by
  filter_upwards [coordinates_coe 2 4 (mixedCoordinates (pairedState (hf2.toLp f) (hg.toLp g))),
    (split_preserves_volume 2 4).quasiMeasurePreserving.ae
      (mixedCoordinates_functions_coe f g hf1 hf2 hg)] with x hx hy
  exact hx.trans hy

def packetState (c : ℝ) (q k : Joint 2 4) (f : Block 2 → ℂ) (g : Block 4 → ℂ)
    (hf : MemLp f 2) (hg : MemLp g 2) : KFCausalConfigurationTestSpace.Hilbert :=
  pairedState
    ((packet_memLp (-(split 2 4 (dilate c⁻¹ q)).1) (split 2 4 (dilate c k)).1 f hf).toLp
      (packet (-(split 2 4 (dilate c⁻¹ q)).1) (split 2 4 (dilate c k)).1 f))
    ((phaseShift_memLp (split 2 4 (dilate c k)).2 (split 2 4 (dilate c⁻¹ q)).2 g hg).toLp
      (phaseShift (split 2 4 (dilate c k)).2 (split 2 4 (dilate c⁻¹ q)).2 g))

theorem packetState_charge (c : ℝ) (q k : Joint 2 4) (f : Block 2 → ℂ) (g : Block 4 → ℂ)
    (hf1 : Integrable f) (hf2 : MemLp f 2) (hg : MemLp g 2) :
    chargeCoordinates (packetState c q k f g hf2 hg) =
      displacement c q k (chargeCoordinates (pairedState (hf2.toLp f) (hg.toLp g))) := by
  apply Lp.ext
  filter_upwards [pairedState_charge_coe _ _ (packet_integrable _ _ f hf1)
      (packet_memLp (-(split 2 4 (dilate c⁻¹ q)).1) (split 2 4 (dilate c k)).1 f hf2)
      (phaseShift_memLp (split 2 4 (dilate c k)).2 (split 2 4 (dilate c⁻¹ q)).2 g hg),
    displacement_coe c q k (chargeCoordinates (pairedState (hf2.toLp f) (hg.toLp g))),
    (shift_preserves_volume (dilate c⁻¹ q)).quasiMeasurePreserving.ae
      (pairedState_charge_coe f g hf1 hf2 hg)] with x hx hy hz
  change chargeCoordinates (packetState c q k f g hf2 hg) x = _ at hx
  change chargeCoordinates (pairedState (hf2.toLp f) (hg.toLp g)) (x+dilate c⁻¹ q) =
    (𝓕 f) (split 2 4 (x+dilate c⁻¹ q)).1*g (split 2 4 (x+dilate c⁻¹ q)).2 at hz
  rw [hx,hy,hz,fourier_packet,phaseShift,phase_split,split_add,sub_neg_eq_add]
  change _ = phase (split 2 4 (dilate c k)).1 (split 2 4 x).1 *
    phase (split 2 4 (dilate c k)).2 (split 2 4 x).2 *
      ((𝓕 f) ((split 2 4 x).1+(split 2 4 (dilate c⁻¹ q)).1) *
        g ((split 2 4 x).2+(split 2 4 (dilate c⁻¹ q)).2))
  ring

theorem packetState_operator (h : ℝ) (q k : Joint 2 4) (f : Block 2 → ℂ) (g : Block 4 → ℂ)
    (hf1 : Integrable f) (hf2 : MemLp f 2) (hg : MemLp g 2) :
    packetState (momentumScale h) q k f g hf2 hg =
      KFCausalClockFloorDisplacedStates.operator h q k (pairedState (hf2.toLp f) (hg.toLp g)) := by
  apply chargeCoordinates.injective
  rw [packetState_charge _ _ _ _ _ hf1,KFCausalClockFloorDisplacedStates.operator_coordinates]

theorem packetState_position_coe (c : ℝ) (q k : Joint 2 4) (f : Block 2 → ℂ) (g : Block 4 → ℂ)
    (hf : MemLp f 2) (hg : MemLp g 2) :
    KFCausalEuclideanConfiguration.euclideanPullback (packetState c q k f g hf hg) =ᵐ[volume]
      fun x => packet (-(split 2 4 (dilate c⁻¹ q)).1) (split 2 4 (dilate c k)).1 f
        (WithLp.toLp 2 ![KFCausalPairedModeCoordinates.scale*(x 1-x 2),
          KFCausalPairedModeCoordinates.scale*(x 3-x 4)]) *
        phaseShift (split 2 4 (dilate c k)).2 (split 2 4 (dilate c⁻¹ q)).2 g
          (WithLp.toLp 2 ![x 0,KFCausalPairedModeCoordinates.scale*(x 1+x 2),
            KFCausalPairedModeCoordinates.scale*(x 3+x 4),x 5]) :=
  pairedState_position_coe _ _ _ _

theorem rawState_packetState (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (q k : Joint 2 4) :
    KFCausalClockFloorDisplacedStates.rawState ε a h hε ha hh q k =
      packetState (momentumScale h) q k
        (KFCausalChargeGaussianProducts.gaussian 2 (KFCausalChargeGaussianGeometry.groundWidth h))
        (KFCausalChargeGaussianProducts.spectator (KFCausalChargeGaussianGeometry.groundWidth h)
          (KFCausalClockFloorInvariantTrial.neutralWidth h) (KFCausalClockFloorInvariantTrial.clockFunction ε a))
        (KFCausalChargeGaussianProducts.gaussian_memLp 2 _
          (KFCausalChargeGaussianGeometry.groundWidth_positive h hh))
        (KFCausalChargeGaussianProducts.spectator_memLp _ _
          (KFCausalChargeGaussianGeometry.groundWidth_positive h hh)
          (KFCausalClockFloorInvariantTrial.neutralWidth_positive h hh) _
          (KFCausalClockFloorInvariantTrial.clockFunction_continuous ε a)
          (KFCausalClockFloorInvariantTrial.clockFunction_memLp ε a hε ha)) := by
  rw [packetState_operator _ _ _ _ _ (KFCausalChargeGaussianProducts.gaussian_integrable 2 _
    (KFCausalChargeGaussianGeometry.groundWidth_positive h hh))]
  rfl

#print axioms split_add
#print axioms phase_split
#print axioms pairedState_charge_coe
#print axioms packetState_charge
#print axioms packetState_operator
#print axioms packetState_position_coe
#print axioms rawState_packetState

end
end UnifiedTheory.Audit.KFCausalDisplacedPairedCoordinates
