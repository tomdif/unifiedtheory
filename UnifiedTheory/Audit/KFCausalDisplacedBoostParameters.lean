/- Explicit six-component physical momentum phases inside the enlarged
displacement family. The 2*pi Fourier scale and the antisymmetric signs
are derived from the paired physical coordinates. -/
import UnifiedTheory.Audit.KFCausalDisplacedPairedCoordinates
import UnifiedTheory.Audit.KFCausalClockFloorBoostedSpectral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalDisplacedBoostParameters
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Block Joint)
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (scale scale_square)
open UnifiedTheory.Audit.KFCausalFourierTranslation (phase)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (scalar)
open UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics (positionFrequency)
open UnifiedTheory.Audit.KFCausalPhysicalMixedCoordinates
open UnifiedTheory.Audit.KFCausalPhysicalMomentumModulation
open UnifiedTheory.Audit.KFCausalFourierPhasePackets
open UnifiedTheory.Audit.KFCausalDisplacedPairedCoordinates
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (euclideanPullback euclideanPullback_coe)

def antisymmetricFrequency (p : Configuration) : Block 2 :=
  WithLp.toLp 2 ![scale*(p.2 0-p.2 1)/(2*Real.pi),scale*(p.2 2-p.2 3)/(2*Real.pi)]

def spectatorFrequency (p : Configuration) : Block 4 :=
  WithLp.toLp 2 ![p.1/(2*Real.pi),scale*(p.2 0+p.2 1)/(2*Real.pi),
    scale*(p.2 2+p.2 3)/(2*Real.pi),p.2 4/(2*Real.pi)]

def boostQ (h : ℝ) (p : Configuration) : Joint 2 4 := WithLp.toLp 2 fun
  | .inl i => -(momentumScale h)*antisymmetricFrequency p i
  | .inr _ => 0

def boostK (p : Configuration) : Joint 2 4 := WithLp.toLp 2 fun
  | .inl _ => 0
  | .inr i => spectatorFrequency p i

theorem boost_shift (h : ℝ) (hh : h ≠ 0) (p : Configuration) :
    KFCausalEuclideanProductCoordinates.split 2 4 (dilate (momentumScale h)⁻¹ (boostQ h p)) =
      (-antisymmetricFrequency p,0) := by
  apply Prod.ext
  · ext i
    change (momentumScale h)⁻¹*(-(momentumScale h)*antisymmetricFrequency p i) =
      -antisymmetricFrequency p i
    field_simp [momentumScale_ne_zero h hh]
  · rfl

theorem boost_phase (h : ℝ) (p : Configuration) :
    KFCausalEuclideanProductCoordinates.split 2 4 (dilate (momentumScale h) (boostK p)) =
      (0,spectatorFrequency p) := by
  apply Prod.ext
  · ext i
    change momentumScale h*0 = 0
    exact mul_zero _
  · rfl

theorem physical_phase (p : Configuration) (x : KFCausalEuclideanConfiguration.Space) :
    phase (antisymmetricFrequency p)
        (WithLp.toLp 2 ![scale*(x 1-x 2),scale*(x 3-x 4)]) *
      phase (spectatorFrequency p)
        (WithLp.toLp 2 ![x 0,scale*(x 1+x 2),scale*(x 3+x 4),x 5]) =
      scalar (positionFrequency p.1 p.2 (KFCausalEuclideanConfiguration.split x)) := by
  simp only [phase,Real.fourierChar_apply,scalar,← Complex.exp_add]
  congr 1
  simp only [PiLp.inner_apply,Fin.sum_univ_succ,RCLike.inner_apply,conj_trivial,
    antisymmetricFrequency,spectatorFrequency,positionFrequency,
    ContinuousLinearMap.coe_mk',LinearMap.coe_mk,AddHom.coe_mk,
    KFCausalEuclideanConfiguration.split_apply,KFCausalPhysicalGaussianConcentration.dot]
  dsimp
  push_cast
  have hs : (scale : ℂ)^2 = (1/2 : ℂ) := by
    rw [← Complex.ofReal_pow,scale_square]
    norm_num
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring_nf
  rw [hs]
  ring

theorem packetState_boost (h : ℝ) (hh : h ≠ 0) (p : Configuration)
    (f : Block 2 → ℂ) (g : Block 4 → ℂ) (hf : MemLp f 2) (hg : MemLp g 2) :
    packetState (momentumScale h) (boostQ h p) (boostK p) f g hf hg =
      modulation (positionFrequency p.1 p.2) (pairedState (hf.toLp f) (hg.toLp g)) := by
  apply euclideanPullback.injective
  apply Lp.ext
  filter_upwards [packetState_position_coe (momentumScale h) (boostQ h p) (boostK p) f g hf hg,
    euclideanPullback_coe (modulation (positionFrequency p.1 p.2) (pairedState (hf.toLp f) (hg.toLp g))),
    KFCausalEuclideanConfiguration.split_preserves_volume.quasiMeasurePreserving.ae
      (modulation_coe (positionFrequency p.1 p.2) (pairedState (hf.toLp f) (hg.toLp g))),
    euclideanPullback_coe (pairedState (hf.toLp f) (hg.toLp g)),
    pairedState_position_coe f g hf hg] with x hx hy hz hw hv
  rw [boost_shift h hh,boost_phase] at hx
  simp only [neg_neg,packet,modulated,phaseShift,add_zero] at hx
  simp only [Function.comp_apply] at hy hw
  rw [hy,hz,← hw,hv,hx,← physical_phase p x]
  ring

#print axioms boost_shift
#print axioms boost_phase
#print axioms physical_phase
#print axioms packetState_boost

end
end UnifiedTheory.Audit.KFCausalDisplacedBoostParameters
