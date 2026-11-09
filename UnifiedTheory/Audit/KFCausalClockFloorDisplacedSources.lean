/- Actual complex Gaussian sources for the enlarged physical state family.
When the clock displacement vanishes, the clock function remains fixed and
all transverse displacements and phases are encoded by explicit sources.
This identifies representatives; averaged energy control is still separate. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedBoostOrbit
import UnifiedTheory.Audit.KFCausalClockFloorCoherentDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Block Joint split)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (scale scale_square)
open UnifiedTheory.Audit.KFCausalFourierTranslation (phase phase_norm)
open UnifiedTheory.Audit.KFCausalFourierPhasePackets
open UnifiedTheory.Audit.KFCausalChargeGaussianProducts
open UnifiedTheory.Audit.KFCausalChargeGaussianIdentities (norm_two_square)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSources (linearSource)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip (clockPhase)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentDerivative (physicalProfile clockMultiplier)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentMoments (sourcedPacket)
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedStates (rawState)
open UnifiedTheory.Audit.KFCausalDisplacedPairedCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
  (clockFunction clockFunction_continuous clockFunction_memLp neutralWidth neutralWidth_positive)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)

def constant (α β : ℝ) (u v : Block 2) (w : Block 4) : ℂ :=
  phase u v * Complex.exp (-((α*((v 0)^2+(v 1)^2+(w 1)^2+(w 2)^2)+β*(w 3)^2:ℝ):ℂ))

def frequency (r : Block 4) : ℝ := 2*Real.pi*r 0

def coefficients (α β : ℝ) (u v : Block 2) (r w : Block 4) : Fin 5 → ℂ :=
  ![(scale:ℂ)*(-2*α*v 0+2*Real.pi*Complex.I*u 0-2*α*w 1+2*Real.pi*Complex.I*r 1),
    (scale:ℂ)*(2*α*v 0-2*Real.pi*Complex.I*u 0-2*α*w 1+2*Real.pi*Complex.I*r 1),
    (scale:ℂ)*(-2*α*v 1+2*Real.pi*Complex.I*u 1-2*α*w 2+2*Real.pi*Complex.I*r 2),
    (scale:ℂ)*(2*α*v 1-2*Real.pi*Complex.I*u 1-2*α*w 2+2*Real.pi*Complex.I*r 2),
    -2*β*w 3+2*Real.pi*Complex.I*r 3]

def positionProfile (α β : ℝ) (g : ℝ → ℂ) (u v : Block 2) (r w : Block 4)
    (x : KFCausalEuclideanConfiguration.Space) : ℂ :=
  packet u v (gaussian 2 α) (WithLp.toLp 2 ![scale*(x 1-x 2),scale*(x 3-x 4)]) *
    phaseShift r w (spectator α β g)
      (WithLp.toLp 2 ![x 0,scale*(x 1+x 2),scale*(x 3+x 4),x 5])

private theorem exp_product (A B C D E F G H J z : ℂ) (he : A+B+C+D = E+F+G+H+J) :
    (Complex.exp A*Complex.exp B)*(Complex.exp C*(z*Complex.exp D)) =
      ((Complex.exp E*Complex.exp F)*Complex.exp G*z)*(Complex.exp H*Complex.exp J) := by
  calc
    _ = z*Complex.exp (A+B+C+D) := by simp only [Complex.exp_add]; ring
    _ = z*Complex.exp (E+F+G+H+J) := congrArg (fun t => z*Complex.exp t) he
    _ = _ := by simp only [Complex.exp_add]; ring

theorem positionProfile_eq (α β : ℝ) (g : ℝ → ℂ) (u v : Block 2) (r w : Block 4)
    (hw : w 0 = 0) (x : KFCausalEuclideanConfiguration.Space) :
    positionProfile α β g u v r w x =
      physicalProfile (constant α β u v w) (frequency r) α β (coefficients α β u v r w) g
        (KFCausalEuclideanConfiguration.split x) := by
  simp only [positionProfile,packet,modulated,phaseShift,gaussian,← Complex.ofReal_pow,
    norm_two_square,spectator,phase,Real.fourierChar_apply,PiLp.inner_apply,
    Fin.sum_univ_succ,RCLike.inner_apply,conj_trivial,physicalProfile,clockMultiplier,
    sourcedPacket,constant,frequency,clockPhase,linearSource,coefficients,
    KFCausalClockFloorShearBounds.physicalGaussian,KFCausalEuclideanConfiguration.split_apply]
  dsimp
  rw [hw,add_zero]
  apply exp_product
  push_cast
  have hs : (scale:ℂ)^2 = (1/2:ℂ) := by
    rw [← Complex.ofReal_pow,scale_square]
    norm_num
  ring_nf
  rw [hs]
  ring

theorem constant_norm_le_one (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (u v : Block 2) (w : Block 4) : ‖constant α β u v w‖ ≤ 1 := by
  rw [constant,norm_mul,phase_norm,one_mul,Complex.norm_exp,Real.exp_le_one_iff]
  simp only [Complex.neg_re,Complex.ofReal_re]
  exact neg_nonpos.mpr (add_nonneg (mul_nonneg hα (by positivity)) (mul_nonneg hβ (sq_nonneg _)))

def uParameter (h : ℝ) (q : Joint 2 4) : Block 2 := -(split 2 4 (dilate (momentumScale h)⁻¹ q)).1
def vParameter (h : ℝ) (k : Joint 2 4) : Block 2 := (split 2 4 (dilate (momentumScale h) k)).1
def rParameter (h : ℝ) (k : Joint 2 4) : Block 4 := (split 2 4 (dilate (momentumScale h) k)).2
def wParameter (h : ℝ) (q : Joint 2 4) : Block 4 := (split 2 4 (dilate (momentumScale h)⁻¹ q)).2

def amplitude (h : ℝ) (q k : Joint 2 4) : ℂ :=
  constant (groundWidth h) (neutralWidth h) (uParameter h q) (vParameter h k) (wParameter h q)

def clockFrequency (h : ℝ) (k : Joint 2 4) : ℝ := frequency (rParameter h k)

def source (h : ℝ) (q k : Joint 2 4) : Fin 5 → ℂ :=
  coefficients (groundWidth h) (neutralWidth h) (uParameter h q) (vParameter h k)
    (rParameter h k) (wParameter h q)

theorem rawState_position_coe (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (q k : Joint 2 4) :
    KFCausalEuclideanConfiguration.euclideanPullback (rawState ε a h hε ha hh q k) =ᵐ[volume]
      positionProfile (groundWidth h) (neutralWidth h) (clockFunction ε a)
        (uParameter h q) (vParameter h k) (rParameter h k) (wParameter h q) := by
  rw [rawState_packetState]
  exact packetState_position_coe _ _ _ _ _ _ _

theorem rawState_configuration_coe (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (q k : Joint 2 4) (hq : q (.inr 0) = 0) :
    rawState ε a h hε ha hh q k =ᵐ[volume]
      physicalProfile (amplitude h q k) (clockFrequency h k) (groundWidth h) (neutralWidth h)
        (source h q k) (clockFunction ε a) := by
  have he : (fun x : KFCausalEuclideanConfiguration.Space => rawState ε a h hε ha hh q k
      (KFCausalEuclideanConfiguration.split x)) =ᵐ[volume]
      fun x => physicalProfile (amplitude h q k) (clockFrequency h k) (groundWidth h) (neutralWidth h)
        (source h q k) (clockFunction ε a) (KFCausalEuclideanConfiguration.split x) := by
    filter_upwards [KFCausalEuclideanConfiguration.euclideanPullback_coe (rawState ε a h hε ha hh q k),
      rawState_position_coe ε a h hε ha hh q k] with x hx hy
    exact hx.symm.trans (hy.trans (positionProfile_eq _ _ _ _ _ _ _ hq x))
  have ht := KFCausalEuclideanConfiguration.split_preserves_volume.symm.quasiMeasurePreserving.ae he
  filter_upwards [ht] with x hx
  simpa only [MeasurableEquiv.apply_symm_apply] using hx

theorem amplitude_norm_le_one (h : ℝ) (hh : h ≠ 0) (q k : Joint 2 4) : ‖amplitude h q k‖ ≤ 1 :=
  constant_norm_le_one _ _ (groundWidth_positive h hh).le (neutralWidth_positive h hh).le _ _ _

theorem boostOrbit_configuration_coe (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (p : KFCausalCoupledLongitudinalFlow.Configuration) (θ : ℝ) :
    let q := KFCausalChargeModulationFlow.parameter θ
      (KFCausalDisplacedBoostParameters.boostQ h (h⁻¹ • p))
    let k := KFCausalChargeModulationFlow.parameter θ
      (KFCausalDisplacedBoostParameters.boostK (h⁻¹ • p))
    KFCausalPhysicalCircleAction.action h hh θ
      (KFCausalClockFloorBoostedKineticLimit.boostedState ε a h hε ha hh
        (KFCausalClockFloorEvolvedCharacteristics.positionFrequency p.1 p.2)) =ᵐ[volume]
      fun x => (‖KFCausalClockFloorInvariantTrial.trialState ε a h hε ha hh‖⁻¹ : ℝ) •
        physicalProfile (amplitude h q k) (clockFrequency h k) (groundWidth h) (neutralWidth h)
          (source h q k) (clockFunction ε a) x := by
  dsimp only
  rw [KFCausalClockFloorDisplacedBoostOrbit.action_boostedState,
    KFCausalClockFloorDisplacedStates.state_normalization]
  filter_upwards [Lp.coeFn_smul
      (‖KFCausalClockFloorInvariantTrial.trialState ε a h hε ha hh‖⁻¹ : ℝ)
      (rawState ε a h hε ha hh
        (KFCausalChargeModulationFlow.parameter θ (KFCausalDisplacedBoostParameters.boostQ h (h⁻¹ • p)))
        (KFCausalChargeModulationFlow.parameter θ (KFCausalDisplacedBoostParameters.boostK (h⁻¹ • p)))),
    rawState_configuration_coe ε a h hε ha hh _ _
      (KFCausalClockFloorDisplacedBoostOrbit.boost_orbit_clock_displacement h p θ)] with x hx hy
  exact hx.trans (congrArg (fun z : ℂ =>
    (‖KFCausalClockFloorInvariantTrial.trialState ε a h hε ha hh‖⁻¹ : ℝ) • z) hy)

#print axioms positionProfile_eq
#print axioms constant_norm_le_one
#print axioms rawState_position_coe
#print axioms rawState_configuration_coe
#print axioms amplitude_norm_le_one
#print axioms boostOrbit_configuration_coe

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources
