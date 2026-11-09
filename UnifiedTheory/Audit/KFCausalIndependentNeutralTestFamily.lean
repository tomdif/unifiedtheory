/- Displaced test packets with independent charged radius, neutral position,
neutral momentum, clock width and clock frequency. The exact charge-orbit
source and amplitude are derived before using this larger family in probes.
No field-energy estimate or response identity along evolution is asserted. -/
import UnifiedTheory.Audit.KFCausalDisplacedQuarticTestFamily
import UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalIndependentNeutralTestFamily
noncomputable section
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse velocity)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (scale scale_square backward)
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow (momentumScale momentumScale_ne_zero)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalClassicalChargePhase (Phase rotate physicalTail shear)
open UnifiedTheory.Audit.KFCausalDisplacedPhysicalPhase (phase phase_parameter)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedCentering
  (center_physical frequencies_physical coefficients_eq)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth)

def positionParameter (A B : ℝ) : Joint 2 4 := WithLp.toLp 2 fun
  | .inl _ => 0
  | .inr i => ![0,0,-scale*A,-B] i

def frequencyParameter (P h p : ℝ) : Joint 2 4 := WithLp.toLp 2 fun
  | .inl _ => 0
  | .inr i => ![p/(2*Real.pi),0,0,P/momentumScale h] i

def testPhase (A B P : ℝ) : Phase :=
  (WithLp.toLp 2 (fun
    | .inl _ => 0
    | .inr i => ![0,0,scale*A,B] i),
   WithLp.toLp 2 (fun
    | .inl _ => 0
    | .inr i => ![0,0,0,P] i))

def position (A B θ : ℝ) : Transverse := ![0,0,A/2*Real.cos θ,A/2*Real.cos θ,B]
def momentum (A P θ : ℝ) : Transverse := ![0,0,A/2*Real.sin θ,-(A/2)*Real.sin θ,P]

theorem parameter_fixed (P h p θ : ℝ) :
    parameter θ (frequencyParameter P h p) = frequencyParameter P h p := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [parameter,KFCausalPairedRotation.rotate,frequencyParameter]

theorem phase_eq (A B P h : ℝ) (hh : h ≠ 0) :
    phase h (positionParameter A B) (frequencyParameter P h 0) = testPhase A B P := by
  ext i <;> rcases i with i | i <;> fin_cases i <;>
    simp [phase,positionParameter,frequencyParameter,testPhase]
  field_simp [momentumScale_ne_zero h hh]

theorem position_center (A B P θ : ℝ) :
    physicalTail (rotate (-θ) (testPhase A B P)).1 = position A B θ := by
  funext i
  fin_cases i <;> simp [physicalTail,rotate,testPhase,backward,position]
  all_goals ring_nf; rw [scale_square]; ring

theorem momentum_center (A B P θ : ℝ) :
    physicalTail (rotate (-θ) (testPhase A B P)).2 = momentum A P θ := by
  funext i
  fin_cases i <;> simp [physicalTail,rotate,testPhase,backward,momentum]
  all_goals ring_nf; rw [scale_square]; ring

theorem actual_center (A B P h p θ : ℝ) (hh : h ≠ 0) :
    KFCausalClockFloorDisplacedCentering.center
      (vParameter h (parameter θ (frequencyParameter P h p)))
      (wParameter h (parameter θ (positionParameter A B))) = position A B θ := by
  rw [parameter_fixed]
  have hz : vParameter h (frequencyParameter P h p) =
      vParameter h (parameter θ (frequencyParameter P h 0)) := by
    rw [parameter_fixed]
    rfl
  rw [hz,center_physical,phase_parameter,phase_eq A B P h hh,position_center]

theorem actual_frequencies (A B P h p θ : ℝ) (hh : h ≠ 0) :
    KFCausalClockFloorDisplacedCentering.frequencies
      (uParameter h (parameter θ (positionParameter A B)))
      (rParameter h (parameter θ (frequencyParameter P h p))) =
      fun i => momentum A P θ i/h := by
  rw [parameter_fixed]
  have hz : KFCausalClockFloorDisplacedCentering.frequencies
      (uParameter h (parameter θ (positionParameter A B)))
      (rParameter h (frequencyParameter P h p)) =
      KFCausalClockFloorDisplacedCentering.frequencies
      (uParameter h (parameter θ (positionParameter A B)))
      (rParameter h (parameter θ (frequencyParameter P h 0))) := by
    rw [parameter_fixed]
    funext i
    fin_cases i <;> rfl
  rw [hz,frequencies_physical h hh,phase_parameter,phase_eq A B P h hh,momentum_center]

theorem source_exact (A B P h p θ : ℝ) (hh : h ≠ 0) :
    source h (parameter θ (positionParameter A B)) (parameter θ (frequencyParameter P h p)) =
      KFCausalClockFloorCenteredGaussian.source (groundWidth h) (neutralWidth h)
        (position A B θ) (fun i => momentum A P θ i/h) := by
  unfold source
  rw [coefficients_eq,actual_center A B P h p θ hh,actual_frequencies A B P h p θ hh]

theorem orbit_v_zero (P h p θ : ℝ) :
    vParameter h (parameter θ (frequencyParameter P h p)) = 0 := by
  rw [parameter_fixed]
  ext i
  fin_cases i <;> simp [vParameter,KFCausalEuclideanProductCoordinates.split,
    KFCausalNormalizedChargeFlow.dilate,frequencyParameter]
  all_goals rfl

theorem amplitude_exact (A B P h p θ : ℝ) (hh : h ≠ 0) :
    amplitude h (parameter θ (positionParameter A B)) (parameter θ (frequencyParameter P h p)) =
      (Real.exp (-(groundWidth h*A^2*(Real.cos θ)^2/2+neutralWidth h*B^2)):ℂ) := by
  rw [amplitude,KFCausalClockFloorDisplacedCentering.constant_eq]
  have hp : KFCausalFourierTranslation.phase
      (uParameter h (parameter θ (positionParameter A B)))
      (vParameter h (parameter θ (frequencyParameter P h p))) = 1 := by
    rw [orbit_v_zero]
    simp [KFCausalFourierTranslation.phase]
  rw [hp,one_mul,actual_center A B P h p θ hh,
    KFCausalClockFloorCenteredGaussian.amplitude,Complex.ofReal_exp]
  congr 1
  simp only [KFCausalClockFloorCenteredGaussian.realQuadratic,
    KFCausalClockFloorCenteredGaussian.weight,position,Fin.sum_univ_succ]
  norm_num
  push_cast
  ring

theorem frequency_eq (P h p θ : ℝ) :
    clockFrequency h (parameter θ (frequencyParameter P h p)) = p := by
  rw [parameter_fixed]
  change 2*Real.pi*(p/(2*Real.pi)) = p
  field_simp

theorem classical_field (A B P θ : ℝ) :
    KFCausalClassicalMatterSymbols.fieldValue (rotate (-θ) (testPhase A B P)) =
      B+A*Real.cos θ := by
  rw [KFCausalClassicalMatterSymbols.fieldValue,position_center]
  simp [KFCausalMatterOrderedDomain.pointField_apply,position]
  ring

theorem classical_shear (A B P θ : ℝ) :
    shear (rotate (-θ) (testPhase A B P)) = A*P*Real.cos θ := by
  unfold shear
  rw [position_center,momentum_center]
  simp [velocity,position,momentum,Fin.sum_univ_succ]
  ring

def packet (A B P a h p : ℝ) (ha : 0 < a) : KFCausalDisplacedStructuredResponse.Packet where
  width := a
  width_pos := ha
  centre := positionParameter A B
  frequency := frequencyParameter P h p
  clock_zero := rfl

theorem packet_width (A B P a h p : ℝ) (ha : 0 < a) :
    (packet A B P a h p ha).width = a := rfl

theorem packet_frequency (A B P a h p θ : ℝ) (ha : 0 < a) :
    clockFrequency h (parameter θ (packet A B P a h p ha).frequency) = p :=
  frequency_eq P h p θ

theorem energy_domain (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (A B P p mass2 quartic vacuum t : ℝ) :
    KFCausalClockFloorDisplacedStates.state ε a h hε ha hh
      (positionParameter A B) (frequencyParameter P h p) ∈
      (KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
        (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hb)
        hh mass2 quartic vacuum t).domain :=
  KFCausalClockFloorDisplacedAveragedDomain.state_mem_energy_domain
    ε a h hε ha hh hb mass2 quartic vacuum t _ _ rfl

#print axioms parameter_fixed
#print axioms phase_eq
#print axioms position_center
#print axioms momentum_center
#print axioms actual_center
#print axioms actual_frequencies
#print axioms source_exact
#print axioms orbit_v_zero
#print axioms amplitude_exact
#print axioms frequency_eq
#print axioms classical_field
#print axioms classical_shear
#print axioms packet_width
#print axioms packet_frequency
#print axioms energy_domain
end
end UnifiedTheory.Audit.KFCausalIndependentNeutralTestFamily
