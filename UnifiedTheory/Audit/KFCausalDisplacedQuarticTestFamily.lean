/- Identify the displaced Gaussian family used to test the signed matter
response. The actual charge orbit, sources and averaged energy domain are
derived. No numerical sign or force/evolution identity is asserted here. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedCentering
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedAveragedDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalDisplacedQuarticTestFamily
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse velocity)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (scale scale_square backward)
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow (momentumScale momentumScale_ne_zero)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalClassicalChargePhase (Phase rotate physicalTail shear)
open UnifiedTheory.Audit.KFCausalDisplacedPhysicalPhase (phase phase_parameter)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedCentering (center_physical frequencies_physical coefficients_eq)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth)

def positionParameter (A : ℝ) : Joint 2 4 := WithLp.toLp 2 fun
  | .inl _ => 0
  | .inr i => ![0,0,-scale*A,-A] i

def momentumParameter (A lam h : ℝ) : Joint 2 4 := WithLp.toLp 2 fun
  | .inl _ => 0
  | .inr i => ![0,0,0,-lam/(A*momentumScale h)] i

def testPhase (A lam : ℝ) : Phase :=
  (WithLp.toLp 2 (fun
    | .inl _ => 0
    | .inr i => ![0,0,scale*A,A] i),
   WithLp.toLp 2 (fun
    | .inl _ => 0
    | .inr i => ![0,0,0,-lam/A] i))

def position (A θ : ℝ) : Transverse := ![0,0,A/2*Real.cos θ,A/2*Real.cos θ,A]
def momentum (A lam θ : ℝ) : Transverse := ![0,0,A/2*Real.sin θ,-(A/2)*Real.sin θ,-lam/A]

theorem position_clock (A : ℝ) : positionParameter A (.inr 0) = 0 := rfl

theorem momentum_fixed (A lam h θ : ℝ) :
    parameter θ (momentumParameter A lam h) = momentumParameter A lam h := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [parameter,KFCausalPairedRotation.rotate,momentumParameter]

theorem phase_eq (A lam h : ℝ) (hA : A ≠ 0) (hh : h ≠ 0) :
    phase h (positionParameter A) (momentumParameter A lam h) = testPhase A lam := by
  ext i <;> rcases i with i | i <;> fin_cases i <;>
    simp [phase,positionParameter,momentumParameter,testPhase]
  field_simp [hA,momentumScale_ne_zero h hh]

theorem position_center (A lam θ : ℝ) :
    physicalTail (rotate (-θ) (testPhase A lam)).1 = position A θ := by
  funext i
  fin_cases i <;> simp [physicalTail,rotate,testPhase,backward,position]
  all_goals ring_nf; rw [scale_square]; ring

theorem momentum_center (A lam θ : ℝ) :
    physicalTail (rotate (-θ) (testPhase A lam)).2 = momentum A lam θ := by
  funext i
  fin_cases i <;> simp [physicalTail,rotate,testPhase,backward,momentum]
  all_goals ring_nf; rw [scale_square]; ring

theorem actual_center (A lam h θ : ℝ) (hA : A ≠ 0) (hh : h ≠ 0) :
    KFCausalClockFloorDisplacedCentering.center
      (vParameter h (parameter θ (momentumParameter A lam h)))
      (wParameter h (parameter θ (positionParameter A))) = position A θ := by
  rw [center_physical,phase_parameter,phase_eq A lam h hA hh,position_center]

theorem actual_frequencies (A lam h θ : ℝ) (hA : A ≠ 0) (hh : h ≠ 0) :
    KFCausalClockFloorDisplacedCentering.frequencies
      (uParameter h (parameter θ (positionParameter A)))
      (rParameter h (parameter θ (momentumParameter A lam h))) =
      fun i => momentum A lam θ i/h := by
  rw [frequencies_physical h hh,phase_parameter,phase_eq A lam h hA hh,momentum_center]

theorem actual_source (A lam h θ : ℝ) (hA : A ≠ 0) (hh : h ≠ 0) :
    source h (parameter θ (positionParameter A)) (parameter θ (momentumParameter A lam h)) =
      KFCausalClockFloorCenteredGaussian.source (groundWidth h) (neutralWidth h)
        (position A θ) (fun i => momentum A lam θ i/h) := by
  unfold source
  rw [coefficients_eq,actual_center A lam h θ hA hh,actual_frequencies A lam h θ hA hh]

theorem amplitude_norm (A lam h θ : ℝ) (hA : A ≠ 0) (hh : h ≠ 0) :
    ‖amplitude h (parameter θ (positionParameter A)) (parameter θ (momentumParameter A lam h))‖ =
      Real.exp (-(groundWidth h*A^2*(Real.cos θ)^2/2+neutralWidth h*A^2)) := by
  rw [amplitude,KFCausalClockFloorDisplacedCentering.constant_eq,norm_mul,
    KFCausalFourierTranslation.phase_norm,one_mul,actual_center A lam h θ hA hh,
    KFCausalClockFloorCenteredGaussian.amplitude,Complex.norm_exp]
  simp only [Complex.neg_re,Complex.ofReal_re]
  congr 1
  simp [KFCausalClockFloorCenteredGaussian.realQuadratic,
    KFCausalClockFloorCenteredGaussian.weight,position,Fin.sum_univ_succ]
  ring

theorem frequency_zero (A lam h θ : ℝ) :
    clockFrequency h (parameter θ (momentumParameter A lam h)) = 0 := by
  rw [momentum_fixed]
  simp [clockFrequency,frequency,rParameter,KFCausalEuclideanProductCoordinates.split,
    KFCausalNormalizedChargeFlow.dilate,momentumParameter]
  rfl

theorem classical_field (A lam θ : ℝ) :
    KFCausalClassicalMatterSymbols.fieldValue (rotate (-θ) (testPhase A lam)) = A*(1+Real.cos θ) := by
  rw [KFCausalClassicalMatterSymbols.fieldValue,position_center]
  simp [KFCausalMatterOrderedDomain.pointField_apply,position]
  ring

theorem classical_shear (A lam θ : ℝ) (hA : A ≠ 0) :
    shear (rotate (-θ) (testPhase A lam)) = -lam*Real.cos θ := by
  unfold shear
  rw [position_center,momentum_center]
  simp [velocity,position,momentum,Fin.sum_univ_succ]
  field_simp [hA]
  ring

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (A lam : ℝ)

local notation "S" => KFCausalClockFloorDisplacedStates.state ε a h hε ha hh
  (positionParameter A) (momentumParameter A lam h)

theorem state_norm : ‖S‖ = 1 :=
  KFCausalClockFloorDisplacedStates.state_norm ε a h hε ha hh _ _

include hb in
theorem energy_domain (mass2 quartic vacuum t : ℝ) :
    S ∈ (KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
      (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hb)
      hh mass2 quartic vacuum t).domain :=
  KFCausalClockFloorDisplacedAveragedDomain.state_mem_energy_domain
    ε a h hε ha hh hb mass2 quartic vacuum t _ _ (position_clock A)

#print axioms position_clock
#print axioms momentum_fixed
#print axioms phase_eq
#print axioms position_center
#print axioms momentum_center
#print axioms actual_center
#print axioms actual_frequencies
#print axioms actual_source
#print axioms amplitude_norm
#print axioms frequency_zero
#print axioms classical_field
#print axioms classical_shear
#print axioms state_norm
#print axioms energy_domain
end
end UnifiedTheory.Audit.KFCausalDisplacedQuarticTestFamily
