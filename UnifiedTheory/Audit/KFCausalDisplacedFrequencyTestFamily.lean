/- Explicit admissible displaced test packets with arbitrary clock frequency.
The transverse source and its charge-dependent phase are unchanged. This
identifies the family used by the integrated matrix probe; it does not
certify the numerical integration or its signs. -/
import UnifiedTheory.Audit.KFCausalDisplacedQuarticOrbitPhase
import UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalDisplacedFrequencyTestFamily
noncomputable section
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow (momentumScale)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources
open UnifiedTheory.Audit.KFCausalDisplacedQuarticTestFamily
  (positionParameter momentumParameter position momentum)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth)

def frequencyParameter (A lam h p : ℝ) : Joint 2 4 := WithLp.toLp 2 fun
  | .inl _ => 0
  | .inr i => ![p/(2*Real.pi),0,0,-lam/(A*momentumScale h)] i

theorem parameter_fixed (A lam h p θ : ℝ) :
    parameter θ (frequencyParameter A lam h p) = frequencyParameter A lam h p := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [parameter,KFCausalPairedRotation.rotate,frequencyParameter]

theorem frequency_eq (A lam h p θ : ℝ) :
    clockFrequency h (parameter θ (frequencyParameter A lam h p)) = p := by
  rw [parameter_fixed]
  change 2*Real.pi*(p/(2*Real.pi)) = p
  field_simp

theorem amplitude_same (A lam h p θ : ℝ) :
    amplitude h (parameter θ (positionParameter A)) (parameter θ (frequencyParameter A lam h p)) =
      amplitude h (parameter θ (positionParameter A)) (parameter θ (momentumParameter A lam h)) := by
  rw [parameter_fixed,KFCausalDisplacedQuarticTestFamily.momentum_fixed]
  rfl

theorem source_same (A lam h p θ : ℝ) :
    source h (parameter θ (positionParameter A)) (parameter θ (frequencyParameter A lam h p)) =
      source h (parameter θ (positionParameter A)) (parameter θ (momentumParameter A lam h)) := by
  rw [parameter_fixed,KFCausalDisplacedQuarticTestFamily.momentum_fixed]
  funext i
  fin_cases i <;> rfl

theorem amplitude_exact (A lam h p θ : ℝ) (hA : A ≠ 0) (hh : h ≠ 0) :
    amplitude h (parameter θ (positionParameter A)) (parameter θ (frequencyParameter A lam h p)) =
      (Real.exp (-(groundWidth h*A^2*(Real.cos θ)^2/2+neutralWidth h*A^2)):ℂ) := by
  rw [amplitude_same]
  exact KFCausalDisplacedQuarticOrbitPhase.amplitude_exact A lam h θ hA hh

theorem source_exact (A lam h p θ : ℝ) (hA : A ≠ 0) (hh : h ≠ 0) :
    source h (parameter θ (positionParameter A)) (parameter θ (frequencyParameter A lam h p)) =
      KFCausalClockFloorCenteredGaussian.source (groundWidth h) (neutralWidth h)
        (position A θ) (fun i => momentum A lam θ i/h) := by
  rw [source_same]
  exact KFCausalDisplacedQuarticTestFamily.actual_source A lam h θ hA hh

def packet (A lam a h p : ℝ) (ha : 0 < a) : KFCausalDisplacedStructuredResponse.Packet where
  width := a
  width_pos := ha
  centre := positionParameter A
  frequency := frequencyParameter A lam h p
  clock_zero := rfl

theorem packet_width (A lam a h p : ℝ) (ha : 0 < a) :
    (packet A lam a h p ha).width = a := rfl

theorem packet_frequency (A lam a h p θ : ℝ) (ha : 0 < a) :
    clockFrequency h (parameter θ (packet A lam a h p ha).frequency) = p :=
  frequency_eq A lam h p θ

#print axioms parameter_fixed
#print axioms frequency_eq
#print axioms amplitude_same
#print axioms source_same
#print axioms amplitude_exact
#print axioms source_exact
#print axioms packet_width
#print axioms packet_frequency
end
end UnifiedTheory.Audit.KFCausalDisplacedFrequencyTestFamily
