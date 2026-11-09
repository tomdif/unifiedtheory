/- The physical displacement parameters supported on the neutral
coordinate have a constant charge orbit. Their exact Gaussian source and
normalization identify the projected profile, without a source hypothesis. -/
import UnifiedTheory.Audit.KFCausalNeutralExponentialProfiles

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalNeutralDisplacedSources
noncomputable section
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (scale)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources
open UnifiedTheory.Audit.KFCausalProjectedPolynomialLocalKernel
open UnifiedTheory.Audit.KFCausalPolynomialLocalGram
open UnifiedTheory.Audit.KFCausalNeutralExponentialProfiles

def neutralParameter (d : ℝ) : Joint 2 4 := WithLp.toLp 2 fun
  | .inl _ => 0
  | .inr i => ![0,0,0,d] i

def neutralCoefficient (h Q K : ℝ) : ℂ :=
  -2*(neutralWidth h:ℂ)*(Q:ℂ)+2*(Real.pi:ℂ)*Complex.I*(K:ℂ)
def neutralAmplitude (h Q : ℝ) : ℂ :=
  Complex.exp (-((neutralWidth h*Q^2:ℝ):ℂ))
def displacedProfile (h Q K : ℝ) (P : Polynomial ℂ) : ℂ → ℂ :=
  exponentialProfile (neutralCoefficient h Q K) (neutralAmplitude h Q) P

theorem parameter_neutral (θ d : ℝ) :
    KFCausalChargeModulationFlow.parameter θ (neutralParameter d) = neutralParameter d := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [KFCausalChargeModulationFlow.parameter,KFCausalPairedRotation.rotate,neutralParameter]

theorem neutral_parameter_values (h d : ℝ) :
    uParameter h (neutralParameter d) = 0 ∧
    vParameter h (neutralParameter d) = 0 ∧
    rParameter h (neutralParameter d) = WithLp.toLp 2 ![0,0,0,d] ∧
    wParameter h (neutralParameter d) = WithLp.toLp 2 ![0,0,0,d] := by
  refine ⟨?_,?_,?_,?_⟩ <;> ext i <;>
    simp [uParameter,vParameter,rParameter,wParameter,neutralParameter,
      KFCausalEuclideanProductCoordinates.split_fst,
      KFCausalEuclideanProductCoordinates.split_snd,KFCausalNormalizedChargeFlow.dilate]

theorem sourceCurve_neutral (h Q K θ : ℝ) :
    sourceCurve h (neutralParameter Q) (neutralParameter K) θ =
      neutralSource (neutralCoefficient h Q K) := by
  simp only [sourceCurve,parameter_neutral,source,
    (neutral_parameter_values h Q).1,(neutral_parameter_values h K).2.1,
    (neutral_parameter_values h K).2.2.1,(neutral_parameter_values h Q).2.2.2]
  funext i
  fin_cases i <;> simp [coefficients,neutralSource,neutralCoefficient]

theorem amplitudeCurve_neutral (h Q K θ : ℝ) :
    amplitudeCurve h (neutralParameter Q) (neutralParameter K) θ = neutralAmplitude h Q := by
  simp [amplitudeCurve,parameter_neutral,amplitude,
    (neutral_parameter_values h Q).1,(neutral_parameter_values h K).2.1,
    (neutral_parameter_values h Q).2.2.2,constant,
    KFCausalFourierTranslation.phase,neutralAmplitude]

theorem meanFactor_neutral (ε h Q K : ℝ) (P : Polynomial ℂ)
    (n : Fin 3) (s : ℝ) (x : Transverse) :
    meanFactor ε h (neutralParameter Q) (neutralParameter K) P n s x =
      profileFactor (groundWidth h) (neutralWidth h) (scale ε (-h/2) s)
        (displacedProfile h Q K P) n x := by
  unfold displacedProfile
  rw [exponentialProfile_factor]
  simp [meanFactor,angleFactor,sourceCurve_neutral,amplitudeCurve_neutral]

#print axioms parameter_neutral
#print axioms neutral_parameter_values
#print axioms sourceCurve_neutral
#print axioms amplitudeCurve_neutral
#print axioms meanFactor_neutral
end
end UnifiedTheory.Audit.KFCausalNeutralDisplacedSources
