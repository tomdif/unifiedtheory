/- Exact physical masses of displaced packets, clock profiles and momentum
outputs. The momentum remainder is a finite fixed-width Gaussian moment. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedMomentumDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedProfileMass
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedPhysicalPackets
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedMomentumDensity
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources (amplitude source clockFrequency)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentDerivative
  (physicalProfile physicalProfile_memLp clockMultiplier clockPhase_real_norm physicalProfile_derivative gradient)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentMoments (sourcedPacket)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedClockMomentum (profileState momentumOutput)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedRescaling (scale scale_positive)
open UnifiedTheory.Audit.KFCausalClockFloorRecenteredJacobian (translate_scale_integral)
open UnifiedTheory.Audit.KFCausalClockFloorRecenteredMajorant (gaussianEnvelope gaussianEnvelope_integrable gaussianEnvelope_mass)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedPhaseLimit (rescaledPosition)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalClockFloorTrialClockEnergy (dampedClockFunction dampedClockFunction_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms (dampedMass)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization (gaussianMass)
open UnifiedTheory.Audit.KFCausalCoupledFunctionEnergy (toLp_square_integral)

def momentMass (v : Transverse) : ℝ := ∫ ξ : Transverse, momentDensity v ξ

theorem momentMass_nonnegative (v : Transverse) : 0 ≤ momentMass v :=
  integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)

theorem displacedPacket_mass (h : ℝ) (hh : h ≠ 0) (q k : Joint 2 4) :
    (∫ X : Transverse, ‖amplitude h q k*sourcedPacket (groundWidth h) (neutralWidth h) (source h q k) X‖^2) =
      gaussianMass (groundWidth h) (neutralWidth h) := by
  rw [translate_scale_integral (positionCenter h q k) (scale h) (scale_positive h hh)]
  change (scale h)^5*(∫ ξ, ‖amplitude h q k*sourcedPacket (groundWidth h) (neutralWidth h)
    (source h q k) (rescaledPosition h (positionCenter h q k) ξ)‖^2) = _
  simp_rw [displacedPacket_recenter_square h hh]
  rw [gaussianEnvelope_mass,KFCausalClockFloorDisplacedEnergyIntegral.gaussianMass_scale h hh]

theorem displacedMomentum_mass (h : ℝ) (hh : h ≠ 0) (q k : Joint 2 4) (v : Transverse) :
    (∫ X : Transverse, ‖(-Complex.I*(h:ℂ))*amplitude h q k*
      gradient (groundWidth h) (neutralWidth h) (source h q k) v X‖^2) =
      (scale h)^5*((pairing v (phaseMomentum h q k))^2*gaussianMass (groundWidth 1) (neutralWidth 1)+
        4*|h| *momentMass v) := by
  rw [translate_scale_integral (positionCenter h q k) (scale h) (scale_positive h hh)]
  change (scale h)^5*(∫ ξ, ‖(-Complex.I*(h:ℂ))*amplitude h q k*
    gradient (groundWidth h) (neutralWidth h) (source h q k) v (rescaledPosition h (positionCenter h q k) ξ)‖^2) = _
  simp_rw [displaced_momentum_square h hh,add_mul]
  have he (ξ : Transverse) : 4*|h| *(moment v ξ)^2*gaussianEnvelope 2 ξ = 4*|h| *momentDensity v ξ := by
    unfold momentDensity
    ring
  simp_rw [he]
  rw [integral_add ((gaussianEnvelope_integrable 2 (by norm_num)).const_mul _)
    ((momentDensity_integrable v).const_mul _),integral_const_mul,integral_const_mul,gaussianEnvelope_mass]
  rfl

theorem physicalProfile_square (C : ℂ) (p α β : ℝ) (b : Fin 5 → ℂ) (g : ℝ → ℂ) (z : Configuration) :
    ‖physicalProfile C p α β b g z‖^2 = ‖g z.1‖^2*‖C*sourcedPacket α β b z.2‖^2 := by
  simp only [physicalProfile,clockMultiplier,norm_mul,mul_pow,clockPhase_real_norm,mul_one]
  ring

theorem profileState_mass (h : ℝ) (hh : h ≠ 0) (q k : Joint 2 4) (p : ℝ) (g : ℝ → ℂ) (hg : MemLp g 2) :
    ‖profileState (groundWidth h) (neutralWidth h) (groundWidth_positive h hh)
      (neutralWidth_positive h hh) (neutralWidth_bound h) (amplitude h q k) p (source h q k) g hg‖^2 =
        (∫ s : ℝ, ‖g s‖^2)*gaussianMass (groundWidth h) (neutralWidth h) := by
  have hm := physicalProfile_memLp (amplitude h q k) p (groundWidth h) (neutralWidth h)
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) (source h q k) g hg
  have hi := (memLp_two_iff_integrable_sq_norm hm.1).mp hm
  rw [profileState,toLp_square_integral]
  rw [Measure.volume_eq_prod ℝ Transverse] at hi ⊢
  rw [integral_prod _ hi]
  simp_rw [physicalProfile_square,integral_const_mul,displacedPacket_mass h hh]
  rw [integral_mul_const]

theorem profileMomentum_square (h : ℝ) (C : ℂ) (p α β : ℝ) (b : Fin 5 → ℂ)
    (g : ℝ → ℂ) (v : Transverse) (z : Configuration) :
    ‖-Complex.I*(h:ℂ)‖^2*‖KFCausalTransverseTrialDerivative.derivative v (physicalProfile C p α β b g) z‖^2 =
      ‖g z.1‖^2*‖(-Complex.I*(h:ℂ))*C*gradient α β b v z.2‖^2 := by
  rw [physicalProfile_derivative]
  simp only [clockMultiplier,norm_mul,mul_pow,clockPhase_real_norm,mul_one]
  ring

theorem sourcedMomentum_mass (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (q k : Joint 2 4) (v : Transverse) :
    ‖momentumOutput ε a (groundWidth h) (neutralWidth h) hε ha (groundWidth_positive h hh)
      (neutralWidth_positive h hh) (neutralWidth_bound h) (amplitude h q k) (clockFrequency h k)
      (source h q k) h v‖^2 =
      dampedMass ε a*((scale h)^5*((pairing v (phaseMomentum h q k))^2*gaussianMass (groundWidth 1) (neutralWidth 1)+
        4*|h| *momentMass v)) := by
  rw [momentumOutput,norm_smul,mul_pow,toLp_square_integral,← integral_const_mul]
  simp_rw [profileMomentum_square]
  have hm := (KFCausalClockFloorCoherentDerivative.gradient_memLp (groundWidth h) (neutralWidth h)
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) (source h q k) v).const_mul
      ((-Complex.I*(h:ℂ))*amplitude h q k)
  have hg := dampedClockFunction_memLp ε a hε ha
  have hi := ((memLp_two_iff_integrable_sq_norm hg.1).mp hg).mul_prod
    ((memLp_two_iff_integrable_sq_norm hm.1).mp hm)
  rw [Measure.volume_eq_prod ℝ Transverse,integral_prod _ hi]
  simp_rw [integral_const_mul,displacedMomentum_mass h hh]
  rw [integral_mul_const]
  rfl

#print axioms momentMass_nonnegative
#print axioms displacedPacket_mass
#print axioms displacedMomentum_mass
#print axioms physicalProfile_square
#print axioms profileState_mass
#print axioms profileMomentum_square
#print axioms sourcedMomentum_mass

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedProfileMass
