/- Exact integrable densities for the actual clock and momentum cross
pairings. This retains the clock damping and every physical direction. -/
import UnifiedTheory.Audit.KFCausalChargedPairKineticOutputs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalChargedPairKineticPairing
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalClockFloorShearBounds (physicalGaussian)
open KFCausalChargedPairCoordinates (pairPolynomial)
open KFCausalChargedPairDifferential
open KFCausalChargedPairKineticOutputs (momentumIndex)
open KFCausalChargedPairHamiltonianForm (baseFactors pairedFactors factorPairing)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorTrialClockEnergy
  (halfClockFunction halfClockFunction_memLp dampedClockFunction dampedClockFunction_memLp)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalClockFloorCoherentDerivative
  (physicalProfile physicalProfile_derivative physicalProfile_derivative_memLp clockMultiplier)
open KFCausalTransverseTrialDerivative (derivative)

def responsePolynomial (α β : ℝ) (v q : Transverse) : ℝ :=
  (-2*weightedLinear α β v q)*derivativePolynomial α β v q

def clockDensity (ε a h : ℝ) (x : Configuration) : ℂ :=
  (‖halfClockFunction ε a x.1‖^2*pairPolynomial x.2*
    ‖physicalGaussian (groundWidth h) (neutralWidth h) x.2‖^2:ℝ)

def momentumDensity (ε a h : ℝ) (v : Transverse) (x : Configuration) : ℂ :=
  (h^2*‖dampedClockFunction ε a x.1‖^2*
    responsePolynomial (groundWidth h) (neutralWidth h) v x.2*
    ‖physicalGaussian (groundWidth h) (neutralWidth h) x.2‖^2:ℝ)

private theorem zero_gradient (α β : ℝ) (v q : Transverse) :
    KFCausalClockFloorCoherentDerivative.gradient α β 0 v q =
      KFCausalPhysicalGaussianDerivative.gradient α β v q := by
  simp [KFCausalClockFloorCoherentDerivative.gradient,
    KFCausalClockFloorCoherentSources.linearSource,
    KFCausalClockFloorCoherentMoments.sourcedPacket,
    KFCausalPhysicalGaussianDerivative.gradient]

theorem scalar_pairing_identity (h A B : ℝ) (c d : ℂ) :
    conj ((-Complex.I*(h:ℂ))*c*(A:ℂ)*d)*((-Complex.I*(h:ℂ))*c*(B:ℂ)*d) =
      (h^2*‖c‖^2*A*B*‖d‖^2:ℝ) := by
  push_cast
  rw [← Complex.conj_mul' c,← Complex.conj_mul' d]
  simp only [map_mul,map_neg,Complex.conj_I,neg_neg,Complex.conj_ofReal]
  ring_nf
  simp [Complex.I_sq]

theorem clock_density_identity (ε a h : ℝ) (x : Configuration) :
    conj (halfClockFunction ε a x.1*physicalGaussian (groundWidth h) (neutralWidth h) x.2)*
      profile (groundWidth h) (neutralWidth h) (halfClockFunction ε a) x =
        clockDensity ε a h x := by
  unfold profile clockDensity
  push_cast
  rw [← Complex.conj_mul' (halfClockFunction ε a x.1),
    ← Complex.conj_mul' (physicalGaussian (groundWidth h) (neutralWidth h) x.2)]
  simp only [map_mul]
  ring

theorem momentum_density_identity (ε a h : ℝ) (v : Transverse) (x : Configuration) :
    conj ((-Complex.I*(h:ℂ))*dampedClockFunction ε a x.1*
      (-2*weightedLinear (groundWidth h) (neutralWidth h) v x.2:ℝ)*
      physicalGaussian (groundWidth h) (neutralWidth h) x.2)*
    ((-Complex.I*(h:ℂ))*dampedClockFunction ε a x.1*
      (derivativePolynomial (groundWidth h) (neutralWidth h) v x.2:ℂ)*
      physicalGaussian (groundWidth h) (neutralWidth h) x.2) =
        momentumDensity ε a h v x := by
  rw [scalar_pairing_identity]
  unfold momentumDensity responsePolynomial
  congr 1
  ring

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => neutralWidth_positive h hh
local notation "hw" => neutralWidth_bound h
local notation "gd" => dampedClockFunction ε a
local notation "hgd" => dampedClockFunction_memLp ε a hε ha

theorem sourcedMomentum_coe (v : Transverse) :
    KFCausalClockFloorSourcedClockMomentum.momentumOutput ε a α β hε ha hα hβ hw 1 0 0 h v =ᵐ[volume]
      fun x => (-Complex.I*(h:ℂ))*gd x.1*(-2*weightedLinear α β v x.2:ℝ)*physicalGaussian α β x.2 := by
  let hd := physicalProfile_derivative_memLp 1 0 α β hα hβ hw 0 gd hgd v
  filter_upwards [Lp.coeFn_smul (-Complex.I*(h:ℂ))
    (hd.toLp (derivative v (physicalProfile 1 0 α β 0 gd))),hd.coeFn_toLp] with x hx hy
  change ((-Complex.I*(h:ℂ)) • hd.toLp (derivative v (physicalProfile 1 0 α β 0 gd)) : Hilbert) x = _
  rw [hx,Pi.smul_apply,smul_eq_mul,hy,physicalProfile_derivative,zero_gradient,gaussian_gradient]
  simp only [clockMultiplier,KFCausalClockFloorCoherentStrip.clockPhase,Complex.ofReal_zero,
    zero_mul,Complex.exp_zero,one_mul]
  ring

variable (hb : |h| ≤ 2*Real.pi*ε/3)

theorem base_half_coe :
    baseFactors ε a h hε ha hh hb 0 =ᵐ[volume]
      fun x => halfClockFunction ε a x.1*physicalGaussian α β x.2 := by
  have he := KFCausalClockFloorSourcedClockMomentum.profileState_coe α β hα hβ hw
    1 0 0 (halfClockFunction ε a) (halfClockFunction_memLp ε a hε ha)
  change baseFactors ε a h hε ha hh hb 0 =ᵐ[volume] _ at he
  filter_upwards [he] with x hx
  rw [hx]
  simp [physicalProfile,clockMultiplier,KFCausalClockFloorCoherentMoments.sourcedPacket,
    KFCausalClockFloorCoherentSources.linearSource,KFCausalClockFloorCoherentStrip.clockPhase]

theorem base_momentum_coe (j : Fin 4) :
    baseFactors ε a h hε ha hh hb (momentumIndex j) =ᵐ[volume] fun x =>
      (-Complex.I*(h:ℂ))*gd x.1*(-2*weightedLinear α β (modelDirections j) x.2:ℝ)*
        physicalGaussian α β x.2 := by
  fin_cases j <;> exact sourcedMomentum_coe ε a h hε ha hh _

include hε ha hh hb in
theorem clockDensity_integrable : Integrable (clockDensity ε a h) volume := by
  have hi := (Lp.memLp (baseFactors ε a h hε ha hh hb 0)).star.integrable_mul
    (Lp.memLp (pairedFactors ε a h hε ha hh hb 0))
  apply hi.congr
  filter_upwards [base_half_coe ε a h hε ha hh hb,
    KFCausalChargedPairKineticOutputs.halfOutput_coe ε a h hε ha hh hb] with x hx hy
  change conj (baseFactors ε a h hε ha hh hb 0 x)*pairedFactors ε a h hε ha hh hb 0 x = _
  rw [hx,hy]
  exact clock_density_identity ε a h x

include hε ha hh hb in
theorem momentumDensity_integrable (j : Fin 4) :
    Integrable (momentumDensity ε a h (modelDirections j)) volume := by
  have hi := (Lp.memLp (baseFactors ε a h hε ha hh hb (momentumIndex j))).star.integrable_mul
    (Lp.memLp (pairedFactors ε a h hε ha hh hb (momentumIndex j)))
  apply hi.congr
  filter_upwards [base_momentum_coe ε a h hε ha hh hb j,
    KFCausalChargedPairKineticOutputs.momentumOutput_coe ε a h hε ha hh hb j] with x hx hy
  change conj (baseFactors ε a h hε ha hh hb (momentumIndex j) x)*
    pairedFactors ε a h hε ha hh hb (momentumIndex j) x = _
  rw [hx,hy]
  exact momentum_density_identity ε a h (modelDirections j) x

theorem clock_pairing :
    factorPairing ε a h hε ha hh hb 0 = ∫ x, clockDensity ε a h x := by
  rw [factorPairing,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [base_half_coe ε a h hε ha hh hb,
    KFCausalChargedPairKineticOutputs.halfOutput_coe ε a h hε ha hh hb] with x hx hy
  rw [hx,hy,← clock_density_identity]
  simp only [RCLike.inner_apply]
  ring

theorem momentum_pairing (j : Fin 4) :
    factorPairing ε a h hε ha hh hb (momentumIndex j) =
      ∫ x, momentumDensity ε a h (modelDirections j) x := by
  rw [factorPairing,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [base_momentum_coe ε a h hε ha hh hb j,
    KFCausalChargedPairKineticOutputs.momentumOutput_coe ε a h hε ha hh hb j] with x hx hy
  rw [hx,hy,← momentum_density_identity]
  simp only [RCLike.inner_apply]
  ring

#print axioms scalar_pairing_identity
#print axioms clock_density_identity
#print axioms momentum_density_identity
#print axioms sourcedMomentum_coe
#print axioms base_half_coe
#print axioms base_momentum_coe
#print axioms clockDensity_integrable
#print axioms momentumDensity_integrable
#print axioms clock_pairing
#print axioms momentum_pairing
end
end UnifiedTheory.Audit.KFCausalChargedPairKineticPairing
