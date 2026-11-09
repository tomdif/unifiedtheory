/- A corrected quartic excitation is an actual nonzero zero-charge
state. The uncorrected square of the paired polynomial is not fixed by
the physical charge circle. This is a statement about charge and Hilbert
states; energy domains and response estimates for this new state are separate. -/
import UnifiedTheory.Audit.KFCausalQuarticChargeProfiles
import UnifiedTheory.Audit.KFCausalContinuousChargeDetection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalPairedQuarticCharge
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalQuarticChargeAlgebra (correctedCoefficients squareCoefficients)
open KFCausalQuarticChargeProfiles
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive groundWidth_matching)
open KFCausalChargeGaussianIdentities (configurationProfile)
open KFCausalClockFloorInvariantTrial
  (clockFunction clockFunction_continuous clockFunction_memLp neutralWidth neutralWidth_positive)
open KFCausalClockFloorCoherentStates (weight weight_ne_zero weight_flow)
open KFCausalNormalizedChargeFlow (momentumScale momentumScale_ne_zero flowEquiv)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalContinuousChargeDetection
open KFCausalStandingChargeOperator
  (zeroSector standingCharge standingCharge_zero_iff zeroProjection zeroProjection_fixes)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => neutralWidth_positive h hh
local notation "hc" => clockFunction_continuous ε a
local notation "hg" => clockFunction_memLp ε a hε ha

def correctedState : Hilbert :=
  KFCausalQuarticTensorStates.state α β hα hβ (clockFunction ε a) hc hg
    (correctedCoefficients α)
def squareState : Hilbert :=
  KFCausalQuarticTensorStates.state α β hα hβ (clockFunction ε a) hc hg squareCoefficients
def correctedDensity (x : Joint 2 4) : ℂ :=
  (correctedWeight α (momentumScale h) x:ℂ)*weight ε a h x
def squareDensity (x : Joint 2 4) : ℂ :=
  (squareWeight α (momentumScale h) x:ℂ)*weight ε a h x

theorem corrected_configuration_coe :
    correctedState ε a h hε ha hh =ᵐ[volume] fun x =>
      (quarticPolynomial α x.2:ℂ)*configurationProfile α β (clockFunction ε a) x := by
  filter_upwards [KFCausalQuarticTensorStates.state_configuration_coe
    α β hα hβ (clockFunction ε a) hc hg (correctedCoefficients α)] with x hx
  exact hx.trans (configuration_corrected α β (clockFunction ε a) x)

theorem square_configuration_coe :
    squareState ε a h hε ha hh =ᵐ[volume] fun x =>
      ((KFCausalChargedPairCoordinates.pairPolynomial x.2)^2:ℝ)*
        configurationProfile α β (clockFunction ε a) x := by
  filter_upwards [KFCausalQuarticTensorStates.state_configuration_coe
    α β hα hβ (clockFunction ε a) hc hg squareCoefficients] with x hx
  exact hx.trans (configuration_square α β (clockFunction ε a) x)

theorem corrected_coordinates_coe :
    chargeCoordinates (correctedState ε a h hε ha hh) =ᵐ[volume] correctedDensity ε a h := by
  filter_upwards [KFCausalQuarticTensorStates.state_coordinates_coe
    α β hα hβ (clockFunction ε a) hc hg (correctedCoefficients α)] with x hx
  exact hx.trans (mixed_corrected α β (momentumScale h) hα (groundWidth_matching h hh)
    (clockFunction ε a) x)

theorem square_coordinates_coe :
    chargeCoordinates (squareState ε a h hε ha hh) =ᵐ[volume] squareDensity ε a h := by
  filter_upwards [KFCausalQuarticTensorStates.state_coordinates_coe
    α β hα hβ (clockFunction ε a) hc hg squareCoefficients] with x hx
  exact hx.trans (mixed_square α β (momentumScale h) hα (groundWidth_matching h hh)
    (clockFunction ε a) x)

theorem weight_continuous : Continuous (weight ε a h) := by
  unfold weight KFCausalChargeGaussianGeometry.profile
  simp only [KFCausalChargeGaussianGeometry.radius_coordinates]
  have hclock := clockFunction_continuous ε a
  fun_prop

theorem correctedDensity_continuous : Continuous (correctedDensity ε a h) :=
  ((Complex.continuous_ofReal.comp (correctedWeight_continuous α (momentumScale h))).mul
    (weight_continuous ε a h))

theorem squareDensity_continuous : Continuous (squareDensity ε a h) :=
  ((Complex.continuous_ofReal.comp (squareWeight_continuous α (momentumScale h))).mul
    (weight_continuous ε a h))

theorem corrected_zeroSector : correctedState ε a h hε ha hh ∈ zeroSector h hh := by
  apply (fixed_iff_pointwise h hh _ _ (corrected_coordinates_coe ε a h hε ha hh)
    (correctedDensity_continuous ε a h)).mpr
  intro θ x
  simp only [correctedDensity,correctedWeight_flow,weight_flow ε a h hh]

theorem corrected_charge_zero :
    (correctedState ε a h hε ha hh,0) ∈ (standingCharge h hh).graph :=
  (standingCharge_zero_iff h hh _).mpr (corrected_zeroSector ε a h hε ha hh)

theorem corrected_projection :
    zeroProjection h hh (correctedState ε a h hε ha hh) = correctedState ε a h hε ha hh :=
  zeroProjection_fixes h hh _ (corrected_zeroSector ε a h hε ha hh)

theorem corrected_ne_zero : correctedState ε a h hε ha hh ≠ 0 := by
  apply nonzero_of_pointwise _ _ (corrected_coordinates_coe ε a h hε ha hh)
    (correctedDensity_continuous ε a h) (0 : Joint 2 4)
  apply mul_ne_zero _ (weight_ne_zero ε a h hε hh 0)
  apply Complex.ofReal_ne_zero.mpr
  have hz : correctedWeight α (momentumScale h) (0 : Joint 2 4) = 1/(8*α^2) := by
    simp [correctedWeight,KFCausalChargeZeroSwapWitness.imbalance,
      KFCausalChargeZeroSwapWitness.imbalanceRaw,KFCausalNormalizedChargeFlow.dilate,
      KFCausalChargeGaussianGeometry.radius_coordinates]
  rw [hz]
  exact one_div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 (hα).ne'))

def defectPoint : Joint 2 4 :=
  WithLp.toLp 2 (fun i : Fin 2 ⊕ Fin 4 => if i = Sum.inr (1:Fin 4) then 1 else 0)

theorem square_not_zeroSector : squareState ε a h hε ha hh ∉ zeroSector h hh := by
  intro hf
  have he := (fixed_iff_pointwise h hh _ _ (square_coordinates_coe ε a h hε ha hh)
    (squareDensity_continuous ε a h)).mp hf (Real.pi/2) defectPoint
  unfold squareDensity at he
  rw [weight_flow ε a h hh] at he
  have he' := mul_right_cancel₀ (weight_ne_zero ε a h hε hh defectPoint) he
  have hr := Complex.ofReal_injective he'
  have hd := squareWeight_quarter_defect α (momentumScale h) (momentumScale_ne_zero h hh) defectPoint
  rw [hr,sub_self] at hd
  have hz : frequencyRadius (momentumScale h) defectPoint -
      ((defectPoint (.inr 1))^2+(defectPoint (.inr 2))^2) = -1 := by
    norm_num [frequencyRadius,defectPoint,Sum.inl_ne_inr,Fin.reduceEq]
    decide
  rw [hz] at hd
  exact (div_ne_zero (by norm_num : (-1:ℝ) ≠ 0)
    (mul_ne_zero (by norm_num) (hα).ne')) hd.symm

#print axioms corrected_configuration_coe
#print axioms square_configuration_coe
#print axioms corrected_coordinates_coe
#print axioms square_coordinates_coe
#print axioms weight_continuous
#print axioms correctedDensity_continuous
#print axioms squareDensity_continuous
#print axioms corrected_zeroSector
#print axioms corrected_charge_zero
#print axioms corrected_projection
#print axioms corrected_ne_zero
#print axioms square_not_zeroSector
end
end UnifiedTheory.Audit.KFCausalPairedQuarticCharge
