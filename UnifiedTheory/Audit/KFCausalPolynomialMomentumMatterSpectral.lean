/- Actual polynomial momentum spectral endpoints, retaining the factor
one half from the doubled clock parameter and the original source circles. -/
import UnifiedTheory.Audit.KFCausalCoherentMomentumMatterSpectralProfile
import UnifiedTheory.Audit.KFCausalPolynomialMomentumSecondFactors
import UnifiedTheory.Audit.KFCausalVariableWidthOrderedMomentum
import UnifiedTheory.Audit.KFCausalReciprocalNeutralMatterSpectral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalPolynomialMomentumMatterSpectral
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalUnboundedMultiplierIntegral (relation relation_integral relation_smul relation_sum)
open KFCausalCoherentMatterSpectralProfile (multiplier multiplier_continuous)
open KFCausalPolynomialGaussianStates (circleSource)
open KFCausalSourceCircleCoefficients
open KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open KFCausalVariableWidthPolynomialMomentum (factorCurve factorCurve_continuous powerMomentumFactor momentumFactor)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalGaussianVacuumSquare (double_strip)
open KFCausalReciprocalNeutralMatterSpectral (matterIndex)
open KFCausalPolynomialOrderedMomentumDensity (clockSlope)

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (h : ℝ) (hb : |h| ≤ Real.pi*ε/3)
  (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) (i : Fin 5)
local notation "hb₂" => double_strip ε h hb

def powerSpectral (n : ℕ) (j : Fin 2) : Hilbert := (C*normalization n) •
  KFCausalPolynomialMomentumMatterCurve.meanSpectral ε a α β hε ha hα hβ hw h hb p b i n j

theorem power_relation (n : ℕ) (j : Fin 2) : relation (multiplier ε h j)
    ((1/2:ℂ) • powerMomentumFactor ε a α β hε ha hα hβ hw (2*h) p b i C hb₂ n modelDirections pointField 7)
    (powerSpectral ε a α β hε ha hα hβ hw h hb C p b i n j) := by
  let F : ℝ → Hilbert := fun θ => (1/2:ℂ) • factorCurve ε a α β hε ha hα hβ hw (2*h) p b i hb₂ n modelDirections pointField 7 θ
  let G := KFCausalPolynomialMomentumMatterCurve.spectralCurve ε a α β hε ha hα hβ hw h hb p b i n j
  have hF : Continuous F := continuous_const.smul
    (factorCurve_continuous ε a α β hε ha hα hβ hw (2*h) p b i hb₂ n modelDirections pointField 7)
  have hG : Continuous G := KFCausalPolynomialMomentumMatterCurve.spectral_continuous ε a α β hε ha hα hβ hw h hb p b i n j
  have hr := relation_integral (multiplier ε h j) (multiplier_continuous ε h hε hb j).measurable F G
    ((continuous_angle_memLp F hF).integrable (by norm_num))
    ((continuous_angle_memLp G hG).integrable (by norm_num))
    (Filter.Eventually.of_forall (fun θ => KFCausalCoherentMomentumMatterSpectralProfile.spectral_relation
      ε a α β hε ha hα hβ hw h hb (weight n θ) p (circleSource b i θ) j))
  have hs := relation_smul _ (multiplier_continuous ε h hε hb j).measurable _ _ hr (C*normalization n)
  simpa only [F,G,powerMomentumFactor,powerSpectral,KFCausalPolynomialMomentumMatterCurve.meanSpectral,
    integral_smul,smul_comm (C*normalization n) (1/2:ℂ)] using hs

def spectral (P : Polynomial ℂ) (j : Fin 2) : Hilbert :=
  ∑ n ∈ P.support, P.coeff n • powerSpectral ε a α β hε ha hα hβ hw h hb C p b i n j

theorem polynomial_relation (P : Polynomial ℂ) (j : Fin 2) : relation (multiplier ε h j)
    ((1/2:ℂ) • momentumFactor ε a α β hε ha hα hβ hw (2*h) p b i C hb₂ P modelDirections pointField 7)
    (spectral ε a α β hε ha hα hβ hw h hb C p b i P j) := by
  have hs := relation_sum _ (multiplier_continuous ε h hε hb j).measurable P.support _ _ (fun n _ =>
    relation_smul _ (multiplier_continuous ε h hε hb j).measurable _ _
      (power_relation ε a α β hε ha hα hβ hw h hb C p b i n j) (P.coeff n))
  simpa only [momentumFactor,spectral,Finset.smul_sum,smul_comm (1/2:ℂ)] using hs

theorem spectral_coe (hh : h ≠ 0) (P : Polynomial ℂ) (j : Fin 2) :
    spectral ε a α β hε ha hα hβ hw h hb C p b i P j =ᵐ[volume] fun x =>
      multiplier ε h j x*((1/2:ℂ)*clockSlope ε a (2*h) p x*
        KFCausalVariableWidthOrderedProfile.orderedProfile ε a α β (2*h) C p b i P x) := by
  have hh₂ : 2*h ≠ 0 := mul_ne_zero (by norm_num) hh
  filter_upwards [polynomial_relation ε a α β hε ha hα hβ hw h hb C p b i P j,
    Lp.coeFn_smul (1/2:ℂ) (momentumFactor ε a α β hε ha hα hβ hw (2*h) p b i C hb₂ P modelDirections pointField 7),
    KFCausalVariableWidthOrderedMomentum.polynomial_relation ε a α β hε ha hα hβ hw (2*h) hh₂ hb₂ C p b i P modelDirections pointField 0,
    KFCausalVariableWidthOrderedProfile.output_vacuum_coe ε a α β hε ha hα hβ hw (2*h) hb₂ C p b i P modelDirections pointField]
    with x hs hm hr hg
  change momentumFactor ε a α β hε ha hα hβ hw (2*h) p b i C hb₂ P modelDirections pointField 7 x =
    clockSlope ε a (2*h) p x*(KFCausalVariableWidthPolynomialDomain.output ε a α β hε ha hα hβ hw
      (2*h) C p b i hb₂ P modelDirections pointField 7) x at hr
  rw [hs,hm,Pi.smul_apply,smul_eq_mul,hr,hg]
  ring

theorem powerSecond_eq (n : ℕ) (j : Fin 2) :
    KFCausalPolynomialMomentumSecondFactors.powerSecond ε a α β hε ha hα hβ hw h hb p b i C n (matterIndex j) =
      inverseL ε hε (powerSpectral ε a α β hε ha hα hβ hw h hb C p b i n j) := by
  rw [powerSpectral,map_smul]
  fin_cases j <;> rfl

theorem second_eq (P : Polynomial ℂ) (j : Fin 2) :
    KFCausalPolynomialMomentumSecondFactors.second ε a α β hε ha hα hβ hw h hb p b i C P (matterIndex j) =
      inverseL ε hε (spectral ε a α β hε ha hα hβ hw h hb C p b i P j) := by
  simp only [KFCausalPolynomialMomentumSecondFactors.second,spectral,map_sum,map_smul,powerSecond_eq]

#print axioms power_relation
#print axioms polynomial_relation
#print axioms spectral_coe
#print axioms powerSecond_eq
#print axioms second_eq
end
end UnifiedTheory.Audit.KFCausalPolynomialMomentumMatterSpectral
