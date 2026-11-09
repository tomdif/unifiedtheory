/- Expose the actual polynomial matter spectral endpoints. Their
unbounded field multiplication relation follows through the existing
continuous source-circle curves and finite sums. -/
import UnifiedTheory.Audit.KFCausalCoherentMatterSpectralProfile
import UnifiedTheory.Audit.KFCausalPolynomialMatterSquare

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalPolynomialMatterSpectral
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalUnboundedMultiplierIntegral (relation relation_integral relation_smul relation_sum)
open KFCausalCoherentMatterSpectralProfile (multiplier multiplier_continuous spectral_relation)
open KFCausalPolynomialGaussianStates (circleSource sourceBound circleSource_continuous circleSource_bound)
open KFCausalSourceCircleCoefficients
open KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open KFCausalVariableWidthPolynomialDomain (powerOutput output)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalGaussianVacuumSquare (double_strip)

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (h : ℝ) (hb : |h| ≤ Real.pi*ε/3)
  (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) (i : Fin 5)
local notation "hb₂" => double_strip ε h hb

def powerSpectral (n : ℕ) (j : Fin 2) : Hilbert := (C*normalization n) •
  KFCausalCoherentMatterCurve.meanSpectral ε a α β hε ha hα hβ hw h hb
    (weight n) (fun _ => p) (circleSource b i) j

theorem power_relation (n : ℕ) (j : Fin 2) : relation (multiplier ε h j)
    (powerOutput ε a α β hε ha hα hβ hw (2*h) C p b i hb₂ n modelDirections pointField 7)
    (powerSpectral ε a α β hε ha hα hβ hw h hb C p b i n j) := by
  let F : ℝ → Hilbert := fun θ => KFCausalClockFloorSourcedSpectral.shiftedOutput
    ε a α β hε ha hα hβ hw (weight n θ) p (circleSource b i θ) (2*h) hb₂
  let G : ℝ → Hilbert := fun θ => KFCausalCoherentMatterSquare.spectralOutput
    ε a α β hε ha hα hβ hw h hb (weight n θ) p (circleSource b i θ) j
  have hF : Continuous F :=
    (KFCausalVariableWidthFieldContinuity.outputs_curve_continuous ε a α β (2*h) hε ha hα hβ hw hb₂
      |p| (sourceBound b) (weight n) (fun _ => p) (circleSource b i)
      (weight_continuous n) continuous_const (circleSource_continuous b i)
      (fun θ => (weight_norm n θ).le) (fun _ => le_rfl) (circleSource_bound b i)).1
  have hG : Continuous G :=
    KFCausalCoherentMatterCurve.spectral_continuous ε a α β hε ha hα hβ hw h hb
      |p| (sourceBound b) (weight n) (fun _ => p) (circleSource b i)
      (weight_continuous n) continuous_const (circleSource_continuous b i)
      (fun _ => le_rfl) (circleSource_bound b i) j
  have hr := relation_integral (multiplier ε h j) (multiplier_continuous ε h hε hb j).measurable F G
    ((continuous_angle_memLp F hF).integrable (by norm_num))
    ((continuous_angle_memLp G hG).integrable (by norm_num))
    (Filter.Eventually.of_forall (fun θ => spectral_relation ε a α β hε ha hα hβ hw h hb
      (weight n θ) p (circleSource b i θ) j))
  exact relation_smul _ (multiplier_continuous ε h hε hb j).measurable _ _ hr (C*normalization n)

def spectral (P : Polynomial ℂ) (j : Fin 2) : Hilbert :=
  ∑ n ∈ P.support, P.coeff n • powerSpectral ε a α β hε ha hα hβ hw h hb C p b i n j

theorem polynomial_relation (P : Polynomial ℂ) (j : Fin 2) : relation (multiplier ε h j)
    (output ε a α β hε ha hα hβ hw (2*h) C p b i hb₂ P modelDirections pointField 7)
    (spectral ε a α β hε ha hα hβ hw h hb C p b i P j) :=
  relation_sum _ (multiplier_continuous ε h hε hb j).measurable P.support _ _ (fun n _ =>
    relation_smul _ (multiplier_continuous ε h hε hb j).measurable _ _
      (power_relation ε a α β hε ha hα hβ hw h hb C p b i n j) (P.coeff n))

theorem spectral_coe (P : Polynomial ℂ) (j : Fin 2) :
    spectral ε a α β hε ha hα hβ hw h hb C p b i P j =ᵐ[volume] fun x =>
      multiplier ε h j x*KFCausalVariableWidthOrderedProfile.orderedProfile ε a α β (2*h) C p b i P x := by
  filter_upwards [polynomial_relation ε a α β hε ha hα hβ hw h hb C p b i P j,
    KFCausalVariableWidthOrderedProfile.output_vacuum_coe ε a α β hε ha hα hβ hw (2*h) hb₂
      C p b i P modelDirections pointField] with x hs hg
  rw [hs,hg]

theorem powerSecond_eq (n : ℕ) (j : Fin 2) :
    KFCausalPolynomialMatterSquare.powerSecond ε a α β hε ha hα hβ hw h hb C p b i n j =
      inverseL ε hε (powerSpectral ε a α β hε ha hα hβ hw h hb C p b i n j) := by
  simp only [KFCausalPolynomialMatterSquare.powerSecond,KFCausalCoherentMatterCurve.meanOutput,
    powerSpectral,map_smul]

theorem second_eq (P : Polynomial ℂ) (j : Fin 2) :
    KFCausalPolynomialMatterSquare.second ε a α β hε ha hα hβ hw h hb C p b i P j =
      inverseL ε hε (spectral ε a α β hε ha hα hβ hw h hb C p b i P j) := by
  simp only [KFCausalPolynomialMatterSquare.second,spectral,map_sum,map_smul,powerSecond_eq]

#print axioms power_relation
#print axioms polynomial_relation
#print axioms spectral_coe
#print axioms powerSecond_eq
#print axioms second_eq
end
end UnifiedTheory.Audit.KFCausalPolynomialMatterSpectral
