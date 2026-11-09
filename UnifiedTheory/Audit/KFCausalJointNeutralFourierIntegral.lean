/- The actual complete neutral/charged positive Gram integral has a
neutral Fourier representation. This is an equality with all original
cross terms and quartic weights, not a uniform response estimate. -/
import UnifiedTheory.Audit.KFCausalNeutralFourierEnergy
import UnifiedTheory.Audit.KFCausalJointNeutralRadialEstimate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalJointNeutralFourierIntegral
noncomputable section
open MeasureTheory
open KFCausalNeutralFourierShift (line)
open KFCausalNeutralFourierEnergy (frequencyDensity)
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalReciprocalNeutralPositiveForm (positiveDensity pairing)
open KFCausalNeutralJointCurvatureForm (coefficients)
open KFCausalJointNeutralRadialEstimate (jointSlice)
open KFCausalQuarticPlaneDomination (potential)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalReciprocalWedgeGeometry (chart)
open KFCausalNeutralExponentialProfiles (exponentialProfile)

variable (n : ℕ) (β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ)

def frequencySlice (r z : ℂ) (v k : ℝ) : ℝ :=
  frequencyDensity n β b (coefficients n w c z) P (fieldSlope r*v) (2*r.im*v) k

theorem jointSlice_line (r z : ℂ) (v x : ℝ) :
    jointSlice n β w b c P r z v x =
      potential (x+fieldSlope r*v)*‖line n β b (coefficients n w c z) P (2*r.im*v) x‖^2 := by
  unfold jointSlice
  rw [KFCausalNeutralJointCurvatureForm.joint_profile_family]
  congr 3
  unfold KFCausalReciprocalNeutralKernel.neutral line KFCausalGaussianContourShift.horizontal
  push_cast
  ring

theorem slice_plancherel (hβ : 0 < β) (r z : ℂ) (v : ℝ) :
    (∫ x, jointSlice n β w b c P r z v x) =
      ∫ k, frequencySlice n β w b c P r z v k := by
  simp_rw [jointSlice_line]
  exact KFCausalNeutralFourierEnergy.quartic_plancherel n β b (coefficients n w c z) P hβ _ _

theorem frequencySlice_integrable (hβ : 0 < β) (r z : ℂ) (v : ℝ) :
    Integrable (frequencySlice n β w b c P r z v) :=
  KFCausalNeutralFourierEnergy.frequencyDensity_integrable n β b (coefficients n w c z) P hβ _ _

theorem frequencySlice_nonnegative (r z : ℂ) (v k : ℝ) :
    0 ≤ frequencySlice n β w b c P r z v k :=
  KFCausalNeutralFourierEnergy.frequencyDensity_nonnegative n β b (coefficients n w c z) P _ _ _

omit n β w b c P in
theorem integral_finTwo (f : (Fin 2 → ℝ) → ℝ) (hf : Integrable f) :
    (∫ p, f p) = ∫ v : ℝ, ∫ x : ℝ, f ![v,x] := by
  let e : (Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ) := MeasurableEquiv.finTwoArrow
  have hp : MeasurePreserving e.symm volume volume := (volume_preserving_finTwoArrow ℝ).symm
  have hi := hp.integrable_comp_of_integrable hf
  rw [← hp.integral_comp' f]
  rw [Measure.volume_eq_prod ℝ ℝ] at hi ⊢
  exact integral_prod _ hi

omit n β w b c P in
theorem joint_integral_iterated (f : Joint → ℝ) (hf : Integrable f jointMeasure) :
    (∫ p, f p ∂jointMeasure) =
      ∫ Y in Set.Ioi (0:ℝ), ∫ u : ℝ, ∫ v : ℝ, ∫ x : ℝ, f ((u,![v,x]),Y) := by
  unfold jointMeasure at hf ⊢
  rw [integral_prod_symm _ hf]
  apply integral_congr_ae
  filter_upwards [hf.prod_left_ae] with Y hY
  rw [Measure.volume_eq_prod ℝ (Fin 2 → ℝ)] at hY ⊢
  rw [integral_prod _ hY]
  apply integral_congr_ae
  filter_upwards [hY.prod_right_ae] with u hu
  exact integral_finTwo _ hu

theorem density_slice (α : ℝ) (r : ℂ) (u v x Y : ℝ) :
    positiveDensity n α β w r c (fun i => exponentialProfile (b i) 1 (P i)) ((u,![v,x]),Y) =
      jointSlice n β w b c P r (chart α r (u^2+v^2) Y) v x := by
  rw [KFCausalReciprocalNeutralHolomorphic.density_absorbed]
  rfl

variable (α ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β) (hwidth : 32*β ≤ α)
  (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hw : ∀ i, 1 ≤ w i)
local notation "r" => KFCausalClockFloorRelativeShift.scale ε y s
include hα hβ hwidth hε hy hw

theorem actual_positive_integral :
    (∫ p, positiveDensity n α β w r c (fun i => exponentialProfile (b i) 1 (P i)) p ∂jointMeasure) =
      ∫ Y in Set.Ioi (0:ℝ), ∫ u : ℝ, ∫ v : ℝ, ∫ k : ℝ,
        frequencySlice n β w b c P r (chart α r (u^2+v^2) Y) v k := by
  rw [joint_integral_iterated _
    (KFCausalReciprocalNeutralActualPositive.positive_integrable n α β ε y s w b c P hα hβ hwidth hε hy hw)]
  apply integral_congr_ae
  filter_upwards [] with Y
  apply integral_congr_ae
  filter_upwards [] with u
  apply integral_congr_ae
  filter_upwards [] with v
  simp_rw [density_slice]
  exact slice_plancherel n β w b c P hβ r _ v

theorem actual_pairing_integral :
    pairing n α β w r c c (fun i => exponentialProfile (b i) 1 (P i)) =
      ((Real.pi/4*(∫ Y in Set.Ioi (0:ℝ), ∫ u : ℝ, ∫ v : ℝ, ∫ k : ℝ,
        frequencySlice n β w b c P r (chart α r (u^2+v^2) Y) v k):ℝ):ℂ) := by
  rw [KFCausalReciprocalNeutralActualPositive.pairing_positive_integral n α β ε y s w b c P hα hβ hwidth hε hy hw,
    actual_positive_integral n β w b c P α ε y s hα hβ hwidth hε hy hw]

#print axioms jointSlice_line
#print axioms slice_plancherel
#print axioms frequencySlice_integrable
#print axioms frequencySlice_nonnegative
#print axioms integral_finTwo
#print axioms joint_integral_iterated
#print axioms density_slice
#print axioms actual_positive_integral
#print axioms actual_pairing_integral
end
end UnifiedTheory.Audit.KFCausalJointNeutralFourierIntegral
