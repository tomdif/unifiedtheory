/- Specialize the derived strong curves to the actual inverse-clock shift.
Their derivatives are the bounded complex clock coefficient times the
actual first and second shear outputs. No derivative or graph is supplied
as an extra assumption for the Gaussian family. -/
import UnifiedTheory.Audit.KFCausalStrongImaginaryShearCurve
import UnifiedTheory.Audit.KFCausalBoundedLpMultiplier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalActualImaginaryShearCurve
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalImaginaryShearCoefficient
open UnifiedTheory.Audit.KFCausalImaginaryShearInterpolation
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (Interval displacement_strip_bound)
open UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile (clockAmplitude clockAmplitude_smooth)
open UnifiedTheory.Audit.KFCausalStrongImaginaryShearCurve
open UnifiedTheory.Audit.KFCausalGaussianSecondShearDifferential (first second)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)

variable (ε a p h α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
variable (hw : 32*β ≤ α) (hb : |h| ≤ 2*Real.pi*ε/3) (b : Fin 5 → ℂ)
local notation "A" => clockAmplitude ε a p (-h/2)
local notation "D" => displacement ε h
local notation "hA" => clockAmplitude_smooth ε a p (-h/2) hε (half_shift_bound ε h hb)
local notation "hAm" => KFCausalShiftedClockAmplitude.clockAmplitude_memLp ε a p (-h/2) hε ha (half_shift_bound ε h hb)
local notation "hD" => displacement_smooth ε h hε hb
local notation "hDb" => displacement_strip_bound ε h hε hb

def input : ℝ → Hilbert := inputCurve A D hA hAm hD hDb α β hα hβ hw b
def shear : ℝ → Hilbert := outputCurve A D hA hAm hD hDb α β hα hβ hw b h
def secondShear (t : Interval) : Hilbert := (-Complex.I*(h:ℂ))^2 •
  secondState A D hA hAm hD hDb α β hα hβ hw b t

def coefficientOperator (hh : h ≠ 0) : Hilbert →L[ℂ] Hilbert :=
  KFCausalBoundedLpMultiplier.operator (fun x : Configuration => coefficient ε h x.1)
    ((coefficient_smooth ε h hε hb).continuous.comp continuous_fst).measurable
    (1/(2*ε)) (by positivity) (fun x => coefficient_bound ε h x.1 hε hh hb)

theorem coefficientOperator_coe (hh : h ≠ 0) (f : Hilbert) :
    coefficientOperator ε h hε hb hh f =ᵐ[volume] fun x => coefficient ε h x.1*f x :=
  KFCausalBoundedLpMultiplier.operator_coe _ _ _ _ _ f

theorem input_continuous : Continuous (input ε a p h α β hε ha hα hβ hw hb b) :=
  inputCurve_continuous A D hA hAm hD hDb α β hα hβ hw b

theorem shear_continuous : Continuous (shear ε a p h α β hε ha hα hβ hw hb b) :=
  outputCurve_continuous A D hA hAm hD hDb α β hα hβ hw b h

theorem input_eq_state (t : Interval) : input ε a p h α β hε ha hα hβ hw hb b t =
    KFCausalImaginaryShearPathDomain.actualState α β hα hβ hw b ε a p h hε ha hb t :=
  KFCausalIntervalL2Derivative.curve_value _
    (KFCausalImaginaryShearPathBounds.path_memLp A D hA hAm hD hDb α β hα hβ hw b) t t.property

theorem input_one : input ε a p h α β hε ha hα hβ hw hb b 1 =
    KFCausalClockFloorCoherentSpectral.gaussianState ε a α β p b (-h/2)
      hε ha hα hβ hw (half_shift_bound ε h hb) := by
  rw [input_eq_state ε a p h α β hε ha hα hβ hw hb b ⟨1,by constructor <;> norm_num⟩]
  exact KFCausalImaginaryShearPathDomain.actualState_one α β hα hβ hw b ε a p h hε ha hb

theorem shear_coe (t : Interval) : shear ε a p h α β hε ha hα hβ hw hb b t =ᵐ[volume]
    fun x => (-Complex.I*(h:ℂ))*first (timeAmplitude A D t) (timeScale D t) α β b x := by
  filter_upwards [Lp.coeFn_smul (-Complex.I*(h:ℂ)) (firstCurve A D hA hAm hD hDb α β hα hβ hw b t),
    KFCausalIntervalL2Derivative.curve_coe _
      (KFCausalGaussianSecondShearBounds.first_path_memLp A D hA hAm hD hDb α β hα hβ hw b) t] with x hs hf
  change ((-Complex.I*(h:ℂ)) • firstCurve A D hA hAm hD hDb α β hα hβ hw b t) x = _
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul]
  change firstCurve A D hA hAm hD hDb α β hα hβ hw b t x = _ at hf
  rw [hf,KFCausalIntervalL2Derivative.clip_eq t t.property]

theorem secondShear_coe (t : Interval) : secondShear ε a p h α β hε ha hα hβ hw hb b t =ᵐ[volume]
    fun x => (-Complex.I*(h:ℂ))^2*second (timeAmplitude A D t) (timeScale D t) α β b x := by
  filter_upwards [Lp.coeFn_smul ((-Complex.I*(h:ℂ))^2) (secondState A D hA hAm hD hDb α β hα hβ hw b t),
    (KFCausalGaussianSecondShearBounds.second_path_memLp A D hA hAm hD hDb α β hα hβ hw b t t.property).coeFn_toLp] with x hs hf
  change (((-Complex.I*(h:ℂ))^2) • secondState A D hA hAm hD hDb α β hα hβ hw b t) x = _
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul]
  change secondState A D hA hAm hD hDb α β hα hβ hw b t x = _ at hf
  rw [hf]

theorem input_derivative_identity (hh : h ≠ 0) (t : Interval) :
    inputDerivative A D hA hAm hD hDb α β hα hβ hw b t =
      coefficientOperator ε h hε hb hh (shear ε a p h α β hε ha hα hβ hw hb b t) := by
  apply Lp.ext
  filter_upwards [(inputDerivative_memLp A D hA hAm hD hDb α β hα hβ hw b t).coeFn_toLp,
    coefficientOperator_coe ε h hε hb hh (shear ε a p h α β hε ha hα hβ hw hb b t),
    shear_coe ε a p h α β hε ha hα hβ hw hb b t] with x hd hc hs
  change inputDerivative A D hA hAm hD hDb α β hα hβ hw b t x = _ at hd
  rw [hd,hc,hs]
  have he : coefficient ε h x.1*(-Complex.I*(h:ℂ)) = D x.1 := by
    convert coefficient_generator_identity ε h x.1 hh using 1
    ring
  rw [← mul_assoc,he]

theorem shear_derivative_identity (hh : h ≠ 0) (t : Interval) :
    (-Complex.I*(h:ℂ)) • firstDerivative A D hA hAm hD hDb α β hα hβ hw b t =
      coefficientOperator ε h hε hb hh (secondShear ε a p h α β hε ha hα hβ hw hb b t) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul (-Complex.I*(h:ℂ)) (firstDerivative A D hA hAm hD hDb α β hα hβ hw b t),
    (firstDerivative_memLp A D hA hAm hD hDb α β hα hβ hw b t).coeFn_toLp,
    coefficientOperator_coe ε h hε hb hh (secondShear ε a p h α β hε ha hα hβ hw hb b t),
    secondShear_coe ε a p h α β hε ha hα hβ hw hb b t] with x hs hd hc hj
  rw [hs,hc,hj]
  simp only [Pi.smul_apply,smul_eq_mul]
  change firstDerivative A D hA hAm hD hDb α β hα hβ hw b t x = _ at hd
  rw [hd]
  have he : coefficient ε h x.1*(-Complex.I*(h:ℂ)) = D x.1 := by
    convert coefficient_generator_identity ε h x.1 hh using 1
    ring
  calc
    _ = (coefficient ε h x.1*(-Complex.I*(h:ℂ)))*(-Complex.I*(h:ℂ))*
        second (timeAmplitude A D t) (timeScale D t) α β b x := by rw [he]; ring
    _ = _ := by ring

theorem input_strong_derivative (hh : h ≠ 0) (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (input ε a p h α β hε ha hα hβ hw hb b)
      (coefficientOperator ε h hε hb hh (shear ε a p h α β hε ha hα hβ hw hb b t)) t := by
  rw [← input_derivative_identity ε a p h α β hε ha hα hβ hw hb b hh ⟨t,ht.1.le,ht.2.le⟩]
  exact inputCurve_derivative A D hA hAm hD hDb α β hα hβ hw b t ht

theorem shear_strong_derivative (hh : h ≠ 0) (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (shear ε a p h α β hε ha hα hβ hw hb b)
      (coefficientOperator ε h hε hb hh (secondShear ε a p h α β hε ha hα hβ hw hb b ⟨t,ht.1.le,ht.2.le⟩)) t := by
  rw [← shear_derivative_identity ε a p h α β hε ha hα hβ hw hb b hh ⟨t,ht.1.le,ht.2.le⟩]
  exact outputCurve_derivative A D hA hAm hD hDb α β hα hβ hw b h t ht

theorem input_shear_graph (hh : h ≠ 0) (t : Interval) :
    (input ε a p h α β hε ha hα hβ hw hb b t,shear ε a p h α β hε ha hα hβ hw hb b t) ∈
      (shearMomentum h).graph := input_graph A D hA hAm hD hDb α β hα hβ hw b h hh t

theorem shear_second_graph (hh : h ≠ 0) (t : Interval) :
    (shear ε a p h α β hε ha hα hβ hw hb b t,secondShear ε a p h α β hε ha hα hβ hw hb b t) ∈
      (shearMomentum h).graph := output_graph A D hA hAm hD hDb α β hα hβ hw b h hh t

#print axioms coefficientOperator_coe
#print axioms input_continuous
#print axioms shear_continuous
#print axioms input_eq_state
#print axioms input_one
#print axioms shear_coe
#print axioms secondShear_coe
#print axioms input_derivative_identity
#print axioms shear_derivative_identity
#print axioms input_strong_derivative
#print axioms shear_strong_derivative
#print axioms input_shear_graph
#print axioms shear_second_graph
end
end UnifiedTheory.Audit.KFCausalActualImaginaryShearCurve
