/- Specialize the polynomial curves to the actual inverse-clock shift.
The first and second weighted outputs mean P*JG and P*J^2G; they are
not identified with J(PG) without the field commutator. -/
import UnifiedTheory.Audit.KFCausalPolynomialImaginaryShearCurve
import UnifiedTheory.Audit.KFCausalForcedShearVariation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalActualPolynomialShearCurve
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalPolynomialImaginaryShearCurve (Weight)
open UnifiedTheory.Audit.KFCausalImaginaryShearCoefficient
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (Interval displacement_strip_bound)
open UnifiedTheory.Audit.KFCausalImaginaryShearInterpolation
open UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile (clockAmplitude clockAmplitude_smooth)
open UnifiedTheory.Audit.KFCausalGaussianSecondShearDifferential (first second)
open UnifiedTheory.Audit.KFCausalActualImaginaryShearCurve (coefficientOperator coefficientOperator_coe)

variable (P : Weight) (ε a p h α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (hb : |h| ≤ 2*Real.pi*ε/3) (b : Fin 5 → ℂ)
local notation "A" => clockAmplitude ε a p (-h/2)
local notation "D" => displacement ε h
local notation "hA" => clockAmplitude_smooth ε a p (-h/2) hε (half_shift_bound ε h hb)
local notation "hAm" => KFCausalShiftedClockAmplitude.clockAmplitude_memLp ε a p (-h/2) hε ha (half_shift_bound ε h hb)
local notation "hD" => displacement_smooth ε h hε hb
local notation "hDb" => displacement_strip_bound ε h hε hb

def input : ℝ → Hilbert :=
  KFCausalPolynomialImaginaryShearCurve.input P A D hA hAm hD hDb α β hα hβ hw b
def weightedFirst (t : ℝ) : Hilbert := (-Complex.I*(h:ℂ)) •
  KFCausalPolynomialImaginaryShearCurve.firstState P A D hA hAm hD hDb α β hα hβ hw b t
def weightedSecond (t : Interval) : Hilbert := (-Complex.I*(h:ℂ))^2 •
  KFCausalPolynomialImaginaryShearCurve.secondState P A D hA hAm hD hDb α β hα hβ hw b t

theorem input_continuous : Continuous (input P ε a p h α β hε ha hα hβ hw hb b) :=
  KFCausalPolynomialImaginaryShearCurve.input_continuous P A D hA hAm hD hDb α β hα hβ hw b

theorem weightedFirst_continuous : Continuous (weightedFirst P ε a p h α β hε ha hα hβ hw hb b) :=
  (KFCausalPolynomialImaginaryShearCurve.first_continuous P A D hA hAm hD hDb α β hα hβ hw b).const_smul _

theorem input_coe (t : Interval) : input P ε a p h α β hε ha hα hβ hw hb b t =ᵐ[volume]
    fun x => P.value x*actualPath ε a α β p h b t x :=
  KFCausalPolynomialImaginaryShearCurve.input_coe P A D hA hAm hD hDb α β hα hβ hw b t

theorem weightedFirst_coe (t : Interval) : weightedFirst P ε a p h α β hε ha hα hβ hw hb b t =ᵐ[volume]
    fun x => (-Complex.I*(h:ℂ))*(P.value x*first (timeAmplitude A D t) (timeScale D t) α β b x) := by
  filter_upwards [Lp.coeFn_smul (-Complex.I*(h:ℂ))
    (KFCausalPolynomialImaginaryShearCurve.firstState P A D hA hAm hD hDb α β hα hβ hw b t),
    KFCausalPolynomialImaginaryShearCurve.first_coe P A D hA hAm hD hDb α β hα hβ hw b t] with x hs hf
  unfold weightedFirst
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul,hf]

theorem weightedSecond_coe (t : Interval) : weightedSecond P ε a p h α β hε ha hα hβ hw hb b t =ᵐ[volume]
    fun x => (-Complex.I*(h:ℂ))^2*(P.value x*second (timeAmplitude A D t) (timeScale D t) α β b x) := by
  filter_upwards [Lp.coeFn_smul ((-Complex.I*(h:ℂ))^2)
    (KFCausalPolynomialImaginaryShearCurve.secondState P A D hA hAm hD hDb α β hα hβ hw b t),
    KFCausalPolynomialImaginaryShearCurve.second_coe P A D hA hAm hD hDb α β hα hβ hw b t] with x hs hf
  unfold weightedSecond
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul,hf]

theorem input_derivative_identity (hh : h ≠ 0) (t : Interval) :
    KFCausalPolynomialImaginaryShearCurve.inputDerivative P A D hA hAm hD hDb α β hα hβ hw b t =
      coefficientOperator ε h hε hb hh (weightedFirst P ε a p h α β hε ha hα hβ hw hb b t) := by
  apply Lp.ext
  filter_upwards [(KFCausalPolynomialImaginaryShearCurve.inputDerivative_memLp P A D hA hAm hD hDb α β hα hβ hw b t).coeFn_toLp,
    coefficientOperator_coe ε h hε hb hh (weightedFirst P ε a p h α β hε ha hα hβ hw hb b t),
    weightedFirst_coe P ε a p h α β hε ha hα hβ hw hb b t] with x hd hc hs
  change KFCausalPolynomialImaginaryShearCurve.inputDerivative P A D hA hAm hD hDb α β hα hβ hw b t x = _ at hd
  rw [hd,hc,hs]
  have he : coefficient ε h x.1*(-Complex.I*(h:ℂ)) = D x.1 := by
    convert coefficient_generator_identity ε h x.1 hh using 1
    ring
  rw [← he]
  ring

theorem first_derivative_identity (hh : h ≠ 0) (t : Interval) :
    (-Complex.I*(h:ℂ)) • KFCausalPolynomialImaginaryShearCurve.firstDerivative P A D hA hAm hD hDb α β hα hβ hw b t =
      coefficientOperator ε h hε hb hh (weightedSecond P ε a p h α β hε ha hα hβ hw hb b t) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul (-Complex.I*(h:ℂ))
    (KFCausalPolynomialImaginaryShearCurve.firstDerivative P A D hA hAm hD hDb α β hα hβ hw b t),
    (KFCausalPolynomialImaginaryShearCurve.firstDerivative_memLp P A D hA hAm hD hDb α β hα hβ hw b t).coeFn_toLp,
    coefficientOperator_coe ε h hε hb hh (weightedSecond P ε a p h α β hε ha hα hβ hw hb b t),
    weightedSecond_coe P ε a p h α β hε ha hα hβ hw hb b t] with x hs hd hc hj
  rw [hs,hc,hj]
  simp only [Pi.smul_apply,smul_eq_mul]
  change KFCausalPolynomialImaginaryShearCurve.firstDerivative P A D hA hAm hD hDb α β hα hβ hw b t x = _ at hd
  rw [hd]
  have he : coefficient ε h x.1*(-Complex.I*(h:ℂ)) = D x.1 := by
    convert coefficient_generator_identity ε h x.1 hh using 1
    ring
  calc
    _ = (coefficient ε h x.1*(-Complex.I*(h:ℂ)))*(-Complex.I*(h:ℂ))*
        (P.value x*second (timeAmplitude A D t) (timeScale D t) α β b x) := by rw [he]; ring
    _ = _ := by ring

theorem input_strong_derivative (hh : h ≠ 0) (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (input P ε a p h α β hε ha hα hβ hw hb b)
      (coefficientOperator ε h hε hb hh (weightedFirst P ε a p h α β hε ha hα hβ hw hb b t)) t := by
  rw [← input_derivative_identity P ε a p h α β hε ha hα hβ hw hb b hh ⟨t,ht.1.le,ht.2.le⟩]
  exact KFCausalPolynomialImaginaryShearCurve.input_strong_derivative P A D hA hAm hD hDb α β hα hβ hw b t ht

theorem weightedFirst_strong_derivative (hh : h ≠ 0) (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (weightedFirst P ε a p h α β hε ha hα hβ hw hb b)
      (coefficientOperator ε h hε hb hh (weightedSecond P ε a p h α β hε ha hα hβ hw hb b ⟨t,ht.1.le,ht.2.le⟩)) t := by
  rw [← first_derivative_identity P ε a p h α β hε ha hα hβ hw hb b hh ⟨t,ht.1.le,ht.2.le⟩]
  exact HasDerivAt.const_smul (-Complex.I*(h:ℂ))
    (KFCausalPolynomialImaginaryShearCurve.first_strong_derivative P A D hA hAm hD hDb α β hα hβ hw b t ht)

theorem input_one_coe : input P ε a p h α β hε ha hα hβ hw hb b 1 =ᵐ[volume]
    fun x => P.value x*KFCausalClockFloorCoherentSpectral.gaussianState ε a α β p b (-h/2)
      hε ha hα hβ hw (half_shift_bound ε h hb) x := by
  filter_upwards [input_coe P ε a p h α β hε ha hα hβ hw hb b ⟨1,by constructor <;> norm_num⟩,
    actualPath_one_gaussian ε a α β p h b hε ha hα hβ hw hb] with x hx hg
  rw [hx,hg]

#print axioms input_continuous
#print axioms weightedFirst_continuous
#print axioms input_coe
#print axioms weightedFirst_coe
#print axioms weightedSecond_coe
#print axioms input_derivative_identity
#print axioms first_derivative_identity
#print axioms input_strong_derivative
#print axioms weightedFirst_strong_derivative
#print axioms input_one_coe
end
end UnifiedTheory.Audit.KFCausalActualPolynomialShearCurve
