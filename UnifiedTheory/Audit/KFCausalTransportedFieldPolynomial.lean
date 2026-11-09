/- Exact clock transport of the two physical field powers. The three
eigenpolynomial components recombine before any norm or charge mean.
The resulting complex polynomial is not the untransported real field. -/
import UnifiedTheory.Audit.KFCausalFieldEigenpolynomials
import UnifiedTheory.Audit.KFCausalMatterOrderedDomain

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalTransportedFieldPolynomial
noncomputable section
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalFieldEigenpolynomials
open UnifiedTheory.Audit.KFCausalPolynomialImaginaryShearCurve (fieldWeight)
open UnifiedTheory.Audit.KFCausalFieldShearDifferential (powerValue)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField pointField_apply)

def transportedValue (D : ℂ) (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (x : Configuration) : ℂ :=
  ((constantField l x.2:ℂ)+Complex.exp (-D/2)*(scaleField l x.2:ℂ))^(i.val+1)

theorem mode_real (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (k : Fin 3) (x : Configuration) :
    (modes l i k).value x = (((modes l i k).value x).re:ℂ) := by
  fin_cases i <;> fin_cases k <;>
    simp [modes,fixedPower,scalingPower,zeroWeight,powerWeight,fieldWeight,powerValue,mixed,mixed_value]
  all_goals rw [← Complex.ofReal_pow,Complex.ofReal_re]

theorem mode_re_continuous (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (k : Fin 3) :
    Continuous (fun x => ((modes l i k).value x).re) :=
  Complex.continuous_re.comp (modes l i k).smooth.continuous

private theorem exp_half_square (D : ℂ) : Complex.exp (-D/2)^2 = Complex.exp (-D) := by
  rw [pow_two,← Complex.exp_add]
  congr 1
  ring

theorem weighted_modes_sum (D : ℂ) (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (x : Configuration) :
    (∑ k, Complex.exp (-(modes l i k).degree*D)*(modes l i k).value x) =
      transportedValue D l i x := by
  have hhalf : -((2:ℂ)⁻¹*D) = -D/2 := by ring
  have hwhole : -(((1:ℂ)+1)*2⁻¹*D) = -D := by ring
  fin_cases i
  · simp [modes,Fin.sum_univ_succ,fixedPower,scalingPower,zeroWeight,powerWeight,
      fieldWeight,powerValue,transportedValue,hhalf]
  · simp [modes,Fin.sum_univ_succ,fixedPower,scalingPower,powerWeight,
      fieldWeight,powerValue,mixed,mixed_value,transportedValue]
    rw [hhalf,hwhole,← exp_half_square D]
    ring

theorem physical_field_parts (x : Transverse) :
    constantField pointField x = x 4-2*(x 2+x 3) ∧
      scaleField pointField x = 3*(x 2+x 3) := by
  change pointField (KFCausalFieldPolynomialPackets.constantPart x) = _ ∧
    pointField (KFCausalFieldPolynomialPackets.scalePart x) = _
  norm_num [pointField,KFCausalFieldPolynomialPackets.constantPart,KFCausalFieldPolynomialPackets.scalePart,
    show (2:Fin 5) ≠ 4 by decide,show (3:Fin 5) ≠ 4 by decide]
  ring

theorem physical_transported_value (D : ℂ) (i : Fin 2) (x : Configuration) :
    transportedValue D pointField i x =
      ((x.2 4:ℂ)+(3*Complex.exp (-D/2)-2)*((x.2 2:ℂ)+(x.2 3:ℂ)))^(i.val+1) := by
  unfold transportedValue
  rw [(physical_field_parts x.2).1,(physical_field_parts x.2).2]
  push_cast
  congr 1
  ring

theorem transported_zero (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (x : Configuration) :
    transportedValue 0 l i x = powerValue l i x := by
  unfold transportedValue powerValue
  simp only [neg_zero,zero_div,Complex.exp_zero,one_mul,← Complex.ofReal_add,field_split]

#print axioms mode_real
#print axioms mode_re_continuous
#print axioms weighted_modes_sum
#print axioms physical_field_parts
#print axioms physical_transported_value
#print axioms transported_zero
end
end UnifiedTheory.Audit.KFCausalTransportedFieldPolynomial
