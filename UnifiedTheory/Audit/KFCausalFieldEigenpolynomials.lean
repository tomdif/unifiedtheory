/- The original field and its square split into at most three components
with definite shear degrees. This is an exact polynomial identity, with
the existing Gaussian multiplier bounds; no field or energy is added. -/
import UnifiedTheory.Audit.KFCausalEigenfieldShearGraphs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalFieldEigenpolynomials
noncomputable section
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse velocity)
open UnifiedTheory.Audit.KFCausalFieldPolynomialPackets (constantPart scalePart)
open UnifiedTheory.Audit.KFCausalFieldShearDifferential
open UnifiedTheory.Audit.KFCausalPolynomialImaginaryShearCurve (Weight fieldWeight)
open UnifiedTheory.Audit.KFCausalEigenfieldShearGraphs (EigenWeight)

def constantField (l : Transverse →L[ℝ] ℝ) := l.comp constantPart
def scaleField (l : Transverse →L[ℝ] ℝ) := l.comp scalePart

theorem field_split (l : Transverse →L[ℝ] ℝ) (x : Transverse) :
    constantField l x+scaleField l x = l x := by
  change l (constantPart x)+l (scalePart x)=l x
  rw [← map_add]
  congr 1
  funext i
  by_cases hi : i=4 <;> simp [constantPart,scalePart,hi]

theorem constant_velocity (l : Transverse →L[ℝ] ℝ) (x : Transverse) :
    constantField l (velocity x) = 0 := by
  have he : constantPart (velocity x) = 0 := by
    funext i
    by_cases hi : i=4 <;> simp [constantPart,velocity,hi]
    ring
  change l (constantPart (velocity x)) = 0
  rw [he,map_zero]

theorem scale_velocity (l : Transverse →L[ℝ] ℝ) (x : Transverse) :
    scaleField l (velocity x) = (1/2:ℝ)*scaleField l x := by
  have he : scalePart (velocity x) = (1/2:ℝ) • scalePart x := by
    funext i
    by_cases hi : i=4 <;> simp [scalePart,velocity,hi] <;> ring
  change l (scalePart (velocity x)) = _
  rw [he,map_smul]
  rfl

def powerWeight (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (r : ℝ)
    (hl : ∀ x, l (velocity x)=r*l x) : EigenWeight where
  toWeight := fieldWeight l i
  degree := (i.val+1)*r
  differential x := by
    convert power_line_derivative l i x using 1
    dsimp only [fieldWeight]
    simp only [powerValue,powerSlope,fieldSlope_apply,hl,Nat.cast_add,Nat.cast_one,
      Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one,pow_succ]
    ring

def fixedPower (l : Transverse →L[ℝ] ℝ) (i : Fin 2) : EigenWeight :=
  powerWeight (constantField l) i 0 (fun x => by rw [constant_velocity,zero_mul])
def scalingPower (l : Transverse →L[ℝ] ℝ) (i : Fin 2) : EigenWeight :=
  powerWeight (scaleField l) i (1/2) (scale_velocity l)

def subtract (P Q : Weight) : Weight where
  value x := P.value x-Q.value x
  smooth := P.smooth.sub Q.smooth
  bound := P.bound+Q.bound
  nonnegative := add_nonneg P.nonnegative Q.nonnegative
  estimate x := (norm_sub_le _ _).trans (by nlinarith only [P.estimate x,Q.estimate x])

def mixedWeight (l : Transverse →L[ℝ] ℝ) : Weight :=
  subtract (subtract (fieldWeight (constantField l+scaleField l) 1)
    (fieldWeight (constantField l) 1)) (fieldWeight (scaleField l) 1)

theorem mixed_value (l : Transverse →L[ℝ] ℝ) (x : Configuration) :
    (mixedWeight l).value x = 2*(constantField l x.2:ℂ)*(scaleField l x.2:ℂ) := by
  simp only [mixedWeight,subtract,fieldWeight,powerValue,ContinuousLinearMap.add_apply,
    Complex.ofReal_add]
  norm_num
  ring

theorem linear_line (l : Transverse →L[ℝ] ℝ) (x : Configuration) :
    HasLineDerivAt ℝ (fun y : Configuration => (l y.2:ℂ)) (l (velocity x.2):ℂ)
      x ((0,velocity x.2):Configuration) := by
  have he : powerValue l 0 = fun y => (l y.2:ℂ) := by
    funext y
    simp [powerValue]
  have hd := power_line_derivative l 0 x
  rw [he] at hd
  simpa [powerSlope,fieldSlope_apply] using hd

def mixed (l : Transverse →L[ℝ] ℝ) : EigenWeight where
  toWeight := mixedWeight l
  degree := 1/2
  differential x := by
    have hd := ((linear_line (constantField l) x).mul (linear_line (scaleField l) x)).const_mul 2
    change HasDerivAt (fun t : ℝ => (mixedWeight l).value (x+t • (0,velocity x.2))) _ 0
    convert hd using 1
    · funext t
      rw [mixed_value]
      dsimp only [Pi.mul_apply]
      ring
    · simp only [mixed_value,constant_velocity,scale_velocity,zero_smul,add_zero]
      push_cast
      ring

def zeroWeight : EigenWeight := powerWeight 0 0 0 (fun _ => by simp)

def modes (l : Transverse →L[ℝ] ℝ) (i : Fin 2) : Fin 3 → EigenWeight :=
  if i=0 then ![fixedPower l 0,scalingPower l 0,zeroWeight]
  else ![fixedPower l 1,mixed l,scalingPower l 1]

theorem modes_sum (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (x : Configuration) :
    ∑ k, (modes l i k).value x = powerValue l i x := by
  have he : (constantField l x.2:ℂ)+(scaleField l x.2:ℂ)=(l x.2:ℂ) := by
    rw [← Complex.ofReal_add,field_split]
  fin_cases i
  · simpa [modes,Fin.sum_univ_succ,fixedPower,scalingPower,zeroWeight,powerWeight,fieldWeight,powerValue] using he
  · simp [modes,Fin.sum_univ_succ,fixedPower,scalingPower,powerWeight,fieldWeight,powerValue,mixed,mixed_value]
    rw [← he]
    ring

#print axioms field_split
#print axioms constant_velocity
#print axioms scale_velocity
#print axioms mixed_value
#print axioms linear_line
#print axioms modes_sum
end
end UnifiedTheory.Audit.KFCausalFieldEigenpolynomials
