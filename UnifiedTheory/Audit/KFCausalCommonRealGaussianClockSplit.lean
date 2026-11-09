/- Exact original sourced-kernel clock split for a common real neutral
source. The simultaneous charged dilation is removed before the actual
imaginary and field derivatives are estimated. -/
import UnifiedTheory.Audit.KFCausalCommonRealGaussianImaginaryDerivative
import UnifiedTheory.Audit.KFCausalJointFourierRealDilationClock

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCommonRealGaussianClockSplit
noncomputable section
open scoped ComplexConjugate BigOperators
open KFCausalGaussianSourceKernelDerivative (kernel slope pairSlope familySlope)
open KFCausalGaussianSourceJointKernel (pairKernel familyForm sourceV sourceX)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalJointFourierRealDilationClock (realDilationRate)
open KFCausalNeutralPlaneClockGeometry (velocity denominator)
open KFCausalNeutralPlaneNormalizedGeometry (realNumerator)
open KFCausalReciprocalWedgeVelocity (radius)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalNeutralPlaneNormalizedGeometry (fraction)

def pairFieldSlope (α β w v : ℝ) (r : ℂ) (B : ℝ) : ℂ :=
  slope (KFCausalReciprocalCrossGeometry.B α w v r)
    (conj (KFCausalReciprocalCrossGeometry.B α w v r))
    (KFCausalReciprocalCrossGeometry.C α β w v r) 0 (2*(B:ℂ)) 0 0 0 0 β (fieldSlope r) 1

def familyFieldSlope (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ) (B : ℝ) (c : Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, ((conj (c i)*c j)*(w i:ℂ)*(w j:ℂ))*pairFieldSlope α β (w i) (w j) r B

def clockQ (t : ℝ) (r : ℂ) : ℝ := t*radius r/denominator (1-t) t r
def clockChi (t : ℝ) (r : ℂ) : ℝ := realNumerator t r/(2*radius r)

private theorem linear_split (S T H f Sd Td Hd : ℂ) (β L h q b : ℝ)
    (hS : S ≠ 0) (hT : T ≠ 0) (hH : H ≠ 0) :
    slope S T H 0 f (2*(h:ℂ)*S-((q*b:ℝ):ℂ)*Sd)
      (2*(h:ℂ)*T-((q*b:ℝ):ℂ)*Td) (2*(h:ℂ)*H-((q*b:ℝ):ℂ)*Hd) 0 β L (h*L-3*h) =
      (-4*(h:ℂ))*kernel S T H 0 f β L-
        ((q*b:ℝ):ℂ)*slope S T H 0 f Sd Td Hd 0 β L 0-
        ((3*h:ℝ):ℂ)*slope S T H 0 f 0 0 0 0 β L 1 := by
  have he : slope S T H 0 f (2*(h:ℂ)*S-((q*b:ℝ):ℂ)*Sd)
      (2*(h:ℂ)*T-((q*b:ℝ):ℂ)*Td) (2*(h:ℂ)*H-((q*b:ℝ):ℂ)*Hd) 0 β L (h*L-3*h) =
      slope S T H 0 f (2*(h:ℂ)*S) (2*(h:ℂ)*T) (2*(h:ℂ)*H) 0 β L (h*L)-
        ((q*b:ℝ):ℂ)*slope S T H 0 f Sd Td Hd 0 β L 0-
        ((3*h:ℝ):ℂ)*slope S T H 0 f 0 0 0 0 β L 1 := by
    unfold KFCausalGaussianSourceKernelDerivative.slope KFCausalGaussianSourceKernelDerivative.logSlope
      KFCausalGaussianSourceKernelDerivative.meanSlope KFCausalGaussianSourceKernelDerivative.varianceSlope
    push_cast
    ring
  rw [he]
  have hd := KFCausalGaussianSourceKernelDerivative.dilation_slope S T H 0 f β L h hS hT hH
  simpa only [mul_zero] using congrArg
    (fun z => z-((q*b:ℝ):ℂ)*slope S T H 0 f Sd Td Hd 0 β L 0-
      ((3*h:ℝ):ℂ)*slope S T H 0 f 0 0 0 0 β L 1) hd

theorem pair_split (α β w v h q B : ℝ) (r : ℂ)
    (hS : 0 < (KFCausalReciprocalCrossGeometry.B α w v r).re)
    (hH : 0 < (KFCausalReciprocalCrossGeometry.C α β w v r).re) :
    pairSlope α β w v r ((h:ℂ)*r-Complex.I*((q*r.im:ℝ):ℂ)) (B:ℂ) (B:ℂ) =
      (-4*(h:ℂ))*pairKernel α β w v r (B:ℂ) (B:ℂ)-
      ((q*r.im:ℝ):ℂ)*pairSlope α β w v r Complex.I (B:ℂ) (B:ℂ)-
      ((3*h:ℝ):ℂ)*pairFieldSlope α β w v r B := by
  let S := KFCausalReciprocalCrossGeometry.B α w v r
  let H := KFCausalReciprocalCrossGeometry.C α β w v r
  let Sd := KFCausalGaussianSourceKernelDerivative.chargedVelocity α w v r Complex.I
  have hv : KFCausalGaussianSourceKernelDerivative.chargedVelocity α w v r
      ((h:ℂ)*r-Complex.I*((q*r.im:ℝ):ℂ)) = 2*(h:ℂ)*S-((q*r.im:ℝ):ℂ)*Sd := by
    unfold Sd S KFCausalGaussianSourceKernelDerivative.chargedVelocity KFCausalReciprocalCrossGeometry.B
    simp only [map_mul,map_sub,Complex.conj_ofReal,Complex.conj_I]
    push_cast
    ring
  have hvT : conj (KFCausalGaussianSourceKernelDerivative.chargedVelocity α w v r
      ((h:ℂ)*r-Complex.I*((q*r.im:ℝ):ℂ))) = 2*(h:ℂ)*conj S-((q*r.im:ℝ):ℂ)*conj Sd := by
    rw [hv]
    simp only [map_mul,map_sub,Complex.conj_ofReal,map_ofNat]
  have hvH : KFCausalGaussianSourceKernelDerivative.chargedVelocity α w v r
      ((h:ℂ)*r-Complex.I*((q*r.im:ℝ):ℂ))-((16*β*r.im*((h:ℂ)*r-Complex.I*((q*r.im:ℝ):ℂ)).im:ℝ):ℂ) =
      2*(h:ℂ)*H-((q*r.im:ℝ):ℂ)*(Sd-((16*β*r.im:ℝ):ℂ)) := by
    rw [hv]
    unfold H KFCausalReciprocalCrossGeometry.C
    simp only [Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,zero_mul,one_mul,add_zero]
    push_cast
    dsimp only [S]
    ring
  have hL : -2*((h:ℂ)*r-Complex.I*((q*r.im:ℝ):ℂ)).re=h*fieldSlope r-3*h := by
    simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,zero_mul,mul_zero,sub_zero]
    unfold fieldSlope
    ring
  rw [KFCausalGaussianSourceKernelDerivative.pairKernel_eq_kernel]
  unfold pairSlope pairFieldSlope
  simp only [sourceV,sourceX,Complex.conj_ofReal,sub_self,mul_zero,
    Complex.I_im,Complex.I_re,mul_one]
  rw [hvT,hvH,hv,hL]
  have hSn : S ≠ 0 := by intro hz; simp only [S] at hz; rw [hz] at hS; simp at hS
  have hHn : H ≠ 0 := by intro hz; simp only [H] at hz; rw [hz] at hH; simp at hH
  have hTn : conj S ≠ 0 := by simpa using hSn
  simpa only [S,H,Sd,← two_mul] using
    linear_split S (conj S) H (2*(B:ℂ)) Sd (conj Sd) (Sd-((16*β*r.im:ℝ):ℂ))
      β (fieldSlope r) h q r.im hSn hTn hHn

theorem family_split (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ) (h q B : ℝ)
    (c : Fin n → ℂ) (hβ : 0 < β)
    (hd : ∀ i, 0 < (w i*α)*KFCausalReciprocalGaussianCoordinates.area r-8*β*r.im^2) :
    familySlope n α β w r ((h:ℂ)*r-Complex.I*((q*r.im:ℝ):ℂ)) (fun _ => (B:ℂ)) c =
      (-4*(h:ℂ))*familyForm n α β w r (fun _ => (B:ℂ)) c-
      ((q*r.im:ℝ):ℂ)*familySlope n α β w r Complex.I (fun _ => (B:ℂ)) c-
      ((3*h:ℝ):ℂ)*familyFieldSlope n α β w r B c := by
  unfold familySlope familyForm familyFieldSlope
  simp only [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hf := KFCausalGaussianSourceJointKernel.pair_floors α β (w i) (w j) r hβ (hd i) (hd j)
  rw [pair_split α β (w i) (w j) h q B r hf.1 hf.2]
  ring

theorem clock_velocity (t : ℝ) (r : ℂ) (ha : r.re ≠ 0) :
    velocity (1-t) t r=(realDilationRate t r:ℂ)*r-Complex.I*((clockQ t r*r.im:ℝ):ℂ) := by
  have he := KFCausalJointFourierRealDilationClock.corrected_velocity t r ha
  have hq : t*KFCausalJointFourierDissipationClock.normalizedRealCooling t r/r.re=clockQ t r := by
    unfold KFCausalJointFourierDissipationClock.normalizedRealCooling clockQ
    field_simp
  have hc : -t*KFCausalJointFourierDissipationClock.normalizedRealCooling t r*r.im/r.re =
      -(clockQ t r*r.im) := by rw [← hq]; ring
  rw [hc,Complex.ofReal_neg,mul_neg] at he
  linear_combination he

theorem rate_eq_q_chi (t : ℝ) (r : ℂ) (hR : radius r ≠ 0) :
    realDilationRate t r=clockQ t r*clockChi t r := by
  unfold realDilationRate clockQ clockChi
  field_simp

variable (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
local notation "r" => scale ε y s
include hε hy

theorem clock_q_bounds (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    0 ≤ clockQ t r ∧ clockQ t r ≤ 20*t := by
  have hR1 := KFCausalClockFloorExactScaleRegion.norm_square_one_le ε y s hε hy
  have hR2 := KFCausalClockFloorExactScaleRegion.norm_square_le_two ε y s hε hy
  change 1 ≤ radius r at hR1
  change radius r ≤ 2 at hR2
  have hD := KFCausalJointClockCoolingCoercivity.normalized_denominator_bounds ε y s hε hy t ht
  have hDp : 0 < denominator (1-t) t r := by linarith [hD.1]
  have ht0 := ht.1
  unfold clockQ
  refine ⟨div_nonneg (mul_nonneg ht.1 (by linarith)) hDp.le,?_⟩
  apply (div_le_iff₀ hDp).mpr
  have h1 := mul_le_mul_of_nonneg_left hR2 ht.1
  have h2 := mul_le_mul_of_nonneg_left hD.1 (show 0 ≤ 20*t by positivity)
  nlinarith

theorem clock_chi_bound (t : ℝ) (ht : t ∈ Set.Icc 0 1) : |clockChi t r| ≤ 1 := by
  have hR := KFCausalClockFloorExactScaleRegion.norm_square_one_le ε y s hε hy
  change 1 ≤ radius r at hR
  have hb := KFCausalClockFloorExactScaleRegion.imaginary_square_le_half ε y s hε hy
  have hN := KFCausalJointFourierRealDilationClock.real_numerator_bounds ε y s hε hy t ht
  have hNp : |realNumerator t r| ≤ 4*(r).im^2 := abs_le.mpr ⟨by linarith [hN.1],hN.2⟩
  unfold clockChi
  rw [abs_div,abs_of_pos (show 0 < 2*radius r by linarith)]
  apply (div_le_iff₀ (show 0 < 2*radius r by linarith)).mpr
  nlinarith

theorem actual_family_split (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (B : ℝ) (c : Fin n → ℂ)
    (hα : 0 < α) (hβ : 0 < β) (hwidth : 32*β ≤ α) (hw : ∀ i, 1 ≤ w i) :
    familySlope n α β w r (deriv (scale ε y) s) (fun _ => (B:ℂ)) c =
      (-4*(realDilationRate (fraction ε s) r:ℂ))*familyForm n α β w r (fun _ => (B:ℂ)) c-
      ((clockQ (fraction ε s) r*(r).im:ℝ):ℂ)*familySlope n α β w r Complex.I (fun _ => (B:ℂ)) c-
      ((3*realDilationRate (fraction ε s) r:ℝ):ℂ)*familyFieldSlope n α β w r B c := by
  rw [(KFCausalNeutralPlaneNormalizedGeometry.actual_normalized_velocity ε y s hε hy).deriv,
    clock_velocity _ _ (KFCausalNeutralPlaneClockGeometry.scale_re_positive ε y s hε hy).ne']
  apply family_split n α β w r _ _ B c hβ
  intro i
  have hp := KFCausalChargedPairCompactGeometry.actual_mem_region α β ε y s hα hβ.le hwidth hε hy
  obtain ⟨hc,ha⟩ := KFCausalChargedPairCompactGeometry.region_widths_positive α β hα _ hp
  exact (KFCausalJointFourierDilationQuartic.width_floors α _ (w i) β (hw i) ha hc).2

#print axioms pair_split
#print axioms family_split
#print axioms clock_velocity
#print axioms rate_eq_q_chi
#print axioms clock_q_bounds
#print axioms clock_chi_bound
#print axioms actual_family_split
end
end UnifiedTheory.Audit.KFCausalCommonRealGaussianClockSplit
