/- Exact weighted clock split for arbitrary fixed complex neutral sources,
including the nonzero sourceV and its actual derivative. This is a kernel
identity; it does not supply a sign or an unrestricted response estimate. -/
import UnifiedTheory.Audit.KFCausalGaussianWeightedSourceKernelDerivative
import UnifiedTheory.Audit.KFCausalCommonRealGaussianClockSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalGaussianWeightedGeneralClockSplit
noncomputable section
open scoped ComplexConjugate BigOperators
open KFCausalGaussianSourceJointKernel (sourceV sourceX)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalJointFourierRealDilationClock (realDilationRate)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalNeutralPlaneNormalizedGeometry (fraction)
open KFCausalCommonRealGaussianClockSplit (clockQ clockChi clock_velocity)
variable (mass2 quartic vacuum : ℝ)
local notation "kernel" => KFCausalGaussianWeightedSourceKernelDerivative.kernel mass2 quartic vacuum
local notation "slope" => KFCausalGaussianWeightedSourceKernelDerivative.slope mass2 quartic vacuum
local notation "pairKernel" => KFCausalGaussianWeightedSourceKernelDerivative.pairKernel mass2 quartic vacuum
local notation "pairSlope" => KFCausalGaussianWeightedSourceKernelDerivative.pairSlope mass2 quartic vacuum
local notation "familyForm" => KFCausalGaussianWeightedSourceKernelDerivative.familyForm mass2 quartic vacuum
local notation "familySlope" => KFCausalGaussianWeightedSourceKernelDerivative.familySlope mass2 quartic vacuum

def pairFieldSlope (α β w v : ℝ) (r si sj : ℂ) : ℂ :=
  slope (KFCausalReciprocalCrossGeometry.B α w v r)
    (conj (KFCausalReciprocalCrossGeometry.B α w v r))
    (KFCausalReciprocalCrossGeometry.C α β w v r) (sourceV r si sj) (sourceX si sj) 0 0 0 0 β (fieldSlope r) 1

def familyFieldSlope (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ) (b c : Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, ((conj (c i)*c j)*(w i:ℂ)*(w j:ℂ))*pairFieldSlope mass2 quartic vacuum α β (w i) (w j) r (b i) (b j)

private theorem linear_split (S T H e f Sd Td Hd ed : ℂ) (β L h q b : ℝ)
    (hS : S ≠ 0) (hT : T ≠ 0) (hH : H ≠ 0) :
    slope S T H e f (2*(h:ℂ)*S-((q*b:ℝ):ℂ)*Sd)
      (2*(h:ℂ)*T-((q*b:ℝ):ℂ)*Td) (2*(h:ℂ)*H-((q*b:ℝ):ℂ)*Hd)
      ((h:ℂ)*e-((q*b:ℝ):ℂ)*ed) β L (h*L-3*h) =
      (-4*(h:ℂ))*kernel S T H e f β L-
        ((q*b:ℝ):ℂ)*slope S T H e f Sd Td Hd ed β L 0-
        ((3*h:ℝ):ℂ)*slope S T H e f 0 0 0 0 β L 1 := by
  have he : slope S T H e f (2*(h:ℂ)*S-((q*b:ℝ):ℂ)*Sd)
      (2*(h:ℂ)*T-((q*b:ℝ):ℂ)*Td) (2*(h:ℂ)*H-((q*b:ℝ):ℂ)*Hd)
      ((h:ℂ)*e-((q*b:ℝ):ℂ)*ed) β L (h*L-3*h) =
      slope S T H e f (2*(h:ℂ)*S) (2*(h:ℂ)*T) (2*(h:ℂ)*H) ((h:ℂ)*e) β L (h*L)-
        ((q*b:ℝ):ℂ)*slope S T H e f Sd Td Hd ed β L 0-
        ((3*h:ℝ):ℂ)*slope S T H e f 0 0 0 0 β L 1 := by
    unfold KFCausalGaussianWeightedSourceKernelDerivative.slope KFCausalGaussianSourceKernelDerivative.logSlope
      KFCausalGaussianSourceKernelDerivative.meanSlope KFCausalGaussianSourceKernelDerivative.varianceSlope
    push_cast
    ring
  rw [he]
  have hd := KFCausalGaussianWeightedSourceKernelDerivative.dilation_slope mass2 quartic vacuum S T H e f β L h hS hT hH
  exact congrArg
    (fun z => z-((q*b:ℝ):ℂ)*slope S T H e f Sd Td Hd ed β L 0-
      ((3*h:ℝ):ℂ)*slope S T H e f 0 0 0 0 β L 1) hd

theorem pair_split (α β w v h q : ℝ) (r si sj : ℂ)
    (hS : 0 < (KFCausalReciprocalCrossGeometry.B α w v r).re)
    (hH : 0 < (KFCausalReciprocalCrossGeometry.C α β w v r).re) :
    pairSlope α β w v r ((h:ℂ)*r-Complex.I*((q*r.im:ℝ):ℂ)) si sj =
      (-4*(h:ℂ))*pairKernel α β w v r si sj-
      ((q*r.im:ℝ):ℂ)*pairSlope α β w v r Complex.I si sj-
      ((3*h:ℝ):ℂ)*pairFieldSlope mass2 quartic vacuum α β w v r si sj := by
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
  have he : sourceV ((h:ℂ)*r-Complex.I*((q*r.im:ℝ):ℂ)) si sj =
      (h:ℂ)*sourceV r si sj-((q*r.im:ℝ):ℂ)*sourceV Complex.I si sj := by
    unfold sourceV
    simp only [Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,zero_mul,one_mul,add_zero]
    push_cast
    ring
  unfold KFCausalGaussianWeightedSourceKernelDerivative.pairSlope pairFieldSlope KFCausalGaussianWeightedSourceKernelDerivative.pairKernel
  rw [hvT,hvH,hv,hL,he]
  simp only [Complex.I_im,Complex.I_re,mul_one,mul_zero]
  have hSn : S ≠ 0 := by intro hz; simp only [S] at hz; rw [hz] at hS; simp at hS
  have hHn : H ≠ 0 := by intro hz; simp only [H] at hz; rw [hz] at hH; simp at hH
  have hTn : conj S ≠ 0 := by simpa using hSn
  simpa only [S,H,Sd,← two_mul] using
    linear_split mass2 quartic vacuum S (conj S) H (sourceV r si sj) (sourceX si sj)
      Sd (conj Sd) (Sd-((16*β*r.im:ℝ):ℂ)) (sourceV Complex.I si sj)
      β (fieldSlope r) h q r.im hSn hTn hHn

theorem family_split (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ) (h q : ℝ)
    (b c : Fin n → ℂ) (hβ : 0 < β)
    (hd : ∀ i, 0 < (w i*α)*KFCausalReciprocalGaussianCoordinates.area r-8*β*r.im^2) :
    familySlope n α β w r ((h:ℂ)*r-Complex.I*((q*r.im:ℝ):ℂ)) b c =
      (-4*(h:ℂ))*familyForm n α β w r b c-
      ((q*r.im:ℝ):ℂ)*familySlope n α β w r Complex.I b c-
      ((3*h:ℝ):ℂ)*familyFieldSlope mass2 quartic vacuum n α β w r b c := by
  unfold KFCausalGaussianWeightedSourceKernelDerivative.familySlope KFCausalGaussianWeightedSourceKernelDerivative.familyForm familyFieldSlope
  simp only [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hf := KFCausalGaussianSourceJointKernel.pair_floors α β (w i) (w j) r hβ (hd i) (hd j)
  rw [pair_split mass2 quartic vacuum α β (w i) (w j) h q r (b i) (b j) hf.1 hf.2]
  ring

variable (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
local notation "r" => scale ε y s
include hε hy

theorem actual_family_split (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
    (hα : 0 < α) (hβ : 0 < β) (hwidth : 32*β ≤ α) (hw : ∀ i, 1 ≤ w i) :
    familySlope n α β w r (deriv (scale ε y) s) b c =
      (-4*(realDilationRate (fraction ε s) r:ℂ))*familyForm n α β w r b c-
      ((clockQ (fraction ε s) r*(r).im:ℝ):ℂ)*familySlope n α β w r Complex.I b c-
      ((3*realDilationRate (fraction ε s) r:ℝ):ℂ)*familyFieldSlope mass2 quartic vacuum n α β w r b c := by
  rw [(KFCausalNeutralPlaneNormalizedGeometry.actual_normalized_velocity ε y s hε hy).deriv,
    clock_velocity _ _ (KFCausalNeutralPlaneClockGeometry.scale_re_positive ε y s hε hy).ne']
  apply family_split mass2 quartic vacuum n α β w r _ _ b c hβ
  intro i
  have hp := KFCausalChargedPairCompactGeometry.actual_mem_region α β ε y s hα hβ.le hwidth hε hy
  obtain ⟨hc,ha⟩ := KFCausalChargedPairCompactGeometry.region_widths_positive α β hα _ hp
  exact (KFCausalJointFourierDilationQuartic.width_floors α _ (w i) β (hw i) ha hc).2

#print axioms pair_split
#print axioms family_split
#print axioms actual_family_split
end
end UnifiedTheory.Audit.KFCausalGaussianWeightedGeneralClockSplit
