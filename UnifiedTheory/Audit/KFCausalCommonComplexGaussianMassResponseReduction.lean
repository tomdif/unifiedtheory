/- Exact common-complex-source translation of the ORIGINAL quadratic
physical channel and its geometric clock response. The resulting scalar
discriminant is an equivalence, not a proof of a response bound. Every
evaluation retains the same finite amplitudes, widths and imaginary source. -/
import UnifiedTheory.Audit.KFCausalCommonRealGaussianWeightedTransport
import Mathlib.Algebra.QuadraticDiscriminant

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCommonComplexGaussianMassResponseReduction
noncomputable section
open scoped ComplexConjugate
open KFCausalGaussianWeightedSourceKernelDerivative
open KFCausalGaussianSourceKernelDerivative (prefactor logSlope meanSlope varianceSlope)
open KFCausalGaussianSourcePlaneKernel (mean variance)
open KFCausalGaussianSourceJointKernel (sourceV sourceX)
open KFCausalWeightedReciprocalNeutralWholeClock (positiveSlice transportResponse)

def commonSource (A D : ℝ) : ℂ := (A:ℂ)+(D:ℂ)*Complex.I

private def quadratic (β : ℝ) (u v z : ℂ) (A : ℝ) : ℂ :=
  (Real.exp (A^2/(2*β)):ℂ)*(u*((A/(2*β):ℝ):ℂ)^2+v*((A/(2*β):ℝ):ℂ)+z)

private theorem quadratic_reconstruct (β A : ℝ) (hβ : 0 < β) (u v z : ℂ) :
    quadratic β u v z A = (Real.exp (A^2/(2*β)):ℂ)*
      (((A/(2*β):ℝ):ℂ)^2*u+
        ((A/(2*β):ℝ):ℂ)*(Real.exp (-2*β):ℂ)/2*
          (quadratic β u v z (2*β)-quadratic β u v z (-2*β))+
        quadratic β u v z 0) := by
  have hb : β ≠ 0 := ne_of_gt hβ
  have hp : (2*β)^2/(2*β) = 2*β := by field_simp
  have hn : (-2*β)^2/(2*β) = 2*β := by field_simp
  have hneg : -2*β/(2*β) = -1 := by field_simp
  have he : (Real.exp (-2*β):ℂ)*(Real.exp (2*β):ℂ) = 1 := by
    rw [← Complex.ofReal_mul,← Real.exp_add]
    norm_num
  have hdiv : 2*β/(2*β) = 1 := div_self (mul_ne_zero (by norm_num) hb)
  simp only [quadratic,hp,hn,hneg,hdiv,zero_pow (by decide : (2:ℕ) ≠ 0),
    zero_div,Real.exp_zero,Complex.ofReal_zero,Complex.ofReal_one,Complex.ofReal_neg,
    neg_one_sq,one_pow,mul_one,mul_zero,add_zero]
  linear_combination -((Real.exp (A^2/(2*β)):ℂ)*((A/(2*β):ℝ):ℂ)*v) * he

private theorem prefactor_source (S T H e : ℂ) (β A : ℝ) :
    prefactor S T H e (2*(A:ℂ)) β =
      (Real.exp (A^2/(2*β)):ℂ)*prefactor S T H e 0 β := by
  unfold prefactor KFCausalShiftedComplexGaussianMoments.mass
  have he : (2*(A:ℂ))^2/(4*(2*(β:ℂ))) = ((A^2/(2*β):ℝ):ℂ) := by
    push_cast
    ring
  rw [he,Complex.ofReal_exp]
  simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_div,Complex.exp_zero,mul_one]
  ring

private theorem mean_source (H e : ℂ) (β L A : ℝ) :
    mean H (2*(β:ℂ)) e (2*(A:ℂ)) L =
      ((A/(2*β):ℝ):ℂ)+mean H (2*(β:ℂ)) e 0 L := by
  unfold mean
  push_cast
  ring

private theorem kernel_quadratic (S T H e : ℂ) (β L A : ℝ) :
    kernel 2 0 0 S T H e (2*(A:ℂ)) β L =
      quadratic β (kernel 0 0 1 S T H e 0 β L)
        (2*prefactor S T H e 0 β*mean H (2*(β:ℂ)) e 0 L)
        (kernel 2 0 0 S T H e 0 β L) A := by
  unfold kernel
  rw [prefactor_source,mean_source]
  unfold quadratic KFCausalGaussianWeightedSourcePlaneKernel.wick
  norm_num
  ring

private theorem slope_quadratic (S T H e Sd Td Hd ed : ℂ) (β L Ld A : ℝ) :
    slope 2 0 0 S T H e (2*(A:ℂ)) Sd Td Hd ed β L Ld =
      quadratic β (slope 0 0 1 S T H e 0 Sd Td Hd ed β L Ld)
        (2*prefactor S T H e 0 β*
          (logSlope S T H e Sd Td Hd ed*mean H (2*(β:ℂ)) e 0 L+
            meanSlope H e Hd ed L Ld))
        (slope 2 0 0 S T H e 0 Sd Td Hd ed β L Ld) A := by
  unfold KFCausalGaussianWeightedSourceKernelDerivative.slope
  rw [prefactor_source,mean_source]
  unfold quadratic KFCausalGaussianWeightedSourcePlaneKernel.wick
  norm_num
  ring

theorem kernel_mass_translation (S T H e : ℂ) (β L A : ℝ) (hβ : 0 < β) :
    kernel 2 0 0 S T H e (2*(A:ℂ)) β L = (Real.exp (A^2/(2*β)):ℂ)*
      (((A/(2*β):ℝ):ℂ)^2*kernel 0 0 1 S T H e 0 β L+
        ((A/(2*β):ℝ):ℂ)*(Real.exp (-2*β):ℂ)/2*
          (kernel 2 0 0 S T H e (2*((2*β:ℝ):ℂ)) β L-
           kernel 2 0 0 S T H e (2*((-2*β:ℝ):ℂ)) β L)+
        kernel 2 0 0 S T H e 0 β L) := by
  simp_rw [kernel_quadratic]
  convert quadratic_reconstruct β A hβ (kernel 0 0 1 S T H e 0 β L)
    (2*prefactor S T H e 0 β*mean H (2*(β:ℂ)) e 0 L)
    (kernel 2 0 0 S T H e 0 β L) using 1
  simp [quadratic]

theorem slope_mass_translation (S T H e Sd Td Hd ed : ℂ) (β L Ld A : ℝ) (hβ : 0 < β) :
    slope 2 0 0 S T H e (2*(A:ℂ)) Sd Td Hd ed β L Ld = (Real.exp (A^2/(2*β)):ℂ)*
      (((A/(2*β):ℝ):ℂ)^2*slope 0 0 1 S T H e 0 Sd Td Hd ed β L Ld+
        ((A/(2*β):ℝ):ℂ)*(Real.exp (-2*β):ℂ)/2*
          (slope 2 0 0 S T H e (2*((2*β:ℝ):ℂ)) Sd Td Hd ed β L Ld-
           slope 2 0 0 S T H e (2*((-2*β:ℝ):ℂ)) Sd Td Hd ed β L Ld)+
        slope 2 0 0 S T H e 0 Sd Td Hd ed β L Ld) := by
  simp_rw [slope_quadratic]
  convert quadratic_reconstruct β A hβ (slope 0 0 1 S T H e 0 Sd Td Hd ed β L Ld)
    (2*prefactor S T H e 0 β*
      (logSlope S T H e Sd Td Hd ed*mean H (2*(β:ℂ)) e 0 L+meanSlope H e Hd ed L Ld))
    (slope 2 0 0 S T H e 0 Sd Td Hd ed β L Ld) using 1
  simp [quadratic]

private theorem sourceV_common (r : ℂ) (A D : ℝ) :
    sourceV r (commonSource A D) (commonSource A D) = sourceV r (commonSource 0 D) (commonSource 0 D) := by
  simp only [sourceV,commonSource,map_add,map_mul,Complex.conj_ofReal,Complex.conj_I,
    Complex.ofReal_zero,zero_add]
  ring

private theorem sourceX_common (A D : ℝ) :
    sourceX (commonSource A D) (commonSource A D) = 2*(A:ℂ) := by
  simp only [sourceX,commonSource,map_add,map_mul,Complex.conj_ofReal,Complex.conj_I]
  ring

theorem family_mass_translation (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ)
    (D A : ℝ) (c : Fin n → ℂ) (hβ : 0 < β) :
    familyForm 2 0 0 n α β w r (fun _ => commonSource A D) c =
      (Real.exp (A^2/(2*β)):ℂ)*
        (((A/(2*β):ℝ):ℂ)^2*familyForm 0 0 1 n α β w r (fun _ => commonSource 0 D) c+
          ((A/(2*β):ℝ):ℂ)*(Real.exp (-2*β):ℂ)/2*
            (familyForm 2 0 0 n α β w r (fun _ => commonSource (2*β) D) c-
             familyForm 2 0 0 n α β w r (fun _ => commonSource (-2*β) D) c)+
          familyForm 2 0 0 n α β w r (fun _ => commonSource 0 D) c) := by
  simp only [familyForm,mul_add,mul_sub,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [pairKernel,sourceV_common,sourceX_common,Complex.ofReal_zero,mul_zero]
  rw [kernel_mass_translation _ _ _ _ β _ A hβ]
  ring

theorem familySlope_mass_translation (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r rd : ℂ)
    (D A : ℝ) (c : Fin n → ℂ) (hβ : 0 < β) :
    familySlope 2 0 0 n α β w r rd (fun _ => commonSource A D) c =
      (Real.exp (A^2/(2*β)):ℂ)*
        (((A/(2*β):ℝ):ℂ)^2*familySlope 0 0 1 n α β w r rd (fun _ => commonSource 0 D) c+
          ((A/(2*β):ℝ):ℂ)*(Real.exp (-2*β):ℂ)/2*
            (familySlope 2 0 0 n α β w r rd (fun _ => commonSource (2*β) D) c-
             familySlope 2 0 0 n α β w r rd (fun _ => commonSource (-2*β) D) c)+
          familySlope 2 0 0 n α β w r rd (fun _ => commonSource 0 D) c) := by
  simp only [familySlope,mul_add,mul_sub,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [pairSlope,sourceV_common,sourceX_common,Complex.ofReal_zero,mul_zero]
  rw [slope_mass_translation _ _ _ _ _ _ _ _ β _ _ A hβ]
  ring

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C : Fin n → ℂ) (D : ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "α" => KFCausalChargeGaussianGeometry.groundWidth h
local notation "β" => KFCausalClockFloorInvariantTrial.neutralWidth h
local notation "E" => fun m v A s => positiveSlice m 0 v n ε h a w p C (fun _ => commonSource A D) (fun _ => 1) s
local notation "R" => fun m v A s => transportResponse m 0 v n ε h a w p C (fun _ => commonSource A D) (fun _ => 1) s

include hε hh hw hb in
theorem positiveSlice_translation (A s : ℝ) :
    E 2 0 A s = Real.exp (A^2/(2*β))*
      ((A/(2*β))^2*E 0 1 0 s+A/(2*β)*Real.exp (-2*β)/2*
        (E 2 0 (2*β) s-E 2 0 (-2*β) s)+E 2 0 0 s) := by
  have hE (m v X : ℝ) : E m v X s = Real.pi/4*
      (familyForm m 0 v n α β w (KFCausalClockFloorRelativeShift.scale ε (-h/2) s)
        (fun _ => commonSource X D) (KFCausalReciprocalNeutralPositiveEnergy.coefficients n ε h a p C s)).re := by
    have he := KFCausalCommonRealGaussianWeightedTransport.clockPairing_family m 0 v n ε h a w p C
      (fun _ => commonSource X D) hε hh hw hb s
    have hr := congrArg Complex.re he
    simpa only [Complex.mul_re,Complex.div_ofNat_re,Complex.div_ofNat_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_div,zero_mul,sub_zero] using hr
  rw [hE 2 0 A,hE 0 1 0,hE 2 0 (2*β),hE 2 0 (-2*β),hE 2 0 0]
  rw [family_mass_translation n α β w _ D A _
    (KFCausalClockFloorInvariantTrial.neutralWidth_positive h hh)]
  simp only [Complex.mul_re,Complex.add_re,Complex.sub_re,Complex.div_ofNat_re,
    Complex.div_ofNat_im,Complex.ofReal_re,Complex.ofReal_im,← Complex.ofReal_pow,
    Complex.mul_im,zero_mul,mul_zero,sub_zero,add_zero]
  ring

include hε hh hw hb in
theorem transport_translation (A s : ℝ) :
    R 2 0 A s = Real.exp (A^2/(2*β))*
      ((A/(2*β))^2*R 0 1 0 s+A/(2*β)*Real.exp (-2*β)/2*
        (R 2 0 (2*β) s-R 2 0 (-2*β) s)+R 2 0 0 s) := by
  simp_rw [KFCausalCommonRealGaussianWeightedTransport.transport_family
    _ _ _ n ε h a w p C _ hε hh hw hb]
  rw [familySlope_mass_translation n α β w _ _ D A _
    (KFCausalClockFloorInvariantTrial.neutralWidth_positive h hh)]
  simp only [Complex.mul_re,Complex.add_re,Complex.sub_re,Complex.div_ofNat_re,
    Complex.div_ofNat_im,Complex.ofReal_re,Complex.ofReal_im,← Complex.ofReal_pow,
    Complex.mul_im,zero_mul,mul_zero,sub_zero,add_zero]
  ring

/-- The proposed bound minus the original physical geometric response.
The bound coefficient K can, in particular, be C*fraction epsilon s. -/
def defect (m v K A s : ℝ) : ℝ := K*E m v A s-R m v A s

def oddDefect (K s : ℝ) : ℝ := Real.exp (-2*β)/4*
  (defect n ε h a w p C D 2 0 K (2*β) s-
   defect n ε h a w p C D 2 0 K (-2*β) s)

include hε hh hw hb in
theorem defect_translation (K A s : ℝ) :
    defect n ε h a w p C D 2 0 K A s = Real.exp (A^2/(2*β))*
      ((A/(2*β))^2*defect n ε h a w p C D 0 1 K 0 s+
        2*(A/(2*β))*oddDefect n ε h a w p C D K s+
        defect n ε h a w p C D 2 0 K 0 s) := by
  unfold oddDefect defect
  rw [positiveSlice_translation n ε h a w p C D hε hh hw hb A s,
    transport_translation n ε h a w p C D hε hh hw hb A s]
  ring

private theorem quadratic_nonnegative_iff (u v z : ℝ) :
    (∀ x : ℝ, 0 ≤ u*x^2+2*v*x+z) ↔ 0 ≤ u ∧ 0 ≤ z ∧ v^2 ≤ u*z := by
  constructor
  · intro hp
    have hz : 0 ≤ z := by simpa using hp 0
    have hd := discrim_le_zero (a := u) (b := 2*v) (c := z) (fun x => by simpa [pow_two] using hp x)
    have hv : v^2 ≤ u*z := by unfold discrim at hd; nlinarith
    refine ⟨?_,hz,hv⟩
    rcases eq_or_lt_of_le hz with hzero | hpos
    · rw [← hzero,mul_zero] at hv
      have hv0 : v = 0 := by nlinarith [sq_nonneg v]
      have h1 := hp 1
      nlinarith
    · nlinarith [sq_nonneg v]
  · rintro ⟨hu,hz,hv⟩ x
    rcases eq_or_lt_of_le hu with hzero | hpos
    · have hv0 : v = 0 := by nlinarith [sq_nonneg v]
      simpa only [← hzero,hv0,zero_mul,mul_zero,zero_add] using hz
    · have hs := sq_nonneg (u*x+v)
      nlinarith

include hε hh hw hb in
theorem mass_response_all_sources_iff (K s : ℝ) :
    (∀ A : ℝ, R 2 0 A s ≤ K*E 2 0 A s) ↔
      0 ≤ defect n ε h a w p C D 0 1 K 0 s ∧
      0 ≤ defect n ε h a w p C D 2 0 K 0 s ∧
      (oddDefect n ε h a w p C D K s)^2 ≤
        defect n ε h a w p C D 0 1 K 0 s*defect n ε h a w p C D 2 0 K 0 s := by
  have hβ : 0 < β := KFCausalClockFloorInvariantTrial.neutralWidth_positive h hh
  have hβn : 2*β ≠ 0 := ne_of_gt (by positivity : 0 < 2*β)
  rw [← quadratic_nonnegative_iff]
  constructor
  · intro hbound x
    have hd : 0 ≤ defect n ε h a w p C D 2 0 K (2*β*x) s := sub_nonneg.mpr (hbound _)
    rw [defect_translation n ε h a w p C D hε hh hw hb] at hd
    have he := (mul_nonneg_iff_of_pos_left (Real.exp_pos _)).mp hd
    have hx : 2*β*x/(2*β) = x := by field_simp
    rw [hx] at he
    nlinarith only [he]
  · intro hp A
    have hx := hp (A/(2*β))
    have hd : 0 ≤ defect n ε h a w p C D 2 0 K A s := by
      rw [defect_translation n ε h a w p C D hε hh hw hb]
      apply mul_nonneg (Real.exp_pos _).le
      nlinarith only [hx]
    exact sub_nonneg.mp hd

#print axioms kernel_mass_translation
#print axioms slope_mass_translation
#print axioms family_mass_translation
#print axioms familySlope_mass_translation
#print axioms positiveSlice_translation
#print axioms transport_translation
#print axioms defect_translation
#print axioms mass_response_all_sources_iff
end
end UnifiedTheory.Audit.KFCausalCommonComplexGaussianMassResponseReduction
