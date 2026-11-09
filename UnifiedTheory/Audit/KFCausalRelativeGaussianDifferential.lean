/- Physical Gaussian profiles with a clock-dependent complex transverse
scale. Their exact shear differential is quadratic in the physical
coordinates. This file proves the differential identity, not its L2 bound. -/
import UnifiedTheory.Audit.KFCausalShearPolynomialMoments
import UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse velocity)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments (widths)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalReconstruction (shearDerivative)

def position (r : ℂ) (q : Transverse) (i : Fin 5) : ℂ :=
  if i=4 then (q 4:ℂ)+2*(r-1)*((q 2:ℂ)+(q 3:ℂ)) else r*(q i:ℂ)

def direction (r : ℂ) (q : Transverse) (i : Fin 5) : ℂ :=
  if i=4 then r*((q 2:ℂ)+(q 3:ℂ)) else r*(q i:ℂ)/2

def exponent (α β : ℝ) (b : Fin 5 → ℂ) (r : ℂ) (q : Transverse) : ℂ :=
  (∑ i, b i*position r q i)-(∑ i, (widths α β i:ℂ)*(position r q i)^2)

def profile (A r : ℝ → ℂ) (α β : ℝ) (b : Fin 5 → ℂ) (x : Configuration) : ℂ :=
  A x.1*Complex.exp (exponent α β b (r x.1) x.2)

def slope (r : ℝ → ℂ) (α β : ℝ) (b : Fin 5 → ℂ) (x : Configuration) : ℂ :=
  ∑ i, (b i-2*(widths α β i:ℂ)*position (r x.1) x.2 i)*direction (r x.1) x.2 i

theorem profile_smooth (A r : ℝ → ℂ) (hA : ContDiff ℝ 1 A) (hr : ContDiff ℝ 1 r)
    (α β : ℝ) (b : Fin 5 → ℂ) : ContDiff ℝ 1 (profile A r α β b) := by
  have hp (i : Fin 5) : ContDiff ℝ 1 (fun x : Configuration => position (r x.1) x.2 i) := by
    unfold position
    split_ifs
    · exact (Complex.ofRealCLM.contDiff.comp (by fun_prop)).add
        ((contDiff_const.mul ((hr.comp contDiff_fst).sub contDiff_const)).mul
          ((Complex.ofRealCLM.contDiff.comp (by fun_prop)).add
            (Complex.ofRealCLM.contDiff.comp (by fun_prop))))
    · exact (hr.comp contDiff_fst).mul (Complex.ofRealCLM.contDiff.comp (by fun_prop))
  exact (hA.comp contDiff_fst).mul
    ((ContDiff.sum (fun i _ => contDiff_const.mul (hp i))).sub
      (ContDiff.sum (fun i _ => contDiff_const.mul ((hp i).pow 2)))).cexp

theorem position_derivative (r : ℂ) (q : Transverse) (i : Fin 5) :
    HasDerivAt (fun t : ℝ => position r (q+t • velocity q) i) (direction r q i) 0 := by
  have hl (j : Fin 5) : HasDerivAt (fun t : ℝ => (q j+t*velocity q j:ℝ)) (velocity q j) 0 := by
    simpa only [id_eq,one_mul] using ((hasDerivAt_id (0:ℝ)).mul_const (velocity q j)).const_add (q j)
  by_cases hi : i=4
  · subst i
    have hd := (hl 4).ofReal_comp.add (((hl 2).ofReal_comp.add (hl 3).ofReal_comp).const_mul (2*(r-1)))
    convert hd using 1
    simp [direction,velocity]
    ring
  · have hd := (hl i).ofReal_comp.const_mul r
    convert hd using 1
    · funext t
      simp only [position,if_neg hi,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    · simp only [direction,if_neg hi,velocity,Complex.ofReal_div,Complex.ofReal_ofNat]
      ring

theorem profile_line_derivative (A r : ℝ → ℂ) (α β : ℝ) (b : Fin 5 → ℂ) (x : Configuration) :
    HasLineDerivAt ℝ (profile A r α β b) (slope r α β b x*profile A r α β b x)
      x ((0,velocity x.2):Configuration) := by
  have hl := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 5))) => (position_derivative (r x.1) x.2 i).const_mul (b i))
  have hq := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 5))) =>
      ((position_derivative (r x.1) x.2 i).pow 2).const_mul (widths α β i:ℂ))
  have hd := (hl.sub hq).cexp.const_mul (A x.1)
  change HasDerivAt (fun t : ℝ => profile A r α β b (x+t • (0,velocity x.2))) _ 0
  convert hd using 1
  · funext t
    simp [profile,exponent]
  · simp only [Pi.sub_apply,Pi.pow_apply,zero_smul,add_zero,Nat.cast_ofNat]
    have he : slope r α β b x =
        (∑ i, b i*direction (r x.1) x.2 i)-
        ∑ i, (widths α β i:ℂ)*(2*position (r x.1) x.2 i*direction (r x.1) x.2 i) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    unfold profile exponent
    ring

theorem profile_shear (A r : ℝ → ℂ) (hA : ContDiff ℝ 1 A) (hr : ContDiff ℝ 1 r)
    (α β : ℝ) (b : Fin 5 → ℂ) (x : Configuration) :
    shearDerivative (profile A r α β b) x =
      slope r α β b x*profile A r α β b x+profile A r α β b x := by
  have he := (profile_line_derivative A r α β b x).unique
    (((profile_smooth A r hA hr α β b).differentiable (by norm_num) x).hasFDerivAt.hasLineDerivAt
      ((0,velocity x.2):Configuration))
  exact congrArg (fun z => z+profile A r α β b x) he.symm

#print axioms profile_smooth
#print axioms position_derivative
#print axioms profile_line_derivative
#print axioms profile_shear
end
end UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential
