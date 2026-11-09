/- A concrete interpolation to the actual complex-shifted physical
Gaussian. The density factor is included. The derivative proved here is
pointwise in configuration; no strong L2 derivative is assumed or claimed. -/
import UnifiedTheory.Audit.KFCausalImaginaryShearCoefficient
import UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalImaginaryShearInterpolation
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments (widths)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential
open UnifiedTheory.Audit.KFCausalImaginaryShearCoefficient
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalReconstruction (shearDerivative)

def timeScale (D : ℝ → ℂ) (t s : ℝ) : ℂ := Complex.exp ((t:ℂ)*D s/2)
def timeAmplitude (A D : ℝ → ℂ) (t s : ℝ) : ℂ :=
  Complex.exp (((t:ℂ)-1)*D s)*A s
def path (A D : ℝ → ℂ) (α β : ℝ) (b : Fin 5 → ℂ) (t : ℝ) : Configuration → ℂ :=
  profile (timeAmplitude A D t) (timeScale D t) α β b

theorem path_one (A D : ℝ → ℂ) (α β : ℝ) (b : Fin 5 → ℂ) :
    path A D α β b 1 = profile A (fun s => Complex.exp (D s/2)) α β b := by
  funext x
  simp [path,profile,timeAmplitude,timeScale]

theorem path_zero (A D : ℝ → ℂ) (α β : ℝ) (b : Fin 5 → ℂ) :
    path A D α β b 0 = profile (fun s => Complex.exp (-D s)*A s) (fun _ => 1) α β b := by
  funext x
  simp [path,profile,timeAmplitude,timeScale]

theorem timeScale_smooth (D : ℝ → ℂ) (hD : ContDiff ℝ 1 D) (t : ℝ) :
    ContDiff ℝ 1 (timeScale D t) :=
  ((contDiff_const.mul hD).div_const 2).cexp

theorem timeAmplitude_smooth (A D : ℝ → ℂ)
    (hA : ContDiff ℝ 1 A) (hD : ContDiff ℝ 1 D) (t : ℝ) :
    ContDiff ℝ 1 (timeAmplitude A D t) :=
  (contDiff_const.mul hD).cexp.mul hA

theorem path_smooth (A D : ℝ → ℂ) (hA : ContDiff ℝ 1 A) (hD : ContDiff ℝ 1 D)
    (α β : ℝ) (b : Fin 5 → ℂ) (t : ℝ) : ContDiff ℝ 1 (path A D α β b t) :=
  profile_smooth _ _ (timeAmplitude_smooth A D hA hD t) (timeScale_smooth D hD t) α β b

theorem position_time_derivative (D : ℝ → ℂ) (s t : ℝ) (q : Transverse) (i : Fin 5) :
    HasDerivAt (fun u : ℝ => position (timeScale D u s) q i)
      (D s*direction (timeScale D t s) q i) t := by
  have hr : HasDerivAt (fun u : ℝ => timeScale D u s) (D s/2*timeScale D t s) t := by
    convert (((hasDerivAt_id t).ofReal_comp.mul_const (D s)).div_const 2).cexp using 1
    simp [timeScale,mul_comm]
  by_cases hi : i=4
  · subst i
    have hd := (((hr.sub_const 1).const_mul 2).mul_const ((q 2:ℂ)+(q 3:ℂ))).const_add (q 4:ℂ)
    convert hd using 1
    simp [direction]
    ring
  · convert hr.mul_const (q i:ℂ) using 1
    · funext u; simp only [position,if_neg hi]
    · simp only [direction,if_neg hi]
      ring

theorem path_time_derivative (A D : ℝ → ℂ) (α β : ℝ) (b : Fin 5 → ℂ)
    (t : ℝ) (x : Configuration) :
    HasDerivAt (fun u : ℝ => path A D α β b u x)
      (D x.1*(slope (timeScale D t) α β b x+1)*path A D α β b t x) t := by
  have hl := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 5))) =>
      (position_time_derivative D x.1 t x.2 i).const_mul (b i))
  have hq := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 5))) =>
      ((position_time_derivative D x.1 t x.2 i).pow 2).const_mul (widths α β i:ℂ))
  have ha : HasDerivAt (fun u : ℝ => timeAmplitude A D u x.1)
      (D x.1*timeAmplitude A D t x.1) t := by
    convert (((hasDerivAt_id t).ofReal_comp.sub_const 1).mul_const (D x.1)).cexp.mul_const (A x.1) using 1
    simp [timeAmplitude]
    ring
  have he : (∑ i, b i*(D x.1*direction (timeScale D t x.1) x.2 i))-
      (∑ i, (widths α β i:ℂ)*(2*position (timeScale D t x.1) x.2 i*
        (D x.1*direction (timeScale D t x.1) x.2 i))) =
      D x.1*slope (timeScale D t) α β b x := by
    rw [KFCausalRelativeGaussianDifferential.slope,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  convert ha.mul (hl.sub hq).cexp using 1
  simp only [Nat.cast_ofNat,show 2-1=1 from rfl,pow_one,Pi.sub_apply,Pi.pow_apply,he]
  unfold path profile exponent
  ring

theorem path_shear_derivative (A D : ℝ → ℂ) (hA : ContDiff ℝ 1 A) (hD : ContDiff ℝ 1 D)
    (α β : ℝ) (b : Fin 5 → ℂ) (t : ℝ) (x : Configuration) :
    HasDerivAt (fun u : ℝ => path A D α β b u x)
      (D x.1*shearDerivative (path A D α β b t) x) t := by
  have hs := profile_shear _ _ (timeAmplitude_smooth A D hA hD t)
    (timeScale_smooth D hD t) α β b x
  change shearDerivative (path A D α β b t) x = _ at hs
  rw [hs,mul_add]
  convert path_time_derivative A D α β b t x using 1
  unfold path
  ring

def actualPath (ε a α β p h : ℝ) (b : Fin 5 → ℂ) (t : ℝ) : Configuration → ℂ :=
  path (KFCausalShiftedGaussianPhysicalProfile.clockAmplitude ε a p (-h/2))
    (displacement ε h) α β b t

theorem actualPath_one (ε a α β p h : ℝ) (b : Fin 5 → ℂ) :
    actualPath ε a α β p h b 1 =
      profile (KFCausalShiftedGaussianPhysicalProfile.clockAmplitude ε a p (-h/2))
        (KFCausalClockFloorRelativeShift.scale ε (-h/2)) α β b :=
  path_one _ _ _ _ _

theorem actualPath_one_gaussian (ε a α β p h : ℝ) (b : Fin 5 → ℂ)
    (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hb : |h| ≤ 2*Real.pi*ε/3) :
    KFCausalClockFloorCoherentSpectral.gaussianState ε a α β p b (-h/2)
      hε ha hα hβ hw (half_shift_bound ε h hb) =ᵐ[volume]
        actualPath ε a α β p h b 1 := by
  rw [actualPath_one]
  exact KFCausalShiftedGaussianPhysicalProfile.gaussianState_profile _ _ _ _ _ _ _
    hε ha hα hβ hw (half_shift_bound ε h hb)

theorem actualPath_generator_derivative (ε a α β p h : ℝ) (b : Fin 5 → ℂ)
    (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
    (t : ℝ) (x : Configuration) :
    HasDerivAt (fun u : ℝ => actualPath ε a α β p h b u x)
      (coefficient ε h x.1 * (-(h:ℂ)*Complex.I*
        shearDerivative (actualPath ε a α β p h b t) x)) t := by
  rw [← mul_assoc,coefficient_generator_identity ε h x.1 hh]
  exact path_shear_derivative _ _
    (KFCausalShiftedGaussianPhysicalProfile.clockAmplitude_smooth ε a p (-h/2)
      hε (half_shift_bound ε h hb)) (displacement_smooth ε h hε hb) α β b t x

#print axioms path_one
#print axioms path_zero
#print axioms timeScale_smooth
#print axioms timeAmplitude_smooth
#print axioms path_smooth
#print axioms position_time_derivative
#print axioms path_time_derivative
#print axioms path_shear_derivative
#print axioms actualPath_one
#print axioms actualPath_one_gaussian
#print axioms actualPath_generator_derivative
end
end UnifiedTheory.Audit.KFCausalImaginaryShearInterpolation
