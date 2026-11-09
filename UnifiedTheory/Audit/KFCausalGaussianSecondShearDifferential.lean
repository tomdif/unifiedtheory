/- Exact first and second shear differentials of the interpolation.
Both spatial shear differentiation and interpolation differentiation
produce the same explicit fourth-degree Gaussian expression. These are
pointwise identities; the strong L2 conclusions require separate bounds. -/
import UnifiedTheory.Audit.KFCausalGaussianShearSlopeBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalGaussianSecondShearDifferential
noncomputable section
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse velocity)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments (widths)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential
open UnifiedTheory.Audit.KFCausalImaginaryShearInterpolation
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalReconstruction (shearDerivative)

def curvature (r : ℝ → ℂ) (α β : ℝ) (b : Fin 5 → ℂ) (x : Configuration) : ℂ :=
  KFCausalRelativeGaussianDifferential.slope r α β b x/2-
    2*∑ i, (widths α β i:ℂ)*(direction (r x.1) x.2 i)^2

def first (A r : ℝ → ℂ) (α β : ℝ) (b : Fin 5 → ℂ) (x : Configuration) : ℂ :=
  (KFCausalRelativeGaussianDifferential.slope r α β b x+1)*profile A r α β b x

def second (A r : ℝ → ℂ) (α β : ℝ) (b : Fin 5 → ℂ) (x : Configuration) : ℂ :=
  (curvature r α β b x+(KFCausalRelativeGaussianDifferential.slope r α β b x+1)^2)*profile A r α β b x

theorem direction_line_derivative (r : ℂ) (q : Transverse) (i : Fin 5) :
    HasDerivAt (fun t : ℝ => direction r (q+t • velocity q) i) (direction r q i/2) 0 := by
  have hl (j : Fin 5) : HasDerivAt (fun t : ℝ => (q j+t*velocity q j:ℝ)) (velocity q j) 0 := by
    simpa only [id_eq,one_mul] using ((hasDerivAt_id (0:ℝ)).mul_const (velocity q j)).const_add (q j)
  by_cases hi : i=4
  · subst i
    convert ((hl 2).ofReal_comp.add (hl 3).ofReal_comp).const_mul r using 1
    simp [direction,velocity]
    ring
  · convert ((hl i).ofReal_comp.const_mul r).div_const 2 using 1
    · funext t; simp only [direction,if_neg hi,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    · simp only [direction,if_neg hi,velocity,Complex.ofReal_div,Complex.ofReal_ofNat]
      ring

theorem direction_time_derivative (D : ℝ → ℂ) (s t : ℝ) (q : Transverse) (i : Fin 5) :
    HasDerivAt (fun u : ℝ => direction (timeScale D u s) q i)
      (D s*direction (timeScale D t s) q i/2) t := by
  have hr : HasDerivAt (fun u : ℝ => timeScale D u s) (D s/2*timeScale D t s) t := by
    convert (((hasDerivAt_id t).ofReal_comp.mul_const (D s)).div_const 2).cexp using 1
    simp [timeScale,mul_comm]
  by_cases hi : i=4
  · subst i
    convert hr.mul_const ((q 2:ℂ)+(q 3:ℂ)) using 1
    simp [direction]
    ring
  · convert (hr.mul_const (q i:ℂ)).div_const 2 using 1
    · funext u; simp only [direction,if_neg hi]
    · simp only [direction,if_neg hi]
      ring

theorem polynomial_derivative (p v : ℝ → Fin 5 → ℂ) (w b : Fin 5 → ℂ) (d : ℂ) (t : ℝ)
    (hp : ∀ i, HasDerivAt (fun u => p u i) (d*v t i) t)
    (hv : ∀ i, HasDerivAt (fun u => v u i) (d*v t i/2) t) :
    HasDerivAt (fun u => ∑ i, (b i-2*w i*p u i)*v u i)
      (d*((∑ i, (b i-2*w i*p t i)*v t i)/2-2*∑ i, w i*(v t i)^2)) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 5))) =>
      ((hasDerivAt_const t (b i)).sub ((hp i).const_mul (2*w i))).mul (hv i))
  convert hd using 1
  simp only [Finset.sum_div,Finset.mul_sum,Pi.sub_apply]
  rw [← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem slope_line_derivative (r : ℝ → ℂ) (α β : ℝ) (b : Fin 5 → ℂ) (x : Configuration) :
    HasLineDerivAt ℝ (KFCausalRelativeGaussianDifferential.slope r α β b)
      (curvature r α β b x) x ((0,velocity x.2):Configuration) := by
  have hd := polynomial_derivative
    (fun t i => position (r x.1) (x.2+t • velocity x.2) i)
    (fun t i => direction (r x.1) (x.2+t • velocity x.2) i)
    (fun i => (widths α β i:ℂ)) b 1 0
    (fun i => by simpa using position_derivative (r x.1) x.2 i)
    (fun i => by simpa using direction_line_derivative (r x.1) x.2 i)
  change HasDerivAt (fun t : ℝ => KFCausalRelativeGaussianDifferential.slope r α β b
    (x+t • (0,velocity x.2))) _ 0
  simpa [curvature,KFCausalRelativeGaussianDifferential.slope] using hd

theorem slope_time_derivative (D : ℝ → ℂ) (α β : ℝ) (b : Fin 5 → ℂ) (t : ℝ) (x : Configuration) :
    HasDerivAt (fun u : ℝ => KFCausalRelativeGaussianDifferential.slope (timeScale D u) α β b x)
      (D x.1*curvature (timeScale D t) α β b x) t :=
  polynomial_derivative (fun u i => position (timeScale D u x.1) x.2 i)
    (fun u i => direction (timeScale D u x.1) x.2 i) (fun i => (widths α β i:ℂ)) b (D x.1) t
    (position_time_derivative D x.1 t x.2) (direction_time_derivative D x.1 t x.2)

theorem slope_smooth (r : ℝ → ℂ) (hr : ContDiff ℝ 1 r) (α β : ℝ) (b : Fin 5 → ℂ) :
    ContDiff ℝ 1 (KFCausalRelativeGaussianDifferential.slope r α β b) := by
  have hc (i : Fin 5) : ContDiff ℝ 1 (fun x : Configuration => (x.2 i:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (by fun_prop)
  have hrc : ContDiff ℝ 1 (fun x : Configuration => r x.1) := hr.comp contDiff_fst
  have hp (i : Fin 5) : ContDiff ℝ 1 (fun x : Configuration => position (r x.1) x.2 i) := by
    unfold position
    split_ifs
    · exact (hc 4).add ((contDiff_const.mul (hrc.sub contDiff_const)).mul ((hc 2).add (hc 3)))
    · exact hrc.mul (hc i)
  have hv (i : Fin 5) : ContDiff ℝ 1 (fun x : Configuration => direction (r x.1) x.2 i) := by
    unfold direction
    split_ifs
    · exact hrc.mul ((hc 2).add (hc 3))
    · exact (hrc.mul (hc i)).div_const 2
  unfold KFCausalRelativeGaussianDifferential.slope
  apply ContDiff.sum
  intro i _
  exact (contDiff_const.sub (contDiff_const.mul (hp i))).mul (hv i)

theorem first_smooth (A r : ℝ → ℂ) (hA : ContDiff ℝ 1 A) (hr : ContDiff ℝ 1 r)
    (α β : ℝ) (b : Fin 5 → ℂ) : ContDiff ℝ 1 (first A r α β b) :=
  ((slope_smooth r hr α β b).add contDiff_const).mul (profile_smooth A r hA hr α β b)

theorem first_eq_shear (A r : ℝ → ℂ) (hA : ContDiff ℝ 1 A) (hr : ContDiff ℝ 1 r)
    (α β : ℝ) (b : Fin 5 → ℂ) : first A r α β b = shearDerivative (profile A r α β b) := by
  funext x
  rw [profile_shear A r hA hr α β b x]
  unfold first
  ring

theorem first_shear (A r : ℝ → ℂ) (hA : ContDiff ℝ 1 A) (hr : ContDiff ℝ 1 r)
    (α β : ℝ) (b : Fin 5 → ℂ) : shearDerivative (first A r α β b) = second A r α β b := by
  funext x
  have hd := ((slope_line_derivative r α β b x).add_const 1).mul (profile_line_derivative A r α β b x)
  have he := hd.unique (((first_smooth A r hA hr α β b).differentiable (by norm_num) x).hasFDerivAt.hasLineDerivAt
    ((0,velocity x.2):Configuration))
  change _ = fderiv ℝ (first A r α β b) x ((0,velocity x.2):Configuration) at he
  rw [shearDerivative,← he]
  simp only [zero_smul,add_zero]
  unfold first second
  ring

theorem first_time_derivative (A D : ℝ → ℂ) (α β : ℝ) (b : Fin 5 → ℂ) (t : ℝ) (x : Configuration) :
    HasDerivAt (fun u : ℝ => first (timeAmplitude A D u) (timeScale D u) α β b x)
      (D x.1*second (timeAmplitude A D t) (timeScale D t) α β b x) t := by
  convert ((slope_time_derivative D α β b t x).add_const 1).mul
    (path_time_derivative A D α β b t x) using 1
  unfold second path
  ring

#print axioms direction_line_derivative
#print axioms direction_time_derivative
#print axioms polynomial_derivative
#print axioms slope_line_derivative
#print axioms slope_time_derivative
#print axioms slope_smooth
#print axioms first_smooth
#print axioms first_eq_shear
#print axioms first_shear
#print axioms first_time_derivative
end
end UnifiedTheory.Audit.KFCausalGaussianSecondShearDifferential
