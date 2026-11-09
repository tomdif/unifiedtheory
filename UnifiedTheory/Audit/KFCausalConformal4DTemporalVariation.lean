import UnifiedTheory.Audit.KFCausalConformal4DBoostedMoments
import UnifiedTheory.Audit.KFCausalMinkowski4DSecondOrder

/-!
The first variation of the actual determinant density in an explicit compact
boosted-coordinate integral.  Its proof uses an exact finite polynomial, not
differentiation of a limiting theorem.  The interval correction and the density
at the operator's integration point are distinct.  No curved BDG limit, causal
diamond identification, or interchange of curvature and density limits is made.
-/

namespace UnifiedTheory.Audit.KFCausalConformal4DTemporalVariation

noncomputable section
open Real
open KFCausalConformal4DDiamondBenchmark KFCausalConformal4DBoostedMoments
open KFCausalMinkowski4DMoments KFCausalMinkowski4DSecondOrder

def density (c t : ℝ) : ℝ :=
  Real.sqrt |Matrix.det (metric (2*c) 0 ![t,0,0,0])|

def coordinateVolume (c T m A B : ℝ) : ℝ :=
  coordinateIntegral T m A B (density c)

def moment (n : ℕ) (T m A B : ℝ) : ℝ :=
  coordinateIntegral T m A B (fun x => x^n)

theorem density_polynomial (c t : ℝ) : density c t = (1+c*t^2)^4 := by
  unfold density
  rw [metric_volume_density]
  congr 1
  simp [omega]
  ring

theorem density_at_point (c : ℝ) (p : Point) :
    Real.sqrt |Matrix.det (metric (2*c) 0 p)| = density c (p 0) := by
  rw [metric_volume_density, density_polynomial]
  congr 1
  simp [omega]
  ring

theorem density_derivative (t : ℝ) : HasDerivAt (fun c => density c t) (4*t^2) 0 := by
  simp_rw [density_polynomial]
  convert (((hasDerivAt_id (0 : ℝ)).mul_const (t^2)).const_add 1).pow 4 using 1
  norm_num

theorem coordinate_volume_polynomial (c T m A B : ℝ) :
    coordinateVolume c T m A B = moment 0 T m A B+
      (4*c)*moment 2 T m A B+(6*c^2)*moment 4 T m A B+
      (4*c^3)*moment 6 T m A B+c^4*moment 8 T m A B := by
  have he : density c = (fun x => x^0+(4*c)*x^2+(6*c^2)*x^4+(4*c^3)*x^6+c^4*x^8) := by
    funext x
    rw [density_polynomial]
    ring
  unfold coordinateVolume
  rw [he]
  simp (disch := fun_prop) only [coordinate_add, coordinate_smul, moment]

theorem coordinate_volume_derivative (T m A B : ℝ) :
    HasDerivAt (fun c => coordinateVolume c T m A B) (4*moment 2 T m A B) 0 := by
  simp_rw [coordinate_volume_polynomial]
  convert ((((hasDerivAt_const (0 : ℝ) (moment 0 T m A B)).add
    ((hasDerivAt_id (0 : ℝ)).const_mul (4*moment 2 T m A B))).add
    ((hasDerivAt_pow 2 (0 : ℝ)).const_mul (6*moment 4 T m A B))).add
    ((hasDerivAt_pow 3 (0 : ℝ)).const_mul (4*moment 6 T m A B))).add
    ((hasDerivAt_pow 4 (0 : ℝ)).const_mul (moment 8 T m A B)) using 1
  · funext c
    simp only [Pi.add_apply, id_eq]
    ring
  · norm_num

theorem coordinate_volume_zero (T m A B : ℝ) :
    coordinateVolume 0 T m A B = 2*π*T^4/3 := by
  unfold coordinateVolume
  change coordinateIntegral T m A B (fun x => density 0 x) = _
  simp_rw [density_polynomial]
  simpa only [zero_mul, add_zero, one_pow] using coordinate_mass T m A B

theorem boosted_volume_derivative (T A B : ℝ) (h : A^2-B^2=1) :
    HasDerivAt (fun c => coordinateVolume c T (A*T) A B)
      ((2*π*T^4/3)*(6/5*(2*A*T)^2-2/15*(4*T^2))) 0 := by
  have he : 4*moment 2 T (A*T) A B =
      (2*π*T^4/3)*(6/5*(2*A*T)^2-2/15*(4*T^2)) := by
    unfold moment
    rw [boosted_second T A B h, coordinate_mass]
    ring
  rw [← he]
  exact coordinate_volume_derivative T (A*T) A B

/-- This is the explicit parameter integral, not a definition of a causal set. -/
def timelikeVolume (c t r : ℝ) : ℝ :=
  coordinateVolume c (sqrt (t^2-r^2)/2) (t/2)
    (t/sqrt (t^2-r^2)) (r/sqrt (t^2-r^2))

private theorem timelike_parameters (t r : ℝ) (hq : 0<t^2-r^2) :
    (t/sqrt (t^2-r^2))^2-(r/sqrt (t^2-r^2))^2=1 ∧
    (t/sqrt (t^2-r^2))*(sqrt (t^2-r^2)/2)=t/2 ∧
    4*(sqrt (t^2-r^2)/2)^2=t^2-r^2 := by
  have hs : sqrt (t^2-r^2) ≠ 0 := ne_of_gt (sqrt_pos.mpr hq)
  have hsq := sq_sqrt hq.le
  refine ⟨?_, ?_, ?_⟩
  · field_simp
    nlinarith
  · field_simp
  · nlinarith

theorem timelike_volume_zero (t r : ℝ) (hq : 0<t^2-r^2) :
    timelikeVolume 0 t r = π*(t^2-r^2)^2/24 := by
  unfold timelikeVolume
  rw [coordinate_volume_zero]
  have hsq := sq_sqrt hq.le
  calc _ = π*(sqrt (t^2-r^2)^2)^2/24 := by ring
    _ = _ := by rw [hsq]

theorem timelike_volume_derivative (t r : ℝ) (hq : 0<t^2-r^2) :
    HasDerivAt (fun c => timelikeVolume c t r)
      ((π*(t^2-r^2)^2/24)*(6/5*t^2-2/15*(t^2-r^2))) 0 := by
  obtain ⟨hl, hm, hq'⟩ := timelike_parameters t r hq
  have h := boosted_volume_derivative (sqrt (t^2-r^2)/2)
    (t/sqrt (t^2-r^2)) (r/sqrt (t^2-r^2)) hl
  rw [hm] at h
  have ht : 2*(t/sqrt (t^2-r^2))*(sqrt (t^2-r^2)/2)=t := by linarith [hm]
  rw [ht, hq'] at h
  have hv : 2*π*(sqrt (t^2-r^2)/2)^4/3=π*(t^2-r^2)^2/24 := by
    calc _ = π*(sqrt (t^2-r^2)^2)^2/24 := by ring
      _ = _ := by rw [sq_sqrt hq.le]
  rw [hv] at h
  exact h

/-- Both the integration density and the interval kernel are differentiated. -/
theorem kernel_first_variation (rho t r : ℝ) (hq : 0<t^2-r^2) :
    HasDerivAt (fun c => density c t * f4D (rho*timelikeVolume c t r))
      (4*t^2*f4D (rho*(π*(t^2-r^2)^2/24))+
        (6/5*t^2-2/15*(t^2-r^2))*(rho*(π*(t^2-r^2)^2/24))*
          deriv f4D (rho*(π*(t^2-r^2)^2/24))) 0 := by
  have hv := (timelike_volume_derivative t r hq).const_mul rho
  have hf := (f4D_hasDerivAt (rho*(π*(t^2-r^2)^2/24))).differentiableAt.hasDerivAt
  rw [← timelike_volume_zero t r hq] at hf
  have h := (density_derivative t).mul (hf.comp 0 hv)
  convert h using 1
  simp only [Function.comp_apply]
  rw [timelike_volume_zero t r hq, density_polynomial]
  ring

#print axioms density_polynomial
#print axioms density_at_point
#print axioms density_derivative
#print axioms coordinate_volume_polynomial
#print axioms coordinate_volume_derivative
#print axioms coordinate_volume_zero
#print axioms boosted_volume_derivative
#print axioms timelike_volume_zero
#print axioms timelike_volume_derivative
#print axioms kernel_first_variation

end
end UnifiedTheory.Audit.KFCausalConformal4DTemporalVariation
