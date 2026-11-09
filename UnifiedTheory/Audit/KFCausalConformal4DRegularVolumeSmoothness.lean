/- Joint regularity of the fixed-box conformal volume and its actual parameter
derivative. The polynomial identity removes the apparent null denominators. -/
import UnifiedTheory.Audit.KFCausalConformal4DRegularVolume
import UnifiedTheory.Audit.KFCausalMinkowski4DEulerIBP

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalConformal4DRegularVolumeSmoothness
noncomputable section
open Real MeasureTheory
open KFCausalConformal4DBoostedMoments KFCausalConformal4DTemporalVariation
open KFCausalConformal4DRegularVolume KFCausalMinkowski4DMoments

theorem moment_continuous (n : ℕ) :
    Continuous (fun p : ℝ × ℝ => moment n 1 (p.1/2) (p.1/2) (p.2/2)) := by
  have hi : Continuous (fun p : ((ℝ × ℝ) × ℝ) × ℝ =>
      ∫ mu in (-1:ℝ)..1, pair 1 (p.1.1.1/2) (p.1.1.1/2) (p.1.1.2/2)
        (fun x => x^n) p.1.2 p.2 mu) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    unfold pair time
    fun_prop
  have hm : Continuous (fun p : (ℝ × ℝ) × ℝ =>
      ∫ v in (0:ℝ)..1, ∫ mu in (-1:ℝ)..1,
        pair 1 (p.1.1/2) (p.1.1/2) (p.1.2/2) (fun x => x^n) p.2 v mu) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hi 0 1
  have ho : Continuous (fun p : ℝ × ℝ => ∫ u in (0:ℝ)..1, ∫ v in (0:ℝ)..1,
      ∫ mu in (-1:ℝ)..1, pair 1 (p.1/2) (p.1/2) (p.2/2) (fun x => x^n) u v mu) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hm 0 1
  exact continuous_const.mul ho

def volumeSlope (c t r : ℝ) : ℝ :=
  ((t^2-r^2)^2/16) * (4*moment 2 1 (t/2) (t/2) (r/2) +
    (12*c)*moment 4 1 (t/2) (t/2) (r/2) +
    (12*c^2)*moment 6 1 (t/2) (t/2) (r/2) +
    (4*c^3)*moment 8 1 (t/2) (t/2) (r/2))

theorem regular_volume_continuous :
    Continuous (fun p : ℝ × (ℝ × ℝ) => regularVolume p.1 p.2.1 p.2.2) := by
  simp_rw [regularVolume, coordinate_volume_polynomial]
  have hm (n : ℕ) : Continuous (fun p : ℝ × (ℝ × ℝ) =>
      moment n 1 (p.2.1/2) (p.2.1/2) (p.2.2/2)) :=
    (moment_continuous n).comp continuous_snd
  fun_prop

theorem volume_slope_continuous :
    Continuous (fun p : ℝ × (ℝ × ℝ) => volumeSlope p.1 p.2.1 p.2.2) := by
  unfold volumeSlope
  have hm (n : ℕ) : Continuous (fun p : ℝ × (ℝ × ℝ) =>
      moment n 1 (p.2.1/2) (p.2.1/2) (p.2.2/2)) :=
    (moment_continuous n).comp continuous_snd
  fun_prop

theorem regular_volume_hasDerivAt (c t r : ℝ) :
    HasDerivAt (fun d => regularVolume d t r) (volumeSlope c t r) c := by
  simp_rw [regularVolume, coordinate_volume_polynomial]
  have hd := ((((hasDerivAt_const c (moment 0 1 (t/2) (t/2) (r/2))).add
    ((hasDerivAt_id c).const_mul (4*moment 2 1 (t/2) (t/2) (r/2)))).add
    ((hasDerivAt_pow 2 c).const_mul (6*moment 4 1 (t/2) (t/2) (r/2)))).add
    ((hasDerivAt_pow 3 c).const_mul (4*moment 6 1 (t/2) (t/2) (r/2)))).add
    ((hasDerivAt_pow 4 c).const_mul (moment 8 1 (t/2) (t/2) (r/2)))
  convert hd.const_mul ((t^2-r^2)^2/16) using 1
  · funext d
    simp only [Pi.add_apply, id_eq]
    ring
  · dsimp [volumeSlope]
    ring

def kernel (rho c t r : ℝ) : ℝ := density c t * f4D (rho*regularVolume c t r)

def kernelSlope (rho c t r : ℝ) : ℝ :=
  (4*(1+c*t^2)^3*t^2)*f4D (rho*regularVolume c t r) +
    density c t * (KFCausalMinkowski4DEulerIBP.fd (rho*regularVolume c t r) *
      (rho*volumeSlope c t r))

theorem kernel_hasDerivAt (rho c t r : ℝ) :
    HasDerivAt (fun d => kernel rho d t r) (kernelSlope rho c t r) c := by
  have hd : HasDerivAt (fun d => density d t) (4*(1+c*t^2)^3*t^2) c := by
    simp_rw [density_polynomial]
    convert (((hasDerivAt_id c).mul_const (t^2)).const_add 1).pow 4 using 1
    dsimp only [id_eq]
    ring
  exact hd.mul ((KFCausalMinkowski4DSecondOrder.f4D_hasDerivAt _).comp c
    ((regular_volume_hasDerivAt c t r).const_mul rho))

theorem kernel_continuous (rho : ℝ) :
    Continuous (fun p : ℝ × (ℝ × ℝ) => kernel rho p.1 p.2.1 p.2.2) := by
  unfold kernel
  simp_rw [density_polynomial]
  have hv : Continuous (fun p : ℝ × (ℝ × ℝ) => rho*regularVolume p.1 p.2.1 p.2.2) :=
    continuous_const.mul regular_volume_continuous
  have hf : Continuous f4D := by unfold f4D; fun_prop
  apply Continuous.mul
  · fun_prop
  · exact hf.comp hv

theorem kernel_slope_continuous (rho : ℝ) :
    Continuous (fun p : ℝ × (ℝ × ℝ) => kernelSlope rho p.1 p.2.1 p.2.2) := by
  unfold kernelSlope
  simp_rw [density_polynomial]
  have hv : Continuous (fun p : ℝ × (ℝ × ℝ) => rho*regularVolume p.1 p.2.1 p.2.2) :=
    continuous_const.mul regular_volume_continuous
  have hs : Continuous (fun p : ℝ × (ℝ × ℝ) => rho*volumeSlope p.1 p.2.1 p.2.2) :=
    continuous_const.mul volume_slope_continuous
  have hf : Continuous f4D := by unfold f4D; fun_prop
  have hfd : Continuous KFCausalMinkowski4DEulerIBP.fd := by
    unfold KFCausalMinkowski4DEulerIBP.fd
    fun_prop
  apply Continuous.add
  · apply Continuous.mul
    · fun_prop
    · exact hf.comp hv
  · apply Continuous.mul
    · fun_prop
    · exact (hfd.comp hv).mul hs

theorem kernel_slope_zero (rho t r : ℝ) :
    kernelSlope rho 0 t r =
      4*t^2*f4D (rho*(π*(t^2-r^2)^2/24)) +
      (6/5*t^2-2/15*(t^2-r^2))*(rho*(π*(t^2-r^2)^2/24))*
        deriv f4D (rho*(π*(t^2-r^2)^2/24)) := by
  have hs := (regular_volume_hasDerivAt 0 t r).unique (regular_volume_derivative t r)
  unfold kernelSlope
  rw [hs, regular_volume_zero, density_polynomial]
  rw [(KFCausalMinkowski4DSecondOrder.f4D_hasDerivAt _).deriv]
  unfold KFCausalMinkowski4DEulerIBP.fd
  ring

#print axioms moment_continuous
#print axioms regular_volume_continuous
#print axioms volume_slope_continuous
#print axioms regular_volume_hasDerivAt
#print axioms kernel_hasDerivAt
#print axioms kernel_continuous
#print axioms kernel_slope_continuous
#print axioms kernel_slope_zero
end
end UnifiedTheory.Audit.KFCausalConformal4DRegularVolumeSmoothness
