/- Exact shifted Gaussian integrals and a genuine product L1 supplier for
quadratic circle-tilt mixtures. The Gaussian majorant retains arbitrary
signed linear tilt and every finite polynomial moment. -/
import UnifiedTheory.Audit.KFCausalAngularQuarticGaussianMoments
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalAngularGaussianTiltKernel
noncomputable section
open MeasureTheory Set
open KFCausalAngularQuarticGaussianMoments

def shifted (t u : ℝ) : ℝ := Real.exp (-u^2+t*u)

private theorem shifted_complete (t u : ℝ) :
    shifted t u=Real.exp (t^2/4)*gaussian (u-t/2) := by
  unfold shifted gaussian
  rw [← Real.exp_add]
  congr 1
  ring

theorem shifted_integrable (n : ℕ) (t : ℝ) :
    Integrable (fun u : ℝ => u^n*shifted t u) := by
  have hi := ((affine_integrable n (t/2) 1).comp_sub_right (t/2)).const_mul (Real.exp (t^2/4))
  apply hi.congr
  filter_upwards [] with u
  rw [shifted_complete]
  have hu : t/2+1*(u-t/2)=u := by ring
  rw [hu]
  ring

theorem shifted_zero (t : ℝ) : (∫ u : ℝ, shifted t u)=mass*Real.exp (t^2/4) := by
  simp_rw [shifted_complete]
  rw [integral_const_mul]
  have hh : (∫ u : ℝ, gaussian (u-t/2))=mass := by
    rw [show (fun u : ℝ => gaussian (u-t/2))=(fun u => gaussian (u+(-t/2))) by
      funext u; congr 1; ring,integral_add_right_eq_self]
    simpa using moment_values 0
  rw [hh]
  ring

theorem shifted_one (t : ℝ) :
    (∫ u : ℝ, u*shifted t u)=(t/2)*mass*Real.exp (t^2/4) := by
  rw [← integral_add_right_eq_self (fun u : ℝ => u*shifted t u) (t/2)]
  have he (u : ℝ) : (u+t/2)*shifted t (u+t/2)=
      Real.exp (t^2/4)*(u*gaussian u+(t/2)*gaussian u) := by
    rw [shifted_complete]
    have hu : u+t/2-t/2=u := by ring
    rw [hu]
    ring
  simp_rw [he]
  rw [integral_const_mul,integral_add (by simpa using moment_integrable 1)
    (by simpa using (moment_integrable 0).const_mul (t/2)),integral_const_mul]
  have h0 : (∫ u : ℝ, gaussian u)=mass := by simpa using moment_values 0
  have h1 : (∫ u : ℝ, u*gaussian u)=0 := by simpa using moment_values 1
  rw [h0,h1]
  ring

theorem gaussian_tilt_bound (d q u theta : ℝ) (hd : 0≤d) :
    gaussian u*Real.exp (-(q-2*Real.sqrt d*u)*Real.cos theta) ≤
      Real.exp (|q|+2*d)*Real.exp (-(1/2:ℝ)*u^2) := by
  have hc : (Real.cos theta)^2≤1 := (sq_le_one_iff_abs_le_one (Real.cos theta)).mpr (Real.abs_cos_le_one theta)
  have hq : -q*Real.cos theta≤|q| := by
    calc
      -q*Real.cos theta≤|-q*Real.cos theta| := le_abs_self _
      _ = |q| * |Real.cos theta| := by rw [abs_mul,abs_neg]
      _ ≤ |q| := by nlinarith [Real.abs_cos_le_one theta,abs_nonneg q]
  have hs : (Real.sqrt d*Real.cos theta)^2≤d := by
    rw [mul_pow,Real.sq_sqrt hd]
    nlinarith
  have ht := sq_nonneg (u-2*(Real.sqrt d*Real.cos theta))
  unfold gaussian
  rw [← Real.exp_add,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem circle_product_integrable (n : ℕ) (d q : ℝ) (hd : 0≤d)
    (f : ℝ→ℝ) (hf : Continuous f) :
    Integrable (fun p : ℝ×ℝ => p.1^n*gaussian p.1*
      Real.exp (-(q-2*Real.sqrt d*p.1)*Real.cos p.2)*f p.2)
      (volume.prod (volume.restrict (Icc 0 (2*Real.pi)))) := by
  obtain ⟨M,hM⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) (2*Real.pi))).bddAbove_image
    hf.norm.continuousOn
  let B : ℝ := Real.exp (|q|+2*d)*max 0 M
  have hB : 0≤B := by dsimp [B]; positivity
  have hi := (KFCausalPolynomialGaussianIntegrals.scalar_moment_integrable
    (1/2) (by norm_num) n).norm.mul_prod
      (show Integrable (fun _ : ℝ => B) (volume.restrict (Icc 0 (2*Real.pi))) from
        integrableOn_const isCompact_Icc.measure_ne_top)
  apply hi.mono' (by unfold gaussian; fun_prop)
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae
    (ae_restrict_mem measurableSet_Icc)] with p hp
  have hfM : |f p.2|≤max 0 M :=
    (hM ⟨p.2,hp,rfl⟩).trans (le_max_right _ _)
  have hfac := mul_le_mul (gaussian_tilt_bound d q p.1 p.2 hd) hfM
    (abs_nonneg (f p.2)) (by positivity : 0≤Real.exp (|q|+2*d)*Real.exp (-(1/2:ℝ)*p.1^2))
  have hh := mul_le_mul_of_nonneg_left hfac (abs_nonneg (p.1^n))
  simpa only [norm_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),gaussian,B,mul_assoc,
    mul_left_comm,mul_comm] using hh

#print axioms shifted_integrable
#print axioms shifted_zero
#print axioms shifted_one
#print axioms gaussian_tilt_bound
#print axioms circle_product_integrable
end
end UnifiedTheory.Audit.KFCausalAngularGaussianTiltKernel
