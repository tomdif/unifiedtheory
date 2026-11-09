/- A second genuine Gaussian mixture adds the quadratic circle tilt.
The mixed base tilt is evaluated using the first Gaussian moment, so
neither an interchange of derivatives nor an unproved tilt identity is used. -/
import UnifiedTheory.Audit.KFCausalAngularGaussianTiltKernel
import UnifiedTheory.Audit.KFCausalAngularMassGaussianSmoothing

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalAngularMassQuadraticTilt
noncomputable section
open MeasureTheory Set
open KFCausalAngularQuarticGaussianMoments (gaussian mass mass_positive)
open KFCausalAngularMassGaussianSmoothing
open KFCausalAngularGaussianTiltKernel (shifted shifted_zero shifted_one)

def energy (sigma d q mu l : ℝ) : ℝ :=
  ∫ theta in 0..(2*Real.pi), Real.exp (d*(Real.cos theta)^2-q*Real.cos theta)*
    weight sigma (mu+l*Real.cos theta)
def fieldSlope (sigma d q mu l : ℝ) : ℝ :=
  ∫ theta in 0..(2*Real.pi), Real.exp (d*(Real.cos theta)^2-q*Real.cos theta)*
    Real.cos theta*weightSlope sigma (mu+l*Real.cos theta)
def tilt (sigma d q mu l : ℝ) : ℝ :=
  ∫ theta in 0..(2*Real.pi), (2*d*(Real.cos theta)^2-q*Real.cos theta)*
    Real.exp (d*(Real.cos theta)^2-q*Real.cos theta)*weight sigma (mu+l*Real.cos theta)
def defect (sigma d q mu l : ℝ) : ℝ :=
  2*tilt sigma d q mu l-l*fieldSlope sigma d q mu l

private def plain (z : ℝ) (f : ℝ→ℝ) : ℝ :=
  ∫ theta in 0..(2*Real.pi), Real.exp (-z*Real.cos theta)*f theta

private theorem compact_integral_eq (f : ℝ→ℝ) :
    (∫ theta in Icc 0 (2*Real.pi), f theta)=∫ theta in 0..(2*Real.pi), f theta := by
  rw [integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le (by positivity : (0:ℝ)≤2*Real.pi)]

private theorem plain_outer_integrable (n : ℕ) (d q : ℝ) (hd : 0≤d)
    (f : ℝ→ℝ) (hf : Continuous f) :
    Integrable (fun u : ℝ => u^n*gaussian u*plain (q-2*Real.sqrt d*u) f) := by
  have hi := (KFCausalAngularGaussianTiltKernel.circle_product_integrable n d q hd f hf).integral_prod_left
  have he (u : ℝ) : (∫ theta in Icc 0 (2*Real.pi), u^n*gaussian u*
      Real.exp (-(q-2*Real.sqrt d*u)*Real.cos theta)*f theta)=
      u^n*gaussian u*plain (q-2*Real.sqrt d*u) f := by
    simp only [mul_assoc,integral_const_mul,compact_integral_eq,plain]
  simpa only [he] using hi

private theorem plain_swap (n : ℕ) (d q : ℝ) (hd : 0≤d)
    (f : ℝ→ℝ) (hf : Continuous f) :
    (∫ u : ℝ, u^n*gaussian u*plain (q-2*Real.sqrt d*u) f)=
      ∫ theta in 0..(2*Real.pi), f theta*(∫ u : ℝ, u^n*gaussian u*
        Real.exp (-(q-2*Real.sqrt d*u)*Real.cos theta)) := by
  have hi := KFCausalAngularGaussianTiltKernel.circle_product_integrable n d q hd f hf
  have hh := integral_integral_swap
    (f := fun u theta : ℝ => u^n*gaussian u*Real.exp (-(q-2*Real.sqrt d*u)*Real.cos theta)*f theta) hi
  have he1 (u : ℝ) : (∫ theta in Icc 0 (2*Real.pi), u^n*gaussian u*
      Real.exp (-(q-2*Real.sqrt d*u)*Real.cos theta)*f theta)=
      u^n*gaussian u*plain (q-2*Real.sqrt d*u) f := by
    simp only [mul_assoc,integral_const_mul,compact_integral_eq,plain]
  have he2 (theta : ℝ) : (∫ u : ℝ, u^n*gaussian u*
      Real.exp (-(q-2*Real.sqrt d*u)*Real.cos theta)*f theta)=
      f theta*(∫ u : ℝ, u^n*gaussian u*Real.exp (-(q-2*Real.sqrt d*u)*Real.cos theta)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with u
    ring
  simpa only [he1,he2,compact_integral_eq] using hh

private theorem point_zero (d q theta : ℝ) (hd : 0≤d) :
    (∫ u : ℝ, gaussian u*Real.exp (-(q-2*Real.sqrt d*u)*Real.cos theta))=
      mass*Real.exp (d*(Real.cos theta)^2-q*Real.cos theta) := by
  have he (u : ℝ) : gaussian u*Real.exp (-(q-2*Real.sqrt d*u)*Real.cos theta)=
      Real.exp (-q*Real.cos theta)*shifted (2*Real.sqrt d*Real.cos theta) u := by
    unfold gaussian shifted
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [integral_const_mul,shifted_zero]
  have hs : (2*Real.sqrt d*Real.cos theta)^2/4=d*(Real.cos theta)^2 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt hd]
    ring
  rw [hs]
  calc
    _ = mass*(Real.exp (-q*Real.cos theta)*Real.exp (d*(Real.cos theta)^2)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

private theorem point_one (d q theta : ℝ) (hd : 0≤d) :
    (∫ u : ℝ, u*gaussian u*Real.exp (-(q-2*Real.sqrt d*u)*Real.cos theta))=
      Real.sqrt d*Real.cos theta*mass*Real.exp (d*(Real.cos theta)^2-q*Real.cos theta) := by
  have he (u : ℝ) : u*gaussian u*Real.exp (-(q-2*Real.sqrt d*u)*Real.cos theta)=
      Real.exp (-q*Real.cos theta)*(u*shifted (2*Real.sqrt d*Real.cos theta) u) := by
    have hx : gaussian u*Real.exp (-(q-2*Real.sqrt d*u)*Real.cos theta)=
        Real.exp (-q*Real.cos theta)*shifted (2*Real.sqrt d*Real.cos theta) u := by
      unfold gaussian shifted
      rw [← Real.exp_add,← Real.exp_add]
      congr 1
      ring
    calc
      _ = u*(gaussian u*Real.exp (-(q-2*Real.sqrt d*u)*Real.cos theta)) := by ring
      _ = _ := by rw [hx]; ring
  simp_rw [he]
  rw [integral_const_mul,shifted_one]
  have hs : (2*Real.sqrt d*Real.cos theta)^2/4=d*(Real.cos theta)^2 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt hd]
    ring
  rw [hs]
  calc
    _ = (Real.sqrt d*Real.cos theta*mass)*
        (Real.exp (-q*Real.cos theta)*Real.exp (d*(Real.cos theta)^2)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

private theorem plain_zero (d q : ℝ) (hd : 0≤d) (f : ℝ→ℝ) (hf : Continuous f) :
    (∫ u : ℝ, gaussian u*plain (q-2*Real.sqrt d*u) f)=
      mass*∫ theta in 0..(2*Real.pi), Real.exp (d*(Real.cos theta)^2-q*Real.cos theta)*f theta := by
  have hh := plain_swap 0 d q hd f hf
  simp only [pow_zero,one_mul] at hh
  rw [hh]
  simp_rw [point_zero d q _ hd]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro theta _
  ring

private theorem plain_one (d q : ℝ) (hd : 0≤d) (f : ℝ→ℝ) (hf : Continuous f) :
    (∫ u : ℝ, u*gaussian u*plain (q-2*Real.sqrt d*u) f)=
      mass*∫ theta in 0..(2*Real.pi), Real.sqrt d*Real.cos theta*
        Real.exp (d*(Real.cos theta)^2-q*Real.cos theta)*f theta := by
  have hh := plain_swap 1 d q hd f hf
  simp only [pow_one] at hh
  rw [hh]
  simp_rw [point_one d q _ hd]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro theta _
  ring

private theorem smooth_field_plain (sigma z mu l : ℝ) :
    smoothFieldSlope sigma z mu l=plain z
      (fun theta => Real.cos theta*weightSlope sigma (mu+l*Real.cos theta)) := by
  apply intervalIntegral.integral_congr
  intro theta _
  ring

private theorem smooth_tilt_plain (sigma z mu l : ℝ) :
    smoothTilt sigma z mu l=(-z)*plain z
      (fun theta => Real.cos theta*weight sigma (mu+l*Real.cos theta)) := by
  unfold smoothTilt plain
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro theta _
  ring

theorem mixture_integrable (sigma d q mu l : ℝ) (hd : 0≤d) :
    Integrable (fun u : ℝ => gaussian u*smoothEnergy sigma (q-2*Real.sqrt d*u) mu l) ∧
    Integrable (fun u : ℝ => gaussian u*smoothFieldSlope sigma (q-2*Real.sqrt d*u) mu l) ∧
    Integrable (fun u : ℝ => gaussian u*smoothTilt sigma (q-2*Real.sqrt d*u) mu l) := by
  have h0 (f : ℝ→ℝ) (hf : Continuous f) := plain_outer_integrable 0 d q hd f hf
  have h1 (f : ℝ→ℝ) (hf : Continuous f) := plain_outer_integrable 1 d q hd f hf
  constructor
  · simpa only [pow_zero,one_mul,plain,smoothEnergy] using
      h0 (fun theta => weight sigma (mu+l*Real.cos theta)) (by unfold weight; fun_prop)
  constructor
  · simp_rw [smooth_field_plain]
    simpa only [pow_zero,one_mul] using
      h0 (fun theta => Real.cos theta*weightSlope sigma (mu+l*Real.cos theta)) (by unfold weightSlope; fun_prop)
  · let f : ℝ→ℝ := fun theta => Real.cos theta*weight sigma (mu+l*Real.cos theta)
    have hf : Continuous f := by dsimp [f,weight]; fun_prop
    have hi0 : Integrable (fun u : ℝ => gaussian u*plain (q-2*Real.sqrt d*u) f) :=
      by simpa only [pow_zero,one_mul] using h0 f hf
    have hi1 : Integrable (fun u : ℝ => u*gaussian u*plain (q-2*Real.sqrt d*u) f) :=
      by simpa only [pow_one] using h1 f hf
    apply ((hi0.const_mul (-q)).add (hi1.const_mul (2*Real.sqrt d))).congr
    filter_upwards [] with u
    rw [smooth_tilt_plain]
    dsimp [f]
    ring

theorem energy_mixture (sigma d q mu l : ℝ) (hd : 0≤d) :
    (∫ u : ℝ, gaussian u*smoothEnergy sigma (q-2*Real.sqrt d*u) mu l)=
      mass*energy sigma d q mu l :=
  plain_zero d q hd (fun theta => weight sigma (mu+l*Real.cos theta)) (by unfold weight; fun_prop)

theorem field_mixture (sigma d q mu l : ℝ) (hd : 0≤d) :
    (∫ u : ℝ, gaussian u*smoothFieldSlope sigma (q-2*Real.sqrt d*u) mu l)=
      mass*fieldSlope sigma d q mu l := by
  simp_rw [smooth_field_plain]
  rw [plain_zero d q hd _ (by unfold weightSlope; fun_prop)]
  congr 1
  apply intervalIntegral.integral_congr
  intro theta _
  ring

theorem tilt_mixture (sigma d q mu l : ℝ) (hd : 0≤d) :
    (∫ u : ℝ, gaussian u*smoothTilt sigma (q-2*Real.sqrt d*u) mu l)=
      mass*tilt sigma d q mu l := by
  let f : ℝ→ℝ := fun theta => Real.cos theta*weight sigma (mu+l*Real.cos theta)
  have hf : Continuous f := by dsimp [f,weight]; fun_prop
  have hi0 : Integrable (fun u : ℝ => gaussian u*plain (q-2*Real.sqrt d*u) f) := by
    simpa only [pow_zero,one_mul] using plain_outer_integrable 0 d q hd f hf
  have hi1 : Integrable (fun u : ℝ => u*gaussian u*plain (q-2*Real.sqrt d*u) f) := by
    simpa only [pow_one] using plain_outer_integrable 1 d q hd f hf
  have he (u : ℝ) : gaussian u*smoothTilt sigma (q-2*Real.sqrt d*u) mu l=
      (-q)*(gaussian u*plain (q-2*Real.sqrt d*u) f)+
      (2*Real.sqrt d)*(u*gaussian u*plain (q-2*Real.sqrt d*u) f) := by
    rw [smooth_tilt_plain]
    dsimp [f]
    ring
  simp_rw [he]
  rw [integral_add (hi0.const_mul (-q)) (hi1.const_mul (2*Real.sqrt d))]
  simp only [integral_const_mul,plain_zero d q hd f hf,plain_one d q hd f hf]
  have hA : IntervalIntegrable (fun theta => Real.exp (d*(Real.cos theta)^2-q*Real.cos theta)*f theta)
      volume 0 (2*Real.pi) := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun theta => Real.sqrt d*Real.cos theta*
      Real.exp (d*(Real.cos theta)^2-q*Real.cos theta)*f theta)
      volume 0 (2*Real.pi) := (by fun_prop : Continuous _).intervalIntegrable _ _
  calc
    _ = mass*((-q)*(∫ theta in 0..(2*Real.pi), Real.exp (d*(Real.cos theta)^2-q*Real.cos theta)*f theta)+
      (2*Real.sqrt d)*(∫ theta in 0..(2*Real.pi), Real.sqrt d*Real.cos theta*
        Real.exp (d*(Real.cos theta)^2-q*Real.cos theta)*f theta)) := by ring
    _ = _ := by
      congr 1
      rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add (hA.const_mul (-q)) (hB.const_mul (2*Real.sqrt d))]
      apply intervalIntegral.integral_congr
      intro theta _
      dsimp [f]
      ring_nf
      rw [Real.sq_sqrt hd]
      ring

theorem defect_mixture_integrable (sigma d q mu l : ℝ) (hd : 0≤d) :
    Integrable (fun u : ℝ => gaussian u*smoothDefect sigma (q-2*Real.sqrt d*u) mu l) := by
  have hi := mixture_integrable sigma d q mu l hd
  have he (u : ℝ) : gaussian u*smoothDefect sigma (q-2*Real.sqrt d*u) mu l=
      2*(gaussian u*smoothTilt sigma (q-2*Real.sqrt d*u) mu l)-
      l*(gaussian u*smoothFieldSlope sigma (q-2*Real.sqrt d*u) mu l) := by unfold smoothDefect; ring
  simp_rw [he]
  exact (hi.2.2.const_mul 2).sub (hi.2.1.const_mul l)

theorem defect_mixture (sigma d q mu l : ℝ) (hd : 0≤d) :
    (∫ u : ℝ, gaussian u*smoothDefect sigma (q-2*Real.sqrt d*u) mu l)=
      mass*defect sigma d q mu l := by
  have hi := mixture_integrable sigma d q mu l hd
  have he (u : ℝ) : gaussian u*smoothDefect sigma (q-2*Real.sqrt d*u) mu l=
      2*(gaussian u*smoothTilt sigma (q-2*Real.sqrt d*u) mu l)-
      l*(gaussian u*smoothFieldSlope sigma (q-2*Real.sqrt d*u) mu l) := by unfold smoothDefect; ring
  simp_rw [he]
  rw [integral_sub (hi.2.2.const_mul 2) (hi.2.1.const_mul l)]
  simp only [integral_const_mul,tilt_mixture sigma d q mu l hd,field_mixture sigma d q mu l hd]
  unfold defect
  ring

theorem global_quadratic_loss : ∃ C : ℝ, 0≤C ∧ ∀ sigma d q mu l : ℝ,
    0≤sigma → 0≤d → 0≤defect sigma d q mu l+C*energy sigma d q mu l := by
  obtain ⟨C,hC,hbound⟩ := global_smoothed_loss
  refine ⟨C,hC,?_⟩
  intro sigma d q mu l hsigma hd
  have hi := mixture_integrable sigma d q mu l hd
  have hdi := defect_mixture_integrable sigma d q mu l hd
  have hn : 0≤∫ u : ℝ, gaussian u*(smoothDefect sigma (q-2*Real.sqrt d*u) mu l+
      C*smoothEnergy sigma (q-2*Real.sqrt d*u) mu l) :=
    integral_nonneg (fun u => mul_nonneg (Real.exp_pos _).le (hbound _ _ _ _ hsigma))
  have he (u : ℝ) : gaussian u*(smoothDefect sigma (q-2*Real.sqrt d*u) mu l+
      C*smoothEnergy sigma (q-2*Real.sqrt d*u) mu l)=
      gaussian u*smoothDefect sigma (q-2*Real.sqrt d*u) mu l+
      C*(gaussian u*smoothEnergy sigma (q-2*Real.sqrt d*u) mu l) := by ring
  simp_rw [he] at hn
  rw [integral_add hdi (hi.1.const_mul C),integral_const_mul,
    defect_mixture sigma d q mu l hd,energy_mixture sigma d q mu l hd] at hn
  nlinarith [mass_positive]


theorem field_derivative (sigma d q mu l : ℝ) :
    HasDerivAt (fun x => energy sigma d q mu x) (fieldSlope sigma d q mu l) l := by
  let F : ℝ→ℝ→ℝ := fun x theta => Real.exp (d*(Real.cos theta)^2-q*Real.cos theta)*
    weight sigma (mu+x*Real.cos theta)
  let F' : ℝ→ℝ→ℝ := fun x theta => Real.exp (d*(Real.cos theta)^2-q*Real.cos theta)*
    Real.cos theta*weightSlope sigma (mu+x*Real.cos theta)
  have hF'c : Continuous F'.uncurry := by dsimp [F',weightSlope]; fun_prop
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image
    (K := Icc (l-1) (l+1) ×ˢ Icc (0:ℝ) (2*Real.pi)) hF'c.norm.continuousOn
  have hFc (x : ℝ) : Continuous (F x) := by dsimp [F,weight]; fun_prop
  have hF'c1 (x : ℝ) : Continuous (F' x) := by dsimp [F',weightSlope]; fun_prop
  have hi : Integrable (F l) (volume.restrict (Icc 0 (2*Real.pi))) :=
    (hFc l).integrableOn_Icc
  have hbound : ∀ᵐ theta ∂volume.restrict (Icc 0 (2*Real.pi)),
      ∀ x ∈ Icc (l-1) (l+1), ‖F' x theta‖ ≤ M := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [] with theta htheta x hx
    exact hM ⟨(x,theta),⟨hx,htheta⟩,rfl⟩
  have hdiff : ∀ᵐ theta ∂volume.restrict (Icc 0 (2*Real.pi)),
      ∀ x ∈ Icc (l-1) (l+1), HasDerivAt (fun t => F t theta) (F' x theta) x := by
    filter_upwards [] with theta x _
    have ht := ((hasDerivAt_id x).mul_const (Real.cos theta)).const_add mu
    have hw := ((ht.pow 2).add_const sigma).const_mul
      (Real.exp (d*(Real.cos theta)^2-q*Real.cos theta))
    convert hw using 1
    dsimp [F,F',weight,weightSlope]
    ring
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Icc (0:ℝ) (2*Real.pi))) (x₀ := l)
    (F := F) (F' := F') (bound := fun _ => M)
    (s := Icc (l-1) (l+1)) (Icc_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall (fun x => (hFc x).aestronglyMeasurable)) hi
    (hF'c1 l).aestronglyMeasurable hbound
    (integrableOn_const isCompact_Icc.measure_ne_top) hdiff
  simpa only [F,F',compact_integral_eq,energy,fieldSlope] using hh.2

theorem global_linked_loss : ∃ C : ℝ, 0≤C ∧ ∀ sigma d q mu l : ℝ,
    0≤sigma → 0≤d →
      0≤2*tilt sigma d q mu l-l*deriv (fun x => energy sigma d q mu x) l+
        C*energy sigma d q mu l := by
  obtain ⟨C,hC,hbound⟩ := global_quadratic_loss
  refine ⟨C,hC,?_⟩
  intro sigma d q mu l hsigma hd
  rw [(field_derivative sigma d q mu l).deriv]
  exact hbound sigma d q mu l hsigma hd

#print axioms mixture_integrable
#print axioms energy_mixture
#print axioms field_mixture
#print axioms tilt_mixture
#print axioms defect_mixture_integrable
#print axioms defect_mixture
#print axioms global_quadratic_loss
#print axioms field_derivative
#print axioms global_linked_loss
end
end UnifiedTheory.Audit.KFCausalAngularMassQuadraticTilt
