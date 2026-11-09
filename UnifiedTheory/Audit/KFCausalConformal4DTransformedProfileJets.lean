import UnifiedTheory.Audit.KFCausalConformal4DTransformedProfile
import UnifiedTheory.Audit.KFCausalConformal4DCriticalHessian
import UnifiedTheory.Audit.KFCausalBDG4DSmoothCompactPartials
import UnifiedTheory.Audit.KFCausalConformal4DFixedParameterLimit

/- Actual second jets of the inverse-radial compact amplitude. The inverse
contributes no second-order term because the original coefficient is critical. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalConformal4DTransformedProfileJets
noncomputable section
open Filter Topology
open scoped ContDiff
open KFCausalConformal4DTransformedProfile KFCausalConformal4DCriticalHessian
open KFCausalConformal4DNormalizedVolume
open KFCausalConformal4DVolumeSmoothPolynomial (jacobian_factor_smooth jacobian_factor_origin_radial_jets)
open KFCausalConformal4DRadialInverse KFCausalConformal4DRadialInverseOrigin
open KFCausalConformal4DTemporalVariation
open KFCausalConformal4DCompactKernelDerivative (cutoff)
open KFCausalBDG4DSmoothCompactPartials (du dv directional)

private def Jets (f : ℝ → ℝ) (a : ℝ) : Prop :=
  f 0=1 ∧ HasDerivAt f 0 0 ∧ HasDerivAt (deriv f) a 0

private theorem jets_mul (f g : ℝ → ℝ) (a b : ℝ)
    (hf : ContDiffAt ℝ 2 f 0) (hg : ContDiffAt ℝ 2 g 0)
    (jf : Jets f a) (jg : Jets g b) : Jets (fun l => f l*g l) (a+b) := by
  refine ⟨by simp only [jf.1,jg.1,mul_one],?_,?_⟩
  · simpa only [jf.1,jg.1,mul_zero,zero_mul,add_zero] using jf.2.1.mul jg.2.1
  · have he : deriv (fun l => f l*g l) =ᶠ[𝓝 (0:ℝ)]
        (fun l => deriv f l*g l+f l*deriv g l) := by
      filter_upwards [hf.eventually (by decide : (2:WithTop ℕ∞)≠∞),
        hg.eventually (by decide : (2:WithTop ℕ∞)≠∞)] with l hfl hgl
      exact deriv_fun_mul (hfl.differentiableAt (by norm_num))
        (hgl.differentiableAt (by norm_num))
    have hh := (jf.2.2.mul jg.2.1).add (jf.2.1.mul jg.2.2)
    have hh' : HasDerivAt (fun l => deriv f l*g l+f l*deriv g l) (a+b) 0 := by
      simpa only [jf.1,jg.1,jf.2.1.deriv,jg.2.1.deriv,mul_one,one_mul,mul_zero,
        zero_mul,zero_add,add_zero] using hh
    exact hh'.congr_of_eventuallyEq he

private theorem jets_pow (f : ℝ → ℝ) (a : ℝ) (n : ℕ)
    (hf : ContDiffAt ℝ 2 f 0) (jf : Jets f a) :
    Jets (fun l => (f l)^n) ((n:ℝ)*a) := by
  induction n with
  | zero =>
      refine ⟨by simp,?_,?_⟩
      · simpa only [pow_zero] using hasDerivAt_const (0:ℝ) (1:ℝ)
      · simpa using hasDerivAt_const (0:ℝ) (0:ℝ)
  | succ n ih =>
      have hh := jets_mul (fun l => (f l)^n) f ((n:ℝ)*a) a (hf.pow n) hf ih jf
      simpa only [← pow_succ,Nat.cast_add,Nat.cast_one,add_mul,one_mul] using hh

private theorem jets_quad (a : ℝ) : Jets (fun l : ℝ => 1+a*l^2) (2*a) := by
  have hd (l : ℝ) : HasDerivAt (fun l : ℝ => 1+a*l^2) (2*a*l) l := by
    convert ((hasDerivAt_pow 2 l).const_mul a).const_add 1 using 1; ring
  refine ⟨by norm_num,by simpa using hd 0,?_⟩
  have he : deriv (fun l : ℝ => 1+a*l^2) = fun l => 2*a*l := funext (fun l => (hd l).deriv)
  rw [he]
  simpa using (hasDerivAt_id (0:ℝ)).const_mul (2*a)

private theorem jets_div (f g : ℝ → ℝ) (a b : ℝ)
    (hf : ContDiffAt ℝ 2 f 0) (hg : ContDiffAt ℝ 2 g 0)
    (jf : Jets f a) (jg : Jets g b) : Jets (fun l => f l/g l) (a-b) := by
  have hn : g 0≠0 := by rw [jg.1]; norm_num
  refine ⟨by simp only [jf.1,jg.1,div_one],?_,?_⟩
  · simpa only [jf.1,jg.1,mul_zero,zero_mul,sub_zero,zero_div] using jf.2.1.div jg.2.1 hn
  · have he : deriv (fun l => f l/g l) =ᶠ[𝓝 (0:ℝ)]
        (fun l => (deriv f l*g l-f l*deriv g l)/(g l)^2) := by
      filter_upwards [hf.eventually (by decide : (2:WithTop ℕ∞)≠∞),
        hg.eventually (by decide : (2:WithTop ℕ∞)≠∞),hg.continuousAt.eventually_ne hn]
        with l hfl hgl hgn
      exact deriv_fun_div (hfl.differentiableAt (by norm_num))
        (hgl.differentiableAt (by norm_num)) hgn
    have hh := ((jf.2.2.mul jg.2.1).sub (jf.2.1.mul jg.2.2)).div
      (jg.2.1.pow 2) (pow_ne_zero 2 hn)
    have hh' : HasDerivAt
        (fun l => (deriv f l*g l-f l*deriv g l)/(g l)^2) (a-b) 0 := by
      simpa only [jf.1,jg.1,jf.2.1.deriv,jg.2.1.deriv,mul_one,one_mul,mul_zero,
        zero_mul,zero_add,add_zero,sub_zero,zero_sub,Pi.pow_apply,one_pow,div_one] using hh
    exact hh'.congr_of_eventuallyEq he

private theorem coefficient_local_ray (c t r : ℝ) :
    (fun l => coefficient c (l*t,l*r)) =ᶠ[𝓝 (0:ℝ)]
      (fun l => ((1+(c*t^2)*l^2)^4*(1+(t+r)^2*l^2)*(1+(t-r)^2*l^2))/
        jacobianFactor c (l*t) (l*r)) := by
  have h1 : ContinuousAt (fun l : ℝ => -(l*t)-l*r) 0 := by fun_prop
  have h2 : ContinuousAt (fun l : ℝ => -(l*t)+l*r) 0 := by fun_prop
  have he1 := h1.eventually (by simpa using KFCausalBDG4DCompactProfile.local_profile)
  have he2 := h2.eventually (by simpa using KFCausalBDG4DCompactProfile.local_profile)
  filter_upwards [he1,he2] with l hl1 hl2
  simp only [coefficient,cutoff,density_polynomial,hl1,hl2]
  congr 1
  ring

theorem coefficient_origin (c : ℝ) : coefficient c 0=1 := by
  have h := (coefficient_local_ray c 0 0).eq_of_nhds
  simpa only [zero_mul,mul_zero,zero_pow (by decide : 2≠0),add_zero,one_pow,
    mul_one,jacobian_factor_origin,div_one] using h

theorem coefficient_ray_jets (c t r : ℝ) :
    HasDerivAt (fun l => coefficient c (l*t,l*r)) 0 0 ∧
    HasDerivAt (deriv (fun l => coefficient c (l*t,l*r)))
      (4*(t^2+r^2)+c*((24/5)*t^2-(2/5)*r^2)) 0 := by
  let f : ℝ → ℝ := fun l => (1+(c*t^2)*l^2)^4*(1+(t+r)^2*l^2)*(1+(t-r)^2*l^2)
  let g : ℝ → ℝ := fun l => jacobianFactor c (l*t) (l*r)
  have hf : ContDiffAt ℝ 2 f 0 := by dsimp [f]; fun_prop
  have hg : ContDiffAt ℝ 2 g 0 := by
    have hi : ContDiff ℝ ∞ (fun l : ℝ => (c,(l*t,l*r))) := by fun_prop
    exact (jacobian_factor_smooth.comp hi).contDiffAt.of_le
      (show (2:WithTop ℕ∞)≤∞ from WithTop.coe_le_coe.mpr le_top)
  have jf : Jets f (8*c*t^2+2*(t+r)^2+2*(t-r)^2) := by
    have h1 := jets_pow _ (2*(c*t^2)) 4 (by fun_prop) (jets_quad (c*t^2))
    have h2 := jets_mul _ _ _ _ (by fun_prop) (by fun_prop) h1 (jets_quad ((t+r)^2))
    have h3 := jets_mul _ _ _ _ (by fun_prop) (by fun_prop) h2 (jets_quad ((t-r)^2))
    convert h3 using 1; dsimp [f]; ring
  have jg : Jets g (c*((16/5)*t^2+(2/5)*r^2)) := by
    refine ⟨?_,(jacobian_factor_origin_radial_jets c t r).1,
      (jacobian_factor_origin_radial_jets c t r).2⟩
    simp only [g,zero_mul,jacobian_factor_origin]
  have hh := jets_div f g _ _ hf hg jf jg
  have he := coefficient_local_ray c t r
  refine ⟨hh.2.1.congr_of_eventuallyEq he,?_⟩
  have hsecond := hh.2.2.congr_of_eventuallyEq he.deriv
  convert hsecond using 1
  ring

theorem coefficient_origin_fderiv (c : ℝ) : fderiv ℝ (coefficient c) 0=0 := by
  have hs := coefficient_smoothAt c 0 (by change jacobianFactor c 0 0≠0; rw [jacobian_factor_origin]; norm_num)
  apply ContinuousLinearMap.ext
  intro d
  have hsf : HasFDerivAt (coefficient c) (fderiv ℝ (coefficient c) 0) ((0:ℝ) • d) := by
    simpa only [zero_smul] using (hs.differentiableAt (by simp)).hasFDerivAt
  have hd := hsf.comp_hasDerivAt (0:ℝ) ((hasDerivAt_id (0:ℝ)).smul_const d)
  have he := hd.unique (coefficient_ray_jets c d.1 d.2).1
  simpa only [id_eq,zero_smul,one_smul,ContinuousLinearMap.zero_apply] using he

theorem coefficient_hessian_ray (c : ℝ) (d : ℝ×ℝ) :
    fderiv ℝ (fderiv ℝ (coefficient c)) 0 d d =
      4*(d.1^2+d.2^2)+c*((24/5)*d.1^2-(2/5)*d.2^2) := by
  have hs := coefficient_smoothAt c 0 (by change jacobianFactor c 0 0≠0; rw [jacobian_factor_origin]; norm_num)
  exact (ray_second_hasDerivAt (coefficient c) (hs.of_le
    (show (2:WithTop ℕ∞)≤∞ from WithTop.coe_le_coe.mpr le_top)) d).unique
    (coefficient_ray_jets c d.1 d.2).2

theorem amplitude_hessian_origin (c : ℝ) (hc : |c|≤1/54) :
    fderiv ℝ (fderiv ℝ (amplitude c hc)) 0=
      fderiv ℝ (fderiv ℝ (coefficient c)) 0 := by
  have he : amplitude c hc =ᶠ[𝓝 (0:ℝ×ℝ)] (coefficient c ∘ inverse c hc) := by
    filter_upwards [targetBox_open.mem_nhds (show (0:ℝ×ℝ)∈targetBox by norm_num [targetBox])]
      with y hy
    exact amplitude_eq c hc y hy
  rw [he.fderiv.fderiv_eq]
  have hs := coefficient_smoothAt c 0 (by change jacobianFactor c 0 0≠0; rw [jacobian_factor_origin]; norm_num)
  exact inverse_critical_hessian c hc (coefficient c) (hs.of_le
    (show (2:WithTop ℕ∞)≤∞ from WithTop.coe_le_coe.mpr le_top)) (coefficient_origin_fderiv c)

theorem profile_hessian_ray (c : ℝ) (hc : |c|≤1/54) (d : ℝ×ℝ) :
    fderiv ℝ (fderiv ℝ (profile c hc)) 0 d d =
      (2+11*c/10)*(d.1^2+d.2^2)+(13*c/5)*d.1*d.2 := by
  have hsF : ContDiffAt ℝ 2 (profile c hc) 0 := (profile_smooth c hc).contDiffAt.of_le
    (show (2:WithTop ℕ∞)≤∞ from WithTop.coe_le_coe.mpr le_top)
  have hsA : ContDiffAt ℝ 2 (amplitude c hc) 0 := (amplitude_smooth c hc).contDiffAt.of_le
    (show (2:WithTop ℕ∞)≤∞ from WithTop.coe_le_coe.mpr le_top)
  have he : (fun l : ℝ => profile c hc (l • d))=
      (fun l : ℝ => amplitude c hc (l • nullMap d)) := by
    funext l
    unfold profile
    congr 1
    ext <;> simp only [nullMap,Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> ring
  have hA := ray_second_hasDerivAt (amplitude c hc) hsA (nullMap d)
  rw [← he] at hA
  have h := (ray_second_hasDerivAt (profile c hc) hsF d).unique hA
  rw [amplitude_hessian_origin,coefficient_hessian_ray] at h
  rw [h]
  simp only [nullMap]
  ring

private theorem directional_second (F : (ℝ×ℝ) → ℝ) (hF : ContDiff ℝ ∞ F)
    (d e p : ℝ×ℝ) : directional (directional F d) e p = fderiv ℝ (fderiv ℝ F) p e d := by
  have hf := (contDiff_infty_iff_fderiv.mp hF).2.differentiable (by norm_num)
  unfold directional
  rw [fderiv_clm_apply hf.differentiableAt (differentiableAt_const d)]
  simp

theorem profile_second_uu (c : ℝ) (hc : |c|≤1/54) :
    du (du (profile c hc)) (0,0)=2+11*c/10 := by
  simp only [du]
  rw [directional_second _ (profile_smooth c hc)]
  simpa only [Prod.fst,Prod.snd,one_pow,zero_pow (by decide : 2≠0),add_zero,
    mul_one,mul_zero] using profile_hessian_ray c hc (1,0)

theorem profile_second_vv (c : ℝ) (hc : |c|≤1/54) :
    dv (dv (profile c hc)) (0,0)=2+11*c/10 := by
  simp only [dv]
  rw [directional_second _ (profile_smooth c hc)]
  simpa only [Prod.fst,Prod.snd,one_pow,zero_pow (by decide : 2≠0),zero_add,
    mul_one,mul_zero,add_zero] using profile_hessian_ray c hc (0,1)

theorem profile_second_vu (c : ℝ) (hc : |c|≤1/54) :
    dv (du (profile c hc)) (0,0)=13*c/10 := by
  let H := fderiv ℝ (fderiv ℝ (profile c hc)) (0,0)
  have h1 : H (1,0) (1,0)=2+11*c/10 := by
    simpa only [Prod.fst,Prod.snd,one_pow,zero_pow (by decide : 2≠0),add_zero,
      mul_one,mul_zero] using profile_hessian_ray c hc (1,0)
  have h2 : H (0,1) (0,1)=2+11*c/10 := by
    simpa only [Prod.fst,Prod.snd,one_pow,zero_pow (by decide : 2≠0),zero_add,
      mul_one,mul_zero,add_zero] using profile_hessian_ray c hc (0,1)
  have hs : H (1,0) (0,1)=H (0,1) (1,0) :=
    (profile_smooth c hc).contDiffAt.isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr le_top) (1,0) (0,1)
  have hsum := profile_hessian_ray c hc (1,1)
  have hex : H (1,1) (1,1)=H (1,0) (1,0)+H (1,0) (0,1)+
      H (0,1) (1,0)+H (0,1) (0,1) := by
    have hp : (1,1)=(1,0)+((0,1) : ℝ×ℝ) := by ext <;> norm_num
    rw [hp]
    simp only [map_add,ContinuousLinearMap.add_apply]
    ring
  change H (1,1) (1,1)=_ at hsum
  simp only [one_pow,mul_one] at hsum
  rw [hex,h1,h2,hs] at hsum
  rw [dv,du,directional_second _ (profile_smooth c hc)]
  change H (0,1) (1,0)=_
  linarith

theorem operator_tendsto (c : ℝ) (hc : |c|≤1/54) :
    Tendsto (fun rho => KFCausalBDG4DActualTemporalVariation.operator rho c) atTop (𝓝 (8-6*c)) := by
  have ht := KFCausalConformal4DFixedParameterLimit.operator_tendsto c hc
  rw [profile_second_uu,profile_second_vv,profile_second_vu] at ht
  have he : 2*((2+11*c/10)+(2+11*c/10))-8*(13*c/10)=8-6*c := by ring
  rw [he] at ht
  exact ht

#print axioms amplitude_hessian_origin
#print axioms profile_hessian_ray
#print axioms profile_second_uu
#print axioms profile_second_vv
#print axioms profile_second_vu
#print axioms operator_tendsto

#print axioms coefficient_origin
#print axioms coefficient_ray_jets
#print axioms coefficient_origin_fderiv
#print axioms coefficient_hessian_ray
end
end UnifiedTheory.Audit.KFCausalConformal4DTransformedProfileJets
