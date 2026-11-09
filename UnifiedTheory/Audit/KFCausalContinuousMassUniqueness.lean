/- Norm differentiation and interval uniqueness for continuous form states
whose mass-applied curves have strong derivatives. The state itself need
not have a form-space or physical strong derivative. -/
import UnifiedTheory.Audit.KFCausalMassGram
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalContinuousMassUniqueness
noncomputable section
open Set Filter Topology
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem norm_square_increment (J : V →L[ℂ] H) (M : V →L[ℂ] V)
    (hM : ∀ x y, inner ℂ (M x) y = inner ℂ (J x) (J y)) (x y : V) :
    ‖J x‖^2-‖J y‖^2 = (inner ℂ (M (x-y)) (x+y)).re := by
  rw [hM,map_sub,map_add,inner_sub_left,inner_add_right,inner_add_right]
  have hn (z : H) : (inner ℂ z z).re = ‖z‖^2 := (norm_sq_eq_re_inner (𝕜 := ℂ) z).symm
  simp only [Complex.sub_re,Complex.add_re,hn]
  have hs : (inner ℂ (J x) (J y)).re = (inner ℂ (J y) (J x)).re :=
    inner_re_symm (𝕜 := ℂ) (J x) (J y)
  rw [hs]
  ring

theorem norm_square_derivative (J : V →L[ℂ] H) (M : V →L[ℂ] V)
    (hM : ∀ x y, inner ℂ (M x) y = inner ℂ (J x) (J y))
    (u : ℝ → V) (d : V) (t : ℝ) (hu : ContinuousAt u t)
    (hd : HasDerivAt (fun z => M (u z)) d t) :
    HasDerivAt (fun z => ‖J (u z)‖^2) (2*(inner ℂ d (u t)).re) t := by
  have hi : Tendsto (fun z : ℝ => z) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_id.mono_right nhdsWithin_le_nhds
  have hshift : Tendsto (fun z : ℝ => t+z) (𝓝[≠] 0) (𝓝 t) := by
    simpa only [add_zero] using hi.const_add t
  have hstate := (hu.tendsto.comp hshift).add_const (u t)
  have hpair := Complex.continuous_re.continuousAt.tendsto.comp
    (hd.tendsto_slope_zero.inner hstate (𝕜 := ℂ))
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  convert hpair using 1
  · funext z
    change z⁻¹*(‖J (u (t+z))‖^2-‖J (u t)‖^2) =
      (inner ℂ (z⁻¹ • (M (u (t+z))-M (u t))) (u (t+z)+u t)).re
    rw [norm_square_increment J M hM,map_sub]
    simp only [inner_smul_left_eq_smul,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero]
  · congr 1
    simp only [inner_add_right,Complex.add_re]
    ring

theorem constant_on_closed_interval (f : ℝ → ℝ) (l r : ℝ)
    (hc : ContinuousOn f (Icc l r)) (hd : ∀ t ∈ Ioo l r, HasDerivAt f 0 t)
    (t : ℝ) (ht : t ∈ Icc l r) : f t = f l := by
  rcases eq_or_lt_of_le ht.1 with he | he
  · exact congrArg f he.symm
  · obtain ⟨z,hz,hval⟩ := exists_hasDerivAt_eq_slope f (fun _ => (0:ℝ)) he
      (hc.mono (fun _ hx => ⟨hx.1,hx.2.trans ht.2⟩))
      (fun z hz => hd z ⟨hz.1,hz.2.trans_le ht.2⟩)
    have hzero : f t-f l = 0 := (div_eq_zero_iff.mp hval.symm).resolve_right (sub_ne_zero.mpr he.ne')
    exact sub_eq_zero.mp hzero

theorem unique (J : V →L[ℂ] H) (M : V →L[ℂ] V) (A : ℝ → V →L[ℂ] V)
    (hJ : Function.Injective J) (hM : ∀ x y, inner ℂ (M x) y = inner ℂ (J x) (J y))
    (hA : ∀ t x, (inner ℂ (A t x) x).re = 0)
    (u v : ℝ → V) (l r : ℝ) (hu : ContinuousOn u (Icc l r)) (hv : ContinuousOn v (Icc l r))
    (hdu : ∀ t ∈ Ioo l r, HasDerivAt (fun z => M (u z)) (A t (u t)) t)
    (hdv : ∀ t ∈ Ioo l r, HasDerivAt (fun z => M (v z)) (A t (v t)) t)
    (hinit : u l = v l) (t : ℝ) (ht : t ∈ Icc l r) : u t = v t := by
  have hc : ContinuousOn (fun z => ‖J (u z-v z)‖^2) (Icc l r) :=
    (J.continuous.comp_continuousOn (hu.sub hv)).norm.pow 2
  have hd (z : ℝ) (hz : z ∈ Ioo l r) : HasDerivAt (fun y => ‖J (u y-v y)‖^2) 0 z := by
    have hstate := (hu.sub hv z (Ioo_subset_Icc_self hz)).continuousAt (Icc_mem_nhds hz.1 hz.2)
    have hmass : HasDerivAt (fun y => M (u y-v y)) (A z (u z-v z)) z := by
      simpa only [map_sub] using (hdu z hz).sub (hdv z hz)
    simpa only [hA,mul_zero] using norm_square_derivative J M hM (fun y => u y-v y)
      (A z (u z-v z)) z hstate hmass
  have he := constant_on_closed_interval (fun z => ‖J (u z-v z)‖^2) l r hc hd t ht
  simp only [hinit,sub_self,map_zero,norm_zero,zero_pow (by norm_num : 2 ≠ 0)] at he
  apply hJ
  exact sub_eq_zero.mp (by simpa only [map_sub] using norm_eq_zero.mp (sq_eq_zero_iff.mp he))

#print axioms norm_square_increment
#print axioms norm_square_derivative
#print axioms constant_on_closed_interval
#print axioms unique
end
end UnifiedTheory.Audit.KFCausalContinuousMassUniqueness
