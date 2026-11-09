/- A form comparison bound that retains the actual dissipated energy.
The free positive parameter permits selection of longer low-loss windows. -/
import UnifiedTheory.Audit.KFCausalSplitFormComparison

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalLossSensitiveComparison
noncomputable section

private theorem young (x y eta : ℝ) (he : 0 < eta) :
    x*y ≤ x^2/(2*eta)+eta*y^2/2 := by
  have hn := sq_nonneg (x-eta*y)
  calc
    x*y ≤ (x^2+eta^2*y^2)/(2*eta) :=
      (le_div_iff₀ (by positivity : 0 < 2*eta)).mpr (by nlinarith only [hn])
    _ = x^2/(2*eta)+eta*y^2/2 := by field_simp

theorem slope_bound {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (h U u L eta E : ℝ) (hU : 0 < U) (hu : U ≤ u)
    (hL : u-U ≤ L) (he : 0 < eta) (x y : K) (hy : ‖y‖^2 ≤ U*E) :
    |(1/h)*(1/u-1/U)*(inner ℂ x y).im| ≤
      L/(2*|h| *eta)*(‖x‖^2/u^2)+eta*E*L/(2*|h| *U) := by
  have hu0 : 0 < u := hU.trans_le hu
  have hdiff : 0 ≤ u-U := sub_nonneg.mpr hu
  have hL0 : 0 ≤ L := (sub_nonneg.mpr hu).trans hL
  have ha : |1/u-1/U|=(u-U)/(u*U) := by
    rw [abs_of_nonpos (sub_nonpos.mpr (one_div_le_one_div_of_le hU hu))]
    field_simp
    ring
  have hb : ‖y‖^2/U^2 ≤ E/U := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hU) hU).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hy hU.le]
  have hj := young (‖x‖/u) (‖y‖/U) eta he
  simp only [div_pow] at hj
  rw [abs_mul,abs_mul,abs_div,abs_one,ha]
  calc
    _ ≤ ((1/|h|)*((u-U)/(u*U)))*(‖x‖*‖y‖) :=
      mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm _).trans (norm_inner_le_norm x y)) (by positivity)
    _ = ((u-U)/|h|)*((‖x‖/u)*(‖y‖/U)) := by ring
    _ ≤ (L/|h|)*((‖x‖/u)*(‖y‖/U)) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hL (abs_nonneg h)) (by positivity)
    _ ≤ (L/|h|)*(‖x‖^2/u^2/(2*eta)+eta*(‖y‖^2/U^2)/2) :=
      mul_le_mul_of_nonneg_left hj (by positivity)
    _ ≤ (L/|h|)*(‖x‖^2/u^2/(2*eta)+eta*(E/U)/2) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb he.le) (show (0:ℝ) ≤ 2 by norm_num))) (by positivity)
    _ = _ := by ring

theorem energy_drop_bound (D E d loss : ℝ → ℝ) (U T a b : ℝ) (hT : 0 ≤ T)
    (hc : ContinuousOn D (Set.Icc U (U+T))) (he : ContinuousOn E (Set.Icc U (U+T)))
    (hi : D U=0)
    (hd : ∀ u ∈ Set.Ioo U (U+T), HasDerivAt D (d u) u)
    (hl : ∀ u ∈ Set.Ioo U (U+T), HasDerivAt E (-loss u) u)
    (hb : ∀ u ∈ Set.Ioo U (U+T), d u ≤ a*loss u+b) :
    D (U+T) ≤ a*(E U-E (U+T))+b*T := by
  have hm : AntitoneOn (fun u => D u+a*E u-b*(u-U)) (Set.Icc U (U+T)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc U (U+T))
      ((hc.add (continuousOn_const.mul he)).sub (by fun_prop))
      (fun x hx => (((hd x (by simpa only [interior_Icc] using hx)).add
        ((hl x (by simpa only [interior_Icc] using hx)).const_mul a)).sub
        (((hasDerivAt_id x).sub_const U).const_mul b)).hasDerivWithinAt)
    intro x hx
    have ht := hb x (by simpa only [interior_Icc] using hx)
    simp only [mul_one]
    linarith only [ht]
  have ht : U ≤ U+T := by linarith
  have hr := hm ⟨le_rfl,ht⟩ ⟨ht,le_rfl⟩ ht
  simp only [hi,sub_self,mul_zero,sub_zero,zero_add,add_sub_cancel_left] at hr
  linarith only [hr]

#print axioms slope_bound
#print axioms energy_drop_bound
end
end UnifiedTheory.Audit.KFCausalLossSensitiveComparison
