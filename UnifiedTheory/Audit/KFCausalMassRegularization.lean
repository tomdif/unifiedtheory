/- Positive mass regularization on a Hilbert space. For a positive symmetric
operator with dense range, delta*(G+delta I)^(-1) converges strongly to zero.
The inverse is constructed from coercivity, and the convergence is proved
by approximation on the dense range. -/
import UnifiedTheory.Audit.KFCausalCoerciveInverse
import UnifiedTheory.Audit.KFCausalSandwichCalculus

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalMassRegularization
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoerciveInverse
open UnifiedTheory.Audit.KFCausalSandwichCalculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def massShift (G : E →L[ℂ] E) (δ : ℝ) : E →L[ℂ] E := G+δ • ContinuousLinearMap.id ℂ E

def massInverse (G : E →L[ℂ] E) (δ : ℝ) : E →L[ℂ] E := Ring.inverse (massShift G δ)

def damping (G : E →L[ℂ] E) (δ : ℝ) : E →L[ℂ] E := δ • massInverse G δ

omit [CompleteSpace E] in
theorem massShift_symm (G : E →L[ℂ] E)
    (hs : ∀ x y, inner ℂ (G x) y = inner ℂ x (G y)) (δ : ℝ) :
    (massShift G δ).toLinearMap.IsSymmetric := by
  intro x y
  change inner ℂ (G x+δ • x) y = inner ℂ x (G y+δ • y)
  rw [inner_add_left,inner_add_right,inner_smul_left_eq_smul,inner_smul_right_eq_smul,hs]

omit [CompleteSpace E] in
theorem massShift_coercive (G : E →L[ℂ] E) (hp : ∀ x, 0 ≤ (inner ℂ (G x) x).re)
    (δ : ℝ) (x : E) : δ*‖x‖^2 ≤ (inner ℂ (massShift G δ x) x).re := by
  change δ*‖x‖^2 ≤ (inner ℂ (G x+δ • x) x).re
  rw [inner_add_left,inner_smul_left_eq_smul,Complex.add_re,
    UnifiedTheory.Audit.KFCausalShiftedForm.complex_inner_square]
  simp only [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  linarith [hp x]

theorem massShift_isUnit (G : E →L[ℂ] E)
    (hs : ∀ x y, inner ℂ (G x) y = inner ℂ x (G y))
    (hp : ∀ x, 0 ≤ (inner ℂ (G x) x).re) (δ : ℝ) (hδ : 0 < δ) : IsUnit (massShift G δ) :=
  coercive_isUnit _ δ hδ (massShift_coercive G hp δ) (massShift_symm G hs δ)

theorem massInverse_symmetric (G : E →L[ℂ] E)
    (hs : ∀ x y, inner ℂ (G x) y = inner ℂ x (G y))
    (hp : ∀ x, 0 ≤ (inner ℂ (G x) x).re) (δ : ℝ) (hδ : 0 < δ) (x y : E) :
    inner ℂ (massInverse G δ x) y = inner ℂ x (massInverse G δ y) :=
  inverse_inner_symm _ (massShift_isUnit G hs hp δ hδ) (massShift_symm G hs δ) x y

theorem massInverse_norm_bound (G : E →L[ℂ] E)
    (hs : ∀ x y, inner ℂ (G x) y = inner ℂ x (G y))
    (hp : ∀ x, 0 ≤ (inner ℂ (G x) x).re) (δ : ℝ) (hδ : 0 < δ) : ‖massInverse G δ‖ ≤ δ⁻¹ :=
  inverse_norm_bound _ δ hδ (massShift_coercive G hp δ) (massShift_symm G hs δ)

theorem damping_contraction (G : E →L[ℂ] E)
    (hs : ∀ x y, inner ℂ (G x) y = inner ℂ x (G y))
    (hp : ∀ x, 0 ≤ (inner ℂ (G x) x).re) (δ : ℝ) (hδ : 0 < δ) (x : E) :
    ‖damping G δ x‖ ≤ ‖x‖ := by
  change ‖δ • massInverse G δ x‖ ≤ ‖x‖
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hδ]
  calc
    _ ≤ δ*(δ⁻¹*‖x‖) := mul_le_mul_of_nonneg_left
      ((massInverse G δ).le_opNorm x |>.trans
        (mul_le_mul_of_nonneg_right (massInverse_norm_bound G hs hp δ hδ) (norm_nonneg x))) hδ.le
    _ = ‖x‖ := by rw [← mul_assoc,mul_inv_cancel₀ hδ.ne',one_mul]

theorem massInverse_split (G : E →L[ℂ] E)
    (hs : ∀ x y, inner ℂ (G x) y = inner ℂ x (G y))
    (hp : ∀ x, 0 ≤ (inner ℂ (G x) x).re) (δ : ℝ) (hδ : 0 < δ) (x : E) :
    massInverse G δ (G x) = x-damping G δ x := by
  have hh := inverse_apply_left (massShift G δ) (massShift_isUnit G hs hp δ hδ) x
  change massInverse G δ (G x+δ • x) = x at hh
  rw [map_add,ContinuousLinearMap.map_smul_of_tower] at hh
  exact eq_sub_iff_add_eq.mpr hh

theorem damping_on_range_bound (G : E →L[ℂ] E)
    (hs : ∀ x y, inner ℂ (G x) y = inner ℂ x (G y))
    (hp : ∀ x, 0 ≤ (inner ℂ (G x) x).re) (δ : ℝ) (hδ : 0 < δ) (x : E) :
    ‖damping G δ (G x)‖ ≤ 2*δ*‖x‖ := by
  change ‖δ • massInverse G δ (G x)‖ ≤ _
  rw [massInverse_split G hs hp δ hδ,norm_smul,Real.norm_eq_abs,abs_of_pos hδ]
  have hn := norm_sub_le x (damping G δ x)
  have hd := damping_contraction G hs hp δ hδ x
  nlinarith

theorem damping_strong_limit (G : E →L[ℂ] E)
    (hs : ∀ x y, inner ℂ (G x) y = inner ℂ x (G y))
    (hp : ∀ x, 0 ≤ (inner ℂ (G x) x).re) (hG : DenseRange G)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hlim : Tendsto δ atTop (𝓝 0)) (x : E) :
    Tendsto (fun n => damping G (δ n) x) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro η hη
  obtain ⟨z,hz⟩ := hG.exists_dist_lt x (show 0 < η/2 by positivity)
  have hsmall : Tendsto (fun n => 2*δ n*‖z‖) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul] using (hlim.const_mul 2).mul_const ‖z‖
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hsmall.eventually (gt_mem_nhds (show 0 < η/2 by positivity)))
  refine ⟨N,?_⟩
  intro n hn
  rw [dist_eq_norm,sub_zero]
  have he : damping G (δ n) x = damping G (δ n) (x-G z)+damping G (δ n) (G z) := by
    rw [map_sub]
    abel
  have hb : ‖damping G (δ n) x‖ ≤ ‖x-G z‖+2*δ n*‖z‖ := by
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add (damping_contraction G hs hp _ (hδ n) _)
      (damping_on_range_bound G hs hp _ (hδ n) z))
  rw [dist_eq_norm] at hz
  linarith [hN n hn]

theorem massInverse_gram_limit (G : E →L[ℂ] E)
    (hs : ∀ x y, inner ℂ (G x) y = inner ℂ x (G y))
    (hp : ∀ x, 0 ≤ (inner ℂ (G x) x).re) (hG : DenseRange G)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hlim : Tendsto δ atTop (𝓝 0)) (x : E) :
    Tendsto (fun n => massInverse G (δ n) (G x)) atTop (𝓝 x) := by
  have hh := (tendsto_const_nhds (x := x)).sub (damping_strong_limit G hs hp hG δ hδ hlim x)
  simpa only [sub_zero,← massInverse_split G hs hp _ (hδ _)] using hh

#print axioms massShift_isUnit
#print axioms massInverse_symmetric
#print axioms massInverse_norm_bound
#print axioms damping_contraction
#print axioms massInverse_split
#print axioms damping_on_range_bound
#print axioms damping_strong_limit
#print axioms massInverse_gram_limit

end
end UnifiedTheory.Audit.KFCausalMassRegularization
