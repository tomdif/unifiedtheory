/- The quartic forms are the integrals of the exact pointwise transport
jets. Integration by parts uses proved polynomial L2 domains. Passing
parameter derivatives through the unbounded integral is not asserted. -/
import UnifiedTheory.Audit.KFCausalNeutralJointCurvatureForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalNeutralQuarticTransportForms
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalNeutralLineDomain
open KFCausalNeutralQuarticBoundary
open KFCausalNeutralQuarticFormBound (energy first second)
open KFCausalQuarticNeutralDefect
open KFCausalQuarticPlaneDomination (potential potentialSlope potential_derivative)

def velocity (η L : ℝ) : ℂ := -(L:ℂ)+(η:ℂ)*Complex.I
def rate (η L x : ℝ) (f g : ℂ) : ℝ :=
  2*potential x*(conj f*(velocity η L*g)).re
def acceleration (η L x : ℝ) (f g k : ℂ) : ℝ :=
  2*potential x*(‖velocity η L*g‖^2+(conj f*(velocity η L^2*k)).re)

theorem pair_re_derivative (f g k : ℝ → ℂ) (x : ℝ)
    (hf : HasDerivAt f (g x) x) (hg : HasDerivAt g (k x) x) :
    HasDerivAt (fun t => (conj (f t)*g t).re)
      (‖g x‖^2+(conj (f x)*k x).re) x := by
  have he := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hf.star.mul hg)
  convert he using 1
  change _ = (star (g x)*g x+star (f x)*k x).re
  simp only [Complex.star_def,Complex.add_re,Complex.conj_mul',← Complex.ofReal_pow,Complex.ofReal_re]

theorem pair_im_derivative (f g k : ℝ → ℂ) (x : ℝ)
    (hf : HasDerivAt f (g x) x) (hg : HasDerivAt g (k x) x) :
    HasDerivAt (fun t => (conj (f t)*g t).im) (conj (f x)*k x).im x := by
  have he := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hf.star.mul hg)
  convert he using 1
  change _ = (star (g x)*g x+star (f x)*k x).im
  simp only [Complex.star_def,Complex.add_im,Complex.conj_mul',← Complex.ofReal_pow,Complex.ofReal_im,zero_add]

private theorem ni (f : ℝ → ℂ) (hf : Regular f) :
    Integrable (fun x => potential x*‖f x‖^2) := weight_norm_integrable f hf 0
private theorem ns (f : ℝ → ℂ) (hf : Regular f) :
    Integrable (fun x => potentialSlope x*‖f x‖^2) := weight_norm_integrable f hf 1
private theorem nt (f : ℝ → ℂ) (hf : Regular f) :
    Integrable (fun x => potentialSecond x*‖f x‖^2) := weight_norm_integrable f hf 2
private theorem ri (f g : ℝ → ℂ) (hf : Regular f) (hg : Regular g) :
    Integrable (fun x => potential x*(conj (f x)*g x).re) := weight_re_integrable f g hf hg 0
private theorem rs (f g : ℝ → ℂ) (hf : Regular f) (hg : Regular g) :
    Integrable (fun x => potentialSlope x*(conj (f x)*g x).re) := weight_re_integrable f g hf hg 1
private theorem ii (f g : ℝ → ℂ) (hf : Regular f) (hg : Regular g) :
    Integrable (fun x => potential x*(conj (f x)*g x).im) := weight_im_integrable f g hf hg 0
private theorem is (f g : ℝ → ℂ) (hf : Regular f) (hg : Regular g) :
    Integrable (fun x => potentialSlope x*(conj (f x)*g x).im) := weight_im_integrable f g hf hg 1

theorem norm_balance (f g : ℝ → ℂ) (hf : Regular f) (hg : Regular g)
    (hd : ∀ x, HasDerivAt f (g x) x) :
    2*(∫ x, potential x*(conj (f x)*g x).re) = -(∫ x, potentialSlope x*‖f x‖^2) := by
  have hi : Integrable (fun x => potential x*(2*(conj (f x)*g x).re)) := by
    simpa only [mul_left_comm,mul_assoc] using (ri f g hf hg).const_mul 2
  have he := integral_mul_deriv_eq_deriv_mul_of_integrable potential_derivative
    (fun x => norm_square_derivative f g x (hd x)) hi
    (ns f hf) (ni f hf)
  have hh (x : ℝ) : potential x*(2*(conj (f x)*g x).re) = 2*(potential x*(conj (f x)*g x).re) := by ring
  simp_rw [hh] at he
  simpa only [integral_const_mul] using he

theorem pair_balances (f g k : ℝ → ℂ) (hf : Regular f) (hg : Regular g) (hk : Regular k)
    (hd : ∀ x, HasDerivAt f (g x) x) (he : ∀ x, HasDerivAt g (k x) x) :
    (∫ x, potential x*(conj (f x)*k x).re) =
        -(∫ x, potentialSlope x*(conj (f x)*g x).re)-(∫ x, potential x*‖g x‖^2) ∧
      (∫ x, potential x*(conj (f x)*k x).im) =
        -(∫ x, potentialSlope x*(conj (f x)*g x).im) := by
  have hi : Integrable (fun x => potential x*(‖g x‖^2+(conj (f x)*k x).re)) := by
    simpa only [mul_add] using (ni g hg).add (ri f k hf hk)
  have hr := integral_mul_deriv_eq_deriv_mul_of_integrable potential_derivative
    (fun x => pair_re_derivative f g k x (hd x) (he x)) hi
    (rs f g hf hg) (ri f g hf hg)
  simp_rw [mul_add] at hr
  rw [integral_add (ni g hg) (ri f k hf hk)] at hr
  refine ⟨by linarith, ?_⟩
  exact integral_mul_deriv_eq_deriv_mul_of_integrable potential_derivative
    (fun x => pair_im_derivative f g k x (hd x) (he x))
    (ii f k hf hk) (is f g hf hg)
    (ii f g hf hg)

theorem rate_expansion (η L x : ℝ) (f g : ℂ) :
    rate η L x f g = -2*L*(potential x*(conj f*g).re)-2*η*(potential x*(conj f*g).im) := by
  simp only [rate,velocity,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    Complex.neg_re,Complex.neg_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    Complex.conj_re,Complex.conj_im]
  ring

theorem acceleration_expansion (η L x : ℝ) (f g k : ℂ) :
    acceleration η L x f g k = 2*(L^2+η^2)*(potential x*‖g‖^2)+
      2*(L^2-η^2)*(potential x*(conj f*k).re)+4*L*η*(potential x*(conj f*k).im) := by
  simp only [acceleration,velocity,Complex.sq_norm,Complex.normSq_apply]
  simp only [pow_two,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    Complex.neg_re,Complex.neg_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    Complex.conj_re,Complex.conj_im]
  ring

theorem rate_integral (η L : ℝ) (f g : ℝ → ℂ) (hf : Regular f) (hg : Regular g)
    (hd : ∀ x, HasDerivAt f (g x) x) :
    (∫ x, rate η L x (f x) (g x)) = first η L f g := by
  simp_rw [rate_expansion]
  rw [integral_sub ((ri f g hf hg).const_mul (-2*L))
    ((ii f g hf hg).const_mul (2*η)),integral_const_mul,integral_const_mul]
  have heq (x : ℝ) : firstDensity η L x (f x) (g x) =
      L*(potentialSlope x*‖f x‖^2)-(2*η)*(potential x*(conj (f x)*g x).im) := by
    unfold firstDensity
    ring
  unfold first
  simp_rw [heq]
  rw [integral_sub ((ns f hf).const_mul L)
    ((ii f g hf hg).const_mul (2*η)),integral_const_mul,integral_const_mul]
  have hb := norm_balance f g hf hg hd
  have hh : (∫ x, potentialSlope x*‖f x‖^2) = -2*(∫ x, potential x*(conj (f x)*g x).re) := by linarith
  rw [hh]
  ring

theorem acceleration_integral (η L : ℝ) (f g k : ℝ → ℂ)
    (hf : Regular f) (hg : Regular g) (hk : Regular k)
    (hd : ∀ x, HasDerivAt f (g x) x) (he : ∀ x, HasDerivAt g (k x) x) :
    (∫ x, acceleration η L x (f x) (g x) (k x)) = second η L f g := by
  have hb := boundary_integral f g hf hg hd
  unfold boundaryDensity at hb
  simp_rw [mul_assoc] at hb
  rw [integral_add (nt f hf) ((rs f g hf hg).const_mul 2),
    integral_const_mul] at hb
  obtain ⟨hr,hi⟩ := pair_balances f g k hf hg hk hd he
  have ha : Integrable (fun x => 2*(L^2+η^2)*(potential x*‖g x‖^2)+
      2*(L^2-η^2)*(potential x*(conj (f x)*k x).re)) :=
    ((ni g hg).const_mul _).add ((ri f k hf hk).const_mul _)
  simp_rw [acceleration_expansion]
  rw [integral_add ha ((ii f k hf hk).const_mul _),
    integral_add ((ni g hg).const_mul _) ((ri f k hf hk).const_mul _)]
  simp only [integral_const_mul]
  have heq (x : ℝ) : secondDensity η L x (f x) (g x) =
      (4*η^2)*(potential x*‖g x‖^2)-(4*L*η)*(potentialSlope x*(conj (f x)*g x).im)+
        (L^2-η^2)*(potentialSecond x*‖f x‖^2) := by
    unfold secondDensity
    ring
  unfold second
  simp_rw [heq]
  have hs : Integrable (fun x => 4*η^2*(potential x*‖g x‖^2)-
      4*L*η*(potentialSlope x*(conj (f x)*g x).im)) :=
    ((ni g hg).const_mul _).sub ((is f g hf hg).const_mul _)
  rw [integral_add hs ((nt f hf).const_mul _),
    integral_sub ((ni g hg).const_mul _) ((is f g hf hg).const_mul _)]
  simp only [integral_const_mul]
  rw [hr,hi]
  nlinarith

theorem integrated_jet_bound (η L : ℝ) (f g k : ℝ → ℂ)
    (hf : Regular f) (hg : Regular g) (hk : Regular k)
    (hd : ∀ x, HasDerivAt f (g x) x) (he : ∀ x, HasDerivAt g (k x) x) :
    (∫ x, rate η L x (f x) (g x))^2-4*(L^2+η^2)*(energy f)^2 ≤
      energy f*(∫ x, acceleration η L x (f x) (g x) (k x)) := by
  rw [rate_integral η L f g hf hg hd,acceleration_integral η L f g k hf hg hk hd he]
  exact KFCausalNeutralQuarticFormBound.curvature_form_bound η L f g hf hg hd

#print axioms pair_re_derivative
#print axioms pair_im_derivative
#print axioms norm_balance
#print axioms pair_balances
#print axioms rate_expansion
#print axioms acceleration_expansion
#print axioms rate_integral
#print axioms acceleration_integral
#print axioms integrated_jet_bound
end
end UnifiedTheory.Audit.KFCausalNeutralQuarticTransportForms
