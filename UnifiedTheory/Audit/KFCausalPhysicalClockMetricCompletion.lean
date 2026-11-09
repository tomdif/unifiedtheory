/- Division-free completion for the actual complex-clock physical metric.
The quartic field may vanish. Every metric inequality is derived from the
original small complex shear, and the loss retains the physical clock. -/
import UnifiedTheory.Audit.KFCausalPhysicalClockMetric
import UnifiedTheory.Audit.KFCausalCommonRealGaussianWeightedEnergy

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalPhysicalClockMetricCompletion
noncomputable section
open scoped ComplexConjugate
open KFCausalComplexShearPerturbation (Space)
open KFCausalPhysicalClockMetric (baseClock shiftedClock metric normalized_bound metric_coercive)
open KFCausalPairedModeCoordinates (scale)
open KFCausalCommonRealGaussianWeightedEnergy (potential potential_nonnegative)

def fieldVector : Space := WithLp.toLp 2 ![0,0,0,(2*scale:ℝ),1]
def slope (m g x : ℝ) : ℝ := m*x+g*x^3
def second (m g x : ℝ) : ℝ := m+3*g*x^2

theorem field_norm_square : ‖fieldVector‖^2=(3:ℝ) := by
  have hs := KFCausalPairedModeCoordinates.scale_square
  simp only [PiLp.norm_sq_eq_of_L2,fieldVector,Fin.sum_univ_succ,Fin.sum_univ_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,norm_zero,zero_pow,ne_eq,OfNat.ofNat_ne_zero,
    not_false_eq_true,norm_one,one_pow,zero_add,add_zero]
  rw [Complex.norm_real,Real.norm_eq_abs,sq_abs]
  nlinarith

theorem metric_norm_bound (ε s : ℝ) (hε : 0<ε) (δ : ℂ) (hδ : ‖δ‖≤1/20) (x : Space) :
    ‖metric ε s δ x‖≤(4/(3*baseClock ε s))*‖x‖ := by
  have hC : 0<baseClock ε s := add_pos (Real.exp_pos s) hε
  have hd := normalized_bound ε s hε δ hδ x
  have ht := norm_add_le ((baseClock ε s:ℂ) • metric ε s δ x-x) x
  rw [sub_add_cancel,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hC] at ht
  have hh : baseClock ε s*‖metric ε s δ x‖≤(4/3:ℝ)*‖x‖ := by linarith
  have he : (4/(3*baseClock ε s))*‖x‖=((4/3:ℝ)*‖x‖)/baseClock ε s := by ring
  rw [he]
  exact (le_div_iff₀ hC).mpr (by simpa only [mul_comm] using hh)

theorem potential_slope_square (m g k x : ℝ) (hm : 0≤m) (hg : 0≤g) (hk : 0≤k) :
    (slope m g x)^2≤2*potential m g k x*second m g x := by
  have he : 2*potential m g k x*second m g x-(slope m g x)^2=
      2*k*m+6*k*g*x^2+(3/2:ℝ)*m*g*x^4+(1/2:ℝ)*g^2*x^6 := by
    unfold potential slope second
    ring
  have hp : 0≤2*k*m+6*k*g*x^2+(3/2:ℝ)*m*g*x^4+(1/2:ℝ)*g^2*x^6 := by positivity
  linarith

private theorem complex_young (a d : ℝ) (z : ℂ) (ha : 0≤a) (hd : 0≤d)
    (hz : ‖z‖^2≤4*a*d) : -d≤a+z.re := by
  have hr := (sq_le_sq₀ (abs_nonneg z.re) (norm_nonneg z)).mpr (Complex.abs_re_le_norm z)
  rw [sq_abs] at hr
  by_contra hbad
  have hb : z.re < -(a+d) := by linarith
  have hs := sq_nonneg (a-d)
  have hn := mul_pos (show 0< -z.re-(a+d) by linarith)
    (show 0< -z.re+(a+d) by linarith)
  nlinarith

theorem metric_weighted_lower (ε s : ℝ) (hε : 0<ε) (δ : ℂ) (hδ : ‖δ‖≤1/20)
    (m g k φ : ℝ) (hm : 0≤m) (hg : 0≤g) (hk : 0≤k) (z : ℂ) (v : Space) :
    -(4/baseClock ε s)*second m g φ*‖z‖^2≤
      (((potential m g k φ:ℂ)*inner ℂ v (metric ε s δ v)+
        (slope m g φ:ℂ)*conj z*inner ℂ fieldVector (metric ε s δ v)).re) := by
  let C := baseClock ε s
  let W := potential m g k φ
  let V := second m g φ
  let q := (slope m g φ:ℂ)*conj z*inner ℂ fieldVector (metric ε s δ v)
  let a := (2/(3*C))*W*‖v‖^2
  let d := (4/C)*V*‖z‖^2
  have hC : 0<C := add_pos (Real.exp_pos s) hε
  have hW : 0≤W := potential_nonnegative m g k φ hm hg hk
  have hV : 0≤V := by dsimp [V,second]; positivity
  have hN := metric_norm_bound ε s hε δ hδ v
  have hn := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤(4/(3*C))*‖v‖)).mpr hN
  have hi := (sq_le_sq₀ (norm_nonneg (inner ℂ fieldVector (metric ε s δ v)))
    (mul_nonneg (norm_nonneg fieldVector) (norm_nonneg _))).mpr
      (norm_inner_le_norm (𝕜:=ℂ) fieldVector (metric ε s δ v))
  rw [mul_pow,field_norm_square] at hi
  have hip : ‖inner ℂ fieldVector (metric ε s δ v)‖^2≤
      3*((4/(3*C))^2*‖v‖^2) := by rw [mul_pow] at hn; linarith
  have hq : ‖q‖^2≤4*a*d := by
    dsimp only [q]
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_conj,
      mul_pow,mul_pow,sq_abs]
    have hw := mul_le_mul_of_nonneg_right (potential_slope_square m g k φ hm hg hk)
      (sq_nonneg ‖z‖)
    have hh := mul_le_mul hw hip (sq_nonneg _)
      (show 0≤2*W*V*‖z‖^2 by positivity)
    apply hh.trans_eq
    dsimp only [a,d]
    ring
  have hy := complex_young a d q (by positivity) (by positivity) hq
  have hl := mul_le_mul_of_nonneg_left (metric_coercive ε s hε δ hδ v).1 hW
  have he : (((potential m g k φ:ℂ)*inner ℂ v (metric ε s δ v)+q).re)=
      W*(inner ℂ v (metric ε s δ v)).re+q.re := by
    rw [Complex.add_re,Complex.re_ofReal_mul]
  rw [he]
  dsimp only [a,d,C,W,V] at hy
  nlinarith only [hy,hl]

theorem shifted_real_positive (ε s : ℝ) (hε : 0<ε) (δ : ℂ) (hδ : ‖δ‖≤1/20) :
    0<(shiftedClock ε s δ).re := by
  have hi := (Complex.abs_im_le_norm δ).trans hδ
  have hc : 0<Real.cos δ.im := Real.cos_pos_of_mem_Ioo ⟨by
    have hp := Real.pi_gt_three
    linarith [(abs_le.mp hi).1],by
    have hp := Real.pi_gt_three
    linarith [(abs_le.mp hi).2]⟩
  simp only [shiftedClock,Complex.add_re,Complex.exp_re,Complex.add_im,Complex.ofReal_im,
    zero_add,Complex.ofReal_re]
  positivity

def density (ε s h m g k φ : ℝ) (δ z : ℂ) (v : Space) : ℝ :=
  ((shiftedClock ε s δ/2)*(potential m g k φ:ℂ)*(‖z‖^2:ℝ)+
    ((h:ℂ)^2/2)*((potential m g k φ:ℂ)*inner ℂ v (metric ε s δ v)+
      (slope m g φ:ℂ)*conj z*inner ℂ fieldVector (metric ε s δ v))).re

theorem density_lower (ε s h m g k φ : ℝ) (hε : 0<ε) (δ : ℂ) (hδ : ‖δ‖≤1/20)
    (hm : 0≤m) (hg : 0≤g) (hk : 0≤k) (z : ℂ) (v : Space) :
    -(2*h^2/baseClock ε s)*second m g φ*‖z‖^2≤density ε s h m g k φ δ z v := by
  have hW := potential_nonnegative m g k φ hm hg hk
  have hC := shifted_real_positive ε s hε δ hδ
  have hl := mul_le_mul_of_nonneg_left
    (metric_weighted_lower ε s hε δ hδ m g k φ hm hg hk z v)
    (show 0≤h^2/2 by positivity)
  have he : density ε s h m g k φ δ z v=
      (shiftedClock ε s δ).re/2*potential m g k φ*‖z‖^2+
      (h^2/2)*(((potential m g k φ:ℂ)*inner ℂ v (metric ε s δ v)+
        (slope m g φ:ℂ)*conj z*inner ℂ fieldVector (metric ε s δ v)).re) := by
    unfold density
    simp only [←Complex.ofReal_pow,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.div_ofNat_re,Complex.div_ofNat_im,zero_mul,mul_zero,sub_zero]
    ring
  rw [he]
  have hp : 0≤(shiftedClock ε s δ).re/2*potential m g k φ*‖z‖^2 := by positivity
  have heq : (h^2/2)*(-(4/baseClock ε s)*second m g φ*‖z‖^2)=
      -(2*h^2/baseClock ε s)*second m g φ*‖z‖^2 := by ring
  rw [heq] at hl
  linarith only [hl,hp]

theorem potential_second_bound (m g k φ : ℝ) (hm : 0≤m) (hg : 0≤g) (hk : 0<k) :
    second m g φ≤(12+(m+3*g)/k)*potential m g k φ := by
  have hW := potential_nonnegative m g k φ hm hg hk.le
  have h0 : k≤potential m g k φ := by
    unfold potential
    have h1 : 0≤m*φ^2/2 := by positivity
    have h2 : 0≤g*φ^4/4 := by positivity
    linarith
  have h4 : (g/4)*φ^4≤potential m g k φ := by
    unfold potential
    have h1 : 0≤m*φ^2/2 := by positivity
    nlinarith
  have hm0 := mul_le_mul_of_nonneg_left h0 (show 0≤(m+3*g)/k by positivity)
  have hm4 := mul_le_mul_of_nonneg_left h4 (by norm_num : (0:ℝ)≤12)
  have he : ((m+3*g)/k)*k=m+3*g := div_mul_cancel₀ _ hk.ne'
  rw [he] at hm0
  have hs := mul_nonneg (show 0≤3*g by positivity) (sq_nonneg (φ^2-1))
  unfold second
  nlinarith

theorem positive_vacuum_lower (ε s h m g k φ : ℝ) (hε : 0<ε) (δ : ℂ) (hδ : ‖δ‖≤1/20)
    (hm : 0≤m) (hg : 0≤g) (hk : 0<k) (z : ℂ) (v : Space) :
    -((2*h^2/ε)*(12+(m+3*g)/k))*potential m g k φ*‖z‖^2≤
      density ε s h m g k φ δ z v := by
  have hW := potential_nonnegative m g k φ hm hg hk.le
  have hS := potential_second_bound m g k φ hm hg hk
  have hC : ε≤baseClock ε s := by
    dsimp [baseClock]
    linarith [Real.exp_pos s]
  have hCp : 0<baseClock ε s := hε.trans_le hC
  have hK : 0≤12+(m+3*g)/k := by positivity
  have hd := div_le_div_of_nonneg_left (show 0≤2*h^2 by positivity) hε hC
  have h1 := mul_le_mul_of_nonneg_left hS (show 0≤2*h^2/baseClock ε s by positivity)
  have h2 := mul_le_mul_of_nonneg_right hd
    (show 0≤(12+(m+3*g)/k)*potential m g k φ by positivity)
  have h3 := mul_le_mul_of_nonneg_right (h1.trans h2) (sq_nonneg ‖z‖)
  have hl := density_lower ε s h m g k φ hε δ hδ hm hg hk.le z v
  nlinarith only [h3,hl]

#print axioms field_norm_square
#print axioms metric_norm_bound
#print axioms potential_slope_square
#print axioms metric_weighted_lower
#print axioms shifted_real_positive
#print axioms density_lower
#print axioms potential_second_bound
#print axioms positive_vacuum_lower
end
end UnifiedTheory.Audit.KFCausalPhysicalClockMetricCompletion
