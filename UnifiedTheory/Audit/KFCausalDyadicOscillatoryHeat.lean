/- Dyadic Gaussian averaging also controls an oscillatory phase whose
imaginary part and derivative grow at most like the square root of the
Gaussian radius. The derivative bound can be made small by increasing
the number of scales and then decreasing the phase frequency. -/
import UnifiedTheory.Audit.KFCausalDyadicHeatCancellation
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalDyadicOscillatoryHeat
noncomputable section
open scoped BigOperators
open UnifiedTheory.Audit.KFCausalDyadicHeatCancellation (width width_pos dyadic_sum_bound)

theorem width_lower (δ : ℝ) (hδ : 0 ≤ δ) (j : ℕ) : δ ≤ width δ j := by
  simpa only [width,mul_one] using
    mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) hδ

theorem square_root_gaussian (δ R S : ℝ) (hδ : 0 < δ) (hR : S^2 ≤ R) :
    S*Real.exp (-δ*R) ≤ 1/Real.sqrt δ := by
  have hd := Real.sq_sqrt hδ.le
  have hx : (Real.sqrt δ*S)^2 ≤ δ*R := by
    nlinarith [mul_le_mul_of_nonneg_left hR hδ.le]
  have he : Real.sqrt δ*S ≤ Real.exp (δ*R) := by
    nlinarith [Real.add_one_le_exp (δ*R),sq_nonneg (Real.sqrt δ*S-1)]
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-δ*R)).le
  rw [← Real.exp_add,show δ*R+(-δ*R)=0 by ring,Real.exp_zero] at hm
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hδ)).mpr
  nlinarith

theorem exponent_bound (δ v R S : ℝ) (hδ : 0 < δ) (hR : S^2 ≤ R) :
    -2*δ*R+4*|v| *S ≤ -δ*R+4*v^2/δ := by
  have hs := sq_nonneg (δ*S-2*|v|)
  have hv := sq_abs v
  have hr := mul_le_mul_of_nonneg_left hR (sq_nonneg δ)
  have hd : δ*(4*v^2/δ)=4*v^2 := by field_simp
  apply (mul_le_mul_iff_left₀ hδ).mp
  nlinarith

def packet (δ v : ℝ) (z b : ℂ) : ℂ :=
  Complex.exp ((-2*δ:ℝ)*z+(v:ℂ)*Complex.I*b)

def packetSlope (δ v : ℝ) (z b w u : ℂ) : ℂ :=
  (((-2*δ:ℝ):ℂ)*w+(v:ℂ)*Complex.I*u)*packet δ v z b

theorem packet_norm_bound (δ v S : ℝ) (hδ : 0 < δ) (z b : ℂ)
    (hS : S^2 ≤ z.re) (hb : |b.im| ≤ 4*S) :
    ‖packet δ v z b‖ ≤ Real.exp (-δ*z.re)*Real.exp (4*v^2/δ) := by
  rw [packet,Complex.norm_exp,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hv : -v*b.im ≤ 4*|v| *S := by
    have h := mul_le_mul_of_nonneg_left hb (abs_nonneg v)
    have h' := neg_le_abs (v*b.im)
    rw [abs_mul] at h'
    nlinarith
  simp only [Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,
    add_zero,mul_one,zero_sub]
  linarith [exponent_bound δ v z.re S hδ hS]

theorem packet_slope_bound (δ v K L S : ℝ) (hδ : 0 < δ) (hK : 0 ≤ K)
    (hL : 0 ≤ L) (hS : 0 ≤ S) (z b w u : ℂ)
    (hR : S^2 ≤ z.re) (hb : |b.im| ≤ 4*S) (hw : ‖w‖ ≤ K*z.re) (hu : ‖u‖ ≤ L*S) :
    ‖packetSlope δ v z b w u‖ ≤
      (2*δ*K*z.re+|v| *L*S)*Real.exp (-δ*z.re)*Real.exp (4*v^2/δ) := by
  have hR0 : 0 ≤ z.re := (sq_nonneg S).trans hR
  have hc : ‖(((-2*δ:ℝ):ℂ)*w)+(v:ℂ)*Complex.I*u‖ ≤ 2*δ*K*z.re+|v| *L*S := by
    calc
      _ ≤ ‖(((-2*δ:ℝ):ℂ)*w)‖+‖(v:ℂ)*Complex.I*u‖ := norm_add_le _ _
      _ = 2*δ*‖w‖+|v| *‖u‖ := by
        simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
        rw [abs_of_pos hδ]
        norm_num
      _ ≤ _ := by
        nlinarith [mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ 2*δ),
          mul_le_mul_of_nonneg_left hu (abs_nonneg v)]
  rw [packetSlope,norm_mul]
  exact (mul_le_mul hc (packet_norm_bound δ v S hδ z b hR hb) (norm_nonneg _)
    (by positivity)).trans_eq (by ring)

def average (δ v : ℝ) (N : ℕ) (z b : ℂ) : ℂ :=
  (N:ℂ)⁻¹ * ∑ j ∈ Finset.range N, packet (width δ j) v z b

def slope (δ v : ℝ) (N : ℕ) (z b w u : ℂ) : ℂ :=
  (N:ℂ)⁻¹ * ∑ j ∈ Finset.range N, packetSlope (width δ j) v z b w u

theorem average_derivative (δ v : ℝ) (N : ℕ) (A B : ℂ → ℂ) (q w u : ℂ)
    (hA : HasDerivAt A w q) (hB : HasDerivAt B u q) :
    HasDerivAt (fun x => average δ v N (A x) (B x))
      (slope δ v N (A q) (B q) w u) q := by
  have hj (j : ℕ) : HasDerivAt (fun x => packet (width δ j) v (A x) (B x))
      (packetSlope (width δ j) v (A q) (B q) w u) q := by
    simpa only [packet,packetSlope,mul_comm] using
      ((hA.const_mul ((-2*width δ j:ℝ):ℂ)).add (hB.const_mul ((v:ℂ)*Complex.I))).cexp
  simpa only [average,slope,Finset.sum_apply] using
    (HasDerivAt.sum (fun j (_ : j ∈ Finset.range N) => hj j)).const_mul (N:ℂ)⁻¹

theorem slope_bound (δ v K L S : ℝ) (N : ℕ) (hδ : 0 < δ) (hN : 0 < N)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hS : 0 ≤ S) (z b w u : ℂ)
    (hR : S^2 ≤ z.re) (hb : |b.im| ≤ 4*S) (hw : ‖w‖ ≤ K*z.re) (hu : ‖u‖ ≤ L*S) :
    ‖slope δ v N z b w u‖ ≤
      Real.exp (4*v^2/δ)*(4*K/(N:ℝ)+|v| *L/Real.sqrt δ) := by
  let M := Real.exp (4*v^2/δ)
  have hR0 : 0 ≤ z.re := (sq_nonneg S).trans hR
  have hj (j : ℕ) : ‖packetSlope (width δ j) v z b w u‖ ≤
      M*(2*K*(width δ j*z.re*Real.exp (-width δ j*z.re))+|v| *L/Real.sqrt δ) := by
    have hd := width_pos δ hδ j
    have he : Real.exp (4*v^2/width δ j) ≤ M :=
      Real.exp_le_exp.mpr (div_le_div_of_nonneg_left (by positivity) hδ (width_lower δ hδ.le j))
    have hs : S*Real.exp (-width δ j*z.re) ≤ 1/Real.sqrt δ := by
      apply le_trans _ (square_root_gaussian δ z.re S hδ hR)
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hS
      nlinarith [mul_le_mul_of_nonneg_right (width_lower δ hδ.le j) hR0]
    calc
      _ ≤ (2*width δ j*K*z.re+|v| *L*S)*Real.exp (-width δ j*z.re)*
          Real.exp (4*v^2/width δ j) := packet_slope_bound _ v K L S hd hK hL hS z b w u hR hb hw hu
      _ ≤ (2*width δ j*K*z.re+|v| *L*S)*Real.exp (-width δ j*z.re)*M :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ ≤ M*(2*K*(width δ j*z.re*Real.exp (-width δ j*z.re))+|v| *L/Real.sqrt δ) := by
        have h := mul_le_mul_of_nonneg_left hs (show 0 ≤ M*(|v| *L) by positivity)
        convert add_le_add_left h
          (M*(2*K*(width δ j*z.re*Real.exp (-width δ j*z.re)))) using 1 <;> ring
  have hd : ∑ j ∈ Finset.range N, width δ j*z.re*Real.exp (-width δ j*z.re) ≤ 2 := by
    have hh := mul_le_mul_of_nonneg_left (dyadic_sum_bound (δ/2) z.re (by positivity) hR0 N)
      (by norm_num : (0:ℝ) ≤ 2)
    rw [Finset.mul_sum,mul_one] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro j _
    unfold width
    ring_nf
  have hs : ‖∑ j ∈ Finset.range N, packetSlope (width δ j) v z b w u‖ ≤
      M*(4*K+(N:ℝ)*(|v| *L/Real.sqrt δ)) := by
    calc
      _ ≤ ∑ j ∈ Finset.range N, ‖packetSlope (width δ j) v z b w u‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range N,
          M*(2*K*(width δ j*z.re*Real.exp (-width δ j*z.re))+|v| *L/Real.sqrt δ) :=
        Finset.sum_le_sum (fun j _ => hj j)
      _ = M*(2*K*(∑ j ∈ Finset.range N, width δ j*z.re*Real.exp (-width δ j*z.re))+
          (N:ℝ)*(|v| *L/Real.sqrt δ)) := by
        rw [← Finset.mul_sum,Finset.sum_add_distrib,← Finset.mul_sum]
        simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        nlinarith [mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 2*K)]
  rw [slope,norm_mul,norm_inv,Complex.norm_natCast]
  refine (mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq ?_
  dsimp [M]
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

#print axioms width_lower
#print axioms square_root_gaussian
#print axioms exponent_bound
#print axioms packet_norm_bound
#print axioms packet_slope_bound
#print axioms average_derivative
#print axioms slope_bound

end
end UnifiedTheory.Audit.KFCausalDyadicOscillatoryHeat
