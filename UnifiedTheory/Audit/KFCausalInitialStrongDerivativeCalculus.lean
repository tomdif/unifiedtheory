/- Initial strong differentiability from scalar jets and a conserved
Hilbert norm. No strong derivative of the curve is presupposed. -/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalInitialStrongDerivativeCalculus
noncomputable section
open Filter Asymptotics Set
open scoped Topology

theorem vanishing_product_derivative (f g : ℝ → ℝ) (s d : ℝ)
    (hf : HasDerivAt f d s) (hg : ContinuousAt g s) (hf0 : f s = 0) (hg0 : g s = 0) :
    HasDerivAt (fun t => f t*g t) 0 s := by
  have hfo : f =O[𝓝 s] fun t => t-s := by
    simpa only [hf0,sub_zero] using hf.isBigO_sub
  have hgo : g =o[𝓝 s] fun _ => (1:ℝ) :=
    (isLittleO_one_iff ℝ).mpr (by simpa only [hg0] using hg.tendsto)
  rw [hasDerivAt_iff_isLittleO]
  simpa only [hf0,zero_mul,sub_zero,smul_zero,mul_one] using hfo.mul_isLittleO hgo

theorem zero_second_jet (f d : ℝ → ℝ) (s : ℝ)
    (hd : ∀ t, HasDerivAt f (d t) t) (hf0 : f s = 0) (hd0 : d s = 0)
    (hdd : HasDerivAt d 0 s) : f =o[𝓝 s] fun t => (t-s)^2 := by
  have ho : d =o[𝓝 s] fun t => (t-s)^1 := by
    simpa only [hd0,sub_zero,smul_zero,pow_one] using hasDerivAt_iff_isLittleO.mp hdd
  have ht := (convex_univ : Convex ℝ (univ : Set ℝ)).isLittleO_pow_succ_real
    (mem_univ s) (fun t _ => (hd t).hasDerivWithinAt) (n := 1)
    (by simpa only [nhdsWithin_univ] using ho)
  simpa only [nhdsWithin_univ,hf0,sub_zero] using ht

theorem second_jet_remainder (f d : ℝ → ℝ) (s K : ℝ)
    (hd : ∀ t, HasDerivAt f (d t) t) (hd0 : d s = 0)
    (hdd : HasDerivAt d (-K) s) :
    (fun t => f t-f s+(K/2)*(t-s)^2) =o[𝓝 s] fun t => (t-s)^2 := by
  apply zero_second_jet _ (fun t => d t+K*(t-s)) s
  · intro t
    convert ((hd t).sub_const (f s)).add
      ((((hasDerivAt_id t).sub_const s).pow 2).const_mul (K/2)) using 1
    dsimp only [id]
    ring
  · simp only [sub_self,zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero]
  · simp only [hd0,sub_self,mul_zero,add_zero]
  · convert hdd.add (((hasDerivAt_id s).sub_const s).const_mul K) using 1
    ring

theorem affine_error_square {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u f v : H) (a : ℝ) (hn : ‖u‖ = ‖f‖) :
    ‖u-f-a • v‖^2 =
      -2*((inner ℂ u f).re-‖f‖^2)-
        2*a*((inner ℂ u v).re-(inner ℂ f v).re)+a^2*‖v‖^2 := by
  rw [norm_sub_sq (𝕜 := ℂ),norm_sub_sq (𝕜 := ℂ),hn,
    inner_smul_right_eq_smul,inner_sub_left]
  change ‖f‖^2-2*(inner ℂ u f).re+‖f‖^2-
    2*(a • (inner ℂ u v-inner ℂ f v)).re+‖a • v‖^2 = _
  simp only [Complex.smul_re,Complex.sub_re,smul_eq_mul,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring

theorem initial_derivative_of_scalar_jets {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u : ℝ → H) (v : H) (s : ℝ) (d : ℝ → ℝ)
    (hn : ∀ t, ‖u t‖ = ‖u s‖)
    (hd : ∀ t, HasDerivAt (fun z => (inner ℂ (u z) (u s)).re) (d t) t)
    (hd0 : d s = 0) (hdd : HasDerivAt d (-‖v‖^2) s)
    (hv : HasDerivAt (fun z => (inner ℂ (u z) v).re) (‖v‖^2) s) :
    HasDerivAt u v s := by
  have hp := second_jet_remainder (fun t => (inner ℂ (u t) (u s)).re) d s (‖v‖^2) hd hd0 hdd
  have hq := hasDerivAt_iff_isLittleO.mp hv
  have hq' := (isBigO_refl (fun t : ℝ => t-s) (𝓝 s)).mul_isLittleO hq
  have he := (hp.const_mul_left (-2)).add (by
    simpa only [← pow_two] using hq'.const_mul_left (-2))
  have hs : (fun t => ‖u t-u s-(t-s) • v‖^2) =o[𝓝 s] fun t => (t-s)^2 := by
    convert he using 1
    funext t
    dsimp only
    have hself : (inner ℂ (u s) (u s)).re = ‖u s‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) (u s)
    rw [affine_error_square (u t) (u s) v (t-s) (hn t),hself]
    simp only [smul_eq_mul]
    ring
  have ho : (fun t => ‖u t-u s-(t-s) • v‖) =o[𝓝 s] fun t => t-s :=
    hs.of_pow (by decide : 2 ≠ 0)
  exact hasDerivAt_iff_isLittleO.mpr ho.of_norm_left

#print axioms vanishing_product_derivative
#print axioms zero_second_jet
#print axioms second_jet_remainder
#print axioms affine_error_square
#print axioms initial_derivative_of_scalar_jets
end
end UnifiedTheory.Audit.KFCausalInitialStrongDerivativeCalculus
