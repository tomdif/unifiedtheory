/- Bounded difference quotients let dense physical test vectors identify
all weak scalar derivatives. -/
import UnifiedTheory.Audit.KFCausalInitialStrongDerivativeCalculus

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalDenseWeakDerivative
noncomputable section
open Filter Asymptotics
open scoped Topology
variable {H X V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem dense_pairing_littleO (J : V → H) (hJ : DenseRange J)
    (e : X → H) (a : X → ℝ) (l : Filter X) (he : e =O[l] a)
    (hw : ∀ v, (fun t => (inner ℂ (e t) (J v)).re) =o[l] a) (y : H) :
    (fun t => (inner ℂ (e t) y).re) =o[l] a := by
  obtain ⟨C,hC,hb⟩ := he.exists_nonneg
  apply isLittleO_iff.mpr
  intro ε hε
  obtain ⟨v,hv⟩ := hJ.exists_dist_lt y (div_pos hε (by positivity : 0 < 2*(C+1)))
  have hv' : ‖y-J v‖ ≤ ε/(2*(C+1)) := by simpa only [dist_eq_norm] using hv.le
  have hCv : C*‖y-J v‖ ≤ ε/2 := by
    have hp := mul_le_mul_of_nonneg_left hv' hC
    have hc : C*(ε/(2*(C+1))) ≤ ε/2 := by
      apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
      field_simp
      nlinarith
    exact hp.trans hc
  filter_upwards [hb.bound,(hw v).def (half_pos hε)] with t ht ht'
  have hs : (inner ℂ (e t) y).re =
      (inner ℂ (e t) (y-J v)).re+(inner ℂ (e t) (J v)).re := by
    rw [inner_sub_right,Complex.sub_re]
    ring
  rw [Real.norm_eq_abs,hs]
  calc
    _ ≤ |(inner ℂ (e t) (y-J v)).re|+|(inner ℂ (e t) (J v)).re| := abs_add_le _ _
    _ ≤ ‖e t‖*‖y-J v‖+ε/2*‖a t‖ := add_le_add
      ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)) ht'
    _ ≤ (C*‖a t‖)*‖y-J v‖+ε/2*‖a t‖ :=
      add_le_add (mul_le_mul_of_nonneg_right ht (norm_nonneg _)) le_rfl
    _ ≤ ε*‖a t‖ := by nlinarith [mul_le_mul_of_nonneg_right hCv (norm_nonneg (a t))]

theorem pairing_derivative (J : V → H) (hJ : DenseRange J)
    (u : ℝ → H) (v : H) (s : ℝ)
    (hb : (fun t => u t-u s) =O[𝓝 s] fun t => t-s)
    (hw : ∀ w, HasDerivAt (fun t => (inner ℂ (u t) (J w)).re)
      (inner ℂ v (J w)).re s) (y : H) :
    HasDerivAt (fun t => (inner ℂ (u t) y).re) (inner ℂ v y).re s := by
  have hs : (fun t : ℝ => (t-s) • v) =O[𝓝 s] fun t => t-s :=
    IsBigO.of_bound ‖v‖ (Filter.Eventually.of_forall (fun t => by
      simp only [norm_smul,mul_comm,le_refl]))
  have he := hb.sub hs
  have hp (w : V) : (fun t => (inner ℂ (u t-u s-(t-s) • v) (J w)).re)
      =o[𝓝 s] fun t => t-s := by
    simpa only [inner_sub_left,inner_smul_left_eq_smul,Complex.sub_re,Complex.smul_re,
      smul_eq_mul] using hasDerivAt_iff_isLittleO.mp (hw w)
  have hy := dense_pairing_littleO J hJ _ _ (𝓝 s) he hp y
  apply hasDerivAt_iff_isLittleO.mpr
  simpa only [inner_sub_left,inner_smul_left_eq_smul,Complex.sub_re,Complex.smul_re,
    smul_eq_mul] using hy

#print axioms dense_pairing_littleO
#print axioms pairing_derivative
end
end UnifiedTheory.Audit.KFCausalDenseWeakDerivative
