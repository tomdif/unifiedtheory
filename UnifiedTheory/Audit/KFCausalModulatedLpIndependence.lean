/- Distinct Euclidean Fourier modulations of a nowhere-zero L2 weight
are algebraically linearly independent. The proof uses independence of
characters and full support of volume; no Hilbert orthogonality is claimed. -/
import UnifiedTheory.Audit.KFCausalModulatedLpTotality
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.LinearAlgebra.Basis.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalModulatedLpIndependence
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanFourierUniqueness (modulate)
open UnifiedTheory.Audit.KFCausalModulatedLpTotality (state state_coe)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def character (k : E) : Multiplicative E →* ℂ where
  toFun x := (Real.fourierChar (inner ℝ x.toAdd k):ℂ)
  map_one' := by simp
  map_mul' x y := by simp [inner_add_left,AddChar.map_add_eq_mul]

theorem character_line_derivative (k x : E) :
    HasDerivAt (fun t : ℝ => character k (Multiplicative.ofAdd (t • x)))
      ((inner ℝ x k:ℂ)*(2*Real.pi*Complex.I)) 0 := by
  have hd := (Real.hasDerivAt_fourierChar (0*inner ℝ x k)).scomp 0
    ((hasDerivAt_id (0:ℝ)).mul_const (inner ℝ x k))
  simpa [character,inner_smul_left,Complex.real_smul] using hd

theorem character_injective : Function.Injective (character (E := E)) := by
  intro k l he
  have hd (x : E) : inner ℝ x k = inner ℝ x l := by
    have hl := character_line_derivative l x
    rw [← he] at hl
    have hu := (character_line_derivative k x).unique hl
    have hi := congrArg Complex.im hu
    norm_num [Complex.mul_im,Complex.mul_re] at hi
    nlinarith [Real.pi_pos]
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [inner_sub_right,hd (k-l),sub_self]

theorem characters_linearIndependent : LinearIndependent ℂ
    (fun k : E => fun x : E => character k (Multiplicative.ofAdd x)) := by
  have hi := (linearIndependent_monoidHom (Multiplicative E) ℂ).comp character character_injective
  apply linearIndependent_iff'.mpr
  intro s z hz
  apply (linearIndependent_iff'.mp hi) s z
  funext x
  have he := congrFun hz x.toAdd
  simpa only [Finset.sum_apply,Pi.smul_apply,Pi.zero_apply] using he

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem finite_state_representatives (w : E → ℂ) (hw : MemLp w 2)
    (s : Finset E) (z : E → ℂ) :
    (∑ k ∈ s, z k • state w hw k : Lp ℂ 2 (volume : Measure E)) =ᵐ[volume]
      fun x => ∑ k ∈ s, z k*modulate k w x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using Lp.coeFn_zero ℂ 2 (volume : Measure E)
  | @insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    filter_upwards [Lp.coeFn_add (z k • state w hw k) (∑ j ∈ s, z j • state w hw j),
      Lp.coeFn_smul (z k) (state w hw k),state_coe w hw k,ih] with x ha hb hc hd
    simp only [ha,Pi.add_apply,hb,Pi.smul_apply,smul_eq_mul,hc,hd]

theorem state_linearIndependent (w : E → ℂ) (hw : MemLp w 2) (hn : ∀ x, w x ≠ 0) :
    LinearIndependent ℂ (state w hw) := by
  apply linearIndependent_iff'.mpr
  intro s z hz
  have hsum : (fun x => ∑ k ∈ s, z k*character k (Multiplicative.ofAdd x)) =ᵐ[volume] 0 := by
    have hr := finite_state_representatives w hw s z
    rw [hz] at hr
    filter_upwards [hr,Lp.coeFn_zero ℂ 2 (volume : Measure E)] with x hx hzero
    have hm : (∑ k ∈ s, z k*character k (Multiplicative.ofAdd x))*w x = 0 := by
      rw [Finset.sum_mul]
      simpa only [hzero,Pi.zero_apply,modulate,character,MonoidHom.coe_mk,OneHom.coe_mk,
        mul_assoc] using hx.symm
    exact (mul_eq_zero.mp hm).resolve_right (hn x)
  have hc : Continuous (fun x => ∑ k ∈ s, z k*character k (Multiplicative.ofAdd x)) := by
    apply continuous_finset_sum
    intro k _
    exact continuous_const.mul ((continuous_subtype_val.comp Real.continuous_fourierChar).comp
      (continuous_id.inner continuous_const))
  have he := Measure.eq_of_ae_eq hsum hc continuous_const
  apply (linearIndependent_iff'.mp (characters_linearIndependent (E := E))) s z
  ext x
  simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using congrFun he x

#print axioms character_line_derivative
#print axioms character_injective
#print axioms characters_linearIndependent
#print axioms finite_state_representatives
#print axioms state_linearIndependent
end
end UnifiedTheory.Audit.KFCausalModulatedLpIndependence
