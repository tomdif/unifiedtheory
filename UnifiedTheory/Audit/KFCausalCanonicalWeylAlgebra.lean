/- Exact algebra of the actual ordered modulation/translation unitaries.
The commutative limit estimates hold on every L2 state, uniformly over
unit vectors; they do not assume quantum-to-classical state convergence. -/
import UnifiedTheory.Audit.KFCausalLpPhaseTranslation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalLpPhaseTranslation

def scalar (a : ℝ) : ℂ := Complex.exp (Complex.I*(a:ℂ))

theorem scalar_add (a b : ℝ) : scalar (a+b) = scalar a*scalar b := by
  simp only [scalar,Complex.ofReal_add,mul_add,Complex.exp_add]

theorem scalar_norm (a : ℝ) : ‖scalar a‖ = 1 := by
  simp [scalar,Complex.norm_exp]

theorem scalar_sub_one (a : ℝ) : ‖scalar a-1‖ ≤ |a| :=
  Real.norm_exp_I_mul_ofReal_sub_one_le

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [Measure.IsAddHaarMeasure μ]

abbrev Frequency := (X →L[ℝ] ℝ) × X

def operator (h : ℝ) (z : Frequency (X := X)) : Hilbert μ ≃ₗᵢ[ℂ] Hilbert μ :=
  phaseTranslation μ z.1 z.1.continuous.measurable (h • z.2)

theorem operator_coe (h : ℝ) (z : Frequency (X := X)) (f : Hilbert μ) :
    operator μ h z f =ᵐ[μ] fun x => scalar (z.1 x)*f (x+h • z.2) :=
  phaseTranslation_coe μ z.1 z.1.continuous.measurable (h • z.2) f

theorem operator_zero (h : ℝ) (f : Hilbert μ) : operator μ h 0 f = f := by
  apply Lp.ext
  filter_upwards [operator_coe μ h 0 f] with x hx
  simpa only [Prod.fst_zero,Prod.snd_zero,ContinuousLinearMap.zero_apply,smul_zero,
    add_zero,scalar,Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_mul] using hx

theorem operator_product (h : ℝ) (z w : Frequency (X := X)) (f : Hilbert μ) :
    operator μ h z (operator μ h w f) =
      scalar (h*w.1 z.2) • operator μ h (z+w) f := by
  apply Lp.ext
  filter_upwards [operator_coe μ h z (operator μ h w f),
    (shift_preserves μ (h • z.2)).quasiMeasurePreserving.ae (operator_coe μ h w f),
    operator_coe μ h (z+w) f,
    Lp.coeFn_smul (scalar (h*w.1 z.2)) (operator μ h (z+w) f)] with x hx hw hs hc
  change operator μ h w f (x+h • z.2) =
    scalar (w.1 (x+h • z.2))*f ((x+h • z.2)+h • w.2) at hw
  rw [hx,hw,hc]
  simp only [Pi.smul_apply,smul_eq_mul,hs,Prod.fst_add,Prod.snd_add,
    ContinuousLinearMap.add_apply,map_add,map_smul,smul_eq_mul,scalar_add,smul_add]
  rw [add_assoc]
  ring

theorem product_error (h : ℝ) (z w : Frequency (X := X)) (f : Hilbert μ) :
    ‖operator μ h z (operator μ h w f)-operator μ h (z+w) f‖ ≤
      |h| * |w.1 z.2| * ‖f‖ := by
  rw [operator_product]
  have he : scalar (h*w.1 z.2) • operator μ h (z+w) f-operator μ h (z+w) f =
      (scalar (h*w.1 z.2)-1) • operator μ h (z+w) f := by rw [sub_smul,one_smul]
  rw [he,norm_smul,(operator μ h (z+w)).norm_map]
  exact mul_le_mul_of_nonneg_right
    ((scalar_sub_one (h*w.1 z.2)).trans_eq (abs_mul h (w.1 z.2))) (norm_nonneg f)

theorem commutator_bound (h : ℝ) (z w : Frequency (X := X)) (f : Hilbert μ) :
    ‖operator μ h z (operator μ h w f)-operator μ h w (operator μ h z f)‖ ≤
      |h| * (|w.1 z.2|+|z.1 w.2|) * ‖f‖ := by
  have hb := norm_sub_le_norm_sub_add_norm_sub (operator μ h z (operator μ h w f))
    (operator μ h (z+w) f) (operator μ h w (operator μ h z f))
  have hw := product_error μ h w z f
  rw [add_comm w z,norm_sub_rev] at hw
  exact hb.trans ((add_le_add (product_error μ h z w f) hw).trans_eq (by ring))

def characteristic (h : ℝ) (f : Hilbert μ) (z : Frequency (X := X)) : ℂ :=
  inner ℂ f (operator μ h z f)

theorem characteristic_bound (h : ℝ) (f : Hilbert μ) (z : Frequency (X := X)) :
    ‖characteristic μ h f z‖ ≤ ‖f‖^2 := by
  simpa only [characteristic,(operator μ h z).norm_map,pow_two] using
    norm_inner_le_norm (𝕜 := ℂ) f (operator μ h z f)

theorem gram_error (h : ℝ) (f : Hilbert μ) (z w : Frequency (X := X)) :
    ‖inner ℂ (operator μ h z f) (operator μ h w f)-characteristic μ h f (w-z)‖ ≤
      |h| * |(w.1-z.1) z.2| * ‖f‖^2 := by
  have he : characteristic μ h f (w-z) =
      inner ℂ (operator μ h z f) (operator μ h z (operator μ h (w-z) f)) :=
    ((operator μ h z).inner_map_map f (operator μ h (w-z) f)).symm
  rw [he,← inner_sub_right]
  have hb := product_error μ h z (w-z) f
  rw [show z+(w-z)=w by abel] at hb
  rw [norm_sub_rev] at hb
  calc
    _ ≤ ‖operator μ h z f‖*‖operator μ h w f-operator μ h z (operator μ h (w-z) f)‖ := norm_inner_le_norm _ _
    _ ≤ ‖f‖*(|h| * |(w.1-z.1) z.2| * ‖f‖) := by
      rw [(operator μ h z).norm_map]
      exact mul_le_mul_of_nonneg_left hb (norm_nonneg f)
    _ = _ := by ring

#print axioms scalar_add
#print axioms scalar_norm
#print axioms scalar_sub_one
#print axioms operator_coe
#print axioms operator_zero
#print axioms operator_product
#print axioms product_error
#print axioms commutator_bound
#print axioms characteristic_bound
#print axioms gram_error

end
end UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra
