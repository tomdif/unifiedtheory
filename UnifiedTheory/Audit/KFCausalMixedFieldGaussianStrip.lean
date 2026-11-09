/- Joint L1 and L2 estimates for a field polynomial and Gaussian at
different imaginary clock shifts. The two field powers are precisely
those needed by the linear and quadratic matter reverse products. -/
import UnifiedTheory.Audit.KFCausalMixedFieldGaussianBounds
import UnifiedTheory.Audit.KFCausalClockFloorGaussianL1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalMixedFieldGaussianStrip
noncomputable section
open MeasureTheory
open KFCausalClockFloorShearBounds (Grouped packet quadratic)
open KFCausalMixedFieldGaussianBounds
open KFCausalComplexClockChart (targetStrip)
open KFCausalComplexClockInverse
open KFCausalClockInverseStripBounds (inverse_im_third_strip)
open KFCausalClockFloorFullGaussian (third_strip_subset inverse_line_continuous clockFactor)

def ratioBound (ε δ : ℝ) : ℝ := Real.exp (|δ|/ε)
def degree (j : Fin 2) : ℕ := 2*(j.val+1)
def reducedWidth (a : ℝ) : Fin 2 → ℝ := ![a/2,a/4]
def boundConstant (α β M : ℝ) : Fin 2 → ℝ :=
  ![2*momentConstant α β M,4*momentConstant α β M*momentConstant (α/2) (β/2) M]

theorem inverse_exp_compare (ε δ : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : q ∈ targetStrip ε) (hr : q+(δ:ℂ)*Complex.I ∈ targetStrip ε) :
    Real.exp (complexInverse ε q).re ≤
      ratioBound ε δ*Real.exp (complexInverse ε (q+(δ:ℂ)*Complex.I)).re := by
  have hb := complexInverse_norm_bound ε hε q (q+(δ:ℂ)*Complex.I) hq hr
  have he : ‖q-(q+(δ:ℂ)*Complex.I)‖ = |δ| := by
    rw [show q-(q+(δ:ℂ)*Complex.I) = -((δ:ℂ)*Complex.I) by ring,norm_neg,norm_mul]
    simp [Complex.norm_real,Real.norm_eq_abs]
  rw [he] at hb
  have hr' := (le_abs_self (complexInverse ε q-complexInverse ε (q+(δ:ℂ)*Complex.I)).re).trans
    (Complex.abs_re_le_norm _)
  simp only [Complex.sub_re] at hr'
  have h := Real.exp_le_exp.mpr
    (show (complexInverse ε q).re ≤ |δ|/ε+(complexInverse ε (q+(δ:ℂ)*Complex.I)).re by linarith)
  simpa only [Real.exp_add,ratioBound] using h

theorem reduced_positive (a : ℝ) (ha : 0 < a) (j : Fin 2) : 0 < reducedWidth a j := by
  fin_cases j <;> dsimp [reducedWidth] <;> positivity

theorem reduced_width_bound (α β : ℝ) (hw : 32*β ≤ α) (j : Fin 2) :
    32*reducedWidth β j ≤ reducedWidth α j := by
  fin_cases j <;> dsimp [reducedWidth] <;> linarith

theorem boundConstant_nonnegative (α β M : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hM : 0 ≤ M) (j : Fin 2) : 0 ≤ boundConstant α β M j := by
  have h0 := momentConstant_nonnegative α β M hα hβ hM
  have h1 := momentConstant_nonnegative (α/2) (β/2) M (by positivity) (by positivity) hM
  fin_cases j <;> dsimp [boundConstant] <;> positivity

theorem field_packet_bound (α β M : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hM : 0 ≤ M) (z v : ℂ) (hv : |v.im| ≤ Real.pi/3)
    (hzv : Real.exp z.re ≤ M*Real.exp v.re) (x : Grouped) (j : Fin 2) :
    ‖field z x^degree j*packet α β v x‖ ≤
      boundConstant α β M j*‖packet (reducedWidth α j) (reducedWidth β j) v x‖ := by
  fin_cases j
  · exact quadratic_packet_bound α β M hα hβ hw hM z v hv hzv x
  · exact quartic_packet_bound α β M hα hβ hw hM z v hv hzv x

def trial (ε a α β δ : ℝ) (j : Fin 2) (q : ℂ) (x : Grouped) : ℂ :=
  field (complexInverse ε q) x^degree j*
    KFCausalClockFloorFullGaussian.trial ε a α β (q+(δ:ℂ)*Complex.I) x

def line (ε a α β δ y : ℝ) (j : Fin 2) (w : ℝ × Grouped) : ℂ :=
  trial ε a α β δ j ((w.1:ℂ)+(y:ℂ)*Complex.I) w.2

def fieldLine (ε y : ℝ) (w : ℝ × Grouped) : ℂ :=
  field (complexInverse ε ((w.1:ℂ)+(y:ℂ)*Complex.I)) w.2

theorem vertical_add (s y δ : ℝ) :
    ((s:ℂ)+(y:ℂ)*Complex.I)+(δ:ℂ)*Complex.I =
      (s:ℂ)+((y+δ:ℝ):ℂ)*Complex.I := by push_cast; ring

theorem line_formula (ε a α β δ y : ℝ) (j : Fin 2) (w : ℝ × Grouped) :
    line ε a α β δ y j w = fieldLine ε y w^degree j*
      KFCausalClockFloorFullGaussian.line ε a α β (y+δ) w := by
  unfold line trial fieldLine KFCausalClockFloorFullGaussian.line
  rw [vertical_add]

theorem trial_analytic (ε a α β δ : ℝ) (hε : 0 < ε) (j : Fin 2) (x : Grouped)
    (q : ℂ) (hq : q ∈ targetStrip ε) (hr : q+(δ:ℂ)*Complex.I ∈ targetStrip ε) :
    AnalyticAt ℂ (fun q => trial ε a α β δ j q x) q := by
  have hf := (field_analytic x (complexInverse ε q)).comp (complexInverse_analytic ε hε q hq)
  have hg := (KFCausalClockFloorFullGaussian.trial_analytic ε a α β hε x
    (q+(δ:ℂ)*Complex.I) hr).comp (f := fun z : ℂ => z+(δ:ℂ)*Complex.I)
      (show AnalyticAt ℂ (fun q : ℂ => q+(δ:ℂ)*Complex.I) q by fun_prop)
  exact (hf.pow (degree j)).mul hg

theorem fieldLine_continuous (ε y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Continuous (fieldLine ε y) := by
  have hi := (inverse_line_continuous ε y hε hy).comp (continuous_fst (Y := Grouped))
  unfold fieldLine field KFCausalClockFloorShearBounds.complexScale KFCausalClockFloorShearBounds.mix
  fun_prop

theorem line_continuous (ε a α β δ y : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (hyr : |y+δ| ≤ Real.pi*ε/3) (j : Fin 2) :
    Continuous (line ε a α β δ y j) := by
  have he : line ε a α β δ y j = fun w => fieldLine ε y w^degree j*
      KFCausalClockFloorFullGaussian.line ε a α β (y+δ) w :=
    funext (line_formula ε a α β δ y j)
  rw [he]
  exact ((fieldLine_continuous ε y hε hy).pow _).mul
    (KFCausalClockFloorFullGaussian.line_continuous ε a α β (y+δ) hε hyr)

theorem line_bound (ε a α β δ y : ℝ) (hε : 0 < ε) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) (hyr : |y+δ| ≤ Real.pi*ε/3)
    (j : Fin 2) (w : ℝ × Grouped) :
    ‖line ε a α β δ y j w‖ ≤ boundConstant α β (ratioBound ε δ) j*
      ‖KFCausalClockFloorFullGaussian.line ε a (reducedWidth α j) (reducedWidth β j) (y+δ) w‖ := by
  let q : ℂ := (w.1:ℂ)+(y:ℂ)*Complex.I
  have hq : q ∈ targetStrip ε := third_strip_subset ε hε q (by simpa [q] using hy)
  have hr : q+(δ:ℂ)*Complex.I ∈ targetStrip ε := by
    dsimp [q]
    rw [vertical_add]
    exact third_strip_subset ε hε _ (by simpa using hyr)
  have hi : |(complexInverse ε (q+(δ:ℂ)*Complex.I)).im| ≤ Real.pi/3 := by
    apply inverse_im_third_strip ε hε
    simpa [q] using hyr
  have hb := field_packet_bound α β (ratioBound ε δ) hα hβ hw
    (Real.exp_pos _).le (complexInverse ε q) (complexInverse ε (q+(δ:ℂ)*Complex.I))
    hi (inverse_exp_compare ε δ hε q hq hr) w.2 j
  have hc := mul_le_mul_of_nonneg_left hb (norm_nonneg (clockFactor a (q+(δ:ℂ)*Complex.I)))
  dsimp [q] at hc
  rw [vertical_add] at hc
  simpa only [line_formula,fieldLine,KFCausalClockFloorFullGaussian.line,
    KFCausalClockFloorFullGaussian.trial,norm_mul,norm_pow,mul_assoc,mul_left_comm] using hc

theorem line_memLp (ε a α β δ y : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α)
    (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3)
    (hyr : |y+δ| ≤ Real.pi*ε/3) (j : Fin 2) : MemLp (line ε a α β δ y j) 2 volume := by
  have hm := KFCausalClockFloorFullGaussian.line_memLp ε a (reducedWidth α j) (reducedWidth β j)
    (y+δ) hε ha (reduced_positive α hα j) (reduced_positive β hβ j) (reduced_width_bound α β hw j) hyr
  have hC := boundConstant_nonnegative α β (ratioBound ε δ) hα hβ (Real.exp_pos _).le j
  apply (hm.const_mul ((boundConstant α β (ratioBound ε δ) j:ℝ):ℂ)).of_le
    (line_continuous ε a α β δ y hε hy hyr j).aestronglyMeasurable
  filter_upwards [] with w
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC] using
    line_bound ε a α β δ y hε hα hβ hw hy hyr j w

theorem line_integrable (ε a α β δ y : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α)
    (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3)
    (hyr : |y+δ| ≤ Real.pi*ε/3) (j : Fin 2) : Integrable (line ε a α β δ y j) volume := by
  have hi := KFCausalClockFloorGaussianL1.line_integrable ε a (reducedWidth α j) (reducedWidth β j)
    (y+δ) hε ha (reduced_positive α hα j) (reduced_positive β hβ j) (reduced_width_bound α β hw j) hyr
  apply (hi.norm.const_mul (boundConstant α β (ratioBound ε δ) j)).mono'
    (line_continuous ε a α β δ y hε hy hyr j).aestronglyMeasurable
  exact Filter.Eventually.of_forall (line_bound ε a α β δ y hε hα hβ hw hy hyr j)

#print axioms inverse_exp_compare
#print axioms reduced_positive
#print axioms reduced_width_bound
#print axioms boundConstant_nonnegative
#print axioms field_packet_bound
#print axioms vertical_add
#print axioms line_formula
#print axioms trial_analytic
#print axioms fieldLine_continuous
#print axioms line_continuous
#print axioms line_bound
#print axioms line_memLp
#print axioms line_integrable
end
end UnifiedTheory.Audit.KFCausalMixedFieldGaussianStrip
