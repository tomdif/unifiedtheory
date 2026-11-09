/- Mixed clock shifts for physical field powers and arbitrary coherent
sources. Source absorption and the existing mixed Gaussian field bounds
derive joint L1/L2 control; no second operator domain is assumed. -/
import UnifiedTheory.Audit.KFCausalMixedFieldGaussianStrip
import UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalMixedFieldCoherentStrip
noncomputable section
open MeasureTheory
open KFCausalClockFloorShearBounds (Grouped)
open KFCausalMixedFieldGaussianStrip (degree reducedWidth boundConstant ratioBound fieldLine vertical_add)
open KFCausalClockFloorCoherentStrip (envelopeConstant)
open KFCausalComplexClockChart (targetStrip)
open KFCausalComplexClockInverse
open KFCausalClockFloorFullGaussian (third_strip_subset)

def trial (ε a α β δ p : ℝ) (b : Fin 5 → ℂ) (j : Fin 2) (q : ℂ) (x : Grouped) : ℂ :=
  KFCausalMixedFieldGaussianBounds.field (complexInverse ε q) x^degree j*
    KFCausalClockFloorCoherentStrip.trial ε a α β p b (q+(δ:ℂ)*Complex.I) x
def line (ε a α β δ p : ℝ) (b : Fin 5 → ℂ) (y : ℝ) (j : Fin 2) (w : ℝ × Grouped) : ℂ :=
  trial ε a α β δ p b j ((w.1:ℂ)+(y:ℂ)*Complex.I) w.2
def envelope (ε α β δ p : ℝ) (b : Fin 5 → ℂ) (j : Fin 2) : ℝ :=
  envelopeConstant α β p b*boundConstant (α/2) (β/2) (ratioBound ε δ) j

theorem envelope_nonnegative (ε α β δ p : ℝ) (b : Fin 5 → ℂ)
    (hα : 0 < α) (hβ : 0 < β) (j : Fin 2) : 0 ≤ envelope ε α β δ p b j :=
  mul_nonneg (Real.exp_pos _).le
    (KFCausalMixedFieldGaussianStrip.boundConstant_nonnegative (α/2) (β/2) (ratioBound ε δ)
      (by positivity) (by positivity) (Real.exp_pos _).le j)

theorem line_formula (ε a α β δ p : ℝ) (b : Fin 5 → ℂ) (y : ℝ) (j : Fin 2) (w : ℝ × Grouped) :
    line ε a α β δ p b y j w = fieldLine ε y w^degree j*
      KFCausalClockFloorCoherentStrip.line ε a α β p b (y+δ) w := by
  unfold line trial fieldLine KFCausalClockFloorCoherentStrip.line
  rw [vertical_add]

theorem trial_analytic (ε a α β δ p : ℝ) (b : Fin 5 → ℂ) (hε : 0 < ε)
    (j : Fin 2) (x : Grouped) (q : ℂ) (hq : q ∈ targetStrip ε) (hr : q+(δ:ℂ)*Complex.I ∈ targetStrip ε) :
    AnalyticAt ℂ (fun q => trial ε a α β δ p b j q x) q := by
  have hf := (KFCausalMixedFieldGaussianBounds.field_analytic x (complexInverse ε q)).comp
    (complexInverse_analytic ε hε q hq)
  have hg := (KFCausalClockFloorCoherentStrip.trial_analytic ε a α β p b hε x
    (q+(δ:ℂ)*Complex.I) hr).comp (f := fun z : ℂ => z+(δ:ℂ)*Complex.I)
      (show AnalyticAt ℂ (fun q : ℂ => q+(δ:ℂ)*Complex.I) q by fun_prop)
  exact (hf.pow (degree j)).mul hg

theorem line_continuous (ε a α β δ p : ℝ) (b : Fin 5 → ℂ) (y : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (hyr : |y+δ| ≤ Real.pi*ε/3) (j : Fin 2) :
    Continuous (line ε a α β δ p b y j) := by
  have he : line ε a α β δ p b y j = fun w => fieldLine ε y w^degree j*
      KFCausalClockFloorCoherentStrip.line ε a α β p b (y+δ) w :=
    funext (line_formula ε a α β δ p b y j)
  rw [he]
  exact ((KFCausalMixedFieldGaussianStrip.fieldLine_continuous ε y hε hy).pow _).mul
    (KFCausalClockFloorCoherentStrip.line_continuous ε a α β p b (y+δ) hε hyr)

theorem line_bound (ε a α β δ p : ℝ) (b : Fin 5 → ℂ) (y : ℝ) (hε : 0 < ε)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3)
    (hyr : |y+δ| ≤ Real.pi*ε/3) (j : Fin 2) (w : ℝ × Grouped) :
    ‖line ε a α β δ p b y j w‖ ≤ envelope ε α β δ p b j*
      ‖KFCausalClockFloorFullGaussian.line ε a (reducedWidth (α/2) j) (reducedWidth (β/2) j) (y+δ) w‖ := by
  have hc := mul_le_mul_of_nonneg_left
    (KFCausalClockFloorCoherentStrip.line_bound ε a α β p b (y+δ) hε hα hβ hw hyr w)
    (norm_nonneg (fieldLine ε y w^degree j))
  have hg := mul_le_mul_of_nonneg_left
    (KFCausalMixedFieldGaussianStrip.line_bound ε a (α/2) (β/2) δ y hε
      (by positivity) (by positivity) (by linarith) hy hyr j w)
    (Real.exp_pos (|p| * Real.pi/3+KFCausalClockFloorCoherentBounds.sourceConstant α β b/2)).le
  rw [line_formula,norm_mul]
  apply hc.trans
  simpa only [KFCausalMixedFieldGaussianStrip.line_formula,norm_mul,mul_assoc,mul_left_comm,
    envelope,envelopeConstant] using hg

theorem line_memLp (ε a α β δ p : ℝ) (b : Fin 5 → ℂ) (y : ℝ) (hε : 0 < ε)
    (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) (hyr : |y+δ| ≤ Real.pi*ε/3) (j : Fin 2) :
    MemLp (line ε a α β δ p b y j) 2 volume := by
  have hm := KFCausalClockFloorFullGaussian.line_memLp ε a (reducedWidth (α/2) j) (reducedWidth (β/2) j)
    (y+δ) hε ha (KFCausalMixedFieldGaussianStrip.reduced_positive _ (by positivity) j)
    (KFCausalMixedFieldGaussianStrip.reduced_positive _ (by positivity) j)
    (KFCausalMixedFieldGaussianStrip.reduced_width_bound _ _ (by linarith) j) hyr
  have hC := envelope_nonnegative ε α β δ p b hα hβ j
  apply (hm.const_mul (envelope ε α β δ p b j:ℂ)).of_le
    (line_continuous ε a α β δ p b y hε hy hyr j).aestronglyMeasurable
  filter_upwards [] with w
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC] using
    line_bound ε a α β δ p b y hε hα hβ hw hy hyr j w

theorem line_integrable (ε a α β δ p : ℝ) (b : Fin 5 → ℂ) (y : ℝ) (hε : 0 < ε)
    (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) (hyr : |y+δ| ≤ Real.pi*ε/3) (j : Fin 2) :
    Integrable (line ε a α β δ p b y j) := by
  have hi := KFCausalClockFloorGaussianL1.line_integrable ε a (reducedWidth (α/2) j) (reducedWidth (β/2) j)
    (y+δ) hε ha (KFCausalMixedFieldGaussianStrip.reduced_positive _ (by positivity) j)
    (KFCausalMixedFieldGaussianStrip.reduced_positive _ (by positivity) j)
    (KFCausalMixedFieldGaussianStrip.reduced_width_bound _ _ (by linarith) j) hyr
  apply (hi.norm.const_mul (envelope ε α β δ p b j)).mono'
    (line_continuous ε a α β δ p b y hε hy hyr j).aestronglyMeasurable
  exact Filter.Eventually.of_forall (line_bound ε a α β δ p b y hε hα hβ hw hy hyr j)

#print axioms envelope_nonnegative
#print axioms line_formula
#print axioms trial_analytic
#print axioms line_continuous
#print axioms line_bound
#print axioms line_memLp
#print axioms line_integrable
end
end UnifiedTheory.Audit.KFCausalMixedFieldCoherentStrip
