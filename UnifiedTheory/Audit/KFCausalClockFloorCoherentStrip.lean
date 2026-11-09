/- Joint strip bounds for sheared Gaussians with arbitrary complex
transverse sources and real clock modulation. These analytic estimates
are not yet an identification with the physical charge-coordinate family. -/
import UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds
import UnifiedTheory.Audit.KFCausalClockFloorGaussianL1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalComplexClockChart (targetStrip)
open UnifiedTheory.Audit.KFCausalComplexClockInverse
open UnifiedTheory.Audit.KFCausalClockInverseStripBounds
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian (clockFactor third_strip_subset inverse_line_continuous)

def clockPhase (p : ℝ) (z : ℂ) : ℂ := Complex.exp ((p:ℂ)*Complex.I*z)

theorem clockPhase_bound (p : ℝ) (z : ℂ) (hz : |z.im| ≤ Real.pi/3) :
    ‖clockPhase p z‖ ≤ Real.exp (|p| *Real.pi/3) := by
  rw [clockPhase,Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,mul_one,sub_zero,add_zero,zero_sub]
  have h := mul_le_mul_of_nonneg_left hz (abs_nonneg p)
  have ha : -(p*z.im) ≤ |p| *|z.im| := by rw [← abs_mul]; exact neg_le_abs _
  nlinarith

def trial (ε a α β p : ℝ) (b : Fin 5 → ℂ) (q : ℂ) (x : Grouped) : ℂ :=
  clockPhase p (complexInverse ε q)*clockFactor a q*
    coherentPacket α β b (complexInverse ε q) x

def line (ε a α β p : ℝ) (b : Fin 5 → ℂ) (y : ℝ) (w : ℝ × Grouped) : ℂ :=
  trial ε a α β p b ((w.1:ℂ)+(y:ℂ)*Complex.I) w.2

def envelopeConstant (α β p : ℝ) (b : Fin 5 → ℂ) : ℝ :=
  Real.exp (|p| *Real.pi/3+sourceConstant α β b/2)

theorem trial_analytic (ε a α β p : ℝ) (b : Fin 5 → ℂ) (hε : 0 < ε)
    (x : Grouped) (q : ℂ) (hq : q ∈ targetStrip ε) :
    AnalyticAt ℂ (fun q => trial ε a α β p b q x) q := by
  have hi := complexInverse_analytic ε hε q hq
  have hc : AnalyticAt ℂ (clockPhase p) (complexInverse ε q) := by
    unfold clockPhase
    fun_prop
  have hp := (coherentPacket_analytic α β b x (complexInverse ε q)).comp hi
  exact ((hc.comp hi).mul (show AnalyticAt ℂ (clockFactor a) q by unfold clockFactor; fun_prop)).mul hp

theorem line_continuous (ε a α β p : ℝ) (b : Fin 5 → ℂ) (y : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) : Continuous (line ε a α β p b y) := by
  have hi := (inverse_line_continuous ε y hε hy).comp (continuous_fst (Y := Grouped))
  have hs : Continuous (fun w : ℝ × Grouped => source b (complexInverse ε ((w.1:ℂ)+(y:ℂ)*Complex.I)) w.2) := by
    unfold source
    apply continuous_finset_sum
    intro i _
    fin_cases i <;> dsimp [position,neutral,complexScale,mix] <;> fun_prop
  unfold line trial coherentPacket clockPhase clockFactor packet quadratic squared mix complexScale
  fun_prop

theorem line_bound (ε a α β p : ℝ) (b : Fin 5 → ℂ) (y : ℝ) (hε : 0 < ε)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3)
    (w : ℝ × Grouped) :
    ‖line ε a α β p b y w‖ ≤ envelopeConstant α β p b*
      ‖KFCausalClockFloorFullGaussian.line ε a (α/2) (β/2) y w‖ := by
  let q : ℂ := (w.1:ℂ)+(y:ℂ)*Complex.I
  have hz : |(complexInverse ε q).im| ≤ Real.pi/3 :=
    inverse_im_third_strip ε hε q (by simpa [q] using hy)
  have hc := clockPhase_bound p (complexInverse ε q) hz
  have hp := coherentPacket_bound α β hα hβ hw b (complexInverse ε q) hz w.2
  have hm := mul_le_mul hc hp (norm_nonneg _) (Real.exp_pos _).le
  have ht := mul_le_mul_of_nonneg_left hm (norm_nonneg (clockFactor a q))
  simpa only [line,trial,KFCausalClockFloorFullGaussian.line,KFCausalClockFloorFullGaussian.trial,
    envelopeConstant,Real.exp_add,norm_mul,mul_assoc,mul_left_comm,q] using ht

theorem line_memLp (ε a α β p : ℝ) (b : Fin 5 → ℂ) (y : ℝ) (hε : 0 < ε)
    (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) :
    MemLp (line ε a α β p b y) 2 := by
  have hl := KFCausalClockFloorFullGaussian.line_memLp ε a (α/2) (β/2) y hε ha
    (by positivity) (by positivity) (by linarith) hy
  apply (hl.const_mul ((envelopeConstant α β p b:ℝ):ℂ)).of_le
    (line_continuous ε a α β p b y hε hy).aestronglyMeasurable
  filter_upwards [] with w
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (show 0 < envelopeConstant α β p b from Real.exp_pos _)] using line_bound ε a α β p b y hε hα hβ hw hy w

theorem uniform_line_bound (ε a α β p P B : ℝ) (b : Fin 5 → ℂ) (y : ℝ) (hε : 0 < ε)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3)
    (hp : |p| ≤ P) (hb : sourceSize b ≤ B) (w : ℝ × Grouped) :
    ‖line ε a α β p b y w‖ ≤ Real.exp (P*Real.pi/3+B*positionConstant α β/2)*
      ‖KFCausalClockFloorFullGaussian.line ε a (α/2) (β/2) y w‖ := by
  have he : envelopeConstant α β p b ≤ Real.exp (P*Real.pi/3+B*positionConstant α β/2) := by
    unfold envelopeConstant sourceConstant
    apply Real.exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonneg_right hp Real.pi_pos.le
    have h2 := mul_le_mul_of_nonneg_right hb (positionConstant_positive α β hα hβ).le
    linarith
  exact (line_bound ε a α β p b y hε hα hβ hw hy w).trans
    (mul_le_mul_of_nonneg_right he (norm_nonneg _))

theorem line_integrable (ε a α β p : ℝ) (b : Fin 5 → ℂ) (y : ℝ) (hε : 0 < ε)
    (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) :
    Integrable (line ε a α β p b y) := by
  have hl := KFCausalClockFloorGaussianL1.line_integrable ε a (α/2) (β/2) y hε ha
    (by positivity) (by positivity) (by linarith) hy
  apply (hl.norm.const_mul (envelopeConstant α β p b)).mono'
    (line_continuous ε a α β p b y hε hy).aestronglyMeasurable
  exact Filter.Eventually.of_forall (line_bound ε a α β p b y hε hα hβ hw hy)

theorem quadratic_line_memLp (ε a α β p : ℝ) (b : Fin 5 → ℂ) (y : ℝ) (hε : 0 < ε)
    (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3)
    (l : KFCausalTransverseDilationFlow.Transverse →L[ℝ] ℝ) :
    MemLp (fun w : ℝ × Grouped => (KFCausalClockFloorFieldMoments.fieldLine ε hε l w:ℂ)^2*
      line ε a α β p b y w) 2 := by
  have hl := KFCausalClockFloorFieldMoments.quadratic_line_memLp ε a (α/2) (β/2) y hε ha
    (by positivity) (by positivity) (by linarith) hy l
  have hc : Continuous (fun w : ℝ × Grouped => (KFCausalClockFloorFieldMoments.fieldLine ε hε l w:ℂ)^2*
      line ε a α β p b y w) :=
    ((Complex.continuous_ofReal.comp (KFCausalClockFloorFieldMoments.fieldLine_continuous ε hε l)).pow 2).mul
      (line_continuous ε a α β p b y hε hy)
  apply (hl.const_mul ((envelopeConstant α β p b:ℝ):ℂ)).of_le hc.aestronglyMeasurable
  filter_upwards [] with w
  have h := mul_le_mul_of_nonneg_left (line_bound ε a α β p b y hε hα hβ hw hy w)
    (norm_nonneg ((KFCausalClockFloorFieldMoments.fieldLine ε hε l w:ℂ)^2))
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (show 0 < envelopeConstant α β p b from Real.exp_pos _),
    mul_assoc,mul_left_comm] using h

#print axioms clockPhase_bound
#print axioms trial_analytic
#print axioms line_continuous
#print axioms line_bound
#print axioms line_memLp
#print axioms uniform_line_bound
#print axioms line_integrable
#print axioms quadratic_line_memLp

end
end UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip
