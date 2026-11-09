/- Actual strong L2 derivatives of the imaginary-shear curve and its
first shear output. Uniform Gaussian majorants derive all required
derivatives. The second shear graph is constructed for the same vectors. -/
import UnifiedTheory.Audit.KFCausalGaussianSecondShearBounds
import UnifiedTheory.Audit.KFCausalIntervalL2Derivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalStrongImaginaryShearCurve
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalImaginaryShearInterpolation
open UnifiedTheory.Audit.KFCausalImaginaryShearPathBounds
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (Interval)
open UnifiedTheory.Audit.KFCausalGaussianSecondShearDifferential
open UnifiedTheory.Audit.KFCausalGaussianSecondShearBounds
open UnifiedTheory.Audit.KFCausalIntervalL2Derivative (curve curve_value clip)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalReconstruction (shearDerivative)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)

variable (A D : ℝ → ℂ) (hA : ContDiff ℝ 1 A) (hAm : MemLp A 2 volume)
variable (hD : ContDiff ℝ 1 D) (hDb : ∀ s, ‖D s‖ ≤ Real.pi/3)
variable (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (b : Fin 5 → ℂ)

def inputCurve : ℝ → Hilbert :=
  curve (path A D α β b) (path_memLp A D hA hAm hD hDb α β hα hβ hw b)

def firstCurve : ℝ → Hilbert :=
  curve (fun t => first (timeAmplitude A D t) (timeScale D t) α β b)
    (first_path_memLp A D hA hAm hD hDb α β hα hβ hw b)

def secondState (t : Interval) : Hilbert :=
  (second_path_memLp A D hA hAm hD hDb α β hα hβ hw b t t.property).toLp
    (second (timeAmplitude A D t) (timeScale D t) α β b)

include hA hAm hD hDb hα hβ hw in
theorem inputDerivative_memLp (t : Interval) :
    MemLp (fun x : Configuration => D x.1*first (timeAmplitude A D t) (timeScale D t) α β b x) 2 volume :=
  KFCausalShearPolynomialMoments.clock_mul_memLp D hD.continuous (Real.pi/3)
    (by positivity) hDb _ (first_path_memLp A D hA hAm hD hDb α β hα hβ hw b t t.property)

include hA hAm hD hDb hα hβ hw in
theorem firstDerivative_memLp (t : Interval) :
    MemLp (fun x : Configuration => D x.1*second (timeAmplitude A D t) (timeScale D t) α β b x) 2 volume :=
  KFCausalShearPolynomialMoments.clock_mul_memLp D hD.continuous (Real.pi/3)
    (by positivity) hDb _ (second_path_memLp A D hA hAm hD hDb α β hα hβ hw b t t.property)

def inputDerivative (t : Interval) : Hilbert :=
  (inputDerivative_memLp A D hA hAm hD hDb α β hα hβ hw b t).toLp _
def firstDerivative (t : Interval) : Hilbert :=
  (firstDerivative_memLp A D hA hAm hD hDb α β hα hβ hw b t).toLp _

theorem inputCurve_derivative (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (inputCurve A D hA hAm hD hDb α β hα hβ hw b)
      (inputDerivative A D hA hAm hD hDb α β hα hβ hw b ⟨t,ht.1.le,ht.2.le⟩) t := by
  apply KFCausalIntervalL2Derivative.strong_derivative
    (path A D α β b)
    (fun u x => D x.1*first (timeAmplitude A D u) (timeScale D u) α β b x)
    (path_memLp A D hA hAm hD hDb α β hα hβ hw b)
    (fun x => (Real.pi/3:ℝ)*firstEnvelope A α β b x)
    ((firstEnvelope_memLp A hAm α β hα hβ b).const_mul (Real.pi/3:ℝ))
    _ _ t ht (inputDerivative_memLp A D hA hAm hD hDb α β hα hβ hw b ⟨t,ht.1.le,ht.2.le⟩)
  · intro u _ x
    convert path_time_derivative A D α β b u x using 1
    unfold first path
    ring
  · intro u hu x
    have hb := mul_le_mul (hDb x.1) (first_path_bound A D hDb α β hα hβ hw b u hu x)
      (norm_nonneg _) (by positivity : 0 ≤ Real.pi/3)
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < Real.pi/3)] using hb

theorem firstCurve_derivative (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (firstCurve A D hA hAm hD hDb α β hα hβ hw b)
      (firstDerivative A D hA hAm hD hDb α β hα hβ hw b ⟨t,ht.1.le,ht.2.le⟩) t := by
  apply KFCausalIntervalL2Derivative.strong_derivative
    (fun u => first (timeAmplitude A D u) (timeScale D u) α β b)
    (fun u x => D x.1*second (timeAmplitude A D u) (timeScale D u) α β b x)
    (first_path_memLp A D hA hAm hD hDb α β hα hβ hw b)
    (fun x => (Real.pi/3:ℝ)*secondEnvelope A α β b x)
    ((secondEnvelope_memLp A hAm α β hα hβ b).const_mul (Real.pi/3:ℝ))
    (fun u _ x => first_time_derivative A D α β b u x) _ t ht
    (firstDerivative_memLp A D hA hAm hD hDb α β hα hβ hw b ⟨t,ht.1.le,ht.2.le⟩)
  intro u hu x
  have hb := mul_le_mul (hDb x.1) (second_path_bound A D hDb α β hα hβ hw b u hu x)
    (norm_nonneg _) (by positivity : 0 ≤ Real.pi/3)
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < Real.pi/3)] using hb

theorem inputCurve_continuous : Continuous (inputCurve A D hA hAm hD hDb α β hα hβ hw b) :=
  (KFCausalImaginaryShearPathDomain.state_continuous A D hA hAm hD hDb α β hα hβ hw b).comp
    (continuous_projIcc (h := zero_le_one))

theorem firstCurve_continuous : Continuous (firstCurve A D hA hAm hD hDb α β hα hβ hw b) := by
  apply KFCausalDominatedL2Continuity.continuous_toLp
    (fun t : ℝ => first (timeAmplitude A D (clip t)) (timeScale D (clip t)) α β b)
    (fun t => first_path_memLp A D hA hAm hD hDb α β hα hβ hw b (clip t) (clip t).property)
    (firstEnvelope A α β b) (firstEnvelope_memLp A hAm α β hα hβ b)
  · intro t
    exact Filter.Eventually.of_forall (first_path_bound A D hDb α β hα hβ hw b (clip t) (clip t).property)
  · filter_upwards [] with x
    have hc : Continuous (fun t : ℝ => first (timeAmplitude A D t) (timeScale D t) α β b x) :=
      (show Differentiable ℝ (fun t : ℝ => first (timeAmplitude A D t) (timeScale D t) α β b x) from
        fun t => (first_time_derivative A D α β b t x).differentiableAt).continuous
    exact hc.comp (continuous_subtype_val.comp (continuous_projIcc (h := zero_le_one)))

def outputCurve (h : ℝ) (t : ℝ) : Hilbert :=
  (-Complex.I*(h:ℂ)) • firstCurve A D hA hAm hD hDb α β hα hβ hw b t

theorem outputCurve_continuous (h : ℝ) :
    Continuous (outputCurve A D hA hAm hD hDb α β hα hβ hw b h) :=
  (firstCurve_continuous A D hA hAm hD hDb α β hα hβ hw b).const_smul _

theorem outputCurve_derivative (h t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (outputCurve A D hA hAm hD hDb α β hα hβ hw b h)
      ((-Complex.I*(h:ℂ)) • firstDerivative A D hA hAm hD hDb α β hα hβ hw b ⟨t,ht.1.le,ht.2.le⟩) t :=
  HasDerivAt.const_smul (-Complex.I*(h:ℂ)) (firstCurve_derivative A D hA hAm hD hDb α β hα hβ hw b t ht)

theorem input_graph (h : ℝ) (hh : h ≠ 0) (t : Interval) :
    (inputCurve A D hA hAm hD hDb α β hα hβ hw b t,
      outputCurve A D hA hAm hD hDb α β hα hβ hw b h t) ∈ (shearMomentum h).graph := by
  have he := first_eq_shear _ _ (timeAmplitude_smooth A D hA hD t) (timeScale_smooth D hD t) α β b
  change first (timeAmplitude A D t) (timeScale D t) α β b = shearDerivative (path A D α β b t) at he
  let hf := path_memLp A D hA hAm hD hDb α β hα hβ hw b t t.property
  let hfirst := first_path_memLp A D hA hAm hD hDb α β hα hβ hw b t t.property
  have hd : MemLp (shearDerivative (path A D α β b t)) 2 volume := by rw [← he]; exact hfirst
  have hp := hd.toLp_congr hfirst (Filter.Eventually.of_forall (fun x => congrFun he.symm x))
  have hg := KFCausalShearMaximalDifferential.graph_of_shear_differential h hh _
    (path_smooth A D hA hD α β b t) hf hd
  rw [hp] at hg
  simpa only [inputCurve,outputCurve,firstCurve,curve_value _ _ t t.property] using hg

theorem first_graph (h : ℝ) (hh : h ≠ 0) (t : Interval) :
    (firstCurve A D hA hAm hD hDb α β hα hβ hw b t,
      (-Complex.I*(h:ℂ)) • secondState A D hA hAm hD hDb α β hα hβ hw b t) ∈ (shearMomentum h).graph := by
  have he := first_shear _ _ (timeAmplitude_smooth A D hA hD t) (timeScale_smooth D hD t) α β b
  let hf := first_path_memLp A D hA hAm hD hDb α β hα hβ hw b t t.property
  let hsecond := second_path_memLp A D hA hAm hD hDb α β hα hβ hw b t t.property
  have hd : MemLp (shearDerivative (first (timeAmplitude A D t) (timeScale D t) α β b)) 2 volume := by
    rw [he]; exact hsecond
  have hp := hd.toLp_congr hsecond (Filter.Eventually.of_forall (fun x => congrFun he x))
  have hg := KFCausalShearMaximalDifferential.graph_of_shear_differential h hh _
    (first_smooth _ _ (timeAmplitude_smooth A D hA hD t) (timeScale_smooth D hD t) α β b) hf hd
  rw [hp] at hg
  simpa only [firstCurve,secondState,curve_value _ _ t t.property] using hg

theorem output_graph (h : ℝ) (hh : h ≠ 0) (t : Interval) :
    (outputCurve A D hA hAm hD hDb α β hα hβ hw b h t,
      (-Complex.I*(h:ℂ))^2 • secondState A D hA hAm hD hDb α β hα hβ hw b t) ∈ (shearMomentum h).graph := by
  have hg := (shearMomentum h).graph.smul_mem (-Complex.I*(h:ℂ))
    (first_graph A D hA hAm hD hDb α β hα hβ hw b h hh t)
  simpa only [Prod.smul_mk,smul_smul,← pow_two,outputCurve] using hg

#print axioms inputDerivative_memLp
#print axioms firstDerivative_memLp
#print axioms inputCurve_derivative
#print axioms firstCurve_derivative
#print axioms inputCurve_continuous
#print axioms firstCurve_continuous
#print axioms outputCurve_continuous
#print axioms outputCurve_derivative
#print axioms input_graph
#print axioms first_graph
#print axioms output_graph
end
end UnifiedTheory.Audit.KFCausalStrongImaginaryShearCurve
