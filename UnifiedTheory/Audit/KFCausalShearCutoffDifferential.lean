/- Scaled smooth cutoffs for the physical linear shear. The derivative
error has a uniform bound independent of the cutoff scale and vanishes
at scale zero. This prepares actual closed-graph approximation. -/
import UnifiedTheory.Audit.KFCausalTransverseShearDifferential
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalShearCutoffDifferential
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (velocity)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalReconstruction (shearDerivative)

def vector (x : Configuration) : Configuration := (0,velocity x.2)

theorem vector_continuous : Continuous vector := by
  apply continuous_const.prodMk
  apply continuous_pi
  intro i
  simp only [velocity]
  split_ifs <;> fun_prop

theorem vector_smul (t : ℝ) (x : Configuration) : vector (t • x) = t • vector x := by
  apply Prod.ext
  · simp [vector]
  · funext i
    simp only [vector,Prod.smul_snd,velocity,Pi.smul_apply,smul_eq_mul]
    split_ifs <;> ring

def bump : ContDiffBump (0 : Configuration) := ⟨1,2,by norm_num,by norm_num⟩
def cutoff (x : Configuration) : ℂ := (bump x:ℝ)

theorem cutoff_smooth : ContDiff ℝ 1 cutoff := Complex.ofRealCLM.contDiff.comp bump.contDiff

theorem cutoff_compact : HasCompactSupport cutoff :=
  bump.hasCompactSupport.comp_left (show Complex.ofReal 0=0 from rfl)

theorem cutoff_norm (x : Configuration) : ‖cutoff x‖ ≤ 1 := by
  simpa only [cutoff,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg bump.nonneg] using
    (bump.le_one (x := x))

theorem cutoff_zero : cutoff 0 = 1 := by
  rw [cutoff,bump.one_of_mem_closedBall (by simp [bump])]
  rfl

def error (x : Configuration) : ℂ := (fderiv ℝ cutoff x) (vector x)

theorem error_continuous : Continuous error :=
  (cutoff_smooth.continuous_fderiv (by norm_num)).clm_apply vector_continuous

theorem error_compact : HasCompactSupport error := by
  apply cutoff_compact.mono'
  intro x hx
  by_contra hn
  exact hx (by simp only [error,fderiv_of_notMem_tsupport ℝ hn,ContinuousLinearMap.zero_apply])

theorem error_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖error x‖ ≤ M := by
  obtain ⟨B,hB⟩ := error_compact.exists_bound_of_continuousOn error_continuous.continuousOn
  refine ⟨max B 0,le_max_right _ _,?_⟩
  intro x
  by_cases hx : x ∈ tsupport error
  · exact (hB x hx).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx,norm_zero]
    exact le_max_right _ _

theorem error_zero : error 0 = 0 := by
  have hv : vector (0:Configuration) = 0 := by
    simpa only [zero_smul] using vector_smul 0 (0:Configuration)
  rw [error,hv,map_zero]

def cut (t : ℝ) (f : Configuration → ℂ) (x : Configuration) : ℂ := cutoff (t • x)*f x

theorem cut_smooth (t : ℝ) (f : Configuration → ℂ) (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (cut t f) := by
  have ht : ContDiff ℝ 1 (fun x : Configuration => t • x) :=
    (t • ContinuousLinearMap.id ℝ Configuration).contDiff
  exact (cutoff_smooth.comp ht).mul hf

theorem cut_compact (t : ℝ) (ht : t ≠ 0) (f : Configuration → ℂ) : HasCompactSupport (cut t f) :=
  (cutoff_compact.comp_homeomorph (Homeomorph.smulOfNeZero t ht)).mul_right

theorem cut_shear (t : ℝ) (f : Configuration → ℂ) (hf : Differentiable ℝ f) (x : Configuration) :
    shearDerivative (cut t f) x = cutoff (t • x)*shearDerivative f x+error (t • x)*f x := by
  have hd := ((cutoff_smooth.differentiable (by norm_num)) (t • x)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul t)
  have hp := hd.mul (hf x).hasFDerivAt
  change HasFDerivAt (cut t f) _ x at hp
  rw [shearDerivative,hp.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,smul_eq_mul]
  change cutoff (t • x)*(fderiv ℝ f x (vector x))+
    f x*(fderiv ℝ cutoff (t • x) (t • vector x))+cutoff (t • x)*f x = _
  rw [← vector_smul]
  unfold error shearDerivative
  change _ = cutoff (t • x)*(fderiv ℝ f x (vector x)+f x)+
    (fderiv ℝ cutoff (t • x) (vector (t • x)))*f x
  ring

#print axioms vector_continuous
#print axioms vector_smul
#print axioms cutoff_smooth
#print axioms cutoff_compact
#print axioms cutoff_norm
#print axioms cutoff_zero
#print axioms error_continuous
#print axioms error_compact
#print axioms error_bound
#print axioms error_zero
#print axioms cut_smooth
#print axioms cut_compact
#print axioms cut_shear
end
end UnifiedTheory.Audit.KFCausalShearCutoffDifferential
