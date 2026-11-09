/- Literal circle energy and its linked quadratic field response. Positivity
is derived from the affine cosine polynomial, and field differentiation
uses a genuine compact integrable majorant. -/
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalAngularMassCircle
noncomputable section
open MeasureTheory Filter Set
open scoped Topology

def integrand (z mu l theta : ℝ) : ℝ :=
  Real.exp (-z*Real.cos theta)*(mu+l*Real.cos theta)^2

def fieldIntegrand (z mu l theta : ℝ) : ℝ :=
  Real.exp (-z*Real.cos theta)*(2*Real.cos theta*(mu+l*Real.cos theta))

def defectIntegrand (z mu l theta : ℝ) : ℝ :=
  (-2*z*Real.cos theta)*integrand z mu l theta-l*fieldIntegrand z mu l theta

def energy (z mu l : ℝ) : ℝ := ∫ theta in 0..(2*Real.pi), integrand z mu l theta

def fieldSlope (z mu l : ℝ) : ℝ := ∫ theta in 0..(2*Real.pi), fieldIntegrand z mu l theta

def tilt (z mu l : ℝ) : ℝ :=
  ∫ theta in 0..(2*Real.pi), (-z*Real.cos theta)*integrand z mu l theta

def defect (z mu l : ℝ) : ℝ := ∫ theta in 0..(2*Real.pi), defectIntegrand z mu l theta

private theorem circle_pos : (0:ℝ)<2*Real.pi := by positivity

private theorem continuous_integrand :
    Continuous (fun p : (ℝ×ℝ×ℝ)×ℝ => integrand p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  unfold integrand
  fun_prop

private theorem continuous_defect :
    Continuous (fun p : (ℝ×ℝ×ℝ)×ℝ => defectIntegrand p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  unfold defectIntegrand integrand fieldIntegrand
  fun_prop

private theorem compact_integral_eq (f : ℝ→ℝ) :
    (∫ theta in Icc 0 (2*Real.pi), f theta)=∫ theta in 0..(2*Real.pi), f theta := by
  rw [integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le circle_pos.le]

theorem energy_integrable (z mu l : ℝ) :
    IntervalIntegrable (integrand z mu l) volume 0 (2*Real.pi) := by
  exact (by unfold integrand; fun_prop : Continuous (integrand z mu l)).intervalIntegrable _ _

theorem energy_continuous :
    Continuous (fun p : ℝ×ℝ×ℝ => energy p.1 p.2.1 p.2.2) := by
  have hh := continuous_parametric_integral_of_continuous
    (μ := volume) (f := fun (p : ℝ×ℝ×ℝ) theta => integrand p.1 p.2.1 p.2.2 theta) continuous_integrand (isCompact_Icc : IsCompact (Icc (0:ℝ) (2*Real.pi)))
  simpa only [compact_integral_eq,energy] using hh

theorem defect_continuous :
    Continuous (fun p : ℝ×ℝ×ℝ => defect p.1 p.2.1 p.2.2) := by
  have hh := continuous_parametric_integral_of_continuous
    (μ := volume) (f := fun (p : ℝ×ℝ×ℝ) theta => defectIntegrand p.1 p.2.1 p.2.2 theta) continuous_defect (isCompact_Icc : IsCompact (Icc (0:ℝ) (2*Real.pi)))
  simpa only [compact_integral_eq,defect] using hh

theorem energy_nonnegative (z mu l : ℝ) : 0≤energy z mu l := by
  apply intervalIntegral.integral_nonneg circle_pos.le
  intro theta _
  unfold integrand
  positivity

theorem energy_positive (z mu l : ℝ) (hne : mu≠0 ∨ l≠0) : 0<energy z mu l := by
  have hc : Continuous (integrand z mu l) := by unfold integrand; fun_prop
  have hh := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    circle_pos continuous_const.continuousOn hc.continuousOn
    (fun theta _ => show (0:ℝ) ≤ integrand z mu l theta by unfold integrand; positivity) ?_
  · simpa only [intervalIntegral.integral_zero,energy] using hh
  · by_cases hs : mu+l=0
    · refine ⟨Real.pi,⟨Real.pi_pos.le,by linarith [Real.pi_pos]⟩,?_⟩
      have hn : mu-l≠0 := by
        intro he
        have hm : mu=0 := by linarith
        have hl : l=0 := by linarith
        exact hne.elim (fun h => h hm) (fun h => h hl)
      simp only [integrand,Real.cos_pi,mul_neg_one,← sub_eq_add_neg]
      exact mul_pos (Real.exp_pos _) ((by decide : Even 2).pow_pos hn)
    · refine ⟨0,⟨le_rfl,circle_pos.le⟩,?_⟩
      simp only [integrand,Real.cos_zero,mul_one]
      exact mul_pos (Real.exp_pos _) ((by decide : Even 2).pow_pos hs)

theorem energy_scale (z mu l c : ℝ) :
    energy z (c*mu) (c*l)=c^2*energy z mu l := by
  unfold energy
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro theta _
  unfold integrand
  ring

theorem defect_scale (z mu l c : ℝ) :
    defect z (c*mu) (c*l)=c^2*defect z mu l := by
  unfold defect
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro theta _
  unfold defectIntegrand integrand fieldIntegrand
  ring

theorem field_derivative (z mu l : ℝ) :
    HasDerivAt (fun x => energy z mu x) (fieldSlope z mu l) l := by
  let F : ℝ→ℝ→ℝ := fun x theta => integrand z mu x theta
  let F' : ℝ→ℝ→ℝ := fun x theta => fieldIntegrand z mu x theta
  have hF'c : Continuous F'.uncurry := by dsimp [F',fieldIntegrand]; fun_prop
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image
    (K := Icc (l-1) (l+1) ×ˢ Icc (0:ℝ) (2*Real.pi)) hF'c.norm.continuousOn
  have hFc1 (x : ℝ) : Continuous (F x) := by dsimp [F,integrand]; fun_prop
  have hF'c1 (x : ℝ) : Continuous (F' x) := by dsimp [F',fieldIntegrand]; fun_prop
  have hi : Integrable (F l) (volume.restrict (Icc 0 (2*Real.pi))) :=
    (hFc1 l).integrableOn_Icc
  have hmeas : ∀ᶠ x in 𝓝 l,
      AEStronglyMeasurable (F x) (volume.restrict (Icc 0 (2*Real.pi))) :=
    Eventually.of_forall (fun x => (hFc1 x).aestronglyMeasurable)
  have hbound : ∀ᵐ theta ∂volume.restrict (Icc 0 (2*Real.pi)),
      ∀ x ∈ Icc (l-1) (l+1), ‖F' x theta‖ ≤ M := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [] with theta htheta x hx
    exact hM ⟨(x,theta),⟨hx,htheta⟩,rfl⟩
  have hdiff : ∀ᵐ theta ∂volume.restrict (Icc 0 (2*Real.pi)),
      ∀ x ∈ Icc (l-1) (l+1), HasDerivAt (fun t => F t theta) (F' x theta) x := by
    filter_upwards [] with theta x _
    have hh := (((hasDerivAt_id x).mul_const (Real.cos theta)).const_add mu).pow 2
    have ht := hh.const_mul (Real.exp (-z*Real.cos theta))
    convert ht using 1
    dsimp [F,F',integrand,fieldIntegrand]
    ring
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Icc (0:ℝ) (2*Real.pi))) (x₀ := l)
    (F := F) (F' := F') (bound := fun _ => M)
    (s := Icc (l-1) (l+1)) (Icc_mem_nhds (by linarith) (by linarith))
    hmeas hi (hF'c1 l).aestronglyMeasurable hbound
    (integrableOn_const isCompact_Icc.measure_ne_top) hdiff
  simpa only [F,F',compact_integral_eq,energy,fieldSlope] using hd.2

theorem defect_eq (z mu l : ℝ) : defect z mu l=2*tilt z mu l-l*fieldSlope z mu l := by
  have h1 : IntervalIntegrable
      (fun theta => (-2*z*Real.cos theta)*integrand z mu l theta) volume 0 (2*Real.pi) :=
    (by unfold integrand; fun_prop : Continuous _).intervalIntegrable _ _
  have h2 : IntervalIntegrable
      (fun theta => l*fieldIntegrand z mu l theta) volume 0 (2*Real.pi) :=
    (by unfold fieldIntegrand; fun_prop : Continuous _).intervalIntegrable _ _
  unfold defect defectIntegrand
  rw [intervalIntegral.integral_sub h1 h2,intervalIntegral.integral_const_mul]
  congr 1
  unfold tilt
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro theta _
  ring

#print axioms energy_integrable
#print axioms energy_continuous
#print axioms defect_continuous
#print axioms energy_nonnegative
#print axioms energy_positive
#print axioms energy_scale
#print axioms defect_scale
#print axioms field_derivative
#print axioms defect_eq
end
end UnifiedTheory.Audit.KFCausalAngularMassCircle
