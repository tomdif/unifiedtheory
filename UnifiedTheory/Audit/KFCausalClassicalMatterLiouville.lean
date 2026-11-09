/- The probability laws transported by the actual full classical matter
flow solve the weak Liouville equation for C1 compactly supported tests.
This establishes the classical target equation, not quantum convergence. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterLaw
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalClassicalMatterLiouville
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth (TimePhase)
open UnifiedTheory.Audit.KFCausalClassicalMatterODE
open UnifiedTheory.Audit.KFCausalClassicalMatterEvolution
open UnifiedTheory.Audit.KFCausalClassicalMatterLaw

def generator (ε m g κ : ℝ) (f : TimePhase → ℝ) (x : TimePhase) : ℝ :=
  fderiv ℝ f x (field ε m g κ x)

theorem generator_continuous (ε m g κ : ℝ) (hε : 0 ≤ ε)
    (f : TimePhase → ℝ) (hf : ContDiff ℝ 1 f) : Continuous (generator ε m g κ f) :=
  (hf.continuous_fderiv_apply (by norm_num)).comp
    (continuous_id.prodMk (field_contDiff ε m g κ hε).continuous)

theorem generator_hasCompactSupport (ε m g κ : ℝ) (f : TimePhase → ℝ)
    (hs : HasCompactSupport f) : HasCompactSupport (generator ε m g κ f) := by
  apply HasCompactSupport.intro hs.isCompact
  intro x hx
  simp only [generator,fderiv_of_notMem_tsupport ℝ hx,ContinuousLinearMap.zero_apply]

variable (ε m g κ : ℝ) (hε : 0 < ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 < κ)
local notation "Φ" => evolve ε m g κ hε hm hg hκ

theorem test_derivative (f : TimePhase → ℝ) (hf : ContDiff ℝ 1 f) (x : TimePhase) (t : ℝ) :
    HasDerivAt (fun u => f (Φ u x)) (generator ε m g κ f (Φ t x)) t := by
  exact ((hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt).comp_hasDerivAt t
    (evolve_derivative ε m g κ hε hm hg hκ x t)

theorem transport_liouville (μ : Measure TimePhase) [IsFiniteMeasure μ]
    (f : TimePhase → ℝ) (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) (t : ℝ) :
    HasDerivAt (fun u => ∫ x, f x ∂transport ε m g κ hε hm hg hκ μ u)
      (∫ x, generator ε m g κ f x ∂transport ε m g κ hε hm hg hκ μ t) t := by
  have hc := generator_continuous ε m g κ hε.le f hf
  obtain ⟨B,hB⟩ := hs.exists_bound_of_continuous hf.continuous
  obtain ⟨M,hM⟩ := (generator_hasCompactSupport ε m g κ f hs).exists_bound_of_continuous hc
  have hi : Integrable (fun x => f (Φ t x)) μ :=
    (integrable_const B).mono' (hf.continuous.comp
      (evolve_continuous_initial ε m g κ hε hm hg hκ t)).aestronglyMeasurable
      (Eventually.of_forall (fun x => hB (Φ t x)))
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun u x => f (Φ u x))
    (F' := fun u x => generator ε m g κ f (Φ u x)) (bound := fun _ => M)
    (s := Set.univ) (x₀ := t) (Filter.univ_mem)
    (Eventually.of_forall (fun u => (hf.continuous.comp
      (evolve_continuous_initial ε m g κ hε hm hg hκ u)).aestronglyMeasurable)) hi
    (hc.comp (evolve_continuous_initial ε m g κ hε hm hg hκ t)).aestronglyMeasurable
    (Eventually.of_forall (fun _ u _ => hM (Φ u _))) (integrable_const M)
    (Eventually.of_forall (fun x u _ => test_derivative ε m g κ hε hm hg hκ f hf x u))
  simp_rw [transport_integral ε m g κ hε hm hg hκ μ _ f hf.continuous,
    transport_integral ε m g κ hε hm hg hκ μ _ _ hc]
  exact hd.2

#print axioms generator_continuous
#print axioms generator_hasCompactSupport
#print axioms test_derivative
#print axioms transport_liouville

end
end UnifiedTheory.Audit.KFCausalClassicalMatterLiouville
