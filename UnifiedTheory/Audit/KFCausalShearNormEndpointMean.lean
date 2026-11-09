/- The initial tangent bound for squared norms passes from actual finite
Gaussian shear paths to their closed endpoint span and Bochner means.
Bounded clock multipliers are allowed; field multipliers are not assumed bounded. -/
import UnifiedTheory.Audit.KFCausalShearEndpointMean
import UnifiedTheory.Audit.KFCausalImaginaryShearNormConvexity

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalShearNormEndpointMean
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalShearEndpointMean
  (Endpoints endpoint nonnegative_on_closed_span integral_mem_closed_span)
open UnifiedTheory.Audit.KFCausalImaginaryShearSuperposition
  (Seed sumInput sumShear sumSecond input_continuous shear_continuous input_derivative
    shear_derivative input_graph shear_graph)
open UnifiedTheory.Audit.KFCausalActualImaginaryShearCurve (coefficientOperator coefficientOperator_coe)
open UnifiedTheory.Audit.KFCausalImaginaryShearCoefficient (coefficient)
open UnifiedTheory.Audit.KFCausalImaginaryShearNormConvexity (tangent_monotone initial_tangent_lower tangent)
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (Interval)
open UnifiedTheory.Audit.KFCausalClockShearPositiveVariation (clock_commute)
open UnifiedTheory.Audit.KFCausalClockShearRealMultiplier (clock_graph)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

variable (ε h : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3) (hh : h ≠ 0)
local notation "C" => coefficientOperator ε h hε hb hh

def gap (W : Hilbert →L[ℂ] Hilbert) (x : Endpoints) : ℝ :=
  ‖W x.2.1‖^2-‖W x.1.1‖^2-2*(inner ℂ (W x.1.1) (C (W x.1.2))).re

theorem gap_continuous (W : Hilbert →L[ℂ] Hilbert) : Continuous (gap ε h hε hb hh W) := by
  unfold gap
  fun_prop

variable (W : Hilbert →L[ℂ] Hilbert) (w : ℝ → ℂ)
  (hW : ∀ f : Hilbert, W f =ᵐ[volume] fun x => w x.1*f x)

include hW in
theorem finite_gap (n : ℕ) (s : Fin n → Seed) (z : Fin n → ℂ) :
    0 ≤ gap ε h hε hb hh W (∑ i, z i • endpoint ε h hε hb (s i)) := by
  let U := sumInput ε h hε hb s z
  let J := sumShear ε h hε hb s z
  let K := sumSecond ε h hε hb s z
  have hc (f : Hilbert) : W (C f) = C (W f) :=
    clock_commute C W (coefficient ε h) w (coefficientOperator_coe ε h hε hb hh) hW f
  have hU : Continuous (fun t => W (U t)) := W.continuous.comp (input_continuous ε h hε hb s z)
  have hJ : Continuous (fun t => W (J t)) := W.continuous.comp (shear_continuous ε h hε hb s z)
  have hdU (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      HasDerivAt (fun r => W (U r)) (C (W (J t))) t := by
    have he := (W.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (input_derivative ε h hε hb s z hh t ht)
    change HasDerivAt (fun r => W (U r)) (W (C (J t))) t at he
    rw [hc] at he
    exact he
  have hdJ (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      HasDerivAt (fun r => W (J r)) (C (W (K ⟨t,ht.1.le,ht.2.le⟩))) t := by
    have he := (W.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (shear_derivative ε h hε hb s z hh t ht)
    change HasDerivAt (fun r => W (J r)) (W (C (K ⟨t,ht.1.le,ht.2.le⟩))) t at he
    rw [hc] at he
    exact he
  have hgU (t : Interval) : (W (U t),W (J t)) ∈
      (KFCausalTransverseShearMomentum.shearMomentum h).graph :=
    clock_graph W w hW h hh _ _ (input_graph ε h hε hb s z hh t)
  have hgJ (t : Interval) : (W (J t),W (K t)) ∈
      (KFCausalTransverseShearMomentum.shearMomentum h).graph :=
    clock_graph W w hW h hh _ _ (shear_graph ε h hε hb s z hh t)
  have hm := tangent_monotone C (coefficient ε h) (coefficientOperator_coe ε h hε hb hh)
    h hh _ _ (fun t => W (K t)) hU hJ hdU hdJ hgU hgJ
  have he := initial_tangent_lower C _ _ hU hdU hm
  change ‖W (U 0)‖^2+2*(inner ℂ (W (U 0)) (C (W (J 0)))).re ≤ ‖W (U 1)‖^2 at he
  simpa only [gap,endpoint,Prod.fst_sum,Prod.snd_sum,Prod.smul_fst,Prod.smul_snd,
    U,J,sumInput,sumShear,sub_sub,sub_nonneg] using he

include hW in
theorem closed_span_gap (x : Endpoints)
    (hx : x ∈ (Submodule.span ℂ (Set.range (endpoint ε h hε hb))).topologicalClosure) :
    0 ≤ gap ε h hε hb hh W x :=
  nonnegative_on_closed_span (endpoint ε h hε hb) (gap ε h hε hb hh W)
    (gap_continuous ε h hε hb hh W) (finite_gap ε h hε hb hh W w hW) x hx

include hW in
theorem mean_gap (g : ℝ → Endpoints) (hg : Integrable g angleMeasure)
    (hmem : ∀ θ, g θ ∈ Submodule.span ℂ (Set.range (endpoint ε h hε hb))) :
    0 ≤ gap ε h hε hb hh W (∫ θ, g θ ∂angleMeasure) :=
  closed_span_gap ε h hε hb hh W w hW _
    (integral_mem_closed_span (endpoint ε h hε hb) g hg hmem)

#print axioms gap_continuous
#print axioms finite_gap
#print axioms closed_span_gap
#print axioms mean_gap
end
end UnifiedTheory.Audit.KFCausalShearNormEndpointMean
