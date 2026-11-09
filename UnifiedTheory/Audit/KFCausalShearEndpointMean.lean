/- A continuous quadratic endpoint comparison passes from all finite
complex Gaussian superpositions to their closed span and Bochner means.
The finite comparison is derived from the actual shear paths. -/
import UnifiedTheory.Audit.KFCausalImaginaryShearSuperposition
import UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Analysis.Convex.Integral

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalShearEndpointMean
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalImaginaryShearSuperposition (Seed sumInput sumShear)
open UnifiedTheory.Audit.KFCausalActualImaginaryShearCurve (input shear)

theorem nonnegative_on_closed_span {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ι → E) (Q : E → ℝ) (hQ : Continuous Q)
    (hf : ∀ (n : ℕ) (k : Fin n → ι) (z : Fin n → ℂ), 0 ≤ Q (∑ i, z i • f (k i))) :
    ∀ x ∈ (Submodule.span ℂ (Set.range f)).topologicalClosure, 0 ≤ Q x := by
  classical
  have hs : (Submodule.span ℂ (Set.range f) : Set E) ⊆ {x | 0 ≤ Q x} := by
    intro x hx
    obtain ⟨c,hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
    let e := Fintype.equivFin c.support
    have he : x = ∑ i : Fin (Fintype.card c.support), c (e.symm i).val • f (e.symm i).val := by
      calc
        x = ∑ i ∈ c.support, c i • f i := hc.symm
        _ = ∑ i : c.support, c i.val • f i.val := (Finset.sum_attach c.support (fun i => c i • f i)).symm
        _ = _ := (e.symm.sum_comp (fun i : c.support => c i.val • f i.val)).symm
    rw [Set.mem_setOf_eq,he]
    exact hf _ _ _
  exact closure_minimal hs (isClosed_le continuous_const hQ)

theorem integral_mem_closed_span {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    (f : ι → E) (g : ℝ → E) (hg : Integrable g angleMeasure)
    (hmem : ∀ θ, g θ ∈ Submodule.span ℂ (Set.range f)) :
    (∫ θ, g θ ∂angleMeasure) ∈ (Submodule.span ℂ (Set.range f)).topologicalClosure := by
  let V := Submodule.span ℂ (Set.range f)
  exact (V.topologicalClosure.restrictScalars ℝ).convex.integral_mem V.isClosed_topologicalClosure
    (Filter.Eventually.of_forall (fun θ => V.le_topologicalClosure (hmem θ))) hg

abbrev Endpoints := (Hilbert × Hilbert) × (Hilbert × Hilbert)

def gap (W : Hilbert →L[ℂ] Hilbert) (x : Endpoints) : ℝ :=
  (inner ℂ (W x.2.1) (W x.2.2)).re-(inner ℂ (W x.1.1) (W x.1.2)).re

theorem gap_continuous (W : Hilbert →L[ℂ] Hilbert) : Continuous (gap W) := by
  unfold gap
  fun_prop

variable (ε h : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3)

def endpoint (s : Seed) : Endpoints :=
  ((input ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b 0,
    shear ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b 0),
   (input ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b 1,
    shear ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b 1))

variable (hh : h ≠ 0) (W : Hilbert →L[ℂ] Hilbert) (w : ℝ → ℂ)
  (hW : ∀ f : Hilbert, W f =ᵐ[volume] fun x => w x.1*f x)

include hh hW in
theorem finite_gap (n : ℕ) (s : Fin n → Seed) (z : Fin n → ℂ) :
    0 ≤ gap W (∑ i, z i • endpoint ε h hε hb (s i)) := by
  have he := KFCausalImaginaryShearSuperposition.expectation_endpoints ε h hε hb s z hh W w hW
  simpa only [gap,endpoint,Prod.fst_sum,Prod.snd_sum,Prod.smul_fst,Prod.smul_snd,
    KFCausalClockShearPositiveVariation.expectation,sumInput,sumShear] using sub_nonneg.mpr he

include hh hW in
theorem closed_span_gap (x : Endpoints)
    (hx : x ∈ (Submodule.span ℂ (Set.range (endpoint ε h hε hb))).topologicalClosure) :
    0 ≤ gap W x :=
  nonnegative_on_closed_span (endpoint ε h hε hb) (gap W) (gap_continuous W)
    (finite_gap ε h hε hb hh W w hW) x hx

include hh hW in
theorem mean_gap (g : ℝ → Endpoints) (hg : Integrable g angleMeasure)
    (hmem : ∀ θ, g θ ∈ Submodule.span ℂ (Set.range (endpoint ε h hε hb))) :
    0 ≤ gap W (∫ θ, g θ ∂angleMeasure) :=
  closed_span_gap ε h hε hb hh W w hW _
    (integral_mem_closed_span (endpoint ε h hε hb) g hg hmem)

#print axioms nonnegative_on_closed_span
#print axioms integral_mem_closed_span
#print axioms gap_continuous
#print axioms finite_gap
#print axioms closed_span_gap
#print axioms mean_gap
end
end UnifiedTheory.Audit.KFCausalShearEndpointMean
