/- The transported norm secant extends to closed spans of endpoint triples.
The quadratic comparison is applied after integration, retaining every
cross term in a charge-projected superposition. -/
import UnifiedTheory.Audit.KFCausalTransportedNormSecant
import UnifiedTheory.Audit.KFCausalShearEndpointMean

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalTransportedSecantMean
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalImaginaryShearSuperposition (Seed)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalFieldEigenpolynomials (modes)
open UnifiedTheory.Audit.KFCausalPolynomialImaginaryShearCurve (fieldWeight)
open UnifiedTheory.Audit.KFCausalFieldShearPathGraphs (state fieldShear)
open UnifiedTheory.Audit.KFCausalClockFloorShearWeight (root)
open UnifiedTheory.Audit.KFCausalClockSecantMultiplier (operator)

abbrev Endpoints := Hilbert × (Hilbert × Hilbert)

def gap (M W : Hilbert →L[ℂ] Hilbert) (x : Endpoints) : ℝ :=
  (inner ℂ (W x.2.1) (W x.2.2)).re-(‖M x.2.1‖^2-‖M x.1‖^2)/2

theorem gap_continuous (M W : Hilbert →L[ℂ] Hilbert) : Continuous (gap M W) := by
  unfold gap
  fun_prop

variable (ε h : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3) (hh : h ≠ 0)
  (l : Transverse →L[ℝ] ℝ) (i : Fin 2)
local notation "M" => operator ε h hε hb hh
local notation "W" => root ε hε h hb hh

def endpoint (s : Seed) : Endpoints :=
  (∑ k, KFCausalActualTransportedField.input ε h hε hb hh s (modes l i k) 0,
   (state ε h hε hb s (fieldWeight l i) 1,fieldShear ε h hε hb s l i 1))

theorem finite_endpoints {n : ℕ} (s : Fin n → Seed) (z : Fin n → ℂ) :
    (∑ r, z r • endpoint ε h hε hb hh l i (s r)) =
      (KFCausalTransportedMatterInterpolation.input ε h hε hb hh l i s z 0,
       (KFCausalFieldShearInterpolationEstimate.field ε h hε hb l i s z 1,
        KFCausalFieldShearInterpolationEstimate.shear ε h hε hb l i s z 1)) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [endpoint,Prod.fst_sum,Prod.snd_sum,Prod.smul_fst,Prod.smul_snd,
      KFCausalTransportedMatterInterpolation.input,
      KFCausalFieldShearInterpolationEstimate.field,KFCausalFieldShearInterpolationEstimate.shear]

theorem finite_gap (n : ℕ) (s : Fin n → Seed) (z : Fin n → ℂ) :
    0 ≤ gap M W (∑ r, z r • endpoint ε h hε hb hh l i (s r)) := by
  rw [finite_endpoints]
  exact sub_nonneg.mpr (KFCausalTransportedNormSecant.finite_secant ε h hε hb hh l i s z)

theorem closed_span_gap (x : Endpoints)
    (hx : x ∈ (Submodule.span ℂ (Set.range (endpoint ε h hε hb hh l i))).topologicalClosure) :
    0 ≤ gap M W x :=
  KFCausalShearEndpointMean.nonnegative_on_closed_span _ _ (gap_continuous M W)
    (finite_gap ε h hε hb hh l i) x hx

theorem mean_gap (g : ℝ → Endpoints) (hg : Integrable g angleMeasure)
    (hmem : ∀ θ, g θ ∈ Submodule.span ℂ (Set.range (endpoint ε h hε hb hh l i))) :
    0 ≤ gap M W (∫ θ, g θ ∂angleMeasure) :=
  closed_span_gap ε h hε hb hh l i _
    (KFCausalShearEndpointMean.integral_mem_closed_span _ g hg hmem)

#print axioms gap_continuous
#print axioms finite_endpoints
#print axioms finite_gap
#print axioms closed_span_gap
#print axioms mean_gap
end
end UnifiedTheory.Audit.KFCausalTransportedSecantMean
