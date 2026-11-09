/- C1 compact physical states form an actual pure-clock momentum graph
 core. Density and invariance are proved for the concrete clock flow. -/
import UnifiedTheory.Audit.KFCausalUnitaryInvariantCore
import UnifiedTheory.Audit.KFCausalClockFloorPureClockDifferential
import Mathlib.Analysis.Normed.Lp.SmoothApprox

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorPureClockTestCore
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalClockFloorPureClockCoordinates (weight weight_ne_zero)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockTransport
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureGroup pureMomentum)
open UnifiedTheory.Audit.KFCausalUnitaryInvariantCore

def testStates : Set Hilbert := {v | ∃ f : Test, ContDiff ℝ 1 (f : Configuration → ℂ) ∧ embedding f = v}

theorem testStates_dense : Dense testStates := by
  apply (Lp.dense_hasCompactSupport_contDiff (μ := (volume : Measure Configuration))
    (F := ℂ) (p := 2) (by norm_num)).mono
  rintro v ⟨f,hvf,hc,hf⟩
  let g : Test := ⟨⟨f,hf.continuous⟩,hc⟩
  refine ⟨g,hf.of_le (by norm_num),?_⟩
  apply Lp.ext
  exact (embedding_coe g).trans hvf.symm

variable (ε : ℝ) (hε : 0 < ε)

theorem chartInverse_contDiff : ContDiff ℝ 1 (chartIso ε hε).symm := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun q => (chartInverse_derivative ε hε q).differentiableAt,?_⟩
  have he : deriv (chartIso ε hε).symm = fun q => (Real.exp ((chartIso ε hε).symm q)+ε)⁻¹ :=
    funext (fun q => (chartInverse_derivative ε hε q).deriv)
  rw [he]
  exact ((Real.continuous_exp.comp (chartIso ε hε).symm.toHomeomorph.continuous).add continuous_const).inv₀ (fun q => by
    change Real.exp ((chartIso ε hε).symm q)+ε ≠ 0
    positivity)

theorem pureFlow_contDiff (t : ℝ) : ContDiff ℝ 1 (pureFlow ε hε t) := by
  have hc : ContDiff ℝ 1 (chart ε) := by unfold chart; fun_prop
  exact ((chartInverse_contDiff ε hε).comp ((hc.comp contDiff_fst).add contDiff_const)).prodMk contDiff_snd

include hε in
theorem weight_contDiff : ContDiff ℝ 1 (weight ε) := by
  have hc : ContDiff ℝ 1 (fun x : Configuration => Real.exp x.1+ε) := by fun_prop
  exact Complex.ofRealCLM.contDiff.comp (hc.sqrt (fun _ => by positivity))

theorem transportFunction_contDiff (t : ℝ) (f : Configuration → ℂ) (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (transportFunction ε hε t f) :=
  ((weight_contDiff ε hε).mul (((weight_contDiff ε hε).comp (pureFlow_contDiff ε hε t)).inv
    (fun x => weight_ne_zero ε hε (pureFlow ε hε t x)))).mul (hf.comp (pureFlow_contDiff ε hε t))

theorem testTransport_contDiff (t : ℝ) (f : Test) (hf : ContDiff ℝ 1 (f : Configuration → ℂ)) :
    ContDiff ℝ 1 (testTransport ε hε t f : Configuration → ℂ) := by
  have he : (testTransport ε hε t f : Configuration → ℂ) = transportFunction ε hε t f := by
    funext x
    exact testTransport_apply ε hε t f x
  rw [he]
  exact transportFunction_contDiff ε hε t f hf

theorem testStates_invariant (t : ℝ) (v : Hilbert) (hv : v ∈ testStates) :
    transport ε hε t v ∈ testStates := by
  obtain ⟨f,hf,rfl⟩ := hv
  exact ⟨testTransport ε hε t f,testTransport_contDiff ε hε t f hf,(transport_embedding ε hε t f).symm⟩

theorem testStates_domain (h : ℝ) (hh : h ≠ 0) : testStates ⊆ (pureMomentum ε hε h).domain := by
  rintro v ⟨f,hf,rfl⟩
  exact KFCausalClockFloorPureClockDifferential.compact_domain ε hε h hh f hf f.hasCompactSupport

def testGraph (h : ℝ) : Set (Hilbert × Hilbert) :=
  {p | p ∈ (pureMomentum ε hε h).graph ∧ p.1 ∈ testStates}

theorem compact_graph_core (h : ℝ) (hh : h ≠ 0) :
    (Submodule.span ℂ (testGraph ε hε h)).topologicalClosure = (pureMomentum ε hε h).graph :=
  invariant_core (pureGroup ε hε) h hh testStates testStates_dense
    (testStates_domain ε hε h hh) (testStates_invariant ε hε)

#print axioms testStates_dense
#print axioms chartInverse_contDiff
#print axioms pureFlow_contDiff
#print axioms weight_contDiff
#print axioms transportFunction_contDiff
#print axioms testTransport_contDiff
#print axioms testStates_invariant
#print axioms testStates_domain
#print axioms compact_graph_core
end
end UnifiedTheory.Audit.KFCausalClockFloorPureClockTestCore
