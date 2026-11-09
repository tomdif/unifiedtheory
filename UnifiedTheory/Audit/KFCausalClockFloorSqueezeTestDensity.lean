/- Orbit averages in the actual completed energy form supply a dense
common energy/generator test class. No evolved-state domain is assumed. -/
import UnifiedTheory.Audit.KFCausalSqueezeEnergyContinuity
import UnifiedTheory.Audit.KFCausalPairedSqueezeGenerator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorSqueezeTestDensity
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport (FormSpace embedding)
open UnifiedTheory.Audit.KFCausalClockFloorReferenceSqueeze (formAction formAction_embedding)
open UnifiedTheory.Audit.KFCausalSqueezeEnergyContinuity
open UnifiedTheory.Audit.KFCausalPairedSqueezeGenerator (squeezeGroup squeezeMomentum squeeze_domain)
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage (average average_derivative)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (hh : |h| ≤ 2*Real.pi*ε/3)
  (m q k t : ℝ)
local notation "V" => FormSpace ε hε h hne hh m q k t
local notation "J" => embedding ε hε h hne hh m q k t
local notation "R" => (fun a : ℝ => formAction ε hε h hne hh m q k a t)

def formAverage (u : V) (a : ℝ) : V := a⁻¹ • ∫ b in 0..a, R b u

theorem formAverage_embedding (u : V) (a : ℝ) :
    J (formAverage ε hε h hne hh m q k t u a) = average squeezeGroup (J u) a := by
  unfold formAverage KFCausalUnitaryOrbitAverage.average KFCausalUnitaryOrbitAverage.primitive
  rw [map_real_smul J (J).continuous,← (J).intervalIntegral_comp_comm
    ((formAction_strong_continuous ε hε h hne hh m q k t u).intervalIntegrable 0 a)]
  simp only [formAction_embedding,squeezeGroup]

theorem formAverage_domain (u : V) (a : ℝ) :
    J (formAverage ε hε h hne hh m q k t u a) ∈ (squeezeMomentum h).domain := by
  rw [formAverage_embedding,squeeze_domain]
  exact (average_derivative squeezeGroup (J u) a).differentiableAt

theorem formAverage_tendsto (u : V) :
    Tendsto (formAverage ε hε h hne hh m q k t u) (𝓝[≠] 0) (𝓝 u) := by
  letI : SecondCountableTopologyEither ℝ V := ⟨Or.inl inferInstance⟩
  have hc := formAction_strong_continuous ε hε h hne hh m q k t u
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 0)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  have hzero : R 0 u = u := formAction_zero ε hε h hne hh m q k t u
  have hp : HasDerivAt (fun a => ∫ b in 0..a, R b u) u 0 := hd.congr_deriv hzero
  simpa only [zero_add,intervalIntegral.integral_same,sub_zero,formAverage] using hp.tendsto_slope_zero

theorem form_test_dense : Dense {v : V | J v ∈ (squeezeMomentum h).domain} := by
  intro u
  exact mem_closure_of_tendsto (formAverage_tendsto ε hε h hne hh m q k t u)
    (Eventually.of_forall (fun a => formAverage_domain ε hε h hne hh m q k t u a))

theorem physical_test_dense : Dense {f : Hilbert | ∃ v : V, ∃ z : Hilbert,
    J v = f ∧ (f,z) ∈ (squeezeMomentum h).graph} := by
  have hd : DenseRange J := KFCausalClosedGraphForm.embedding_dense
    (KFCausalClockFloorAveragedHamiltonian.formData ε hε h hne hh m q k t)
  intro f
  apply closure_minimal (s := Set.range J) ?_ isClosed_closure (hd f)
  rintro _ ⟨u,rfl⟩
  have hl := ((J).continuous.tendsto u).comp (formAverage_tendsto ε hε h hne hh m q k t u)
  apply mem_closure_of_tendsto hl
  apply Eventually.of_forall
  intro a
  obtain ⟨z,hz⟩ := LinearPMap.mem_domain_iff.mp (formAverage_domain ε hε h hne hh m q k t u a)
  exact ⟨formAverage ε hε h hne hh m q k t u a,z,rfl,hz⟩

#print axioms formAverage_embedding
#print axioms formAverage_domain
#print axioms formAverage_tendsto
#print axioms form_test_dense
#print axioms physical_test_dense
end
end UnifiedTheory.Audit.KFCausalClockFloorSqueezeTestDensity
