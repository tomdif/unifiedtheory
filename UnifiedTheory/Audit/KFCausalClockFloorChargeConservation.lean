/- Conservation of the actual standing charge. The maximal charge
operator domain is invariant under the full propagator; its graph,
expectation and norm are transported exactly. Every angular Fourier
component also has constant norm for arbitrary Hilbert initial data.
No uniform clock-momentum estimate follows from these charge identities. -/
import UnifiedTheory.Audit.KFCausalClockFloorChargeDynamics

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorChargeConservation
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction
open UnifiedTheory.Audit.KFCausalStandingChargeOperator
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorChargeDynamics (evolution_action)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "U" => evolution ε hε h hh hb m g k
local notation "Q" => standingCharge h hh

theorem charge_graph_evolution (s t : ℝ) (f v : Hilbert) (hv : (f,v) ∈ (Q).graph) :
    (U s t f, U s t v) ∈ (Q).graph := by
  apply (standingCharge_graph h hh _ _).mpr
  have hd := (standingCharge_graph h hh f v).mp hv
  let L : Hilbert →L[ℂ] Hilbert := U s t
  have he := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd
  change HasDerivAt (fun θ => U s t (action h hh θ f)) (U s t (Complex.I • v)) 0 at he
  simpa only [evolution_action ε hε h hh hb m g k s t, map_smul] using he

theorem charge_domain_invariant (s t : ℝ) (f : Hilbert) (hf : f ∈ (Q).domain) :
    U s t f ∈ (Q).domain :=
  LinearPMap.mem_domain_iff.mpr ⟨U s t (Q ⟨f,hf⟩),
    charge_graph_evolution ε hε h hh hb m g k s t f (Q ⟨f,hf⟩) ((Q).mem_graph ⟨f,hf⟩)⟩

theorem charge_domain_iff (s t : ℝ) (f : Hilbert) : U s t f ∈ (Q).domain ↔ f ∈ (Q).domain := by
  constructor
  · intro hf
    have he := charge_domain_invariant ε hε h hh hb m g k t s (U s t f) hf
    have hr := congrArg (fun L : Hilbert →L[ℂ] Hilbert => L f)
      (evolution_reverse ε hε h hh hb m g k s t)
    change U t s (U s t f) = f at hr
    rwa [hr] at he
  · exact charge_domain_invariant ε hε h hh hb m g k s t f

theorem charge_value_evolution (s t : ℝ) (f : (Q).domain) :
    Q ⟨U s t (f:Hilbert), charge_domain_invariant ε hε h hh hb m g k s t f f.property⟩ =
      U s t (Q f) :=
  (Q).mem_graph_snd_inj' ((Q).mem_graph _)
    (charge_graph_evolution ε hε h hh hb m g k s t f (Q f) ((Q).mem_graph f)) rfl

theorem charge_expectation_conserved (s t : ℝ) (f : (Q).domain) :
    inner ℂ (U s t (f:Hilbert))
      (Q ⟨U s t (f:Hilbert), charge_domain_invariant ε hε h hh hb m g k s t f f.property⟩) =
        inner ℂ (f:Hilbert) (Q f) := by
  rw [charge_value_evolution ε hε h hh hb m g k s t f]
  exact (U s t).inner_map_map _ _

theorem charge_norm_conserved (s t : ℝ) (f : (Q).domain) :
    ‖Q ⟨U s t (f:Hilbert), charge_domain_invariant ε hε h hh hb m g k s t f f.property⟩‖ =
      ‖Q f‖ := by
  rw [charge_value_evolution ε hε h hh hb m g k s t f]
  exact (U s t).norm_map _

theorem charge_eigenstate_preserved (s t q : ℝ) (f : Hilbert)
    (hf : (f,(q:ℂ) • f) ∈ (Q).graph) :
    (U s t f,(q:ℂ) • U s t f) ∈ (Q).graph := by
  simpa only [map_smul] using charge_graph_evolution ε hε h hh hb m g k s t f _ hf

def component (n : ℤ) (f : Hilbert) : Hilbert :=
  ∫ θ, Complex.exp (-Complex.I*((n:ℂ)*(2*Real.pi*θ:ℝ))) •
    action h hh (2*Real.pi*θ) f ∂angleMeasure

theorem component_integrable (n : ℤ) (f : Hilbert) :
    Integrable (fun θ => Complex.exp (-Complex.I*((n:ℂ)*(2*Real.pi*θ:ℝ))) •
      action h hh (2*Real.pi*θ) f) angleMeasure := by
  have hc : Continuous (fun θ : ℝ => Complex.exp (-Complex.I*((n:ℂ)*(2*Real.pi*θ:ℝ))) •
      action h hh (2*Real.pi*θ) f) :=
    (by fun_prop : Continuous (fun θ : ℝ => Complex.exp (-Complex.I*((n:ℂ)*(2*Real.pi*θ:ℝ))))).smul
      ((action_strong_continuous h hh f).comp (continuous_const.mul continuous_id))
  exact hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self

theorem component_evolution (s t : ℝ) (n : ℤ) (f : Hilbert) :
    component h hh n (U s t f) = U s t (component h hh n f) := by
  let L : Hilbert →L[ℂ] Hilbert := U s t
  have hi := L.integral_comp_comm (component_integrable h hh n f)
  change (∫ θ, U s t (Complex.exp (-Complex.I*((n:ℂ)*(2*Real.pi*θ:ℝ))) •
    action h hh (2*Real.pi*θ) f) ∂angleMeasure) = U s t (component h hh n f) at hi
  simpa only [map_smul, evolution_action ε hε h hh hb m g k s t, component] using hi

theorem component_norm_conserved (s t : ℝ) (n : ℤ) (f : Hilbert) :
    ‖component h hh n (U s t f)‖ = ‖component h hh n f‖ := by
  rw [component_evolution ε hε h hh hb m g k s t n f]
  exact (U s t).norm_map _

#print axioms charge_graph_evolution
#print axioms charge_domain_invariant
#print axioms charge_domain_iff
#print axioms charge_value_evolution
#print axioms charge_expectation_conserved
#print axioms charge_norm_conserved
#print axioms charge_eigenstate_preserved
#print axioms component_integrable
#print axioms component_evolution
#print axioms component_norm_conserved

end
end UnifiedTheory.Audit.KFCausalClockFloorChargeConservation
