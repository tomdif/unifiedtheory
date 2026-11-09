/- Charge rotations preserve the entire maximal canonical clock-momentum
graph. This is an exact symmetry of the canonical observable, not an
invariance claim for the longitudinal exponential or Hamiltonian domain. -/
import UnifiedTheory.Audit.KFCausalCanonicalClockCharge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCanonicalClockChargeGraph
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalConfigurationTranslation (translation)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action action_reverse)
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum (clockGroup clockMomentum)
open UnifiedTheory.Audit.KFCausalUnitaryMomentumEvolution (momentum_graph_iff)
open UnifiedTheory.Audit.KFCausalCanonicalClockCharge (translation_charge)

theorem graph_charge (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (clockMomentum h).graph) :
    (action h hh θ f,action h hh θ g) ∈ (clockMomentum h).graph := by
  apply (momentum_graph_iff clockGroup h hh _ _).mpr
  have hd := (((action h hh θ : Hilbert →L[ℂ] Hilbert).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    ((momentum_graph_iff clockGroup h hh f g).mp hfg))
  change HasDerivAt (fun t : ℝ => action h hh θ (translation t f))
    (action h hh θ ((Complex.I/(h:ℂ)) • g)) 0 at hd
  change HasDerivAt (fun t : ℝ => translation t (action h hh θ f))
    ((Complex.I/(h:ℂ)) • action h hh θ g) 0
  simpa only [← translation_charge,map_smul] using hd

theorem graph_charge_iff (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (f g : Hilbert) :
    (action h hh θ f,action h hh θ g) ∈ (clockMomentum h).graph ↔
      (f,g) ∈ (clockMomentum h).graph := by
  constructor
  · intro hfg
    simpa only [action_reverse] using graph_charge h hh (-θ) _ _ hfg
  · exact graph_charge h hh θ f g

theorem domain_charge_iff (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (f : Hilbert) :
    action h hh θ f ∈ (clockMomentum h).domain ↔ f ∈ (clockMomentum h).domain := by
  constructor
  · intro hf
    obtain ⟨g,hg⟩ := LinearPMap.mem_domain_iff.mp hf
    have he := graph_charge h hh (-θ) _ _ hg
    rw [action_reverse] at he
    exact LinearPMap.mem_domain_of_mem_graph he
  · intro hf
    obtain ⟨g,hg⟩ := LinearPMap.mem_domain_iff.mp hf
    exact LinearPMap.mem_domain_of_mem_graph (graph_charge h hh θ f g hg)

theorem graph_output_norm (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (f g q : Hilbert)
    (hg : (f,g) ∈ (clockMomentum h).graph)
    (hq : (action h hh θ f,q) ∈ (clockMomentum h).graph) : ‖q‖ = ‖g‖ := by
  have he := (clockMomentum h).mem_graph_snd_inj' hq (graph_charge h hh θ f g hg) rfl
  dsimp only at he
  rw [he,LinearIsometryEquiv.norm_map]

theorem characteristic_charge (h : ℝ) (hh : h ≠ 0) (r θ : ℝ) (f : Hilbert) :
    inner ℂ (action h hh θ f) (translation r (action h hh θ f)) =
      inner ℂ f (translation r f) := by
  rw [translation_charge,LinearIsometryEquiv.inner_map_map]

#print axioms graph_charge
#print axioms graph_charge_iff
#print axioms domain_charge_iff
#print axioms graph_output_norm
#print axioms characteristic_charge

end
end UnifiedTheory.Audit.KFCausalCanonicalClockChargeGraph
