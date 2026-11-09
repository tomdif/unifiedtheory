/- Exact polynomial covariance of the signed field and its square under
neutral translation. The actual ordered matter domains and common domain
are preserved, with every intermediate output supplied from those domains. -/
import UnifiedTheory.Audit.KFCausalNeutralTranslationFactors
import UnifiedTheory.Audit.KFCausalClockFloorCommonDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalNeutralTranslationMatter
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalNeutralTranslationCoordinates
open UnifiedTheory.Audit.KFCausalNeutralTranslationFactors
open UnifiedTheory.Audit.KFCausalPhysicalField
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare
open UnifiedTheory.Audit.KFCausalClockFloorTrialMatter (matterFactor)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition (composition_graph composition_domain)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

def shiftValue (l : Transverse →L[ℝ] ℝ) (r : ℝ) : ℂ := (l (Pi.single 4 r) : ℂ)

theorem field_graph_action (l : Transverse →L[ℝ] ℝ) (r : ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (physicalField l).graph) :
    (action r f,action r (g-shiftValue l r • f)) ∈ (physicalField l).graph := by
  have he : g-shiftValue l r • f =ᵐ[volume] fun x => ((l x.2 : ℂ)-shiftValue l r)*f x := by
    filter_upwards [Lp.coeFn_sub g (shiftValue l r • f),Lp.coeFn_smul (shiftValue l r) f,
      (physicalField_graph l f g).mp hfg] with x hs hc hx
    rw [hs]
    simp only [Pi.sub_apply,hc,Pi.smul_apply,smul_eq_mul,hx]
    ring
  apply (physicalField_graph l _ _).mpr
  filter_upwards [action_coe r (g-shiftValue l r • f),action_coe r f,
    (KFCausalLpPhaseTranslation.shift_preserves volume (vector r)).quasiMeasurePreserving.ae he] with x hg hf hh
  change (g-shiftValue l r • f) (x+vector r) = _ at hh
  rw [hg,hf,hh]
  simp [KFCausalLpPhaseTranslation.shift,vector,map_add,shiftValue]

theorem square_graph_action (l : Transverse →L[ℝ] ℝ) (r : ℝ) (f g q : Hilbert)
    (hg : (f,g) ∈ (physicalField l).graph) (hq : (f,q) ∈ (fieldSquare l).graph) :
    (action r f,action r (q-(2*shiftValue l r) • g+(shiftValue l r)^2 • f)) ∈ (fieldSquare l).graph := by
  have he : q-(2*shiftValue l r) • g+(shiftValue l r)^2 • f =ᵐ[volume]
      fun x => ((l x.2 : ℂ)-shiftValue l r)^2*f x := by
    filter_upwards [Lp.coeFn_add (q-(2*shiftValue l r) • g) ((shiftValue l r)^2 • f),
      Lp.coeFn_sub q ((2*shiftValue l r) • g),Lp.coeFn_smul (2*shiftValue l r) g,
      Lp.coeFn_smul ((shiftValue l r)^2) f,(physicalField_graph l f g).mp hg,
      (fieldSquare_graph l f q).mp hq] with x ha hs hcg hcf hgx hqx
    rw [ha]
    simp only [Pi.add_apply,hs,Pi.sub_apply,hcg,hcf,Pi.smul_apply,smul_eq_mul,hgx,hqx]
    ring
  apply (fieldSquare_graph l _ _).mpr
  filter_upwards [action_coe r (q-(2*shiftValue l r) • g+(shiftValue l r)^2 • f),action_coe r f,
    (KFCausalLpPhaseTranslation.shift_preserves volume (vector r)).quasiMeasurePreserving.ae he] with x ha hf hh
  change (q-(2*shiftValue l r) • g+(shiftValue l r)^2 • f) (x+vector r) = _ at hh
  rw [ha,hf,hh]
  simp [KFCausalLpPhaseTranslation.shift,vector,map_add,shiftValue]

theorem linear_matter_graph_action (ε : ℝ) (hε : 0 < ε) (h r : ℝ)
    (l : Transverse →L[ℝ] ℝ) (f e g : Hilbert)
    (he : (f,e) ∈ (orderedExponential ε hε h).graph)
    (hg : (f,g) ∈ (matterFactor ε hε h (physicalField l)).graph) :
    (action r f,action r (g-shiftValue l r • e)) ∈ (matterFactor ε hε h (physicalField l)).graph := by
  rw [matterFactor,composition_graph] at hg ⊢
  obtain ⟨u,hu,hg⟩ := hg
  have hue : u = e := (orderedExponential ε hε h).mem_graph_snd_inj' hu he rfl
  subst u
  exact ⟨action r e,ordered_graph_action ε hε h r f e he,field_graph_action l r e g hg⟩

theorem quadratic_matter_graph_action (ε : ℝ) (hε : 0 < ε) (h r : ℝ)
    (l : Transverse →L[ℝ] ℝ) (f e g q : Hilbert)
    (he : (f,e) ∈ (orderedExponential ε hε h).graph)
    (hg : (f,g) ∈ (matterFactor ε hε h (physicalField l)).graph)
    (hq : (f,q) ∈ (matterFactor ε hε h (fieldSquare l)).graph) :
    (action r f,action r (q-(2*shiftValue l r) • g+(shiftValue l r)^2 • e)) ∈
      (matterFactor ε hε h (fieldSquare l)).graph := by
  rw [matterFactor,composition_graph] at hg hq ⊢
  obtain ⟨u,hu,hg⟩ := hg
  obtain ⟨v,hv,hq⟩ := hq
  have hue : u = e := (orderedExponential ε hε h).mem_graph_snd_inj' hu he rfl
  have hve : v = e := (orderedExponential ε hε h).mem_graph_snd_inj' hv he rfl
  subst u; subst v
  exact ⟨action r e,ordered_graph_action ε hε h r f e he,square_graph_action l r e g q hg hq⟩

theorem linear_matter_domain_action (ε : ℝ) (hε : 0 < ε) (h r : ℝ)
    (l : Transverse →L[ℝ] ℝ) (f : Hilbert)
    (hf : f ∈ (matterFactor ε hε h (physicalField l)).domain) :
    action r f ∈ (matterFactor ε hε h (physicalField l)).domain := by
  obtain ⟨e,he,hf⟩ := (composition_domain _ _ _).mp hf
  apply LinearPMap.mem_domain_of_mem_graph
  apply (composition_graph _ _ _ _).mpr
  exact ⟨action r e,ordered_graph_action ε hε h r f e he,
    field_graph_action l r e _ ((physicalField l).mem_graph ⟨e,hf⟩)⟩

theorem quadratic_matter_domain_action (ε : ℝ) (hε : 0 < ε) (h r : ℝ)
    (l : Transverse →L[ℝ] ℝ) (f : Hilbert)
    (hf : f ∈ (matterFactor ε hε h (fieldSquare l)).domain) :
    action r f ∈ (matterFactor ε hε h (fieldSquare l)).domain := by
  obtain ⟨e,he,hf⟩ := (composition_domain _ _ _).mp hf
  have hl := fieldSquare_domain_le_physicalField l hf
  apply LinearPMap.mem_domain_of_mem_graph
  apply (composition_graph _ _ _ _).mpr
  exact ⟨action r e,ordered_graph_action ε hε h r f e he,
    square_graph_action l r e _ _ ((physicalField l).mem_graph ⟨e,hl⟩) ((fieldSquare l).mem_graph ⟨e,hf⟩)⟩

theorem common_domain_action (ε : ℝ) (hε : 0 < ε) (h r : ℝ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (f : Hilbert)
    (hf : f ∈ commonEnergyDomain ε hε h v l) : action r f ∈ commonEnergyDomain ε hε h v l := by
  have hd := (commonEnergyDomain_iff ε hε h v l f).mp hf
  apply (commonEnergyDomain_iff ε hε h v l _).mpr
  intro i
  fin_cases i
  · exact LinearPMap.mem_domain_of_mem_graph (clockHalf_graph_action ε r f _
      ((KFCausalClockFloorClockHalf.clockHalf ε).mem_graph ⟨f,hd 0⟩))
  · exact LinearPMap.mem_domain_of_mem_graph (kinetic_graph_action ε h r (v 0) f _
      ((KFCausalClockFloorTrialMomentum.clockMomentum ε h (v 0)).mem_graph ⟨f,hd 1⟩))
  · exact LinearPMap.mem_domain_of_mem_graph (kinetic_graph_action ε h r (v 1) f _
      ((KFCausalClockFloorTrialMomentum.clockMomentum ε h (v 1)).mem_graph ⟨f,hd 2⟩))
  · exact LinearPMap.mem_domain_of_mem_graph (kinetic_graph_action ε h r (v 2) f _
      ((KFCausalClockFloorTrialMomentum.clockMomentum ε h (v 2)).mem_graph ⟨f,hd 3⟩))
  · exact LinearPMap.mem_domain_of_mem_graph (kinetic_graph_action ε h r (v 3) f _
      ((KFCausalClockFloorTrialMomentum.clockMomentum ε h (v 3)).mem_graph ⟨f,hd 4⟩))
  · exact linear_matter_domain_action ε hε h r l f (hd 5)
  · exact quadratic_matter_domain_action ε hε h r l f (hd 6)
  · exact LinearPMap.mem_domain_of_mem_graph (ordered_graph_action ε hε h r f _
      ((orderedExponential ε hε h).mem_graph ⟨f,hd 7⟩))

theorem common_domain_action_iff (ε : ℝ) (hε : 0 < ε) (h r : ℝ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (f : Hilbert) :
    action r f ∈ commonEnergyDomain ε hε h v l ↔ f ∈ commonEnergyDomain ε hε h v l := by
  refine ⟨fun hf => ?_,common_domain_action ε hε h r v l f⟩
  simpa only [action_inverse] using common_domain_action ε hε h (-r) v l _ hf

#print axioms field_graph_action
#print axioms square_graph_action
#print axioms linear_matter_graph_action
#print axioms quadratic_matter_graph_action
#print axioms linear_matter_domain_action
#print axioms quadratic_matter_domain_action
#print axioms common_domain_action
#print axioms common_domain_action_iff

end
end UnifiedTheory.Audit.KFCausalNeutralTranslationMatter
