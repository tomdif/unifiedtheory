/- Exact paired-squeeze covariance of both full natural ordered matter
graphs. The neutral component of the physical field is retained. No
field-weighted shear remainder is discarded. This is not a virial law. -/
import UnifiedTheory.Audit.KFCausalClockFloorSqueezeExponential
import UnifiedTheory.Audit.KFCausalClockFloorTrialMatter

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorSqueezeMatter
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalPairedSqueezeFlow (squeeze_field)
open UnifiedTheory.Audit.KFCausalPairedSqueezeTransport
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalPhysicalField (physicalField physicalField_graph)
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare (fieldSquare fieldSquare_graph)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMatter (matterFactor)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition (composition_graph)
open UnifiedTheory.Audit.KFCausalClockFloorSqueezeExponential (ordered_graph_squeeze)

private theorem exp_cancel (a : ℝ) : (Real.exp a:ℂ)*(Real.exp (-a):ℂ) = 1 := by
  rw [← Complex.ofReal_mul,← Real.exp_add,add_neg_cancel,Real.exp_zero,Complex.ofReal_one]

theorem field_graph (a : ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (physicalField pointField).graph) :
    (transport a f,(Real.exp a:ℂ) • transport a g) ∈ (physicalField pointField).graph := by
  apply (physicalField_graph pointField _ _).mpr
  filter_upwards [Lp.coeFn_smul (Real.exp a:ℂ) (transport a g),transport_coe a f,
    transport_coe a g,(squeezeFlow_quasiMeasurePreserving a).ae
      ((physicalField_graph pointField f g).mp hfg)] with x hs hf hg he
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hg,he,hf]
  simp only [squeezeFlow_apply,squeeze_field,Complex.ofReal_mul]
  calc
    _ = ((Real.exp a:ℂ)*(Real.exp (-a):ℂ))*
        ((pointField x.2:ℂ)*((Real.exp (-a/2):ℂ)*f (x.1,_))) := by ring
    _ = _ := by rw [exp_cancel,one_mul]

theorem square_graph (a : ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (fieldSquare pointField).graph) :
    (transport a f,(Real.exp (2*a):ℂ) • transport a g) ∈ (fieldSquare pointField).graph := by
  apply (fieldSquare_graph pointField _ _).mpr
  filter_upwards [Lp.coeFn_smul (Real.exp (2*a):ℂ) (transport a g),transport_coe a f,
    transport_coe a g,(squeezeFlow_quasiMeasurePreserving a).ae
      ((fieldSquare_graph pointField f g).mp hfg)] with x hs hf hg he
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hg,he,hf]
  simp only [squeezeFlow_apply,squeeze_field,Complex.ofReal_mul]
  have hexp : (Real.exp (2*a):ℂ) = (Real.exp a:ℂ)^2 := by
    rw [← Complex.ofReal_pow,← Real.exp_nat_mul]
    norm_num
  rw [hexp]
  calc
    _ = ((Real.exp a:ℂ)*(Real.exp (-a):ℂ))^2*
        ((pointField x.2:ℂ)^2*((Real.exp (-a/2):ℂ)*f (x.1,_))) := by ring
    _ = _ := by rw [exp_cancel,one_pow,one_mul]

theorem matter_graph (ε : ℝ) (hε : 0 < ε) (h a : ℝ)
    (M : Hilbert →ₗ.[ℂ] Hilbert) (c : ℂ)
    (hM : ∀ f g, (f,g) ∈ M.graph → (transport a f,c • transport a g) ∈ M.graph)
    (f g : Hilbert) (hfg : (f,g) ∈ (matterFactor ε hε h M).graph) :
    (transport a f,c • transport a g) ∈ (matterFactor ε hε h M).graph := by
  obtain ⟨u,hu,hg⟩ := (composition_graph _ _ f g).mp hfg
  exact (composition_graph _ _ _ _).mpr
    ⟨_,ordered_graph_squeeze ε hε h a f u hu,hM u g hg⟩

theorem linear_matter_graph (ε : ℝ) (hε : 0 < ε) (h a : ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (matterFactor ε hε h (physicalField pointField)).graph) :
    (transport a f,(Real.exp a:ℂ) • transport a g) ∈
      (matterFactor ε hε h (physicalField pointField)).graph :=
  matter_graph ε hε h a _ _ (field_graph a) f g hfg

theorem quadratic_matter_graph (ε : ℝ) (hε : 0 < ε) (h a : ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (matterFactor ε hε h (fieldSquare pointField)).graph) :
    (transport a f,(Real.exp (2*a):ℂ) • transport a g) ∈
      (matterFactor ε hε h (fieldSquare pointField)).graph :=
  matter_graph ε hε h a _ _ (square_graph a) f g hfg

theorem linear_matter_domain (ε : ℝ) (hε : 0 < ε) (h a : ℝ) (f : Hilbert) :
    transport a f ∈ (matterFactor ε hε h (physicalField pointField)).domain ↔
      f ∈ (matterFactor ε hε h (physicalField pointField)).domain := by
  have forward (b : ℝ) (v : Hilbert)
      (hv : v ∈ (matterFactor ε hε h (physicalField pointField)).domain) :
      transport b v ∈ (matterFactor ε hε h (physicalField pointField)).domain := by
    obtain ⟨w,hw⟩ := LinearPMap.mem_domain_iff.mp hv
    exact LinearPMap.mem_domain_of_mem_graph (linear_matter_graph ε hε h b v w hw)
  constructor
  · intro hf
    simpa only [transport_reverse] using forward (-a) _ hf
  · exact forward a f

theorem quadratic_matter_domain (ε : ℝ) (hε : 0 < ε) (h a : ℝ) (f : Hilbert) :
    transport a f ∈ (matterFactor ε hε h (fieldSquare pointField)).domain ↔
      f ∈ (matterFactor ε hε h (fieldSquare pointField)).domain := by
  have forward (b : ℝ) (v : Hilbert)
      (hv : v ∈ (matterFactor ε hε h (fieldSquare pointField)).domain) :
      transport b v ∈ (matterFactor ε hε h (fieldSquare pointField)).domain := by
    obtain ⟨w,hw⟩ := LinearPMap.mem_domain_iff.mp hv
    exact LinearPMap.mem_domain_of_mem_graph (quadratic_matter_graph ε hε h b v w hw)
  constructor
  · intro hf
    simpa only [transport_reverse] using forward (-a) _ hf
  · exact forward a f

#print axioms field_graph
#print axioms square_graph
#print axioms matter_graph
#print axioms linear_matter_graph
#print axioms quadratic_matter_graph
#print axioms linear_matter_domain
#print axioms quadratic_matter_domain

end
end UnifiedTheory.Audit.KFCausalClockFloorSqueezeMatter
