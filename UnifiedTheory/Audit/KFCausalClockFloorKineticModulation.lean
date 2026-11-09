/- Exact phase covariance of the actual clock half and ordered transverse
kinetic factors. Their natural kinetic graphs are closed. This does not
assert preservation of the longitudinal exponential or full matter form. -/
import UnifiedTheory.Audit.KFCausalPhysicalMomentumModulation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalClockFloorKineticModulation
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalPhysicalTransverseMomentum
open UnifiedTheory.Audit.KFCausalPhysicalMomentumModulation
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum (clockMomentum)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition

theorem clockHalf_graph_modulation (ε : ℝ) (l : Configuration →L[ℝ] ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (clockHalf ε).graph) :
    (modulation l f,modulation l g) ∈ (clockHalf ε).graph := by
  apply (clockHalf_graph ε _ _).mpr
  filter_upwards [modulation_coe l f,modulation_coe l g,(clockHalf_graph ε f g).mp hfg] with x hf hg hx
  rw [hf,hg,hx]
  ring

variable (ε : ℝ) (hε : 0 < ε)
include hε

theorem inverseL_modulation (l : Configuration →L[ℝ] ℝ) (f : Hilbert) :
    inverseL ε hε (modulation l f) = modulation l (inverseL ε hε f) := by
  apply Lp.ext
  filter_upwards [inverseAction_coe ε hε (modulation l f),modulation_coe l f,
    modulation_coe l (inverseL ε hε f),inverseAction_coe ε hε f] with x hx hf hm hi
  change inverseL ε hε (modulation l f) x = _ at hx
  change inverseL ε hε f x = _ at hi
  rw [hx,hf,hm,hi]
  ring

theorem kinetic_graph_iff (h : ℝ) (v : Transverse) (f g : Hilbert) :
    (f,g) ∈ (clockMomentum ε h v).graph ↔ (inverseL ε hε f,g) ∈ (transverseMomentum h v).graph := by
  rw [clockMomentum,composition_graph]
  constructor
  · rintro ⟨y,hy,hg⟩
    rw [(inverseL_graph ε hε f y).mp hy] at hg
    exact hg
  · intro hg
    exact ⟨_,(inverseL_graph ε hε f _).mpr rfl,hg⟩

theorem kinetic_closed (h : ℝ) (v : Transverse) : (clockMomentum ε h v).IsClosed := by
  let T := (inverseL ε hε).prodMap (ContinuousLinearMap.id ℂ Hilbert)
  have he : ((clockMomentum ε h v).graph : Set (Hilbert × Hilbert)) =
      T ⁻¹' ((transverseMomentum h v).graph : Set (Hilbert × Hilbert)) := by
    ext z
    exact kinetic_graph_iff ε hε h v z.1 z.2
  change IsClosed ((clockMomentum ε h v).graph : Set (Hilbert × Hilbert))
  rw [he]
  exact (transverseMomentum_closed h v).preimage T.continuous

theorem kinetic_graph_modulation (h : ℝ) (hh : h ≠ 0) (v : Transverse)
    (l : Configuration →L[ℝ] ℝ) (f g : Hilbert) (hfg : (f,g) ∈ (clockMomentum ε h v).graph) :
    (modulation l f,modulation l (g+((h*l (0,v):ℝ):ℂ) • inverseL ε hε f)) ∈
      (clockMomentum ε h v).graph := by
  rw [kinetic_graph_iff ε hε,inverseL_modulation]
  exact momentum_graph_modulation h hh v l _ _ ((kinetic_graph_iff ε hε h v f g).mp hfg)

theorem kinetic_domain_modulation (h : ℝ) (hh : h ≠ 0) (v : Transverse)
    (l : Configuration →L[ℝ] ℝ) (f : Hilbert) :
    modulation l f ∈ (clockMomentum ε h v).domain ↔ f ∈ (clockMomentum ε h v).domain := by
  constructor
  · intro hf
    have he := kinetic_graph_modulation ε hε h hh v (-l) _ _ ((clockMomentum ε h v).mem_graph ⟨_,hf⟩)
    rw [modulation_inverse] at he
    exact LinearPMap.mem_domain_of_mem_graph he
  · intro hf
    exact LinearPMap.mem_domain_of_mem_graph
      (kinetic_graph_modulation ε hε h hh v l f _ ((clockMomentum ε h v).mem_graph ⟨f,hf⟩))

theorem kinetic_graph_boost (h : ℝ) (hh : h ≠ 0) (v : Transverse)
    (l : Configuration →L[ℝ] ℝ) (f g : Hilbert) (hfg : (f,g) ∈ (clockMomentum ε h v).graph) :
    (modulation (h⁻¹ • l) f,modulation (h⁻¹ • l) (g+(l (0,v):ℂ) • inverseL ε hε f)) ∈
      (clockMomentum ε h v).graph := by
  rw [kinetic_graph_iff ε hε,inverseL_modulation]
  exact momentum_graph_boost h hh v l _ _ ((kinetic_graph_iff ε hε h v f g).mp hfg)

theorem kinetic_boost_error (h : ℝ) (hh : h ≠ 0) (v : Transverse)
    (l : Configuration →L[ℝ] ℝ) (f g k : Hilbert)
    (hfg : (f,g) ∈ (clockMomentum ε h v).graph)
    (hfk : (modulation (h⁻¹ • l) f,k) ∈ (clockMomentum ε h v).graph) :
    ‖k-(l (0,v):ℂ) • modulation (h⁻¹ • l) (inverseL ε hε f)‖ = ‖g‖ := by
  have he := (clockMomentum ε h v).mem_graph_snd_inj' hfk
    (kinetic_graph_boost ε hε h hh v l f g hfg) rfl
  dsimp only [Prod.snd] at he
  rw [he,map_add,map_smul,add_sub_cancel_right,(modulation (h⁻¹ • l)).norm_map]

theorem kinetic_modulation_bound (h : ℝ) (hh : h ≠ 0) (v : Transverse)
    (l : Configuration →L[ℝ] ℝ) (f g k : Hilbert)
    (hfg : (f,g) ∈ (clockMomentum ε h v).graph)
    (hfk : (modulation l f,k) ∈ (clockMomentum ε h v).graph) :
    ‖k-modulation l g‖ ≤ |h| * |l (0,v)| * (Real.sqrt ε)⁻¹*‖f‖ := by
  have he := (clockMomentum ε h v).mem_graph_snd_inj' hfk
    (kinetic_graph_modulation ε hε h hh v l f g hfg) rfl
  dsimp only [Prod.snd] at he
  rw [he,map_add,add_sub_cancel_left,map_smul,norm_smul,(modulation l).norm_map,
    Complex.norm_real,Real.norm_eq_abs,abs_mul]
  have hi := inverseAction_norm_bound ε hε f
  change ‖inverseL ε hε f‖ ≤ _ at hi
  exact (mul_le_mul_of_nonneg_left hi (mul_nonneg (abs_nonneg h) (abs_nonneg _))).trans_eq (by ring)

#print axioms clockHalf_graph_modulation
#print axioms inverseL_modulation
#print axioms kinetic_graph_iff
#print axioms kinetic_closed
#print axioms kinetic_graph_modulation
#print axioms kinetic_domain_modulation
#print axioms kinetic_graph_boost
#print axioms kinetic_boost_error
#print axioms kinetic_modulation_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorKineticModulation
