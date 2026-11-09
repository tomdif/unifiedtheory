/- Exact graph and domain covariance of the full longitudinal exponential
and the actual ordered vacuum factor under chart-clock modulation. -/
import UnifiedTheory.Audit.KFCausalClockFloorChartModulation
import UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorExponentialModulation
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalClockFloorChartModulation
open UnifiedTheory.Audit.KFCausalClockFloorFourierCoordinates (coupledFourier)
open UnifiedTheory.Audit.KFCausalClockFloorFourierMultiplier (symbol)
open UnifiedTheory.Audit.KFCausalClockFloorExponential
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf (inverseAction_coe)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)

variable (ε : ℝ) (hε : 0 < ε)

theorem symbol_shift (h r : ℝ) (x : Space) :
    symbol h (x+ -(r • clockVector)) = symbol h x-2*Real.pi*h*r := by
  change 2*Real.pi*h*(x 0+ -(r*1)) = 2*Real.pi*h*x 0-2*Real.pi*h*r
  ring

theorem exponential_graph_modulation (h a r : ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (longitudinalExponential ε hε h a).graph) :
    (modulation ε r f,(Real.exp (a*(2*Real.pi*h*r)):ℂ) • modulation ε r g) ∈
      (longitudinalExponential ε hε h a).graph := by
  rw [longitudinal_exponential_graph,map_smul,fourier_modulation,fourier_modulation]
  filter_upwards [Lp.coeFn_smul (Real.exp (a*(2*Real.pi*h*r)):ℂ)
      (KFCausalFourierTranslation.translation (-(r • clockVector)) (coupledFourier ε hε g)),
    KFCausalFourierTranslation.translation_coe (-(r • clockVector)) (coupledFourier ε hε g),
    KFCausalFourierTranslation.translation_coe (-(r • clockVector)) (coupledFourier ε hε f),
    (KFCausalFourierTranslation.shift_preserves_volume (-(r • clockVector))).quasiMeasurePreserving.ae
      ((longitudinal_exponential_graph ε hε h a f g).mp hfg)] with x hs hg hf he
  change (coupledFourier ε hε g) (x+ -(r • clockVector)) =
    (Real.exp (a*symbol h (x+ -(r • clockVector))):ℂ)*
      (coupledFourier ε hε f) (x+ -(r • clockVector)) at he
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hg,hf,he,← mul_assoc]
  congr 1
  rw [← Complex.ofReal_mul,← Real.exp_add,symbol_shift]
  congr 2
  ring

theorem exponential_domain_modulation (h a r : ℝ) (f : Hilbert) :
    modulation ε r f ∈ (longitudinalExponential ε hε h a).domain ↔
      f ∈ (longitudinalExponential ε hε h a).domain := by
  constructor
  · intro hf
    have hg := exponential_graph_modulation ε hε h a (-r) _ _
      ((longitudinalExponential ε hε h a).mem_graph ⟨_,hf⟩)
    rw [modulation_inverse] at hg
    exact LinearPMap.mem_domain_of_mem_graph hg
  · intro hf
    exact LinearPMap.mem_domain_of_mem_graph (exponential_graph_modulation ε hε h a r f _
      ((longitudinalExponential ε hε h a).mem_graph ⟨f,hf⟩))

theorem inverseL_modulation (r : ℝ) (f : Hilbert) :
    inverseL ε hε (modulation ε r f) = modulation ε r (inverseL ε hε f) := by
  apply Lp.ext
  filter_upwards [inverseAction_coe ε hε (modulation ε r f),modulation_coe ε r f,
    modulation_coe ε r (inverseL ε hε f),inverseAction_coe ε hε f] with x hx hf hm hi
  change inverseL ε hε (modulation ε r f) x = _ at hx
  change inverseL ε hε f x = _ at hi
  rw [hx,hf,hm,hi]
  ring

theorem ordered_graph_modulation (h r : ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (orderedExponential ε hε h).graph) :
    (modulation ε r f,(Real.exp (Real.pi*h*r):ℂ) • modulation ε r g) ∈
      (orderedExponential ε hε h).graph := by
  rw [ordered_graph_iff,inverseL_modulation]
  have he := exponential_graph_modulation ε hε h (1/2) r _ g
    ((ordered_graph_iff ε hε h f g).mp hfg)
  rw [show (1/2:ℝ)*(2*Real.pi*h*r) = Real.pi*h*r by ring] at he
  exact he

theorem ordered_domain_modulation (h r : ℝ) (f : Hilbert) :
    modulation ε r f ∈ (orderedExponential ε hε h).domain ↔
      f ∈ (orderedExponential ε hε h).domain := by
  constructor
  · intro hf
    have hg := ordered_graph_modulation ε hε h (-r) _ _
      ((orderedExponential ε hε h).mem_graph ⟨_,hf⟩)
    rw [modulation_inverse] at hg
    exact LinearPMap.mem_domain_of_mem_graph hg
  · intro hf
    exact LinearPMap.mem_domain_of_mem_graph (ordered_graph_modulation ε hε h r f _
      ((orderedExponential ε hε h).mem_graph ⟨f,hf⟩))

theorem ordered_energy_modulation (h r : ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (orderedExponential ε hε h).graph) :
    ∃ g' : Hilbert, (modulation ε r f,g') ∈ (orderedExponential ε hε h).graph ∧
      ‖g'‖^2 = Real.exp (2*Real.pi*h*r)*‖g‖^2 := by
  refine ⟨_,ordered_graph_modulation ε hε h r f g hfg,?_⟩
  rw [norm_smul,LinearIsometryEquiv.norm_map,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),mul_pow,← Real.exp_nat_mul]
  congr 2
  ring

#print axioms symbol_shift
#print axioms exponential_graph_modulation
#print axioms exponential_domain_modulation
#print axioms inverseL_modulation
#print axioms ordered_graph_modulation
#print axioms ordered_domain_modulation
#print axioms ordered_energy_modulation
end
end UnifiedTheory.Audit.KFCausalClockFloorExponentialModulation
