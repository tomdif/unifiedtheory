/- Both signs of the actual longitudinal exponential control a genuine
longitudinal second moment and its maximal momentum domain. The negative
exponential is an explicit hypothesis here, supplied for actual initial
states in the successor module; it is not inferred from positive energy. -/
import UnifiedTheory.Audit.KFCausalClockFloorPlanckSign

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorTwoSidedSpectralControl
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorFourierCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorFourierMultiplier
open UnifiedTheory.Audit.KFCausalClockFloorExponential
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum (longitudinalMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalTails
open UnifiedTheory.Audit.KFCausalClockFloorPlanckSign (symbol_neg)
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph (l2_norm_square)

theorem negative_tail_bound (ε : ℝ) (hε : 0 < ε) (h R : ℝ) (f g : Hilbert)
    (hg : (f,g) ∈ (longitudinalExponential ε hε (-h) (1/2)).graph) :
    negativeTail ε hε h R f ≤ Real.exp (-R)*‖g‖^2 := by
  apply LE.le.trans _ (positive_tail_bound ε hε (-h) R f g hg)
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (coupledFourier ε hε f))).mp
    (Lp.memLp (coupledFourier ε hε f))
  apply setIntegral_mono_set hi.integrableOn (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
  filter_upwards [] with k
  intro hk
  change symbol h k < -R at hk
  change R ≤ symbol (-h) k
  rw [symbol_neg]
  linarith

theorem square_exponential_bound (x : ℝ) : x^2 ≤ 2*(Real.exp x+Real.exp (-x)) := by
  by_cases hx : 0 ≤ x
  · have he := Real.pow_div_factorial_le_exp x hx 2
    norm_num at he
    nlinarith [Real.exp_pos (-x)]
  · have he := Real.pow_div_factorial_le_exp (-x) (by linarith) 2
    norm_num at he
    nlinarith [Real.exp_pos x]

theorem two_exponential_density (ε : ℝ) (hε : 0 < ε) (h : ℝ) (f gp gn : Hilbert)
    (hp : (f,gp) ∈ (longitudinalExponential ε hε h (1/2)).graph)
    (hn : (f,gn) ∈ (longitudinalExponential ε hε (-h) (1/2)).graph) :
    Integrable (fun k => ‖(symbol h k:ℂ)*(coupledFourier ε hε f) k‖^2) ∧
      (∫ k, ‖(symbol h k:ℂ)*(coupledFourier ε hε f) k‖^2) ≤ 2*(‖gp‖^2+‖gn‖^2) := by
  obtain ⟨hip,hep⟩ := half_graph_energy ε hε h f gp hp
  obtain ⟨hin,hen⟩ := half_graph_energy ε hε (-h) f gn hn
  have hm := ((Complex.measurable_ofReal.comp (symbol_measurable h)).aestronglyMeasurable.mul
    (Lp.aestronglyMeasurable (coupledFourier ε hε f))).norm.pow 2
  have hi := (hip.add hin).const_mul 2
  simp only [Pi.add_apply] at hi
  have hb : ∀ k, ‖(symbol h k:ℂ)*(coupledFourier ε hε f) k‖^2 ≤
      2*(Real.exp (symbol h k)*‖(coupledFourier ε hε f) k‖^2+
        Real.exp (symbol (-h) k)*‖(coupledFourier ε hε f) k‖^2) := by
    intro k
    rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,symbol_neg]
    nlinarith only [mul_le_mul_of_nonneg_right (square_exponential_bound (symbol h k))
      (sq_nonneg ‖(coupledFourier ε hε f) k‖)]
  have hj := hi.mono' hm (Filter.Eventually.of_forall (fun k => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact hb k))
  refine ⟨hj,?_⟩
  have he := integral_mono hj hi hb
  rw [integral_const_mul,integral_add hip hin,hep,hen] at he
  exact he

theorem two_exponential_domain (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (f gp gn : Hilbert)
    (hp : (f,gp) ∈ (longitudinalExponential ε hε h (1/2)).graph)
    (hn : (f,gn) ∈ (longitudinalExponential ε hε (-h) (1/2)).graph) :
    f ∈ (longitudinalMomentum ε hε h).domain := by
  apply (momentum_domain_fourier_iff ε hε h hh f).mpr
  exact (memLp_two_iff_integrable_sq_norm
    ((Complex.measurable_ofReal.comp (symbol_measurable h)).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable (coupledFourier ε hε f)))).mpr
    (two_exponential_density ε hε h f gp gn hp hn).1

theorem two_exponential_momentum_bound (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (f gp gn : Hilbert)
    (hp : (f,gp) ∈ (longitudinalExponential ε hε h (1/2)).graph)
    (hn : (f,gn) ∈ (longitudinalExponential ε hε (-h) (1/2)).graph) :
    ‖longitudinalMomentum ε hε h ⟨f,two_exponential_domain ε hε h hh f gp gn hp hn⟩‖^2 ≤
      2*(‖gp‖^2+‖gn‖^2) := by
  let u : (longitudinalMomentum ε hε h).domain :=
    ⟨f,two_exponential_domain ε hε h hh f gp gn hp hn⟩
  have he : ‖longitudinalMomentum ε hε h u‖^2 =
      ∫ k, ‖(symbol h k:ℂ)*(coupledFourier ε hε f) k‖^2 := by
    rw [← (coupledFourier ε hε).norm_map (longitudinalMomentum ε hε h u),l2_norm_square]
    apply integral_congr_ae
    filter_upwards [momentum_fourier_coe ε hε h hh u] with k hk
    rw [hk]
  exact he.trans_le (two_exponential_density ε hε h f gp gn hp hn).2

#print axioms negative_tail_bound
#print axioms square_exponential_bound
#print axioms two_exponential_density
#print axioms two_exponential_domain
#print axioms two_exponential_momentum_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorTwoSidedSpectralControl
