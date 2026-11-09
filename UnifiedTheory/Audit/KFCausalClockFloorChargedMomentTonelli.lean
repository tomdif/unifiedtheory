/- Nonnegative charge averaging is valid before any weighted state moment
is known finite. Tonelli connects the actual weighted momentum graph to
the mixed momentum-position moment without an integrability assumption. -/
import UnifiedTheory.Audit.KFCausalClockFloorRotatedAntiSymbol
import UnifiedTheory.Audit.KFCausalAveragedEnergyGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClockFloorChargedMomentTonelli
noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates action action_coordinates)
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow
open UnifiedTheory.Audit.KFCausalClockFloorRotatedAntiSymbol
open UnifiedTheory.Audit.KFCausalClockFloorAntisymmetricGraph (weightedAntiSymbol weightedAnti_graph_coe)
open UnifiedTheory.Audit.KFCausalAntisymmetricMomentumCoordinates (antiDirection)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum (clockMomentum)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph (l2_norm_square)

def kineticMass (ε h : ℝ) (i : Fin 2) (f : Hilbert) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (weightedAntiSymbol ε h i x^2*‖(chargeCoordinates f) x‖^2)

def chargedMass (ε h : ℝ) (i : Fin 2) (f : Hilbert) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (chargedWeight ε h i x*‖(chargeCoordinates f) x‖^2)

theorem kineticMass_graph (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (i : Fin 2) (f g : Hilbert) (hfg : (f,g) ∈ (clockMomentum ε h (antiDirection i)).graph) :
    kineticMass ε h i f = ENNReal.ofReal (‖g‖^2) := by
  have hn : (fun x => ‖(chargeCoordinates g) x‖^2) =ᵐ[volume]
      fun x => weightedAntiSymbol ε h i x^2*‖(chargeCoordinates f) x‖^2 := by
    filter_upwards [weightedAnti_graph_coe ε hε h hh i f g hfg] with x hx
    rw [hx,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (chargeCoordinates g))).mp
    (Lp.memLp (chargeCoordinates g))
  calc
    kineticMass ε h i f = ∫⁻ x, ENNReal.ofReal (‖(chargeCoordinates g) x‖^2) :=
      (lintegral_congr_ae (hn.fun_comp ENNReal.ofReal)).symm
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun _ => sq_nonneg _)),
        ← l2_norm_square,chargeCoordinates.norm_map]

theorem kineticMass_smul (ε h : ℝ) (i : Fin 2) (c : ℝ) (f : Hilbert) :
    kineticMass ε h i ((c : ℂ) • f) = ENNReal.ofReal (c^2)*kineticMass ε h i f := by
  unfold kineticMass
  rw [map_smul]
  calc
    _ = ∫⁻ x, ENNReal.ofReal (c^2)*
        ENNReal.ofReal (weightedAntiSymbol ε h i x^2*‖(chargeCoordinates f) x‖^2) := by
      apply lintegral_congr_ae
      filter_upwards [Lp.coeFn_smul (c : ℂ) (chargeCoordinates f)] with x hx
      rw [hx,Pi.smul_apply,norm_smul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
        ← ENNReal.ofReal_mul (sq_nonneg c)]
      congr 1
      ring
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem kineticMass_action (ε h : ℝ) (hh : h ≠ 0) (i : Fin 2) (θ : ℝ) (f : Hilbert) :
    kineticMass ε h i (action h hh θ f) =
      ∫⁻ x, ENNReal.ofReal (weightedAntiSymbol ε h i
        (flowEquiv (momentumScale h) (momentumScale_ne_zero h hh) (-θ) x)^2*
          ‖(chargeCoordinates f) x‖^2) := by
  unfold kineticMass
  rw [action_coordinates]
  have he : (∫⁻ x, ENNReal.ofReal (weightedAntiSymbol ε h i x^2*
      ‖(KFCausalMixedCircleAction.action (momentumScale h) (momentumScale_ne_zero h hh) θ
        (chargeCoordinates f)) x‖^2)) =
      ∫⁻ x, ENNReal.ofReal (weightedAntiSymbol ε h i x^2*
        ‖(chargeCoordinates f) (flowEquiv (momentumScale h) (momentumScale_ne_zero h hh) θ x)‖^2) := by
    apply lintegral_congr_ae
    filter_upwards [KFCausalMixedCircleAction.action_coe _ _ θ (chargeCoordinates f)] with x hx
    rw [hx,Function.comp_apply]
  rw [he]
  rw [MeasurePreserving.lintegral_map_equiv _
    (flowEquiv (momentumScale h) (momentumScale_ne_zero h hh) (-θ))
    (flow_preserves_volume _ _ (-θ))]
  apply lintegral_congr
  intro x
  rw [flow_compose,add_neg_cancel,flow_zero]

theorem kineticMass_angle (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (i : Fin 2) (f : Hilbert) :
    (∫⁻ θ, kineticMass ε h i (action h hh (2*Real.pi*θ) f) ∂angleMeasure) =
      chargedMass ε h i f := by
  simp_rw [kineticMass_action]
  have hc : Continuous (fun z : ℝ × Joint 2 4 => weightedAntiSymbol ε h i
      (flowEquiv (momentumScale h) (momentumScale_ne_zero h hh) (-(2*Real.pi*z.1)) z.2)^2) :=
    ((weightedAntiSymbol_continuous ε hε h i).comp
      ((flow_continuous _ _).comp ((continuous_const.mul continuous_fst).neg.prodMk continuous_snd))).pow 2
  have hf := ((Lp.aestronglyMeasurable (chargeCoordinates f)).norm.pow 2).comp_quasiMeasurePreserving
    (quasiMeasurePreserving_snd (μ := angleMeasure) (ν := (volume : Measure (Joint 2 4))))
  rw [lintegral_lintegral_swap (hc.aestronglyMeasurable.mul hf).aemeasurable.ennreal_ofReal]
  unfold chargedMass
  apply lintegral_congr
  intro x
  rw [← ofReal_integral_eq_lintegral_ofReal ((rotated_square_integrable ε hε h hh i x).mul_const _)
    (Filter.Eventually.of_forall (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))),
    integral_mul_const,rotated_square_mean ε hε h hh]

theorem chargedDensity_measurable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (i : Fin 2) (f : Hilbert) :
    AEStronglyMeasurable (fun x => chargedWeight ε h i x*‖(chargeCoordinates f) x‖^2) volume :=
  (chargedWeight_continuous ε hε h i).aestronglyMeasurable.mul
    ((Lp.aestronglyMeasurable (chargeCoordinates f)).norm.pow 2)

theorem chargedDensity_integrable_iff (ε : ℝ) (hε : 0 < ε) (h : ℝ) (i : Fin 2) (f : Hilbert) :
    Integrable (fun x => chargedWeight ε h i x*‖(chargeCoordinates f) x‖^2) ↔
      chargedMass ε h i f ≠ ⊤ :=
  (lintegral_ofReal_ne_top_iff_integrable (chargedDensity_measurable ε hε h i f)
    (Filter.Eventually.of_forall (fun x => mul_nonneg (chargedWeight_nonnegative ε hε h i x)
      (sq_nonneg _)))).symm

#print axioms kineticMass_graph
#print axioms kineticMass_smul
#print axioms kineticMass_action
#print axioms kineticMass_angle
#print axioms chargedDensity_measurable
#print axioms chargedDensity_integrable_iff

end
end UnifiedTheory.Audit.KFCausalClockFloorChargedMomentTonelli
