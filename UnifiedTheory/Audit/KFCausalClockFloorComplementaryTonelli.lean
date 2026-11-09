/- Nonnegative averaging derives the complementary weighted quantum
moments without assuming their integrability. The neutral momentum term
is part of the second averaged square. -/
import UnifiedTheory.Audit.KFCausalClockFloorSymmetricOrbitGraph
import UnifiedTheory.Audit.KFCausalAveragedEnergyGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClockFloorComplementaryTonelli
noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalChargeTransverseSplit (dualPhysical)
open UnifiedTheory.Audit.KFCausalClockFloorSymmetricOrbitGraph (rotated_clockMomentum_coe)
open UnifiedTheory.Audit.KFCausalSymmetricMomentumCoordinates (symmetricDirection)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum (clockMomentum)
open UnifiedTheory.Audit.KFCausalComplementaryChargeSymbol
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (clock_positive)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph (l2_norm_square)

def rotatedMass (ε h : ℝ) (hh : h ≠ 0) (θ : ℝ) (i : Fin 2) (f : Hilbert) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (rotatedWeightedSymbol ε h hh θ i x^2*‖(dualPhysical f) x‖^2)

def complementaryMass (ε h : ℝ) (i : Fin 2) (f : Hilbert) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (complementaryWeight ε h i x*‖(dualPhysical f) x‖^2)

theorem rotatedMass_graph (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (θ : ℝ)
    (i : Fin 2) (f g : Hilbert) (hfg : (action h hh θ f,g) ∈ (clockMomentum ε h (symmetricDirection i)).graph) :
    rotatedMass ε h hh θ i f = ENNReal.ofReal (‖g‖^2) := by
  have hn : (fun x => ‖(dualPhysical (action h hh (-θ) g)) x‖^2) =ᵐ[volume]
      fun x => rotatedWeightedSymbol ε h hh θ i x^2*‖(dualPhysical f) x‖^2 := by
    filter_upwards [rotated_clockMomentum_coe ε hε h hh θ i f g hfg] with x hx
    rw [hx,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (dualPhysical (action h hh (-θ) g)))).mp
    (Lp.memLp (dualPhysical (action h hh (-θ) g)))
  calc
    _ = ∫⁻ x, ENNReal.ofReal (‖(dualPhysical (action h hh (-θ) g)) x‖^2) :=
      (lintegral_congr_ae (hn.fun_comp ENNReal.ofReal)).symm
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun _ => sq_nonneg _)),
        ← l2_norm_square,dualPhysical.norm_map,(action h hh (-θ)).norm_map]

theorem rotatedMass_smul (ε h : ℝ) (hh : h ≠ 0) (θ : ℝ) (i : Fin 2) (c : ℝ) (f : Hilbert) :
    rotatedMass ε h hh θ i ((c : ℂ) • f) = ENNReal.ofReal (c^2)*rotatedMass ε h hh θ i f := by
  unfold rotatedMass
  rw [map_smul]
  calc
    _ = ∫⁻ x, ENNReal.ofReal (c^2)*ENNReal.ofReal (rotatedWeightedSymbol ε h hh θ i x^2*‖(dualPhysical f) x‖^2) := by
      apply lintegral_congr_ae
      filter_upwards [Lp.coeFn_smul (c : ℂ) (dualPhysical f)] with x hx
      rw [hx,Pi.smul_apply,norm_smul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
        ← ENNReal.ofReal_mul (sq_nonneg c)]
      congr 1
      ring
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem rotatedMass_half_graph (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (θ : ℝ)
    (i : Fin 2) (f g : Hilbert)
    (hfg : ((Real.sqrt (1/2) : ℂ) • action h hh θ f,g) ∈ (clockMomentum ε h (symmetricDirection i)).graph) :
    ENNReal.ofReal (1/2)*rotatedMass ε h hh θ i f = ENNReal.ofReal (‖g‖^2) := by
  have hg : (action h hh θ ((Real.sqrt (1/2) : ℂ) • f),g) ∈ (clockMomentum ε h (symmetricDirection i)).graph := by
    simpa only [map_smul] using hfg
  have he := rotatedMass_graph ε hε h hh θ i _ g hg
  rw [rotatedMass_smul,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/2)] at he
  exact he

theorem rotatedMass_angle (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (i : Fin 2) (f : Hilbert) :
    (∫⁻ θ, rotatedMass ε h hh (2*Real.pi*θ) i f ∂angleMeasure) = complementaryMass ε h i f := by
  have hc : Continuous (fun z : ℝ × Joint 5 1 => rotatedWeightedSymbol ε h hh (2*Real.pi*z.1) i z.2^2) := by
    simp_rw [rotatedWeighted_square ε hε h hh]
    unfold complementaryMomentum complementaryPosition neutralTerm neutralMomentum
    fin_cases i <;> simp only [Matrix.cons_val_zero',Matrix.cons_val_succ']
    all_goals
      apply Continuous.div (by fun_prop) (by unfold clock; fun_prop)
      intro z
      exact (clock_positive ε (z.2 (.inr 0)) hε.le).ne'
  have hf := ((Lp.aestronglyMeasurable (dualPhysical f)).norm.pow 2).comp_quasiMeasurePreserving
    (quasiMeasurePreserving_snd (μ := angleMeasure) (ν := (volume : Measure (Joint 5 1))))
  unfold rotatedMass
  rw [lintegral_lintegral_swap (hc.aestronglyMeasurable.mul hf).aemeasurable.ennreal_ofReal]
  unfold complementaryMass
  apply lintegral_congr
  intro x
  rw [← ofReal_integral_eq_lintegral_ofReal ((rotatedWeighted_integrable ε hε h hh i x).mul_const _)
    (Filter.Eventually.of_forall (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))),
    integral_mul_const,rotatedWeighted_mean ε hε h hh]

theorem complementaryDensity_measurable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (i : Fin 2) (f : Hilbert) :
    AEStronglyMeasurable (fun x => complementaryWeight ε h i x*‖(dualPhysical f) x‖^2) volume :=
  (complementaryWeight_continuous ε hε h i).aestronglyMeasurable.mul
    ((Lp.aestronglyMeasurable (dualPhysical f)).norm.pow 2)

theorem complementaryDensity_integrable_iff (ε : ℝ) (hε : 0 < ε) (h : ℝ) (i : Fin 2) (f : Hilbert) :
    Integrable (fun x => complementaryWeight ε h i x*‖(dualPhysical f) x‖^2) ↔
      complementaryMass ε h i f ≠ ⊤ :=
  (lintegral_ofReal_ne_top_iff_integrable (complementaryDensity_measurable ε hε h i f)
    (Filter.Eventually.of_forall (fun x => mul_nonneg (complementaryWeight_nonnegative ε hε h i x)
      (sq_nonneg _)))).symm

#print axioms rotatedMass_graph
#print axioms rotatedMass_smul
#print axioms rotatedMass_half_graph
#print axioms rotatedMass_angle
#print axioms complementaryDensity_measurable
#print axioms complementaryDensity_integrable_iff

end
end UnifiedTheory.Audit.KFCausalClockFloorComplementaryTonelli
