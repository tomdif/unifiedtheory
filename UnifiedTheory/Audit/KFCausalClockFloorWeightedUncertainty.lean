/- A canonical pair in the actual mixed representation, weighted by the
bounded inverse half-clock. Its position and momentum domains follow from
the previously derived charged and complementary moments. -/
import UnifiedTheory.Audit.KFCausalCanonicalUncertainty
import UnifiedTheory.Audit.KFCausalChargeDualMomentumDomain
import UnifiedTheory.Audit.KFCausalMultiplierMomentBound
import UnifiedTheory.Audit.KFCausalClockFloorAveragedChargedMoment
import UnifiedTheory.Audit.KFCausalClockFloorAveragedComplementaryMoment

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorWeightedUncertainty
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalChargeTransverseSplit
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (clock_positive)
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse (inverseL)
open UnifiedTheory.Audit.KFCausalClockFloorAntisymmetricGraph (inverseL_charge_coe)
open UnifiedTheory.Audit.KFCausalClockFloorDualClock (inverseL_dual_coe)
open UnifiedTheory.Audit.KFCausalClockFloorRotatedAntiSymbol (chargedWeight)
open UnifiedTheory.Audit.KFCausalComplementaryChargeSymbol
open UnifiedTheory.Audit.KFCausalClockFloorAveragedChargedMoment (chargedMoment)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedComplementaryMoment (complementaryMoment)
open UnifiedTheory.Audit.KFCausalMultiplierMomentBound (multiplier_output)
open UnifiedTheory.Audit.KFCausalDirectionalTranslationMomentum (spectralMomentum)
open UnifiedTheory.Audit.KFCausalChargeDualMomentumDomain (dualMomentum_graph_iff)

def coordinate : Joint 2 4 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 ⊕ Fin 4 => ℝ) (.inr 1)
def direction : Joint 2 4 := WithLp.toLp 2 (Pi.single (.inr 1) 1)

theorem coordinate_direction : coordinate direction = 1 := by simp [coordinate,direction]
theorem direction_clock : direction (.inr 0) = 0 := by simp [direction]

theorem direction_symbol (h : ℝ) (x : Joint 5 1) :
    KFCausalChargeDualMomentum.dualSymbol h direction x = complementaryMomentum h 0 x := by
  simp [KFCausalChargeDualMomentum.dualSymbol,KFCausalChargeDualMomentum.transverseBlock,
    repackIsometry,repackEquiv,repack,split_fst,PiLp.inner_apply,RCLike.inner_apply,
    Fin.sum_univ_succ,direction,complementaryMomentum,symmetricDualIndex,
    KFCausalNormalizedChargeFlow.momentumScale]

theorem weighted_position_output (ε : ℝ) (hε : 0 < ε) (h : ℝ) (f : Hilbert)
    (hf : Integrable (fun x => chargedWeight ε h 0 x*‖(chargeCoordinates f) x‖^2)) :
    ∃ q : JointHilbert 2 4,
      q =ᵐ[volume] (fun x => (coordinate x : ℂ)*(chargeCoordinates (inverseL ε hε f)) x) ∧
      ‖q‖^2 ≤ chargedMoment ε h 0 f := by
  apply multiplier_output (chargeCoordinates (inverseL ε hε f)) coordinate coordinate.continuous.measurable
    _ hf
  filter_upwards [inverseL_charge_coe ε hε f] with x hx
  rw [hx,norm_mul,norm_inv,mul_pow,inv_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    Real.sq_sqrt (clock_positive ε _ hε.le).le]
  change (x (.inr 1))^2*((clock ε (x (.inr 0)))⁻¹*‖(chargeCoordinates f) x‖^2) ≤
    ((KFCausalClockFloorRotatedAntiSymbol.momentum h 0 x)^2+(x (.inr 1))^2)/
      clock ε (x (.inr 0))*‖(chargeCoordinates f) x‖^2
  have hle : (x (.inr 1))^2 ≤ (KFCausalClockFloorRotatedAntiSymbol.momentum h 0 x)^2+(x (.inr 1))^2 :=
    le_add_of_nonneg_left (sq_nonneg _)
  have hb := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hle
      (clock_positive ε (x (.inr 0)) hε.le).le) (sq_nonneg ‖(chargeCoordinates f) x‖)
  simpa only [div_eq_mul_inv,mul_assoc] using hb

theorem weighted_momentum_output (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (f : Hilbert)
    (hf : Integrable (fun x => complementaryWeight ε h 0 x*‖(dualPhysical f) x‖^2)) :
    ∃ p : JointHilbert 2 4,
      (chargeCoordinates (inverseL ε hε f),p) ∈ (spectralMomentum h direction).graph ∧
      ‖p‖^2 ≤ complementaryMoment ε h 0 f := by
  have hm : Measurable (complementaryMomentum h 0) := by unfold complementaryMomentum; fun_prop
  obtain ⟨p,hp,hb⟩ := multiplier_output (dualPhysical (inverseL ε hε f))
    (complementaryMomentum h 0) hm _ hf (by
      filter_upwards [inverseL_dual_coe ε hε f] with x hx
      rw [hx,norm_mul,norm_inv,mul_pow,inv_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
        Real.sq_sqrt (clock_positive ε _ hε.le).le]
      have hle : complementaryMomentum h 0 x^2 ≤ complementarySquare h 0 x := by
        unfold complementarySquare
        nlinarith [sq_nonneg (complementaryPosition 0 x),sq_nonneg (neutralTerm h 0 x)]
      have hh := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hle (clock_positive ε (x (.inr 0)) hε.le).le) (sq_nonneg ‖(dualPhysical f) x‖)
      simpa only [complementaryWeight,div_eq_mul_inv,mul_assoc] using hh)
  refine ⟨dualMixed.symm p,?_,?_⟩
  · apply (dualMomentum_graph_iff h hne direction direction_clock _ _).mpr
    rw [dualMixed.apply_symm_apply]
    simpa only [direction_symbol] using hp
  · simpa only [dualMixed.symm.norm_map] using hb

theorem weighted_uncertainty (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (f : Hilbert)
    (hq : Integrable (fun x => chargedWeight ε h 0 x*‖(chargeCoordinates f) x‖^2))
    (hp : Integrable (fun x => complementaryWeight ε h 0 x*‖(dualPhysical f) x‖^2)) :
    ∃ q p : JointHilbert 2 4,
      |h| * ‖inverseL ε hε f‖^2 ≤ 2*‖q‖*‖p‖ ∧
      ‖q‖^2 ≤ chargedMoment ε h 0 f ∧ ‖p‖^2 ≤ complementaryMoment ε h 0 f := by
  obtain ⟨q,hqg,hqb⟩ := weighted_position_output ε hε h f hq
  obtain ⟨p,hpg,hpb⟩ := weighted_momentum_output ε hε h hne f hp
  have hu := KFCausalCanonicalUncertainty.maximal_uncertainty h hne coordinate direction _ q p hqg hpg
  refine ⟨q,p,?_,hqb,hpb⟩
  simpa only [coordinate_direction,abs_one,mul_one,chargeCoordinates.norm_map] using hu

#print axioms coordinate_direction
#print axioms direction_clock
#print axioms direction_symbol
#print axioms weighted_position_output
#print axioms weighted_momentum_output
#print axioms weighted_uncertainty
end
end UnifiedTheory.Audit.KFCausalClockFloorWeightedUncertainty
