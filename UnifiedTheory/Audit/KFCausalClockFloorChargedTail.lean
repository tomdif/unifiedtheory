/- The positive clock moment and inverse-clock weighted charged moment
control a genuine mixed position/momentum tail. The two quantities commute
in the existing charge representation; no full phase-space law is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedChargedMoment

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClockFloorChargedTail
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalClockFloorAntisymmetricGraph (inverseL_charge_coe)
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse (inverseL inverseL_graph)
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf (clockHalf half_inverse_graph)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (clock_positive)
open UnifiedTheory.Audit.KFCausalClockFloorRotatedAntiSymbol
open UnifiedTheory.Audit.KFCausalClockFloorAveragedChargedMoment (chargedMoment)
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph (l2_norm_square)

theorem chargeClockHalf_coe (ε : ℝ) (hε : 0 < ε) (f g : Hilbert)
    (hg : (f,g) ∈ (clockHalf ε).graph) :
    chargeCoordinates g =ᵐ[volume] fun x =>
      (Real.sqrt (clock ε (x (.inr 0))) : ℂ)*(chargeCoordinates f) x := by
  have he := (inverseL_graph ε hε g f).mp ((half_inverse_graph ε hε f g).mp hg)
  have hi := inverseL_charge_coe ε hε g
  rw [← he] at hi
  filter_upwards [hi] with x hx
  have hc : (Real.sqrt (clock ε (x (.inr 0))) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (clock_positive ε _ hε.le)).ne'
  rw [hx,← mul_assoc,mul_inv_cancel₀ hc,one_mul]

theorem chargeClock_density (ε : ℝ) (hε : 0 < ε) (f g : Hilbert)
    (hg : (f,g) ∈ (clockHalf ε).graph) :
    (fun x => ‖(chargeCoordinates g) x‖^2) =ᵐ[volume]
      fun x => clock ε (x (.inr 0))*‖(chargeCoordinates f) x‖^2 := by
  filter_upwards [chargeClockHalf_coe ε hε f g hg] with x hx
  rw [hx,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    Real.sq_sqrt (clock_positive ε _ hε.le).le]

theorem chargeClock_integrable (ε : ℝ) (hε : 0 < ε) (f g : Hilbert)
    (hg : (f,g) ∈ (clockHalf ε).graph) :
    Integrable (fun x => clock ε (x (.inr 0))*‖(chargeCoordinates f) x‖^2) :=
  ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (chargeCoordinates g))).mp
    (Lp.memLp (chargeCoordinates g))).congr (chargeClock_density ε hε f g hg)

theorem chargeClock_integral (ε : ℝ) (hε : 0 < ε) (f g : Hilbert)
    (hg : (f,g) ∈ (clockHalf ε).graph) :
    (∫ x, clock ε (x (.inr 0))*‖(chargeCoordinates f) x‖^2) = ‖g‖^2 := by
  rw [← integral_congr_ae (chargeClock_density ε hε f g hg),← l2_norm_square,chargeCoordinates.norm_map]

def planeTail (h R : ℝ) (i : Fin 2) (f : Hilbert) : ℝ :=
  ∫ x : Joint 2 4 in {x | R^2 ≤ momentum h i x^2+position i x^2}, ‖(chargeCoordinates f) x‖^2

theorem planeTail_nonnegative (h R : ℝ) (i : Fin 2) (f : Hilbert) : 0 ≤ planeTail h R i f :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem planeTail_bound (ε : ℝ) (hε : 0 < ε) (h R : ℝ) (i : Fin 2) (f g : Hilbert)
    (hg : (f,g) ∈ (clockHalf ε).graph)
    (hi : Integrable (fun x => chargedWeight ε h i x*‖(chargeCoordinates f) x‖^2)) :
    2*R*planeTail h R i f ≤ ‖g‖^2+chargedMoment ε h i f := by
  have hs : MeasurableSet {x : Joint 2 4 | R^2 ≤ momentum h i x^2+position i x^2} := by
    apply measurableSet_le measurable_const
    unfold momentum position
    fun_prop
  have hf := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (chargeCoordinates f))).mp
    (Lp.memLp (chargeCoordinates f))
  rw [← chargeClock_integral ε hε f g hg,chargedMoment,planeTail,← integral_indicator hs,
    ← integral_const_mul,← integral_add (chargeClock_integrable ε hε f g hg) hi]
  apply integral_mono_ae ((hf.indicator hs).const_mul _) ((chargeClock_integrable ε hε f g hg).add hi)
  filter_upwards [] with x
  simp only [Pi.add_apply]
  by_cases hx : R^2 ≤ momentum h i x^2+position i x^2
  · rw [Set.indicator_of_mem (show x ∈ {x : Joint 2 4 | R^2 ≤ momentum h i x^2+position i x^2} from hx)]
    have hc := clock_positive ε (x (.inr 0)) hε.le
    have hw : clock ε (x (.inr 0))*chargedWeight ε h i x = momentum h i x^2+position i x^2 := by
      unfold chargedWeight
      exact mul_div_cancel₀ _ hc.ne'
    have hp : 2*R ≤ clock ε (x (.inr 0))+chargedWeight ε h i x := by
      have hsq := sq_nonneg (clock ε (x (.inr 0))-R)
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hp (sq_nonneg ‖(chargeCoordinates f) x‖)]
  · rw [Set.indicator_of_notMem (show x ∉ {x : Joint 2 4 | R^2 ≤ momentum h i x^2+position i x^2} from hx),mul_zero]
    exact add_nonneg (mul_nonneg (clock_positive ε _ hε.le).le (sq_nonneg _))
      (mul_nonneg (chargedWeight_nonnegative ε hε h i x) (sq_nonneg _))

#print axioms chargeClockHalf_coe
#print axioms chargeClock_density
#print axioms chargeClock_integrable
#print axioms chargeClock_integral
#print axioms planeTail_nonnegative
#print axioms planeTail_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorChargedTail
