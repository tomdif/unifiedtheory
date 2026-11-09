/- The natural half-clock graph gives the actual weighted position integral.
Its energy controls the upper log-clock tail. Two one-sided tails bound
the probability outside a compact interval. -/
import UnifiedTheory.Audit.KFCausalClockFloorClockHalf
import UnifiedTheory.Audit.KFCausalClockFloorClockMomentLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorClockPositionMass
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (clock_positive)
open UnifiedTheory.Audit.KFCausalClockFloorClockMomentLaw (leftMass)
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph (l2_norm_square)

def clockMass (ε : ℝ) (f : Hilbert) : ℝ := ∫ x : Configuration, clock ε x.1*‖f x‖^2

theorem clockHalf_density (ε : ℝ) (hε : 0 < ε) (f g : Hilbert)
    (hg : (f,g) ∈ (clockHalf ε).graph) :
    (fun x => ‖g x‖^2) =ᵐ[volume] fun x => clock ε x.1*‖f x‖^2 := by
  filter_upwards [(clockHalf_graph ε f g).mp hg] with x hx
  rw [hx,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    halfWeight,Real.sq_sqrt (by positivity : 0 ≤ Real.exp x.1+ε)]
  rfl

theorem clockMass_integrable (ε : ℝ) (hε : 0 < ε) (f g : Hilbert)
    (hg : (f,g) ∈ (clockHalf ε).graph) :
    Integrable (fun x : Configuration => clock ε x.1*‖f x‖^2) :=
  ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)).congr
    (clockHalf_density ε hε f g hg)

theorem clockMass_eq (ε : ℝ) (hε : 0 < ε) (f g : Hilbert)
    (hg : (f,g) ∈ (clockHalf ε).graph) : clockMass ε f = ‖g‖^2 := by
  rw [clockMass,l2_norm_square]
  exact integral_congr_ae (clockHalf_density ε hε f g hg).symm

def rightMass (R : ℝ) (f : Hilbert) : ℝ := ∫ x : Configuration in {x | R ≤ x.1}, ‖f x‖^2

theorem rightMass_nonnegative (R : ℝ) (f : Hilbert) : 0 ≤ rightMass R f :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem rightMass_clock_bound (ε : ℝ) (hε : 0 < ε) (R : ℝ) (f g : Hilbert)
    (hg : (f,g) ∈ (clockHalf ε).graph) :
    Real.exp R*rightMass R f ≤ ‖g‖^2 := by
  have hset : MeasurableSet {x : Configuration | R ≤ x.1} := measurableSet_le measurable_const measurable_fst
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  rw [← clockMass_eq ε hε f g hg,rightMass,← integral_indicator hset,← integral_const_mul,clockMass]
  apply integral_mono_ae ((hi.indicator hset).const_mul _) (clockMass_integrable ε hε f g hg)
  filter_upwards [] with x
  by_cases hx : R ≤ x.1
  · rw [Set.indicator_of_mem (show x ∈ {x : Configuration | R ≤ x.1} from hx)]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    unfold clock
    linarith [Real.exp_le_exp.mpr hx]
  · rw [Set.indicator_of_notMem (show x ∉ {x : Configuration | R ≤ x.1} from hx),mul_zero]
    exact mul_nonneg (clock_positive ε x.1 hε.le).le (sq_nonneg _)

def outsideMass (S R : ℝ) (f : Hilbert) : ℝ :=
  ∫ x : Configuration in {x | x.1 ∉ Set.Icc S R}, ‖f x‖^2

theorem outsideMass_nonnegative (S R : ℝ) (f : Hilbert) : 0 ≤ outsideMass S R f :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem outsideMass_le_tails (S R : ℝ) (f : Hilbert) :
    outsideMass S R f ≤ leftMass S f+rightMass R f := by
  have hL : MeasurableSet {x : Configuration | x.1 ≤ S} := measurableSet_le measurable_fst measurable_const
  have hR : MeasurableSet {x : Configuration | R ≤ x.1} := measurableSet_le measurable_const measurable_fst
  have hO : MeasurableSet {x : Configuration | x.1 ∉ Set.Icc S R} :=
    ((measurableSet_Icc.preimage measurable_fst).compl)
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  rw [outsideMass,leftMass,rightMass,← integral_indicator hO,← integral_indicator hL,
    ← integral_indicator hR,← integral_add (hi.indicator hL) (hi.indicator hR)]
  apply integral_mono_ae (hi.indicator hO) ((hi.indicator hL).add (hi.indicator hR))
  filter_upwards [] with x
  simp only [Pi.add_apply]
  have hL0 : 0 ≤ ({z : Configuration | z.1 ≤ S}.indicator (fun z => ‖f z‖^2)) x :=
    Set.indicator_nonneg (fun _ _ => sq_nonneg _) _
  have hR0 : 0 ≤ ({z : Configuration | R ≤ z.1}.indicator (fun z => ‖f z‖^2)) x :=
    Set.indicator_nonneg (fun _ _ => sq_nonneg _) _
  by_cases ho : x.1 ∈ Set.Icc S R
  · rw [Set.indicator_of_notMem (show x ∉ {z : Configuration | z.1 ∉ Set.Icc S R} from fun h => h ho)]
    exact add_nonneg hL0 hR0
  · rw [Set.indicator_of_mem (show x ∈ {z : Configuration | z.1 ∉ Set.Icc S R} from ho)]
    by_cases hl : x.1 ≤ S
    · rw [Set.indicator_of_mem (show x ∈ {z : Configuration | z.1 ≤ S} from hl)]
      exact le_add_of_nonneg_right hR0
    · have hr : R ≤ x.1 := by
        by_contra hr
        exact ho ⟨le_of_not_ge hl,le_of_not_ge hr⟩
      rw [Set.indicator_of_mem (show x ∈ {z : Configuration | R ≤ z.1} from hr)]
      exact le_add_of_nonneg_left hL0

#print axioms clockHalf_density
#print axioms clockMass_integrable
#print axioms clockMass_eq
#print axioms rightMass_nonnegative
#print axioms rightMass_clock_bound
#print axioms outsideMass_nonnegative
#print axioms outsideMass_le_tails

end
end UnifiedTheory.Audit.KFCausalClockFloorClockPositionMass
