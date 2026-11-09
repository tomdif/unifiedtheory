/- Two-sided canonical clock tails and their exact charge invariance.
The maximal momentum graph supplies a second-moment bound; no claim is
made that the full Hamiltonian trajectory satisfies that bound. -/
import UnifiedTheory.Audit.KFCausalCanonicalClockProbability

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalCanonicalClockTails
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (Space fourierCoordinates)
open UnifiedTheory.Audit.KFCausalClockFloorFourierMultiplier (symbol)
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum (clockMomentum)
open UnifiedTheory.Audit.KFCausalCanonicalClockDerivative (clock_graph_fourier)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalCanonicalClockProbability (law symbol_continuous law_charge)
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph (l2_norm_square)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

def tail (h R : ℝ) (f : Hilbert) : ℝ :=
  ∫ k in {k | R^2 ≤ (symbol h k)^2}, ‖(fourierCoordinates f) k‖^2

theorem tail_nonnegative (h R : ℝ) (f : Hilbert) : 0 ≤ tail h R f :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem law_tail (h R : ℝ) (f : Hilbert) :
    law h f {p | R^2 ≤ p^2} = ENNReal.ofReal (tail h R f) := by
  have hm : MeasurableSet {p : ℝ | R^2 ≤ p^2} := measurableSet_le measurable_const (by fun_prop)
  rw [law,Measure.map_apply (symbol_continuous h).measurable hm,
    KFCausalL2BornLaw.law_apply _ _ _ (hm.preimage (symbol_continuous h).measurable)]
  rfl

theorem tail_charge (h : ℝ) (hh : h ≠ 0) (R θ : ℝ) (f : Hilbert) :
    tail h R (action h hh θ f) = tail h R f := by
  have he := congrArg (fun μ : Measure ℝ => (μ {p | R^2 ≤ p^2}).toReal) (law_charge h hh θ f)
  simpa only [law_tail,ENNReal.toReal_ofReal (tail_nonnegative _ _ _)] using he

theorem averaged_tail (h : ℝ) (hh : h ≠ 0) (R : ℝ) (f : Hilbert) :
    (∫ θ, tail h R (action h hh (2*Real.pi*θ) f) ∂angleMeasure) = tail h R f := by
  simp only [tail_charge,integral_const,probReal_univ,one_smul]

theorem graph_density (h : ℝ) (hh : h ≠ 0) (f g : Hilbert)
    (hg : (f,g) ∈ (clockMomentum h).graph) :
    Integrable (fun k => (symbol h k)^2*‖(fourierCoordinates f) k‖^2) ∧
      (∫ k, (symbol h k)^2*‖(fourierCoordinates f) k‖^2) = ‖g‖^2 := by
  have he : (fun k => ‖(fourierCoordinates g) k‖^2) =ᵐ[volume]
      fun k => (symbol h k)^2*‖(fourierCoordinates f) k‖^2 := by
    filter_upwards [(clock_graph_fourier h hh f g).mp hg] with k hk
    rw [hk,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  refine ⟨((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (fourierCoordinates g))).mp
    (Lp.memLp (fourierCoordinates g))).congr he,?_⟩
  rw [← integral_congr_ae he,← l2_norm_square,LinearIsometryEquiv.norm_map]

theorem graph_tail_bound (h : ℝ) (hh : h ≠ 0) (R : ℝ) (f g : Hilbert)
    (hg : (f,g) ∈ (clockMomentum h).graph) : R^2*tail h R f ≤ ‖g‖^2 := by
  have hs : MeasurableSet {k : Space | R^2 ≤ (symbol h k)^2} :=
    measurableSet_le measurable_const ((symbol_continuous h).pow 2).measurable
  have hf := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (fourierCoordinates f))).mp
    (Lp.memLp (fourierCoordinates f))
  obtain ⟨hi,he⟩ := graph_density h hh f g hg
  rw [← he,tail,← integral_indicator hs,← integral_const_mul]
  apply integral_mono_ae ((hf.indicator hs).const_mul _) hi
  filter_upwards [] with k
  by_cases hk : R^2 ≤ (symbol h k)^2
  · rw [Set.indicator_of_mem (show k ∈ {k : Space | R^2 ≤ (symbol h k)^2} from hk)]
    exact mul_le_mul_of_nonneg_right hk (sq_nonneg _)
  · rw [Set.indicator_of_notMem (show k ∉ {k : Space | R^2 ≤ (symbol h k)^2} from hk),mul_zero]
    positivity

theorem law_outside_bound (h : ℝ) (hh : h ≠ 0) (R : ℝ) (hR : 0 < R) (f g : Hilbert)
    (hg : (f,g) ∈ (clockMomentum h).graph) :
    law h f (Set.Icc (-R) R)ᶜ ≤ ENNReal.ofReal (‖g‖^2/R^2) := by
  have hs : (Set.Icc (-R) R)ᶜ ⊆ {p : ℝ | R^2 ≤ p^2} := by
    intro p hp
    have ha : R < |p| := lt_of_not_ge (fun hp' => hp (abs_le.mp hp'))
    change R^2 ≤ p^2
    nlinarith [sq_abs p]
  apply (measure_mono hs).trans
  rw [law_tail]
  apply ENNReal.ofReal_le_ofReal
  apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
  simpa only [mul_comm] using graph_tail_bound h hh R f g hg

#print axioms tail_nonnegative
#print axioms law_tail
#print axioms tail_charge
#print axioms averaged_tail
#print axioms graph_density
#print axioms graph_tail_bound
#print axioms law_outside_bound

end
end UnifiedTheory.Audit.KFCausalCanonicalClockTails
