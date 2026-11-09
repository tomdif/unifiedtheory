/- Exact maximal half-clock and full-clock graphs in the actual mixed
coordinates, derived from the bounded inverse and its natural inverse graph. -/
import UnifiedTheory.Audit.KFCausalClockFloorAntisymmetricGraph
import UnifiedTheory.Audit.KFCausalClockFloorMixedRadial
import UnifiedTheory.Audit.KFCausalClockFloorClockOperator
import UnifiedTheory.Audit.KFCausalEnergyReverseFactors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalClockMixedClockGraph
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalRegularizedLongitudinalChart (chartIso)
open KFCausalClockFloorMixedRadial (clockMixed clockMixed_relation)
open KFCausalClockFloorBoundedInverse (inverseL inverseL_eq inverseL_graph)
open KFCausalClockFloorClockHalf (clockHalf half_inverse_graph inverseAction_coe)
open KFCausalClockFloorClockOperator (clockOperator)
open KFCausalClockFloorFlow (clock)
open KFCausalClockFloorCanonicalDefect (clock_positive)
open KFCausalOrderedOperatorComposition (composition composition_graph)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalEnergyReverseFactors (reverseFactor)

variable (ε : ℝ) (hε : 0 < ε)

def clockWeight (q : ℝ) : ℝ := Real.exp ((chartIso ε hε).symm q)+ε

def halfWeight (q : ℝ) : ℝ := Real.sqrt (clockWeight ε hε q)

theorem clockWeight_positive (q : ℝ) : 0 < clockWeight ε hε q := by
  unfold clockWeight
  positivity

theorem halfWeight_positive (q : ℝ) : 0 < halfWeight ε hε q :=
  Real.sqrt_pos.mpr (clockWeight_positive ε hε q)

theorem halfWeight_sq (q : ℝ) : (halfWeight ε hε q)^2=clockWeight ε hε q :=
  Real.sq_sqrt (clockWeight_positive ε hε q).le

theorem clockWeight_continuous : Continuous (clockWeight ε hε) :=
  (Real.continuous_exp.comp (chartIso ε hε).symm.toHomeomorph.continuous).add continuous_const

theorem halfWeight_continuous : Continuous (halfWeight ε hε) :=
  Real.continuous_sqrt.comp (clockWeight_continuous ε hε)

theorem inverseL_clockMixed_coe (f : Hilbert) :
    clockMixed ε hε (inverseL ε hε f) =ᵐ[volume] fun x =>
      (halfWeight ε hε (x.2 0):ℂ)⁻¹*(clockMixed ε hε f) x := by
  have he := clockMixed_relation ε hε _ f (inverseL ε hε f)
    (KFCausalClockFloorAntisymmetricGraph.inverseL_charge_coe ε hε f)
  exact he

theorem clockHalf_graph_iff (f g : Hilbert) :
    (f,g) ∈ (clockHalf ε).graph ↔
      clockMixed ε hε g =ᵐ[volume] fun x =>
        (halfWeight ε hε (x.2 0):ℂ)*(clockMixed ε hε f) x := by
  rw [half_inverse_graph ε hε,inverseL_graph ε hε]
  have hd := inverseL_clockMixed_coe ε hε g
  constructor
  · intro he
    rw [← he] at hd
    filter_upwards [hd] with x hx
    rw [hx,← mul_assoc,mul_inv_cancel₀
      (Complex.ofReal_ne_zero.mpr (halfWeight_positive ε hε _).ne'),one_mul]
  · intro he
    apply (clockMixed ε hε).injective
    apply Lp.ext
    filter_upwards [hd,he] with x hx hg
    rw [hx,hg,← mul_assoc,inv_mul_cancel₀
      (Complex.ofReal_ne_zero.mpr (halfWeight_positive ε hε _).ne'),one_mul]

theorem inverseL_sq_clockMixed_coe (f : Hilbert) :
    clockMixed ε hε (inverseL ε hε (inverseL ε hε f)) =ᵐ[volume] fun x =>
      (clockWeight ε hε (x.2 0):ℂ)⁻¹*(clockMixed ε hε f) x := by
  filter_upwards [inverseL_clockMixed_coe ε hε (inverseL ε hε f),
    inverseL_clockMixed_coe ε hε f] with x h2 h1
  rw [h2,h1,← mul_assoc,← pow_two,inv_pow,← Complex.ofReal_pow,halfWeight_sq]

private theorem inverseL_sq_physical_coe (f : Hilbert) :
    inverseL ε hε (inverseL ε hε f) =ᵐ[volume] fun x : Configuration =>
      (clock ε x.1:ℂ)⁻¹*f x := by
  have hd (u : Hilbert) : inverseL ε hε u =ᵐ[volume] fun x : Configuration =>
      (Real.sqrt (clock ε x.1):ℂ)⁻¹*u x := inverseAction_coe ε hε u
  filter_upwards [hd (inverseL ε hε f),hd f] with x h2 h1
  rw [h2,h1,← mul_assoc,← pow_two,inv_pow,← Complex.ofReal_pow,
    Real.sq_sqrt (clock_positive ε x.1 hε.le).le]

theorem clockOperator_inverse_iff (f g : Hilbert) :
    (f,g) ∈ (clockOperator ε hε).graph ↔ f=inverseL ε hε (inverseL ε hε g) := by
  rw [KFCausalClockFloorClockOperator.clockOperator_graph]
  have hd := inverseL_sq_physical_coe ε hε g
  constructor
  · intro hg
    apply Lp.ext
    filter_upwards [hd,hg] with x hx hg
    rw [hx,hg,← mul_assoc,inv_mul_cancel₀
      (Complex.ofReal_ne_zero.mpr (clock_positive ε x.1 hε.le).ne'),one_mul]
  · intro he
    rw [← he] at hd
    filter_upwards [hd] with x hx
    rw [hx,← mul_assoc,mul_inv_cancel₀
      (Complex.ofReal_ne_zero.mpr (clock_positive ε x.1 hε.le).ne'),one_mul]

theorem clockOperator_graph_iff (f g : Hilbert) :
    (f,g) ∈ (clockOperator ε hε).graph ↔
      clockMixed ε hε g =ᵐ[volume] fun x =>
        (clockWeight ε hε (x.2 0):ℂ)*(clockMixed ε hε f) x := by
  rw [clockOperator_inverse_iff]
  have hd := inverseL_sq_clockMixed_coe ε hε g
  constructor
  · intro he
    rw [← he] at hd
    filter_upwards [hd] with x hx
    rw [hx,← mul_assoc,mul_inv_cancel₀
      (Complex.ofReal_ne_zero.mpr (clockWeight_positive ε hε _).ne'),one_mul]
  · intro he
    apply (clockMixed ε hε).injective
    apply Lp.ext
    filter_upwards [hd,he] with x hx hg
    rw [hx,hg,← mul_assoc,inv_mul_cancel₀
      (Complex.ofReal_ne_zero.mpr (clockWeight_positive ε hε _).ne'),one_mul]

theorem clockHalf_square_graph_iff (f g : Hilbert) :
    (f,g) ∈ (composition (clockHalf ε) (clockHalf ε)).graph ↔
      (f,g) ∈ (clockOperator ε hε).graph := by
  rw [composition_graph,clockOperator_inverse_iff]
  constructor
  · rintro ⟨u,hfu,hug⟩
    rw [half_inverse_graph ε hε,inverseL_graph ε hε] at hfu hug
    rw [hfu,hug]
  · intro he
    refine ⟨inverseL ε hε g,?_,?_⟩
    · rw [half_inverse_graph ε hε,inverseL_graph ε hε]
      exact he
    · rw [half_inverse_graph ε hε,inverseL_graph ε hε]

theorem clockHalf_square_eq : composition (clockHalf ε) (clockHalf ε)=clockOperator ε hε := by
  apply LinearPMap.eq_of_eq_graph
  ext z
  exact clockHalf_square_graph_iff ε hε z.1 z.2

theorem actual_clockSecond_eq (h : ℝ)
    (v : Fin 4 → KFCausalTransverseDilationFlow.Transverse)
    (l : KFCausalTransverseDilationFlow.Transverse →L[ℝ] ℝ) :
    composition (reverseFactor ε hε h v l 0) (energyFactor ε hε h v l 0) =
      clockOperator ε hε := clockHalf_square_eq ε hε

#print axioms clockWeight_positive
#print axioms halfWeight_positive
#print axioms halfWeight_sq
#print axioms clockWeight_continuous
#print axioms halfWeight_continuous
#print axioms inverseL_clockMixed_coe
#print axioms clockHalf_graph_iff
#print axioms inverseL_sq_clockMixed_coe
#print axioms clockOperator_inverse_iff
#print axioms clockOperator_graph_iff
#print axioms clockHalf_square_graph_iff
#print axioms clockHalf_square_eq
#print axioms actual_clockSecond_eq
end
end UnifiedTheory.Audit.KFCausalClockMixedClockGraph
