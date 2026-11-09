/- Exact positive clock production and a quantitative lower bound survive
charge-angle L2 averaging. Both production forms are continuous. -/
import UnifiedTheory.Audit.KFCausalClockFloorClockOutputProduction
import UnifiedTheory.Audit.KFCausalClockFloorClockReferenceRate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedClockProduction
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open UnifiedTheory.Audit.KFCausalClockFloorClockOutputForm (deltaOutput deltaLp response)
open UnifiedTheory.Audit.KFCausalClockFloorClockOutputProduction (responseOutput)
open UnifiedTheory.Audit.KFCausalNeutralReferencePairing (coefficient)

theorem coefficient_pairing (h : ℝ) (z : ℂ) : coefficient h*(conj z-z) = ((2/h)*z.im:ℝ) := by
  apply Complex.ext <;>
    simp only [coefficient,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.sub_re,Complex.sub_im,Complex.conj_re,Complex.conj_im]
    <;> ring

theorem response_pairing {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) (h : ℝ) (g : E) :
    coefficient h*(inner ℂ (A g) g-inner ℂ g (A g)) = ((2/h)*(inner ℂ g (A g)).im:ℝ) := by
  rw [← inner_conj_symm (𝕜 := ℂ) (A g) g]
  exact coefficient_pairing h _

private theorem quadratic_integrable {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (μ : Measure Ω)
    (q : E → ℝ) (hq : Continuous q) (hb : ∀ x, 0 ≤ q x ∧ q x ≤ ‖x‖^2) (g : Lp E 2 μ) :
    Integrable (fun x => q (g x)) μ := by
  apply ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)).mono'
    (hq.comp_aestronglyMeasurable (Lp.aestronglyMeasurable g))
  exact Eventually.of_forall (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hb (g x)).1]; exact (hb (g x)).2)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (hh : |h| ≤ 2*Real.pi*ε/3)
local notation "Y" => EnergyOutputSpace
local notation "P" => KFCausalClockFloorClockOutputProduction.production ε hε h hh
local notation "Q" => KFCausalClockFloorClockOutputProduction.classicalProduction ε hε

def production (g : Y) : ℝ := (2/h)*(inner ℂ g (deltaLp ε hε h hh g)).im
def classicalProduction (g : Y) : ℝ := (inner ℂ g ((responseOutput ε hε).compLp g)).re

theorem production_integral (g : Y) : production ε hε h hh g = ∫ θ, P (g θ) ∂angleMeasure := by
  rw [production,KFCausalStrictMultiplierPairing.imaginary_pairing_integral]
  apply integral_congr_ae
  filter_upwards [(deltaOutput ε hε h hh).coeFn_compLp g] with θ ht
  change (2/h)*(inner ℂ (g θ) ((deltaOutput ε hε h hh).compLp g θ)).im = _
  rw [ht]
  rfl

theorem classicalProduction_integral (g : Y) : classicalProduction ε hε g = ∫ θ, Q (g θ) ∂angleMeasure := by
  have he := integral_re (L2.integrable_inner (𝕜 := ℂ) g ((responseOutput ε hε).compLp g))
  change (∫ θ, (inner ℂ (g θ) ((responseOutput ε hε).compLp g θ)).re ∂angleMeasure) =
    (∫ θ, inner ℂ (g θ) ((responseOutput ε hε).compLp g θ) ∂angleMeasure).re at he
  rw [classicalProduction,L2.inner_def,← he]
  apply integral_congr_ae
  filter_upwards [(responseOutput ε hε).coeFn_compLp g] with θ ht
  rw [ht,← KFCausalClockFloorClockOutputProduction.classicalProduction_pairing]

theorem classicalProduction_bounds (g : Y) : 0 ≤ classicalProduction ε hε g ∧ classicalProduction ε hε g ≤ ‖g‖^2 := by
  have hi := quadratic_integrable angleMeasure Q
    (KFCausalClockFloorClockOutputProduction.classicalProduction_continuous ε hε)
    (KFCausalClockFloorClockOutputProduction.classicalProduction_bounds ε hε) g
  rw [classicalProduction_integral,KFCausalAveragedEnergyGraph.l2_norm_square angleMeasure g]
  refine ⟨integral_nonneg (fun θ => (KFCausalClockFloorClockOutputProduction.classicalProduction_bounds ε hε (g θ)).1),?_⟩
  exact integral_mono_ae hi ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g))
    (Eventually.of_forall (fun θ => (KFCausalClockFloorClockOutputProduction.classicalProduction_bounds ε hε (g θ)).2))

include hne in
theorem production_nonnegative (g : Y) : 0 ≤ production ε hε h hh g := by
  rw [production_integral]
  exact integral_nonneg (fun θ => KFCausalClockFloorClockOutputProduction.production_nonnegative ε hε h hne hh (g θ))

include hne in
theorem production_bounds (g : Y) :
    (1/2)*classicalProduction ε hε g ≤ production ε hε h hh g ∧ production ε hε h hh g ≤ ‖g‖^2 := by
  have hi := quadratic_integrable angleMeasure Q
    (KFCausalClockFloorClockOutputProduction.classicalProduction_continuous ε hε)
    (KFCausalClockFloorClockOutputProduction.classicalProduction_bounds ε hε) g
  have hp := quadratic_integrable angleMeasure P
    (KFCausalClockFloorClockOutputProduction.production_continuous ε hε h hh)
    (fun x => ⟨KFCausalClockFloorClockOutputProduction.production_nonnegative ε hε h hne hh x,
      (KFCausalClockFloorClockOutputProduction.production_bounds ε hε h hne hh x).2⟩) g
  rw [production_integral,classicalProduction_integral,← integral_const_mul,
    KFCausalAveragedEnergyGraph.l2_norm_square angleMeasure g]
  exact ⟨integral_mono_ae (hi.const_mul (1/2)) hp (Eventually.of_forall
    (fun θ => (KFCausalClockFloorClockOutputProduction.production_bounds ε hε h hne hh (g θ)).1)),
    integral_mono_ae hp ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g))
      (Eventually.of_forall (fun θ => (KFCausalClockFloorClockOutputProduction.production_bounds ε hε h hne hh (g θ)).2))⟩

theorem clock_response_eq (g : Y) : coefficient h*response ε hε h hh g g = (production ε hε h hh g:ℂ) :=
  response_pairing (deltaLp ε hε h hh) h g

theorem production_continuous : Continuous (production ε hε h hh) :=
  continuous_const.mul (Complex.continuous_im.comp (continuous_id.inner (deltaLp ε hε h hh).continuous))

theorem classicalProduction_continuous : Continuous (classicalProduction ε hε) :=
  Complex.continuous_re.comp (continuous_id.inner ((responseOutput ε hε).compLpL 2 angleMeasure).continuous)

#print axioms coefficient_pairing
#print axioms response_pairing
#print axioms production_integral
#print axioms classicalProduction_integral
#print axioms classicalProduction_bounds
#print axioms production_nonnegative
#print axioms production_bounds
#print axioms clock_response_eq
#print axioms production_continuous
#print axioms classicalProduction_continuous
end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedClockProduction
