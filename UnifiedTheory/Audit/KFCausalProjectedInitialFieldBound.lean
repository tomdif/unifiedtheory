/- The actual transported initial field moments are bounded by the
ordinary initial field moments, with a constant uniform on the admitted
clock strip. This is not a comparison with final Hamiltonian energy. -/
import UnifiedTheory.Audit.KFCausalStructuredInitialParity
import UnifiedTheory.Audit.KFCausalParityPolynomialBound
import UnifiedTheory.Audit.KFCausalProjectedMatterCostDensity

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalProjectedInitialFieldBound
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse (StructuredState)
open UnifiedTheory.Audit.KFCausalInitialParityReflection (reflection reflection_apply reflection_preserving)
open UnifiedTheory.Audit.KFCausalParityPolynomialBound (stripConstant physical_paired_bound)
open UnifiedTheory.Audit.KFCausalStructuredInitialParity (mean_initial_coe)
open UnifiedTheory.Audit.KFCausalStructuredShearMean (meanInputAt)
open UnifiedTheory.Audit.KFCausalProjectedMatterShearGraphs (meanWeightedInput mean_field_graph)
open UnifiedTheory.Audit.KFCausalPolynomialImaginaryShearCurve (fieldWeight)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower_graph)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalFieldShearDifferential (powerValue)
open UnifiedTheory.Audit.KFCausalProjectedMatterNormSecant (meanInitial)
open UnifiedTheory.Audit.KFCausalProjectedMatterCostDensity
  (initialDensity norm_density weighted_norm_density initial_norm_density initial_weighted_density)
open UnifiedTheory.Audit.KFCausalImaginaryShearCoefficient (displacement)
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (displacement_strip_bound)
open UnifiedTheory.Audit.KFCausalClockSecantRatio (ratio ratio_nonnegative)
open UnifiedTheory.Audit.KFCausalClockSecantMultiplier (operator)

theorem reflected_integral_bound (A B : Configuration → ℝ) (C : ℝ)
    (hA : Integrable A volume) (hB : Integrable B volume)
    (hp : ∀ᵐ x ∂volume, A x+A (reflection x) ≤ C*(B x+B (reflection x))) :
    (∫ x, A x) ≤ C*(∫ x, B x) := by
  have hAr := reflection_preserving.integrable_comp_of_integrable hA
  have hBr := reflection_preserving.integrable_comp_of_integrable hB
  change Integrable (fun x => A (reflection x)) volume at hAr
  change Integrable (fun x => B (reflection x)) volume at hBr
  have hi := integral_mono_ae (hA.add hAr) ((hB.add hBr).const_mul C) hp
  change (∫ x, A x+A (reflection x)) ≤ ∫ x, C*(B x+B (reflection x)) at hi
  rw [integral_add hA hAr,integral_const_mul,integral_add hB hBr,
    reflection_preserving.integral_comp' A,reflection_preserving.integral_comp' B] at hi
  linarith

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (S : StructuredState)
local notation "G0" => meanInputAt ε h hε hh hb S 0
local notation "M" => operator ε h hε hb hh

def fieldInitial (i : Fin 2) : Hilbert :=
  meanWeightedInput ε h hε hh hb S (fieldWeight pointField i) 0

def fieldDensity (i : Fin 2) (x : Configuration) : ℝ :=
  ‖powerValue pointField i x‖^2*‖G0 x‖^2

theorem field_initial_coe (i : Fin 2) : fieldInitial ε h hε hh hb S i =ᵐ[volume]
    fun x => powerValue pointField i x*G0 x :=
  (fieldPower_graph pointField i _ _).mp
    (mean_field_graph ε h hε hh hb S pointField i ⟨0,by constructor <;> norm_num⟩)

theorem field_initial_density (i : Fin 2) :
    Integrable (fieldDensity ε h hε hh hb S i) volume ∧
      ‖fieldInitial ε h hε hh hb S i‖^2 = ∫ x, fieldDensity ε h hε hh hb S i x :=
  norm_density _ _ _ (field_initial_coe ε h hε hh hb S i)

theorem field_initial_weighted_density (i : Fin 2) :
    Integrable (fun x => ratio ε h x.1*fieldDensity ε h hε hh hb S i x) volume ∧
      ‖M (fieldInitial ε h hε hh hb S i)‖^2 =
        ∫ x, ratio ε h x.1*fieldDensity ε h hε hh hb S i x := by
  simpa only [fieldDensity,mul_assoc] using
    weighted_norm_density ε h hε hh hb _ _ _ (field_initial_coe ε h hε hh hb S i)

theorem weighted_integral_bound (i : Fin 2) (w : ℝ → ℝ) (hw : ∀ s, 0 ≤ w s)
    (hI : Integrable (fun x => w x.1*initialDensity ε h hε hh hb S i x) volume)
    (hF : Integrable (fun x => w x.1*fieldDensity ε h hε hh hb S i x) volume) :
    (∫ x, w x.1*initialDensity ε h hε hh hb S i x) ≤
      stripConstant^(2*(i.val+1))*(∫ x, w x.1*fieldDensity ε h hε hh hb S i x) := by
  apply reflected_integral_bound _ _ _ hI hF
  filter_upwards [mean_initial_coe ε h hε hh hb S] with x hx
  have he := mul_le_mul_of_nonneg_right
    (physical_paired_bound (displacement ε h) (displacement_strip_bound ε h hε hb) i x)
    (mul_nonneg (hw x.1) (sq_nonneg ‖G0 x‖))
  dsimp only [initialDensity,fieldDensity]
  rw [hx]
  have hr : (reflection x).1 = x.1 := rfl
  rw [hr] at he ⊢
  nlinarith only [he]

theorem initial_norm_bound (i : Fin 2) :
    ‖meanInitial ε h hε hh hb S pointField i‖^2 ≤
      stripConstant^(2*(i.val+1))*‖fieldInitial ε h hε hh hb S i‖^2 := by
  rw [(initial_norm_density ε h hε hh hb S i).2,(field_initial_density ε h hε hh hb S i).2]
  have he := weighted_integral_bound ε h hε hh hb S i (fun _ => 1) (fun _ => by norm_num)
    (by simpa only [one_mul] using (initial_norm_density ε h hε hh hb S i).1)
    (by simpa only [one_mul] using (field_initial_density ε h hε hh hb S i).1)
  simpa only [one_mul] using he

theorem initial_weighted_bound (i : Fin 2) :
    ‖M (meanInitial ε h hε hh hb S pointField i)‖^2 ≤
      stripConstant^(2*(i.val+1))*‖M (fieldInitial ε h hε hh hb S i)‖^2 := by
  rw [(initial_weighted_density ε h hε hh hb S i).2,
    (field_initial_weighted_density ε h hε hh hb S i).2]
  exact weighted_integral_bound ε h hε hh hb S i (ratio ε h)
    (ratio_nonnegative ε h hε hb hh)
    (initial_weighted_density ε h hε hh hb S i).1
    (field_initial_weighted_density ε h hε hh hb S i).1

#print axioms reflected_integral_bound
#print axioms field_initial_coe
#print axioms field_initial_density
#print axioms field_initial_weighted_density
#print axioms weighted_integral_bound
#print axioms initial_norm_bound
#print axioms initial_weighted_bound
end
end UnifiedTheory.Audit.KFCausalProjectedInitialFieldBound
