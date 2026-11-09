/- Integrable configuration densities for the actual projected secant
costs. The initial and final means remain distinct; their clock weights
and polynomial transport are retained exactly. -/
import UnifiedTheory.Audit.KFCausalProjectedTransportedInitialFormula
import UnifiedTheory.Audit.KFCausalProjectedHamiltonianNormLower

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalProjectedMatterCostDensity
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse (StructuredState)
open UnifiedTheory.Audit.KFCausalTransportedFieldPolynomial (transportedValue)
open UnifiedTheory.Audit.KFCausalImaginaryShearCoefficient (displacement)
open UnifiedTheory.Audit.KFCausalStructuredShearMean (meanInputAt)
open UnifiedTheory.Audit.KFCausalProjectedMatterNormSecant (meanInitial)
open UnifiedTheory.Audit.KFCausalProjectedTransportedInitialFormula (mean_initial_coe)
open UnifiedTheory.Audit.KFCausalClockSecantMultiplier (operator operator_coe value_square)
open UnifiedTheory.Audit.KFCausalClockSecantRatio (ratio)
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph (l2_norm_square)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalStructuredProjectedHamiltonian (meanInput)
open UnifiedTheory.Audit.KFCausalCoherentMatterResponseAverage (matterIndex)
open UnifiedTheory.Audit.KFCausalFieldShearDifferential (powerValue powerSlope)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower_graph)
open UnifiedTheory.Audit.KFCausalProjectedMatterCommutatorResponse
  (projected_field_graphs projected_slope_coe slopeOutput)
open UnifiedTheory.Audit.KFCausalMatterAbsorptionWeight (moment moment_integral weight)
open UnifiedTheory.Audit.KFCausalMatterScalarAbsorption (coefficient)
open UnifiedTheory.Audit.KFCausalProjectedHamiltonianNormLower (normCost sharpLower)

private theorem norm_integrable (f : Hilbert) : Integrable (fun x => ‖f x‖^2) volume := by
  simpa only [inner_self_eq_norm_sq_to_K,← RCLike.ofReal_pow,RCLike.ofReal_re] using
    (L2.integrable_inner (𝕜 := ℂ) f f).re

theorem norm_density (f g : Hilbert) (P : Configuration → ℂ)
    (hf : f =ᵐ[volume] fun x => P x*g x) :
    Integrable (fun x => ‖P x‖^2*‖g x‖^2) volume ∧
      ‖f‖^2 = ∫ x, ‖P x‖^2*‖g x‖^2 := by
  have he : (fun x => ‖f x‖^2) =ᵐ[volume] fun x => ‖P x‖^2*‖g x‖^2 :=
    hf.mono (fun x hx => by dsimp only at hx ⊢; rw [hx,norm_mul,mul_pow])
  exact ⟨(norm_integrable f).congr he,(l2_norm_square volume f).trans (integral_congr_ae he)⟩

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "M" => operator ε h hε hb hh

theorem weighted_norm_density (f g : Hilbert) (P : Configuration → ℂ)
    (hf : f =ᵐ[volume] fun x => P x*g x) :
    Integrable (fun x => ratio ε h x.1*‖P x‖^2*‖g x‖^2) volume ∧
      ‖M f‖^2 = ∫ x, ratio ε h x.1*‖P x‖^2*‖g x‖^2 := by
  have he : (fun x => ‖M f x‖^2) =ᵐ[volume] fun x => ratio ε h x.1*‖P x‖^2*‖g x‖^2 := by
    filter_upwards [operator_coe ε h hε hb hh f,hf] with x hm hp
    rw [hm,hp,norm_mul,norm_mul,mul_pow,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
      value_square ε h hε hb hh]
    ring
  exact ⟨(norm_integrable (M f)).congr he,(l2_norm_square volume (M f)).trans (integral_congr_ae he)⟩

variable (S : StructuredState)
local notation "G0" => meanInputAt ε h hε hh hb S 0
local notation "G1" => meanInput ε h hε hh hb S 7

def initialDensity (i : Fin 2) (x : Configuration) : ℝ :=
  ‖transportedValue (displacement ε h x.1) pointField i x‖^2*‖G0 x‖^2

def finalDensity (i : Fin 2) (x : Configuration) : ℝ :=
  ‖powerValue pointField i x‖^2*‖G1 x‖^2

def slopeDensity (i : Fin 2) (x : Configuration) : ℝ :=
  weight ε x*‖powerSlope pointField i x‖^2*‖G1 x‖^2

theorem initial_norm_density (i : Fin 2) :
    Integrable (initialDensity ε h hε hh hb S i) volume ∧
      ‖meanInitial ε h hε hh hb S pointField i‖^2 = ∫ x, initialDensity ε h hε hh hb S i x :=
  norm_density _ _ _ (mean_initial_coe ε h hε hh hb S pointField i)

theorem initial_weighted_density (i : Fin 2) :
    Integrable (fun x => ratio ε h x.1*initialDensity ε h hε hh hb S i x) volume ∧
      ‖M (meanInitial ε h hε hh hb S pointField i)‖^2 =
        ∫ x, ratio ε h x.1*initialDensity ε h hε hh hb S i x := by
  simpa only [initialDensity,mul_assoc] using
    weighted_norm_density ε h hε hh hb _ _ _ (mean_initial_coe ε h hε hh hb S pointField i)

theorem final_weighted_density (i : Fin 2) :
    Integrable (fun x => ratio ε h x.1*finalDensity ε h hε hh hb S i x) volume ∧
      ‖M (meanInput ε h hε hh hb S (matterIndex i))‖^2 =
        ∫ x, ratio ε h x.1*finalDensity ε h hε hh hb S i x := by
  have hg := (fieldPower_graph pointField i _ _).mp (projected_field_graphs ε h hε hh hb S i).1
  simpa only [finalDensity,powerValue,mul_assoc] using weighted_norm_density ε h hε hh hb _ _ _ hg

theorem slope_moment_density (i : Fin 2) :
    Integrable (slopeDensity ε h hε hh hb S i) volume ∧
      moment ε hε (slopeOutput ε h hε hh hb S i) = ∫ x, slopeDensity ε h hε hh hb S i x := by
  have he : (fun x => weight ε x*‖slopeOutput ε h hε hh hb S i x‖^2) =ᵐ[volume]
      slopeDensity ε h hε hh hb S i := by
    filter_upwards [projected_slope_coe ε h hε hh hb S i] with x hx
    rw [hx,norm_mul,mul_pow]
    exact (mul_assoc _ _ _).symm
  obtain ⟨hi,hr⟩ := moment_integral ε hε (slopeOutput ε h hε hh hb S i)
  exact ⟨hi.congr he,hr.trans (integral_congr_ae he)⟩

theorem normCost_density (i : Fin 2) : normCost ε h hε hh hb S i =
    (1/(2*ε))*(∫ x, initialDensity ε h hε hh hb S i x)+
      coefficient ε h*(∫ x, slopeDensity ε h hε hh hb S i x) := by
  rw [normCost,(initial_norm_density ε h hε hh hb S i).2,(slope_moment_density ε h hε hh hb S i).2]

theorem sharpLower_density (i : Fin 2) : sharpLower ε h hε hh hb S i =
    (2/ε^2)*((∫ x, ratio ε h x.1*finalDensity ε h hε hh hb S i x)-
      (∫ x, ratio ε h x.1*initialDensity ε h hε hh hb S i x))-
        coefficient ε h*(∫ x, slopeDensity ε h hε hh hb S i x) := by
  rw [sharpLower,(final_weighted_density ε h hε hh hb S i).2,
    (initial_weighted_density ε h hε hh hb S i).2,(slope_moment_density ε h hε hh hb S i).2]

#print axioms norm_density
#print axioms weighted_norm_density
#print axioms initial_norm_density
#print axioms initial_weighted_density
#print axioms final_weighted_density
#print axioms slope_moment_density
#print axioms normCost_density
#print axioms sharpLower_density
end
end UnifiedTheory.Audit.KFCausalProjectedMatterCostDensity
