/- A uniform lower bound for field forcing in the actual imaginary-shear
coefficient, and the precise graph/strong-derivative criterion for applying
it to an expectation curve. This is an interpolation statement, not an
identity along Hamiltonian time evolution. -/
import UnifiedTheory.Audit.KFCausalImaginaryShearCocoercivity
import UnifiedTheory.Audit.KFCausalClockShearPositiveVariation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalForcedShearVariation
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalImaginaryShearCoefficient (coefficient)
open UnifiedTheory.Audit.KFCausalActualImaginaryShearCurve (coefficientOperator coefficientOperator_coe)
open UnifiedTheory.Audit.KFCausalImaginaryShearCocoercivity
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph (l2_norm_square)
open UnifiedTheory.Audit.KFCausalClockShearPositiveVariation (expectation clock_commute pairing_integral density_integrable)
open UnifiedTheory.Audit.KFCausalClockShearRealMultiplier (clock_graph)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum shear_selfAdjoint)
open UnifiedTheory.Audit.KFCausalSelfAdjointCoreWeakGraph (graph_iff_weak)

variable (ε h : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3) (hh : h ≠ 0)
local notation "C" => coefficientOperator ε h hε hb hh
local notation "c" => coefficient ε h

theorem operator_coercivity (f : Hilbert) : 2*ε*‖C f‖^2 ≤ (inner ℂ f (C f)).re := by
  rw [l2_norm_square volume,pairing_integral C c (coefficientOperator_coe ε h hε hb hh),← integral_const_mul]
  apply integral_mono_ae
    (((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (C f))).mp (Lp.memLp (C f))).const_mul (2*ε))
    (density_integrable C c (coefficientOperator_coe ε h hε hb hh) f)
  filter_upwards [coefficientOperator_coe ε h hε hb hh f] with x hx
  rw [hx,norm_mul,mul_pow]
  convert mul_le_mul_of_nonneg_right (coefficient_coercivity ε h x.1 hε hh hb) (sq_nonneg ‖f x‖) using 1
  ring

theorem forced_pairing_lower (f d : Hilbert) :
    -(h^2/(4*ε))*‖d‖^2 ≤ 2*(inner ℂ f (C (f+(Complex.I*(h:ℂ)) • d))).re := by
  let v := f+(Complex.I*(h:ℂ)) • d
  have hr := integral_re (L2.integrable_inner (𝕜 := ℂ) f (C v))
  change (∫ x, (inner ℂ (f x) (C v x)).re) = (∫ x, inner ℂ (f x) (C v x)).re at hr
  change -(h^2/(4*ε))*‖d‖^2 ≤ 2*(inner ℂ f (C v)).re
  rw [l2_norm_square volume,L2.inner_def,← hr,← integral_const_mul,← integral_const_mul]
  apply integral_mono_ae
    (((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable d)).mp (Lp.memLp d)).const_mul _)
    (((L2.integrable_inner (𝕜 := ℂ) f (C v)).re).const_mul 2)
  filter_upwards [coefficientOperator_coe ε h hε hb hh v,
    Lp.coeFn_add f ((Complex.I*(h:ℂ)) • d),Lp.coeFn_smul (Complex.I*(h:ℂ)) d] with x hc hv hd
  change C v x = c x.1*v x at hc
  rw [hc]
  change v x = f x+((Complex.I*(h:ℂ)) • d) x at hv
  rw [hv,hd]
  simp only [Pi.smul_apply,smul_eq_mul]
  exact scalar_forced_lower ε h hε (c x.1) (f x) (d x)
    (coefficient_coercivity ε h x.1 hε hh hb)

theorem forced_expectation_derivative (W : Hilbert →L[ℂ] Hilbert) (w : ℝ → ℂ)
    (hW : ∀ f : Hilbert, W f =ᵐ[volume] fun x => w x.1*f x)
    (U J : ℝ → Hilbert) (V JV : Hilbert) (t : ℝ)
    (hU : HasDerivAt U (C V) t) (hJ : HasDerivAt J (C JV) t)
    (hu : (U t,J t) ∈ (shearMomentum h).graph) (hv : (V,JV) ∈ (shearMomentum h).graph) :
    HasDerivAt (expectation W U J) (2*(inner ℂ (W (J t)) (C (W V))).re) t := by
  have hwU := clock_graph W w hW h hh (U t) (J t) hu
  have hCV := clock_graph C c (coefficientOperator_coe ε h hε hb hh) h hh V JV hv
  have hwCV := clock_graph W w hW h hh (C V) (C JV) hCV
  have hp : inner ℂ (W (U t)) (W (C JV)) = inner ℂ (W (J t)) (W (C V)) :=
    ((graph_iff_weak _ (shear_selfAdjoint h hh) (W (C V)) (W (C JV))).mp hwCV
      (W (U t)) (W (J t)) hwU).symm
  have hdu := (W.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hU
  have hdj := (W.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hJ
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hdu.inner ℂ hdj)
  change HasDerivAt (expectation W U J)
    (inner ℂ (W (U t)) (W (C JV))+inner ℂ (W (C V)) (W (J t))).re t at hd
  have hs : (inner ℂ (W (C V)) (W (J t))).re =
      (inner ℂ (W (J t)) (W (C V))).re := inner_re_symm (𝕜 := ℂ) _ _
  convert hd using 1
  rw [hp,Complex.add_re,hs,clock_commute C W c w (coefficientOperator_coe ε h hε hb hh) hW]
  ring

theorem forced_expectation_lower (W : Hilbert →L[ℂ] Hilbert) (w : ℝ → ℂ)
    (hW : ∀ f : Hilbert, W f =ᵐ[volume] fun x => w x.1*f x)
    (U J : ℝ → Hilbert) (V JV d : Hilbert) (t : ℝ)
    (hU : HasDerivAt U (C V) t) (hJ : HasDerivAt J (C JV) t)
    (hu : (U t,J t) ∈ (shearMomentum h).graph) (hv : (V,JV) ∈ (shearMomentum h).graph)
    (he : V = J t+(Complex.I*(h:ℂ)) • d) :
    -(h^2/(4*ε))*‖W d‖^2 ≤ deriv (expectation W U J) t := by
  rw [(forced_expectation_derivative ε h hε hb hh W w hW U J V JV t hU hJ hu hv).deriv,he,map_add,map_smul]
  exact forced_pairing_lower ε h hε hb hh (W (J t)) (W d)

#print axioms operator_coercivity
#print axioms forced_pairing_lower
#print axioms forced_expectation_derivative
#print axioms forced_expectation_lower
end
end UnifiedTheory.Audit.KFCausalForcedShearVariation
