/- The actual singular endpoint integral has the quartic polynomial
coefficients dictated by its first six normalized moments. Their limits
are derived from the proved Gamma moment convergence. The resulting
coercive bound holds eventually, uniformly over every real field shift.
No circle pushforward or response estimate is assumed or concluded. -/
import UnifiedTheory.Audit.KFCausalAngularGammaMomentConvergence
import UnifiedTheory.Audit.KFCausalAngularQuarticEndpoint

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalAngularQuarticMomentPolynomial
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
open KFCausalAngularGammaMomentBounds (kernel moment)
open KFCausalAngularGammaMomentConvergence (normalizedMoment normalized_tendsto moment_eventually_positive)
open KFCausalAngularQuarticEndpoint (evaluate endpointCoefficients eventually_uniform_coercive)

def polynomialKernel (z s u : ℝ) : ℝ :=
  kernel 0 z u*(1-u/z)*((u-s)^4+2*(u-s)^3)

def normalizedPolynomial (z s : ℝ) : ℝ :=
  (∫ u in 0..(2*z), polynomialKernel z s u)/moment 0 z

def coefficients (z : ℝ) : Fin 5 → ℝ := ![
  normalizedMoment 4 z+2*normalizedMoment 3 z-
    (normalizedMoment 5 z+2*normalizedMoment 4 z)/z,
  -4*normalizedMoment 3 z-6*normalizedMoment 2 z+
    (4*normalizedMoment 4 z+6*normalizedMoment 3 z)/z,
  6*normalizedMoment 2 z+6*normalizedMoment 1 z-
    (6*normalizedMoment 3 z+6*normalizedMoment 2 z)/z,
  -4*normalizedMoment 1 z-2*normalizedMoment 0 z+
    (4*normalizedMoment 2 z+2*normalizedMoment 1 z)/z,
  normalizedMoment 0 z-normalizedMoment 1 z/z]

private def rawCoefficients (z s : ℝ) : Fin 6 → ℝ := ![
  s^4-2*s^3,
  -4*s^3+6*s^2+(2*s^3-s^4)/z,
  6*s^2-6*s+(4*s^3-6*s^2)/z,
  2-4*s+(6*s-6*s^2)/z,
  1+(4*s-2)/z,
  -1/z]

private theorem kernel_mul_pow (j : ℕ) (z u : ℝ) (hu : 0 < u) :
    kernel 0 z u*u^j=kernel j z u := by
  have he : u^(-(1/2:ℝ))*u^(j:ℝ)=u^((j:ℝ)-1/2) := by
    rw [← Real.rpow_add hu]
    congr 1
    ring
  unfold kernel KFCausalAngularGammaMomentBounds.density
  norm_num only [Nat.cast_zero,zero_sub]
  rw [← Real.rpow_natCast]
  calc
    Real.exp (-u)*u^(-(1/2:ℝ))*KFCausalAngularGammaMomentBounds.correction z u*u^(j:ℝ) =
        Real.exp (-u)*(u^(-(1/2:ℝ))*u^(j:ℝ))*KFCausalAngularGammaMomentBounds.correction z u := by ring
    _ = _ := by rw [he]

private theorem kernel_expansion (z s u : ℝ) (hu : 0 < u) :
    polynomialKernel z s u=∑ j : Fin 6, rawCoefficients z s j*kernel j.val z u := by
  have hp (j : Fin 6) : kernel j.val z u=kernel 0 z u*u^j.val :=
    (kernel_mul_pow j.val z u hu).symm
  simp_rw [hp]
  norm_num [polynomialKernel,rawCoefficients,Fin.sum_univ_succ]
  ring

private theorem expansion_on (z s : ℝ) (hz : 0 < z) :
    EqOn (polynomialKernel z s)
      (fun u => ∑ j : Fin 6, rawCoefficients z s j*kernel j.val z u) (Set.uIoc 0 (2*z)) := by
  intro u hu
  rw [uIoc_of_le (by positivity : (0:ℝ)≤2*z)] at hu
  exact kernel_expansion z s u hu.1

theorem polynomial_integrable (z s : ℝ) (hz : 0 < z) :
    IntervalIntegrable (polynomialKernel z s) volume 0 (2*z) := by
  apply (intervalIntegrable_congr (expansion_on z s hz)).mpr
  exact IntervalIntegrable.sum Finset.univ (fun (j : Fin 6) _ =>
    (KFCausalAngularGammaMomentBounds.kernel_integrable j.val z hz).const_mul _)

theorem normalized_eq_evaluate (z s : ℝ) (hz : 0 < z) :
    normalizedPolynomial z s=evaluate (coefficients z) s := by
  have he := intervalIntegral.integral_congr_ae_restrict (μ := volume)
    ((ae_restrict_mem measurableSet_uIoc).mono (expansion_on z s hz))
  have hi := intervalIntegral.integral_finset_sum (s := Finset.univ)
    (fun (j : Fin 6) _ =>
      (KFCausalAngularGammaMomentBounds.kernel_integrable j.val z hz).const_mul
        (rawCoefficients z s j))
  unfold normalizedPolynomial
  rw [he,hi]
  simp_rw [intervalIntegral.integral_const_mul]
  norm_num [rawCoefficients,coefficients,evaluate,normalizedMoment,moment,
    Fin.sum_univ_succ,div_eq_mul_inv]
  ring

private def momentLimit : Fin 6 → ℝ := ![1,1/2,3/4,15/8,105/16,945/32]

private theorem gamma_ratio (j : Fin 6) :
    Real.Gamma ((j.val:ℝ)+1/2)/Real.Gamma (1/2)=momentLimit j := by
  have h0 : Real.Gamma (1/2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by norm_num : (0:ℝ)<1/2)).ne'
  have h1 := Real.Gamma_add_one (s := (1/2:ℝ)) (by norm_num)
  have h2 := Real.Gamma_add_one (s := (3/2:ℝ)) (by norm_num)
  have h3 := Real.Gamma_add_one (s := (5/2:ℝ)) (by norm_num)
  have h4 := Real.Gamma_add_one (s := (7/2:ℝ)) (by norm_num)
  have h5 := Real.Gamma_add_one (s := (9/2:ℝ)) (by norm_num)
  norm_num at h1 h2 h3 h4 h5
  fin_cases j <;> norm_num [momentLimit,h1,h2,h3,h4,h5,h0]
  all_goals field_simp
  all_goals ring

private theorem moment_limit (j : Fin 6) :
    Tendsto (normalizedMoment j.val) atTop (𝓝 (momentLimit j)) := by
  have hh := normalized_tendsto j.val
  rwa [gamma_ratio j] at hh

theorem coefficients_tendsto (j : Fin 5) :
    Tendsto (fun z => coefficients z j) atTop (𝓝 (endpointCoefficients j)) := by
  have h0 := moment_limit 0
  have h1 := moment_limit 1
  have h2 := moment_limit 2
  have h3 := moment_limit 3
  have h4 := moment_limit 4
  have h5 := moment_limit 5
  change Tendsto (normalizedMoment 0) atTop (𝓝 (1:ℝ)) at h0
  change Tendsto (normalizedMoment 1) atTop (𝓝 (1/2:ℝ)) at h1
  change Tendsto (normalizedMoment 2) atTop (𝓝 (3/4:ℝ)) at h2
  change Tendsto (normalizedMoment 3) atTop (𝓝 (15/8:ℝ)) at h3
  change Tendsto (normalizedMoment 4) atTop (𝓝 (105/16:ℝ)) at h4
  change Tendsto (normalizedMoment 5) atTop (𝓝 (945/32:ℝ)) at h5
  have hi : Tendsto (fun z : ℝ => z⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  fin_cases j
  · convert (h4.add (h3.const_mul 2)).sub ((h5.add (h4.const_mul 2)).mul hi) using 1
    norm_num [coefficients,endpointCoefficients,div_eq_mul_inv]
  · convert ((h3.const_mul (-4)).sub (h2.const_mul 6)).add
      (((h4.const_mul 4).add (h3.const_mul 6)).mul hi) using 1
    norm_num [coefficients,endpointCoefficients,div_eq_mul_inv]
  · convert ((h2.const_mul 6).add (h1.const_mul 6)).sub
      (((h3.const_mul 6).add (h2.const_mul 6)).mul hi) using 1
    norm_num [coefficients,endpointCoefficients,div_eq_mul_inv]
  · convert ((h1.const_mul (-4)).sub (h0.const_mul 2)).add
      (((h2.const_mul 4).add (h1.const_mul 2)).mul hi) using 1
    norm_num [coefficients,endpointCoefficients,div_eq_mul_inv]
  · convert h0.sub (h1.mul hi) using 1
    norm_num [coefficients,endpointCoefficients,div_eq_mul_inv]

theorem eventually_coercive : ∀ᶠ z : ℝ in atTop,
    0 < moment 0 z ∧ ∀ s : ℝ, (1+s^4)/216 ≤ normalizedPolynomial z s := by
  have hc := eventually_uniform_coercive atTop coefficients coefficients_tendsto
  filter_upwards [hc,moment_eventually_positive 0,eventually_gt_atTop (0:ℝ)] with z hc hz hz0
  refine ⟨hz,fun s => ?_⟩
  rw [normalized_eq_evaluate z s hz0]
  exact hc s

#print axioms polynomial_integrable
#print axioms normalized_eq_evaluate
#print axioms coefficients_tendsto
#print axioms eventually_coercive
end
end UnifiedTheory.Audit.KFCausalAngularQuarticMomentPolynomial
