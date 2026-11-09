/- The actual singular endpoint integral has the quadratic polynomial
coefficients dictated by its first four normalized moments. Their limits
are derived from the proved Gamma moment convergence. The resulting
coercive bound holds eventually, uniformly over every real field shift.
No circle pushforward or response estimate is assumed or concluded. -/
import UnifiedTheory.Audit.KFCausalAngularGammaMomentConvergence
import Mathlib.Order.Filter.Finite

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalAngularMassMomentPolynomial
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
open KFCausalAngularGammaMomentBounds (kernel moment)
open KFCausalAngularGammaMomentConvergence (normalizedMoment normalized_tendsto moment_eventually_positive)
def endpointCoefficients : Fin 3 → ℝ := ![5/4,-2,1]

def evaluate (c : Fin 3 → ℝ) (s : ℝ) : ℝ := ∑ i, c i*s^i.val

def polynomialKernel (z s u : ℝ) : ℝ :=
  kernel 0 z u*(1-u/z)*((u-s)^2+(u-s))

def normalizedPolynomial (z s : ℝ) : ℝ :=
  (∫ u in 0..(2*z), polynomialKernel z s u)/moment 0 z

def coefficients (z : ℝ) : Fin 3 → ℝ := ![
  normalizedMoment 2 z+normalizedMoment 1 z-
    (normalizedMoment 3 z+normalizedMoment 2 z)/z,
  -2*normalizedMoment 1 z-normalizedMoment 0 z+
    (2*normalizedMoment 2 z+normalizedMoment 1 z)/z,
  normalizedMoment 0 z-normalizedMoment 1 z/z]

private def rawCoefficients (z s : ℝ) : Fin 4 → ℝ := ![
  s^2-s,
  1-2*s+(s-s^2)/z,
  1+(2*s-1)/z,
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
    polynomialKernel z s u=∑ j : Fin 4, rawCoefficients z s j*kernel j.val z u := by
  have hp (j : Fin 4) : kernel j.val z u=kernel 0 z u*u^j.val :=
    (kernel_mul_pow j.val z u hu).symm
  simp_rw [hp]
  norm_num [polynomialKernel,rawCoefficients,Fin.sum_univ_succ]
  ring

private theorem expansion_on (z s : ℝ) (hz : 0 < z) :
    EqOn (polynomialKernel z s)
      (fun u => ∑ j : Fin 4, rawCoefficients z s j*kernel j.val z u) (Set.uIoc 0 (2*z)) := by
  intro u hu
  rw [uIoc_of_le (by positivity : (0:ℝ)≤2*z)] at hu
  exact kernel_expansion z s u hu.1

theorem polynomial_integrable (z s : ℝ) (hz : 0 < z) :
    IntervalIntegrable (polynomialKernel z s) volume 0 (2*z) := by
  apply (intervalIntegrable_congr (expansion_on z s hz)).mpr
  exact IntervalIntegrable.sum Finset.univ (fun (j : Fin 4) _ =>
    (KFCausalAngularGammaMomentBounds.kernel_integrable j.val z hz).const_mul _)

theorem normalized_eq_evaluate (z s : ℝ) (hz : 0 < z) :
    normalizedPolynomial z s=evaluate (coefficients z) s := by
  have he := intervalIntegral.integral_congr_ae_restrict (μ := volume)
    ((ae_restrict_mem measurableSet_uIoc).mono (expansion_on z s hz))
  have hi := intervalIntegral.integral_finset_sum (s := Finset.univ)
    (fun (j : Fin 4) _ =>
      (KFCausalAngularGammaMomentBounds.kernel_integrable j.val z hz).const_mul
        (rawCoefficients z s j))
  unfold normalizedPolynomial
  rw [he,hi]
  simp_rw [intervalIntegral.integral_const_mul]
  norm_num [rawCoefficients,coefficients,evaluate,normalizedMoment,moment,
    Fin.sum_univ_succ,div_eq_mul_inv]
  ring

private def momentLimit : Fin 4 → ℝ := ![1,1/2,3/4,15/8]

private theorem gamma_ratio (j : Fin 4) :
    Real.Gamma ((j.val:ℝ)+1/2)/Real.Gamma (1/2)=momentLimit j := by
  have h0 : Real.Gamma (1/2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by norm_num : (0:ℝ)<1/2)).ne'
  have h1 := Real.Gamma_add_one (s := (1/2:ℝ)) (by norm_num)
  have h2 := Real.Gamma_add_one (s := (3/2:ℝ)) (by norm_num)
  have h3 := Real.Gamma_add_one (s := (5/2:ℝ)) (by norm_num)
  norm_num at h1 h2 h3
  fin_cases j <;> norm_num [momentLimit,h1,h2,h3,h0]
  all_goals field_simp
  all_goals ring

private theorem moment_limit (j : Fin 4) :
    Tendsto (normalizedMoment j.val) atTop (𝓝 (momentLimit j)) := by
  have hh := normalized_tendsto j.val
  rwa [gamma_ratio j] at hh

theorem coefficients_tendsto (j : Fin 3) :
    Tendsto (fun z => coefficients z j) atTop (𝓝 (endpointCoefficients j)) := by
  have h0 := moment_limit 0
  have h1 := moment_limit 1
  have h2 := moment_limit 2
  have h3 := moment_limit 3
  change Tendsto (normalizedMoment 0) atTop (𝓝 (1:ℝ)) at h0
  change Tendsto (normalizedMoment 1) atTop (𝓝 (1/2:ℝ)) at h1
  change Tendsto (normalizedMoment 2) atTop (𝓝 (3/4:ℝ)) at h2
  change Tendsto (normalizedMoment 3) atTop (𝓝 (15/8:ℝ)) at h3
  have hi : Tendsto (fun z : ℝ => z⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  fin_cases j
  · convert (h2.add h1).sub ((h3.add h2).mul hi) using 1
    norm_num [coefficients,endpointCoefficients,div_eq_mul_inv]
  · convert ((h1.const_mul (-2)).sub h0).add
      (((h2.const_mul 2).add h1).mul hi) using 1
    norm_num [coefficients,endpointCoefficients,div_eq_mul_inv]
  · convert h0.sub (h1.mul hi) using 1
    norm_num [coefficients,endpointCoefficients,div_eq_mul_inv]

private theorem endpoint_coercive (s : ℝ) :
    (1+s^2)/12 ≤ evaluate endpointCoefficients s := by
  norm_num [evaluate,endpointCoefficients,Fin.sum_univ_succ]
  nlinarith [sq_nonneg (s-12/11)]

private theorem power_bound (s : ℝ) (i : Fin 3) : |s^i.val| ≤ 1+s^2 := by
  rw [abs_pow]
  have h2 : |s|^2=s^2 := sq_abs s
  by_cases hs : |s| ≤ 1
  · have hp : |s|^i.val ≤ 1 := pow_le_one₀ (abs_nonneg s) hs
    nlinarith [sq_nonneg s]
  · have hp : |s|^i.val ≤ |s|^2 :=
      pow_le_pow_right₀ (le_of_not_ge hs) (by omega)
    rw [h2] at hp
    linarith

private theorem stable_lower (c : Fin 3 → ℝ)
    (hc : ∀ i, |c i-endpointCoefficients i| ≤ 1/72) (s : ℝ) :
    (1+s^2)/24 ≤ evaluate c s := by
  have hs : evaluate c s-evaluate endpointCoefficients s =
      ∑ i, (c i-endpointCoefficients i)*s^i.val := by
    unfold evaluate
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have he : |evaluate c s-evaluate endpointCoefficients s| ≤ (1+s^2)/24 := by
    rw [hs]
    calc
      |∑ i, (c i-endpointCoefficients i)*s^i.val| ≤
          ∑ i, |(c i-endpointCoefficients i)*s^i.val| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 3, (1/72)*(1+s^2) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul (hc i) (power_bound s i) (abs_nonneg _) (by norm_num)
      _ = (1+s^2)/24 := by simp; ring
  have hl := (abs_le.mp he).1
  have hp := endpoint_coercive s
  linarith

theorem eventually_coercive : ∀ᶠ z : ℝ in atTop,
    0 < moment 0 z ∧ ∀ s : ℝ, (1+s^2)/24 ≤ normalizedPolynomial z s := by
  have hi (i : Fin 3) : ∀ᶠ z : ℝ in atTop,
      |coefficients z i-endpointCoefficients i| ≤ 1/72 := by
    filter_upwards [(Metric.tendsto_nhds.mp (coefficients_tendsto i)) (1/72)
      (by norm_num)] with z hz
    simpa only [Real.dist_eq] using hz.le
  filter_upwards [Filter.eventually_all.mpr hi,moment_eventually_positive 0,
    eventually_gt_atTop (0:ℝ)] with z hc hz hz0
  refine ⟨hz,fun s => ?_⟩
  rw [normalized_eq_evaluate z s hz0]
  exact stable_lower (coefficients z) hc s

#print axioms polynomial_integrable
#print axioms normalized_eq_evaluate
#print axioms coefficients_tendsto
#print axioms eventually_coercive
end
end UnifiedTheory.Audit.KFCausalAngularMassMomentPolynomial
