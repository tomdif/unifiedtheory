/- Joint L2 domination of the clustered quotient and its charged jet,
after summing each original charged cluster. Polynomial coefficients are
controlled uniformly in the clock; neutral shear remains in the Gaussian. -/
import UnifiedTheory.Audit.KFCausalShiftedNarrowControlledFactors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalShiftedNarrowWeightedProfiles
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalRadialMultipliers (Controlled controlled_mul controlled_pow)
open KFCausalShiftedNarrowJointGaussian (gaussian gaussian_continuous Z)
open KFCausalShiftedNarrowControlledFactors (radius_controlled)
open KFCausalClusteredWidthProfiles (quotient)

def quotientJet (n : ℕ) (δ : ℝ) (z : ℂ) : ℂ :=
  (n:ℂ)*quotient δ z^(n-1)*Complex.exp (-(δ:ℂ)*z)-quotient δ z^n

theorem quotientJet_bound (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (z : ℂ) (hz : 0 ≤ z.re) :
    ‖quotientJet n δ z‖ ≤ (n:ℝ)*‖z‖^(n-1)+‖z‖^n := by
  have hj := KFCausalClusteredWidthChargedJet.jet_norm_le n δ hδ z hz
  unfold KFCausalClusteredWidthChargedJet.jet at hj
  rw [norm_mul,Complex.norm_exp,Complex.neg_re] at hj
  exact (mul_le_mul_iff_right₀ (Real.exp_pos (-z.re))).mp hj

theorem quotientJet_tendsto (n : ℕ) (z : ℂ) :
    Tendsto (fun δ => quotientJet n δ z) (𝓝[>] 0) (𝓝 ((n:ℂ)*z^(n-1)-z^n)) := by
  have hq := KFCausalClusteredWidthProfiles.quotient_tendsto z
  have he : Tendsto (fun δ : ℝ => Complex.exp (-(δ:ℂ)*z)) (𝓝[>] 0) (𝓝 (1:ℂ)) := by
    have hc : ContinuousAt (fun δ : ℝ => Complex.exp (-(δ:ℂ)*z)) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  simpa only [mul_one] using (((hq.pow (n-1)).const_mul (n:ℂ)).mul he).sub (hq.pow n)

variable (α β ε y : ℝ) (b : ℂ) (c : ℝ → ℂ) (U : Configuration → ℂ)
local notation "G" => gaussian α β ε y b
local notation "z" => Z α ε y

def weighted (n : ℕ) (δ : ℝ) (x : Configuration) : ℂ := U x*(c x.1*G x)*quotient δ (z x)^n
def moment (n : ℕ) (x : Configuration) : ℂ := U x*(c x.1*G x)*(z x)^n
def weightedJet (n : ℕ) (δ : ℝ) (x : Configuration) : ℂ := U x*(c x.1*G x)*quotientJet n δ (z x)
def limitJet (n : ℕ) (x : Configuration) : ℂ := U x*(c x.1*G x)*((n:ℂ)*(z x)^(n-1)-(z x)^n)

variable (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
  (hc : Continuous c) (hc2 : MemLp c 2 volume) (hU : Controlled U)

include hα hε hy in
theorem radius_nonnegative (x : Configuration) : 0 ≤ (z x).re :=
  KFCausalShiftedNarrowFourierGeometry.radius_re_nonnegative _
    (KFCausalShiftedNarrowFourierGeometry.shifted_coefficient_positive α ε y x.1 hα hε hy).le _ _

include hα hβ hw hε hy hc2 hU in
theorem moment_memLp (n : ℕ) : MemLp (moment α β ε y b c U n) 2 volume := by
  convert KFCausalShiftedNarrowJointMoments.controlled_joint_memLp α β ε y b hα hβ hw hε hy c hc2
    (fun x => U x*(z x)^n) (controlled_mul _ _ hU (controlled_pow _ (radius_controlled ε y hε hy α) n)) using 1
  funext x
  unfold moment
  ring

include hα hε hy in
theorem weighted_bound (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (x : Configuration) :
    ‖weighted α β ε y b c U n δ x‖ ≤ ‖moment α β ε y b c U n x‖ := by
  simp only [weighted,moment,norm_mul,norm_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (KFCausalClusteredWidthProfiles.quotient_norm_le δ (z x) hδ
      (radius_nonnegative α ε y hα hε hy x)) n) (by positivity)

include hα hε hy in
theorem weightedJet_bound (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (x : Configuration) :
    ‖weightedJet α β ε y b c U n δ x‖ ≤
      (n:ℝ)*‖moment α β ε y b c U (n-1) x‖+‖moment α β ε y b c U n x‖ := by
  have hb := mul_le_mul_of_nonneg_left
    (quotientJet_bound n δ hδ (z x) (radius_nonnegative α ε y hα hε hy x))
      (norm_nonneg (U x*(c x.1*G x)))
  simp only [weightedJet,moment,norm_mul,norm_pow]
  simp only [norm_mul] at hb
  convert hb using 1
  ring

include hα hβ hw hε hy hc hc2 hU in
theorem weighted_memLp (n : ℕ) (δ : ℝ) (hδ : 0 < δ) : MemLp (weighted α β ε y b c U n δ) 2 volume := by
  have hz := (radius_controlled ε y hε hy α).1
  have hG := gaussian_continuous α β ε y b hε hy
  have hu := hU.1
  have hcont : Continuous (weighted α β ε y b c U n δ) := by
    unfold weighted KFCausalClusteredWidthProfiles.quotient
    fun_prop
  exact (moment_memLp α β ε y b c U hα hβ hw hε hy hc2 hU n).of_le hcont.aestronglyMeasurable
    (Eventually.of_forall (weighted_bound α β ε y b c U hα hε hy n δ hδ))

include hα hβ hw hε hy hc2 hU in
theorem limitJet_memLp (n : ℕ) : MemLp (limitJet α β ε y b c U n) 2 volume := by
  convert ((moment_memLp α β ε y b c U hα hβ hw hε hy hc2 hU (n-1)).const_mul (n:ℂ)).sub
    (moment_memLp α β ε y b c U hα hβ hw hε hy hc2 hU n) using 1
  funext x
  simp only [Pi.sub_apply,limitJet,moment]
  ring

include hα hβ hw hε hy hc hc2 hU in
theorem weightedJet_memLp (n : ℕ) (δ : ℝ) (hδ : 0 < δ) : MemLp (weightedJet α β ε y b c U n δ) 2 volume := by
  have hz := (radius_controlled ε y hε hy α).1
  have hG := gaussian_continuous α β ε y b hε hy
  have hu := hU.1
  have hcont : Continuous (weightedJet α β ε y b c U n δ) := by
    unfold weightedJet quotientJet KFCausalClusteredWidthProfiles.quotient
    fun_prop
  have hm := (((moment_memLp α β ε y b c U hα hβ hw hε hy hc2 hU (n-1)).norm).const_mul (n:ℝ)).add
    (moment_memLp α β ε y b c U hα hβ hw hε hy hc2 hU n).norm
  apply hm.of_le hcont.aestronglyMeasurable
  filter_upwards [] with x
  have hn : 0 ≤ (n:ℝ)*‖moment α β ε y b c U (n-1) x‖+‖moment α β ε y b c U n x‖ := by positivity
  simpa only [Pi.add_apply,Pi.mul_apply,Real.norm_eq_abs,abs_of_nonneg hn] using
    weightedJet_bound α β ε y b c U hα hε hy n δ hδ x

theorem weighted_tendsto (n : ℕ) (x : Configuration) :
    Tendsto (fun δ => weighted α β ε y b c U n δ x) (𝓝[>] 0)
      (𝓝 (moment α β ε y b c U n x)) :=
  ((KFCausalClusteredWidthProfiles.quotient_tendsto (z x)).pow n).const_mul _

theorem weightedJet_tendsto (n : ℕ) (x : Configuration) :
    Tendsto (fun δ => weightedJet α β ε y b c U n δ x) (𝓝[>] 0)
      (𝓝 (limitJet α β ε y b c U n x)) := (quotientJet_tendsto n (z x)).const_mul _

#print axioms quotientJet_bound
#print axioms quotientJet_tendsto
#print axioms radius_nonnegative
#print axioms moment_memLp
#print axioms weighted_bound
#print axioms weightedJet_bound
#print axioms weighted_memLp
#print axioms limitJet_memLp
#print axioms weightedJet_memLp
#print axioms weighted_tendsto
#print axioms weightedJet_tendsto
end
end UnifiedTheory.Audit.KFCausalShiftedNarrowWeightedProfiles
