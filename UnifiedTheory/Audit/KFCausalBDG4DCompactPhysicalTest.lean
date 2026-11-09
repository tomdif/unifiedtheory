/- The constructed compact radial test has a genuine mostly-plus flat
d'Alembertian equal to eight.  The original BDG density prefactors and
interval-volume density rescaling give that same limit.  This is one
explicit flat test; no emergent curved chart or interacting field is assumed. -/
import UnifiedTheory.Audit.KFCausalBDG4DNonzeroCompactKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalBDG4DCompactPhysicalTest
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ContDiff
open KFCausalBDG4DCompactProfile (profile)
open KFCausalBDG4DNonzeroCompactKernel (functions data)
open KFCausalCSpecBridgeDefectObservable (BDG4DOperatorProfileData)
open KFCausalMinkowski4DMoments (f4D)

def squaredRadius (x : Fin 4 → ℝ) : ℝ := x 1^2+x 2^2+x 3^2
def field (x : Fin 4 → ℝ) : ℝ := functions.mbar (x 0) (Real.sqrt (squaredRadius x))
def axis (i : Fin 4) (t : ℝ) : Fin 4 → ℝ := fun j => if j=i then t else 0
def flatBox : ℝ := -deriv (deriv (fun t => field (axis 0 t))) 0+
  deriv (deriv (fun t => field (axis 1 t))) 0+
  deriv (deriv (fun t => field (axis 2 t))) 0+
  deriv (deriv (fun t => field (axis 3 t))) 0

def polynomialField (x : Fin 4 → ℝ) : ℝ :=
  1+2*(x 0)^2+2*squaredRadius x+((x 0)^2-squaredRadius x)^2

private theorem profile_local (x : ℝ) (hx : |x| ≤ 1) : profile x=1+x^2 := by
  unfold KFCausalBDG4DCompactProfile.profile
  rw [KFCausalBDG4DCompactProfile.bump.one_of_mem_closedBall]
  · exact one_mul _
  · simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero,KFCausalBDG4DCompactProfile.bump] using hx

theorem field_zero : field 0=1 := by
  simp only [field,squaredRadius,Pi.zero_apply,zero_pow (by norm_num : (2:ℕ)≠0),
    Real.sqrt_zero,functions,neg_zero,sub_zero,add_zero,
    KFCausalBDG4DCompactProfile.origin_jet.1,mul_one]

theorem radial_profile (t r : ℝ) (hr : 0 ≤ r) :
    field ![t,r,0,0]=functions.mbar t r := by
  simp [field,squaredRadius,Real.sqrt_sq hr]

theorem field_eq_polynomial (x : Fin 4 → ℝ)
    (hx : |x 0|+Real.sqrt (squaredRadius x) ≤ 1) : field x=polynomialField x := by
  have hR : 0 ≤ squaredRadius x := by unfold squaredRadius; positivity
  have hr : |Real.sqrt (squaredRadius x)|=Real.sqrt (squaredRadius x) :=
    abs_of_nonneg (Real.sqrt_nonneg _)
  have hminus : |-x 0-Real.sqrt (squaredRadius x)| ≤ 1 := by
    calc |-x 0-Real.sqrt (squaredRadius x)| ≤ |-x 0|+|Real.sqrt (squaredRadius x)| := abs_sub _ _
         _ = |x 0|+Real.sqrt (squaredRadius x) := by rw [abs_neg,hr]
         _ ≤ 1 := hx
  have hplus : |-x 0+Real.sqrt (squaredRadius x)| ≤ 1 := by
    calc |-x 0+Real.sqrt (squaredRadius x)| ≤ |-x 0|+|Real.sqrt (squaredRadius x)| := abs_add_le _ _
         _ = |x 0|+Real.sqrt (squaredRadius x) := by rw [abs_neg,hr]
         _ ≤ 1 := hx
  change profile (-x 0-Real.sqrt (squaredRadius x))*profile (-x 0+Real.sqrt (squaredRadius x))=polynomialField x
  rw [profile_local _ hminus,profile_local _ hplus]
  calc
    (1+(-x 0-Real.sqrt (squaredRadius x))^2)*(1+(-x 0+Real.sqrt (squaredRadius x))^2)=
      1+2*(x 0)^2+2*(Real.sqrt (squaredRadius x))^2+
        ((x 0)^2-(Real.sqrt (squaredRadius x))^2)^2 := by ring
    _ = polynomialField x := by rw [Real.sq_sqrt hR]; rfl

theorem field_eventually_polynomial : field =ᶠ[𝓝 (0 : Fin 4 → ℝ)] polynomialField := by
  have hc : Continuous (fun x : Fin 4 → ℝ => |x 0|+Real.sqrt (squaredRadius x)) := by
    unfold squaredRadius
    fun_prop
  have h0 : |(0 : Fin 4 → ℝ) 0|+Real.sqrt (squaredRadius 0) < 1 := by
    norm_num [squaredRadius]
  filter_upwards [hc.continuousAt.tendsto.eventually (gt_mem_nhds h0)] with x hx
  exact field_eq_polynomial x hx.le

theorem field_contDiffAt : ContDiffAt ℝ ∞ field (0 : Fin 4 → ℝ) := by
  have hp : ContDiff ℝ ∞ polynomialField := by
    unfold polynomialField squaredRadius
    fun_prop
  exact hp.contDiffAt.congr_of_eventuallyEq field_eventually_polynomial

theorem axis_local (i : Fin 4) :
    (fun t => field (axis i t)) =ᶠ[𝓝 (0:ℝ)] (fun t => 1+2*t^2+t^4) := by
  filter_upwards [eventually_lt_nhds (by norm_num : (0:ℝ)<1),
    eventually_gt_nhds (by norm_num : (-1:ℝ)<0)] with t ht1 ht2
  have ht : |t| ≤ 1 := abs_le.mpr ⟨ht2.le,ht1.le⟩
  have hn : |-t| ≤ 1 := by simpa only [abs_neg] using ht
  have ha : |(|t|)| ≤ 1 := by simpa only [abs_abs] using ht
  have hna : |(-|t|)| ≤ 1 := by simpa only [abs_neg,abs_abs] using ht
  fin_cases i <;> norm_num [field,axis,squaredRadius,functions,Fin.ext_iff,Real.sqrt_sq_eq_abs,
    profile_local t ht,profile_local (-t) hn,profile_local |t| ha,profile_local (-|t|) hna,
    profile_local 0 (by norm_num)] <;> ring

theorem axis_second (i : Fin 4) : deriv (deriv (fun t => field (axis i t))) 0=4 := by
  have hd (x : ℝ) : HasDerivAt (fun t : ℝ => 1+2*t^2+t^4) (4*x+4*x^3) x := by
    convert ((((hasDerivAt_id x).pow 2).const_mul 2).const_add 1).add
      ((hasDerivAt_id x).pow 4) using 1
    norm_num
    ring
  have he : deriv (fun t : ℝ => 1+2*t^2+t^4) = fun x => 4*x+4*x^3 :=
    funext (fun x => (hd x).deriv)
  rw [(axis_local i).deriv.deriv_eq,he]
  simpa using (((hasDerivAt_id (0:ℝ)).const_mul 4).add
    (((hasDerivAt_id (0:ℝ)).pow 3).const_mul 4)).deriv

theorem flatBox_eq : flatBox=8 := by
  simp only [flatBox,axis_second]
  norm_num

def densityParameter (ρ : ℝ) : ℝ := Real.pi*ρ/24

def densityOperator (ρ : ℝ) : ℝ :=
  (4/Real.sqrt 6)*Real.sqrt ρ*
    (ρ*(4*Real.pi)*(∫ t in Iio (0:ℝ), ∫ r in Ioo (0:ℝ) (-t),
      r^2*f4D (densityParameter ρ*(t^2-r^2)^2)*functions.mbar t r)-field 0)

theorem density_normalization (ρ : ℝ) (hρ : 0 ≤ ρ) :
    densityOperator ρ=(48/Real.sqrt Real.pi)*
      BDG4DOperatorProfileData.mean data.toProfileData (densityParameter ρ) := by
  have hs : Real.sqrt (Real.pi*ρ/24)=Real.sqrt Real.pi*Real.sqrt ρ/(2*Real.sqrt 6) := by
    rw [Real.sqrt_div (mul_nonneg Real.pi_pos.le hρ),Real.sqrt_mul Real.pi_pos.le,
      show (24:ℝ)=2^2*6 by norm_num,Real.sqrt_mul (by norm_num : (0:ℝ)≤2^2),
      Real.sqrt_sq (by norm_num : (0:ℝ)≤2)]
  rw [densityOperator,field_zero]
  change (4/Real.sqrt 6)*Real.sqrt ρ*(ρ*(4*Real.pi)*
    (∫ t in Iio (0:ℝ), ∫ r in Ioo (0:ℝ) (-t),
      r^2*f4D (densityParameter ρ*(t^2-r^2)^2)*functions.mbar t r)-1)=
    (48/Real.sqrt Real.pi)*(Real.sqrt (Real.pi*ρ/24)*
      (16*(Real.pi*ρ/24)*(∫ t in Iio (0:ℝ), ∫ r in Ioo (0:ℝ) (-t),
        r^2*f4D (densityParameter ρ*(t^2-r^2)^2)*functions.mbar t r)-(1/6)*(profile 0*profile 0)))
  rw [KFCausalBDG4DCompactProfile.origin_jet.1,hs]
  field_simp [ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos),ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<6))]
  ring

theorem densityParameter_tendsto : Tendsto densityParameter atTop atTop := by
  have ht : Tendsto (fun ρ : ℝ => (Real.pi/24)*ρ) atTop atTop :=
    Tendsto.const_mul_atTop (by positivity) tendsto_id
  change Tendsto (fun ρ : ℝ => Real.pi*ρ/24) atTop atTop
  simpa only [div_mul_eq_mul_div] using ht

theorem densityOperator_tendsto : Tendsto densityOperator atTop (𝓝 flatBox) := by
  rw [flatBox_eq]
  apply (KFCausalBDG4DNonzeroCompactKernel.normalized_tendsto.comp densityParameter_tendsto).congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with ρ hρ
  exact (density_normalization ρ hρ).symm

#print axioms field_zero
#print axioms radial_profile
#print axioms field_eq_polynomial
#print axioms field_eventually_polynomial
#print axioms field_contDiffAt
#print axioms axis_local
#print axioms axis_second
#print axioms flatBox_eq
#print axioms density_normalization
#print axioms densityParameter_tendsto
#print axioms densityOperator_tendsto
end
end UnifiedTheory.Audit.KFCausalBDG4DCompactPhysicalTest
