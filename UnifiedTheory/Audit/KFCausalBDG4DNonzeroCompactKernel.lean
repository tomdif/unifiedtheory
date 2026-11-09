/- A nonzero compact test profile for the original reduced four-dimensional
BDG operator.  Compact support is two-sided in the null coordinates; the
retarded integration region remains the original positive null quadrant.
This constructs an analytic flat-space supplier, not microscopic geometry. -/
import UnifiedTheory.Audit.KFCausalBDG4DCompactProfile
import UnifiedTheory.Audit.KFCausalCSpecBDG4DCanonicalZeroKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalBDG4DNonzeroCompactKernel
noncomputable section
open Filter Topology
open KFCausalCSpecBridgeDefectObservable
open KFCausalMinkowski4DMoments (f4D)
open KFCausalBDG4DCompactProfile (profile first second bound)

def scales : BDG4DOperatorProfileScales where
  uSupport := 3
  vSupport := 3
  profileBound := bound^2
  profileDerivBound := bound^2
  mixedBound := bound^2
  mixedUDerivBound := bound^2
  mixedVDerivBound := bound^2
  coneBound := 324*bound^2
  huSupport_pos := by norm_num
  hvSupport_pos := by norm_num

def functions : BDG4DOperatorProfileFunctions where
  mbar := fun t r => profile (-t-r)*profile (-t+r)
  profile := fun u v => profile u*profile v
  profileU := fun u v => first u*profile v
  profileUV := fun u v => first u*first v
  profileUVU := fun u v => second u*first v
  profileUVV := fun u v => first u*second v
  profileUU := fun v => second 0*profile v
  profileVV := fun u => profile u*second 0
  profile_def := by
    intro u v
    congr 2 <;> ring
  even_mbar := by
    intro t r
    simp only [sub_neg_eq_add,← sub_eq_add_neg,mul_comm]

def regularity : BDG4DOperatorProfileRegularity functions where
  profile_cont := (KFCausalBDG4DCompactProfile.smooth.continuous.comp continuous_fst).mul
    (KFCausalBDG4DCompactProfile.smooth.continuous.comp continuous_snd)
  profileU_cont := (KFCausalBDG4DCompactProfile.first_smooth.continuous.comp continuous_fst).mul
    (KFCausalBDG4DCompactProfile.smooth.continuous.comp continuous_snd)
  profileUV_cont := (KFCausalBDG4DCompactProfile.first_smooth.continuous.comp continuous_fst).mul
    (KFCausalBDG4DCompactProfile.first_smooth.continuous.comp continuous_snd)
  profile_deriv_u := fun v u => (KFCausalBDG4DCompactProfile.profile_derivative u).mul_const (profile v)
  profileU_deriv_v := fun u v => (KFCausalBDG4DCompactProfile.profile_derivative v).const_mul (first u)
  profileUV_deriv_u := fun v u => (KFCausalBDG4DCompactProfile.first_derivative u).mul_const (first v)
  profileUV_deriv_v := fun u v => (KFCausalBDG4DCompactProfile.first_derivative v).const_mul (first u)
  profileVV_deriv := fun u => (KFCausalBDG4DCompactProfile.profile_derivative u).mul_const (second 0)
  profileUU_deriv := fun v => (KFCausalBDG4DCompactProfile.profile_derivative v).const_mul (second 0)
  profileUVV_axis_cont := KFCausalBDG4DCompactProfile.first_smooth.continuous.mul continuous_const
  profileUVU_axis_cont := continuous_const.mul KFCausalBDG4DCompactProfile.first_smooth.continuous

private theorem product_bound (x y : ℝ) (hx : |x| ≤ bound) (hy : |y| ≤ bound) :
    |x*y| ≤ bound^2 := by
  rw [abs_mul,pow_two]
  exact mul_le_mul hx hy (abs_nonneg _) KFCausalBDG4DCompactProfile.uniform_bound.1

def uniformBounds : BDG4DOperatorProfileUniformBounds scales functions where
  profile_bound := fun u v => product_bound _ _
    (KFCausalBDG4DCompactProfile.uniform_bound.2.1 u) (KFCausalBDG4DCompactProfile.uniform_bound.2.1 v)
  profileU_bound := fun u v => product_bound _ _
    (KFCausalBDG4DCompactProfile.uniform_bound.2.2.1 u) (KFCausalBDG4DCompactProfile.uniform_bound.2.1 v)
  profileUV_bound := fun u v => product_bound _ _
    (KFCausalBDG4DCompactProfile.uniform_bound.2.2.1 u) (KFCausalBDG4DCompactProfile.uniform_bound.2.2.1 v)
  profileUVU_bound := fun u v => product_bound _ _
    (KFCausalBDG4DCompactProfile.uniform_bound.2.2.2 u) (KFCausalBDG4DCompactProfile.uniform_bound.2.2.1 v)
  profileUVV_bound := fun u v => product_bound _ _
    (KFCausalBDG4DCompactProfile.uniform_bound.2.2.1 u) (KFCausalBDG4DCompactProfile.uniform_bound.2.2.2 v)

private theorem profile_high (x : ℝ) (hx : 3 ≤ x) : profile x=0 :=
  (KFCausalBDG4DCompactProfile.outside_support x (hx.trans (le_abs_self x))).1
private theorem first_high (x : ℝ) (hx : 3 ≤ x) : first x=0 :=
  (KFCausalBDG4DCompactProfile.outside_support x (hx.trans (le_abs_self x))).2.1

def support : BDG4DOperatorProfileSupport scales functions where
  profile_support_u := by intro u v hu; change profile u*profile v=0; rw [profile_high u hu,zero_mul]
  profile_support_v := by intro u v hv; change profile u*profile v=0; rw [profile_high v hv,mul_zero]
  profileU_support_u := by intro u v hu; change first u*profile v=0; rw [first_high u hu,zero_mul]
  profileU_support_v := by intro u v hv; change first u*profile v=0; rw [profile_high v hv,mul_zero]
  profileUV_support_u := by intro u v hu; change first u*first v=0; rw [first_high u hu,zero_mul]
  profileUV_support_v := by intro u v hv; change first u*first v=0; rw [first_high v hv,mul_zero]
  profileVV_support := by intro u hu; change profile u*second 0=0; rw [profile_high u hu,zero_mul]
  profileUU_support := by intro v hv; change second 0*profile v=0; rw [profile_high v hv,mul_zero]

theorem cone_bound (a : ℝ) (ha : 0 < a) (u v : ℝ) :
    |a*(v-u)^2*f4D (a*u^2*v^2)*(profile u*profile v)| ≤ 324*bound^2*a := by
  by_cases hu : 3 ≤ |u|
  · rw [(KFCausalBDG4DCompactProfile.outside_support u hu).1,zero_mul,mul_zero,abs_zero]
    positivity
  by_cases hv : 3 ≤ |v|
  · rw [(KFCausalBDG4DCompactProfile.outside_support v hv).1,mul_zero,mul_zero,abs_zero]
    positivity
  have hab : |v-u| ≤ 6 := (abs_sub v u).trans (by linarith [lt_of_not_ge hu,lt_of_not_ge hv])
  have hsq : (v-u)^2 ≤ 36 := by nlinarith [sq_abs (v-u),abs_nonneg (v-u)]
  have hk := KFCausalMinkowski4DRealModes.f4D_abs_le (a*u^2*v^2) (by positivity)
  have hp := product_bound _ _ (KFCausalBDG4DCompactProfile.uniform_bound.2.1 u)
    (KFCausalBDG4DCompactProfile.uniform_bound.2.1 v)
  rw [abs_mul,abs_mul,abs_mul,abs_of_pos ha,abs_sq]
  calc
    a*(v-u)^2*|f4D (a*u^2*v^2)| * |profile u*profile v|
      ≤ (a*36)*9*bound^2 := mul_le_mul
        (mul_le_mul (mul_le_mul_of_nonneg_left hsq ha.le) hk (abs_nonneg _) (by positivity))
        hp (abs_nonneg _) (by positivity)
    _ = 324*bound^2*a := by ring

def data : BDG4DOperatorProfileSplitData where
  scales := scales
  functions := functions
  regularity := regularity
  uniformBounds := uniformBounds
  support := support
  coneBound := ⟨cone_bound⟩

theorem target_eq : BDG4DOperatorProfileData.target data.toProfileData=Real.sqrt Real.pi/6 := by
  change Real.sqrt Real.pi/24*(second 0*profile 0+profile 0*second 0)-
    Real.sqrt Real.pi/6*(first 0*first 0)=Real.sqrt Real.pi/6
  rw [KFCausalBDG4DCompactProfile.origin_jet.1,KFCausalBDG4DCompactProfile.origin_jet.2.1,
    KFCausalBDG4DCompactProfile.origin_jet.2.2]
  ring

theorem target_ne_zero : BDG4DOperatorProfileData.target data.toProfileData ≠ 0 := by
  rw [target_eq]
  exact ne_of_gt (div_pos (Real.sqrt_pos.mpr Real.pi_pos) (by norm_num))

theorem mean_tendsto : Tendsto (BDG4DOperatorProfileData.mean data.toProfileData)
    atTop (𝓝 (Real.sqrt Real.pi/6)) := by
  rw [← target_eq]
  exact data.tendsto

theorem normalized_tendsto :
    Tendsto (fun a => (48/Real.sqrt Real.pi)*BDG4DOperatorProfileData.mean data.toProfileData a)
      atTop (𝓝 (8:ℝ)) := by
  convert mean_tendsto.const_mul (48/Real.sqrt Real.pi) using 1
  field_simp [ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)]
  norm_num

theorem sampled_tendsto (density : ℕ → ℝ) (hd : Tendsto density atTop atTop) :
    Tendsto (fun n => (48/Real.sqrt Real.pi)*BDG4DOperatorProfileData.mean data.toProfileData (density n))
      atTop (𝓝 (8:ℝ)) := normalized_tendsto.comp hd

#print axioms cone_bound
#print axioms target_eq
#print axioms target_ne_zero
#print axioms mean_tendsto
#print axioms normalized_tendsto
#print axioms sampled_tendsto
end
end UnifiedTheory.Audit.KFCausalBDG4DNonzeroCompactKernel
