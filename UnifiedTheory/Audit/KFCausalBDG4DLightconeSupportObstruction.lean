/- The globally regular kernel/profile supplier with one-sided null support
has only zero continuum targets.  This is an obstruction to that supplier,
not to the reduced BDG operator or to a physical theory. -/
import UnifiedTheory.Audit.KFCausalCSpecBDG4DCanonicalZeroKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalBDG4DLightconeSupportObstruction
noncomputable section
open Set Filter Topology
open KFCausalCSpecBridgeDefectObservable

private theorem value_zero (f : ℝ → ℝ) (hf : Continuous f)
    (hz : ∀ x, x < 0 → f x=0) : f 0=0 := by
  have he : EqOn f (fun _ => 0) (Iio 0) := fun x hx => hz x hx
  exact he.closure hf continuous_const (by simp [closure_Iio])

private theorem derivative_negative (f : ℝ → ℝ) (d x : ℝ)
    (hd : HasDerivAt f d x) (hz : ∀ y, y < 0 → f y=0) (hx : x < 0) : d=0 := by
  have he : f =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [eventually_lt_nhds hx] with y hy using hz y hy
  exact hd.unique ((hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq he)

private theorem derivative_boundary (f : ℝ → ℝ) (d : ℝ)
    (hf : Continuous f) (hd : HasDerivAt f d 0) (hz : ∀ x, x < 0 → f x=0) : d=0 := by
  have h0 : HasDerivWithinAt f 0 (Iio 0) 0 :=
    (hasDerivAt_const 0 (0:ℝ)).hasDerivWithinAt.congr (fun x hx => hz x hx) (value_zero f hf hz)
  exact (hd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio 0)).symm.trans
    (h0.derivWithin (uniqueDiffWithinAt_Iio 0))

variable (D : BDG4DOperatorProfileKernelSplitData)

private theorem first_negative_u (u v : ℝ) (hu : u < 0) : D.functions.profileU u v=0 :=
  derivative_negative _ _ _ (D.regularity.profile_deriv_u v u)
    (fun t ht => D.lightconeSupport.profile_support_u_neg t v ht) hu

private theorem first_negative_v (u v : ℝ) (hv : v < 0) : D.functions.profileU u v=0 := by
  have h0 : HasDerivAt (fun t => D.functions.profile t v) 0 u := by
    convert hasDerivAt_const u (0:ℝ) using 1
    funext t
    exact D.lightconeSupport.profile_support_v_neg t v hv
  exact (D.regularity.profile_deriv_u v u).unique h0

private theorem mixed_negative_u (u v : ℝ) (hu : u < 0) : D.functions.profileUV u v=0 := by
  have h0 : HasDerivAt (fun t => D.functions.profileU u t) 0 v := by
    convert hasDerivAt_const v (0:ℝ) using 1
    funext t
    exact first_negative_u D u t hu
  exact (D.regularity.profileU_deriv_v u v).unique h0

private theorem mixed_negative_v (u v : ℝ) (hv : v < 0) : D.functions.profileUV u v=0 :=
  derivative_negative _ _ _ (D.regularity.profileU_deriv_v u v)
    (fun t ht => first_negative_v D u t ht) hv

theorem profile_axis_zero :
    (∀ v, D.functions.profile 0 v=0) ∧ (∀ u, D.functions.profile u 0=0) := by
  constructor
  · intro v
    exact value_zero _ (D.regularity.profile_cont.comp (continuous_id.prodMk continuous_const))
      (fun u hu => D.lightconeSupport.profile_support_u_neg u v hu)
  · intro u
    exact value_zero _ (D.regularity.profile_cont.comp (continuous_const.prodMk continuous_id))
      (fun v hv => D.lightconeSupport.profile_support_v_neg u v hv)

theorem mixed_derivative_axis_zero :
    (∀ v, D.functions.profileUV 0 v=0) ∧ (∀ u, D.functions.profileUV u 0=0) := by
  constructor
  · intro v
    exact value_zero _ (D.regularity.profileUV_cont.comp (continuous_id.prodMk continuous_const))
      (fun u hu => mixed_negative_u D u v hu)
  · intro u
    exact value_zero _ (D.regularity.profileUV_cont.comp (continuous_const.prodMk continuous_id))
      (fun v hv => mixed_negative_v D u v hv)

private theorem third_axis_zero :
    (∀ v, D.functions.profileUVU 0 v=0) ∧ (∀ u, D.functions.profileUVV u 0=0) := by
  constructor
  · intro v
    exact derivative_boundary _ _
      (D.regularity.profileUV_cont.comp (continuous_id.prodMk continuous_const))
      (D.regularity.profileUV_deriv_u v 0) (fun u hu => mixed_negative_u D u v hu)
  · intro u
    exact derivative_boundary _ _
      (D.regularity.profileUV_cont.comp (continuous_const.prodMk continuous_id))
      (D.regularity.profileUV_deriv_v u 0) (fun v hv => mixed_negative_v D u v hv)

theorem pure_axis_zero :
    (∀ v, D.functions.profileUU v=0) ∧ (∀ u, D.functions.profileVV u=0) := by
  constructor
  · intro v
    have he := is_const_of_deriv_eq_zero
      (fun t => (D.regularity.profileUU_deriv t).differentiableAt)
      (fun t => (D.regularity.profileUU_deriv t).deriv.trans ((third_axis_zero D).1 t))
      v D.scales.vSupport
    exact he.trans (D.support.profileUU_support _ le_rfl)
  · intro u
    have he := is_const_of_deriv_eq_zero
      (fun t => (D.regularity.profileVV_deriv t).differentiableAt)
      (fun t => (D.regularity.profileVV_deriv t).deriv.trans ((third_axis_zero D).2 t))
      u D.scales.uSupport
    exact he.trans (D.support.profileVV_support _ le_rfl)

theorem target_zero : BDG4DOperatorProfileData.target D.toProfileData=0 := by
  change Real.sqrt Real.pi/24*(D.functions.profileUU 0+D.functions.profileVV 0)-
    Real.sqrt Real.pi/6*D.functions.profileUV 0 0=0
  rw [(pure_axis_zero D).1 0,(pure_axis_zero D).2 0,(mixed_derivative_axis_zero D).1 0]
  ring

theorem no_nonzero_target : ¬ HasNonzeroBDG4DTarget D := by
  exact fun h => h (target_zero D)

#print axioms profile_axis_zero
#print axioms mixed_derivative_axis_zero
#print axioms pure_axis_zero
#print axioms target_zero
#print axioms no_nonzero_target
end
end UnifiedTheory.Audit.KFCausalBDG4DLightconeSupportObstruction
