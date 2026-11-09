/- Strong angle continuity and uniform Hilbert bounds of the actual outer
matter strip actions, at every horizontal line and both graph endpoints. -/
import UnifiedTheory.Audit.KFCausalOuterMatterHalfField
import UnifiedTheory.Audit.KFCausalDominatedL2Continuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalOuterMatterActionContinuity
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanConfiguration (FrequencyHilbert)
open KFCausalClockFloorDefectCoordinates (straightening)
open KFCausalMixedStripExponentialGraph (unitary)
open KFCausalStripFamilyExponentialGraph (symbol)
open KFCausalOuterMatterHalfField (multiplier multiplierAction bound halfOutput half_line_bound)

variable (ε h a W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
  (k m : ℕ) (hε : 0 < ε) (hh : h ≠ 0) (ha : 0 < a) (hw : 1 ≤ w)
  (hW : w ≤ W) (hb : |h| ≤ ε/10)

theorem multiplier_angle_continuous (q : ℂ) (z : KFCausalEuclideanClockSplit.TailSpace) :
    Continuous (fun θ => multiplier ε h a W w C p b P k m θ q z) :=
  KFCausalOuterMatterMultiplier.multiplier_angle_continuous ε h a
    (KFCausalChargeGaussianGeometry.groundWidth h) W w
    (KFCausalNormalizedChargeFlow.momentumScale h) C p b P k m q
    (KFCausalMixedStripTailAttachment.tailPoint z)

include hε hh ha hw hW hb in
private theorem symbol_bound (θ y : ℝ) (hy : |y| ≤ |h|)
    (x : KFCausalEuclideanConfiguration.Space) :
    ‖symbol (multiplier ε h a W w C p b P k m θ) y x‖ ≤ bound ε h a W w C p b P k m := by
  apply KFCausalOuterMatterMultiplier.multiplier_bound ε h a _ W w _ θ C p b P k m
    hε hb ha.le (KFCausalChargeGaussianGeometry.groundWidth_positive h hh) hw hW
  simpa only [Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,zero_add] using hy

theorem action_norm_bound (θ y : ℝ) (hy : |y| ≤ |h|) (f : Hilbert) :
    ‖multiplierAction ε h a W w C p b P k m hε hh ha hw hW hb θ y hy f‖ ≤
      bound ε h a W w C p b P k m*‖f‖ := by
  unfold multiplierAction
  exact KFCausalMixedStripExponentialGraph.action_norm _ _ _ _ _ _ _ _ _ _ _
    (symbol_bound ε h a W w C p b P k m hε hh ha hw hW hb θ y hy) f

theorem action_continuous (y : ℝ) (hy : |y| ≤ |h|) (f : Hilbert) :
    Continuous (fun θ => multiplierAction ε h a W w C p b P k m hε hh ha hw hW hb θ y hy f) := by
  let g : FrequencyHilbert := straightening ε hε (unitary ε hε f)
  let T : ℝ → FrequencyHilbert := fun θ => straightening ε hε
    (unitary ε hε (multiplierAction ε h a W w C p b P k m hε hh ha hw hW hb θ y hy f))
  let F : ℝ → KFCausalEuclideanConfiguration.Space → ℂ :=
    fun θ x => symbol (multiplier ε h a W w C p b P k m θ) y x*g x
  have hT (θ : ℝ) : T θ =ᵐ[volume] F θ := by
    exact KFCausalMixedStripExponentialGraph.action_coe _ _ _ _ _ _ _ _ _ _ _
  have hF (θ : ℝ) : MemLp (F θ) 2 volume := (Lp.memLp (T θ)).ae_eq (hT θ)
  have he : (fun θ => (hF θ).toLp (F θ)) = T := by
    funext θ
    exact Lp.ext ((hF θ).coeFn_toLp.trans (hT θ).symm)
  have hc : Continuous T := by
    have hM : 0 ≤ bound ε h a W w C p b P k m :=
      KFCausalOuterMatterMultiplier.bound_nonnegative ε h a
        (KFCausalChargeGaussianGeometry.groundWidth h) W w C p b P k m hε
        (KFCausalChargeGaussianGeometry.groundWidth_positive h hh) hw hW
    rw [← he]
    apply KFCausalDominatedL2Continuity.continuous_toLp F hF
      (fun x => (bound ε h a W w C p b P k m:ℂ)*g x) ((Lp.memLp g).const_mul _)
    · intro θ
      filter_upwards [] with x
      dsimp only [F]
      rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hM]
      exact mul_le_mul_of_nonneg_right
        (symbol_bound ε h a W w C p b P k m hε hh ha hw hW hb θ y hy x) (norm_nonneg _)
    · filter_upwards [] with x
      exact (multiplier_angle_continuous ε h a W w C p b P k m _ _).mul continuous_const
  have hbck := (unitary ε hε).symm.continuous.comp ((straightening ε hε).symm.continuous.comp hc)
  simpa only [T,Function.comp_def,LinearIsometryEquiv.symm_apply_apply] using hbck

theorem halfOutput_continuous (f : Hilbert) :
    Continuous (fun θ => halfOutput ε h a W w C p b P k m hε hh ha hw hW hb θ f) :=
  action_continuous ε h a W w C p b P k m hε hh ha hw hW hb (-h/2) (half_line_bound h) f

theorem halfOutput_norm_bound (θ : ℝ) (f : Hilbert) :
    ‖halfOutput ε h a W w C p b P k m hε hh ha hw hW hb θ f‖ ≤
      bound ε h a W w C p b P k m*‖f‖ :=
  action_norm_bound ε h a W w C p b P k m hε hh ha hw hW hb θ (-h/2) (half_line_bound h) f

theorem full_line_continuous (f : Hilbert) :
    Continuous (fun θ => multiplierAction ε h a W w C p b P k m hε hh ha hw hW hb
      θ (-h) (by simp) f) :=
  action_continuous ε h a W w C p b P k m hε hh ha hw hW hb (-h) (by simp) f

theorem full_line_norm_bound (θ : ℝ) (f : Hilbert) :
    ‖multiplierAction ε h a W w C p b P k m hε hh ha hw hW hb θ (-h) (by simp) f‖ ≤
      bound ε h a W w C p b P k m*‖f‖ :=
  action_norm_bound ε h a W w C p b P k m hε hh ha hw hW hb θ (-h) (by simp) f

#print axioms multiplier_angle_continuous
#print axioms action_norm_bound
#print axioms action_continuous
#print axioms halfOutput_continuous
#print axioms halfOutput_norm_bound
#print axioms full_line_continuous
#print axioms full_line_norm_bound
end
end UnifiedTheory.Audit.KFCausalOuterMatterActionContinuity
