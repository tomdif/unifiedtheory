/- Strong angle continuity and uniform bounds for the actual second
exponential and square outputs with one symmetric-position insertion. The domination
is the proved strip multiplier bound, independent of the charge angle. -/
import UnifiedTheory.Audit.KFCausalSourcedWidthSymmetricSquare
import UnifiedTheory.Audit.KFCausalDominatedL2Continuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 1024

namespace UnifiedTheory.Audit.KFCausalSourcedWidthSymmetricContinuity
noncomputable section
open MeasureTheory Filter
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanConfiguration (FrequencyHilbert)
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalClockFloorBoundedInverse (inverseL inverseL_eq inverseAction_norm_bound)
open KFCausalClockFloorDefectCoordinates (straightening)
open KFCausalMixedStripExponentialGraph (unitary)
open KFCausalStripFamilyExponentialGraph (symbol)
open KFCausalComplexShearPerturbation (Space flow rotatedFlow)
open KFCausalNormalizedComplexRotation (rotate rotationIsometry)
open KFCausalComplexQuadraticPerturbation (quadratic)
open KFCausalSourcedWidthSymmetricSquare

variable (ε h a W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ) (i : Fin 2) (hε : 0 < ε) (hh : h ≠ 0)
  (ha : 0 < a) (hw : 1 ≤ w) (hW : w ≤ W) (hb : |h| ≤ ε/10)
local notation "hw₀" => lt_of_lt_of_le zero_lt_one hw
local notation "hW₀" => lt_of_lt_of_le hw₀ hW

theorem multiplier_angle_continuous (q : ℂ) (z : KFCausalEuclideanClockSplit.TailSpace) :
    Continuous (fun θ => multiplier ε h a W w C p b P i θ q z) :=
  KFCausalSourcedWidthSymmetricMultiplier.multiplier_angle_continuous ε h a
    (KFCausalChargeGaussianGeometry.groundWidth h) W w
    (KFCausalNormalizedChargeFlow.momentumScale h) C p b P i q
    (KFCausalMixedStripTailAttachment.tailPoint z)

include hε hh ha hw hW hb in
private theorem symbol_bound (θ y : ℝ) (hy : |y| ≤ |h|)
    (x : KFCausalEuclideanConfiguration.Space) :
    ‖symbol (multiplier ε h a W w C p b P i θ) y x‖ ≤ bound ε h a W w C p b P i := by
  apply KFCausalSourcedWidthSymmetricMultiplier.multiplier_bound
    ε h a _ W w _ θ C p b P i hε hb ha.le (KFCausalChargeGaussianGeometry.groundWidth_positive h hh) hw hW
  simpa only [Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,zero_add] using hy

theorem multiplierAction_norm_bound (θ y : ℝ) (hy : |y| ≤ |h|) (f : Hilbert) :
    ‖multiplierAction ε h a W w C p b P i hε hh ha hw hW hb θ y hy f‖ ≤ bound ε h a W w C p b P i*‖f‖ := by
  unfold multiplierAction
  exact KFCausalMixedStripExponentialGraph.action_norm _ _ _ _ _ _ _ _ _ _ _
    (symbol_bound ε h a W w C p b P i hε hh ha hw hW hb θ y hy) f

theorem multiplierAction_angle_continuous (y : ℝ) (hy : |y| ≤ |h|) (f : Hilbert) :
    Continuous (fun θ => multiplierAction ε h a W w C p b P i hε hh ha hw hW hb θ y hy f) := by
  let g : FrequencyHilbert := straightening ε hε (unitary ε hε f)
  let T : ℝ → FrequencyHilbert := fun θ => straightening ε hε
    (unitary ε hε (multiplierAction ε h a W w C p b P i hε hh ha hw hW hb θ y hy f))
  let F : ℝ → KFCausalEuclideanConfiguration.Space → ℂ :=
    fun θ x => symbol (multiplier ε h a W w C p b P i θ) y x*g x
  have hT (θ : ℝ) : T θ =ᵐ[volume] F θ := by
    exact KFCausalMixedStripExponentialGraph.action_coe _ _ _ _ _ _ _ _ _ _ _
  have hF (θ : ℝ) : MemLp (F θ) 2 volume := (Lp.memLp (T θ)).ae_eq (hT θ)
  have he : (fun θ => (hF θ).toLp (F θ)) = T := by
    funext θ
    exact Lp.ext ((hF θ).coeFn_toLp.trans (hT θ).symm)
  have hc : Continuous T := by
    have hM : 0 ≤ bound ε h a W w C p b P i :=
      KFCausalSourcedWidthSymmetricMultiplier.bound_nonnegative ε h a (KFCausalChargeGaussianGeometry.groundWidth h) W w C p b P i hε (KFCausalChargeGaussianGeometry.groundWidth_positive h hh) hw hW
    rw [← he]
    apply KFCausalDominatedL2Continuity.continuous_toLp F hF
      (fun x => (bound ε h a W w C p b P i:ℂ)*g x) ((Lp.memLp g).const_mul _)
    · intro θ
      filter_upwards [] with x
      dsimp only [F]
      rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg hM]
      exact mul_le_mul_of_nonneg_right (symbol_bound ε h a W w C p b P i hε hh ha hw hW hb θ y hy x) (norm_nonneg _)
    · filter_upwards [] with x
      exact (multiplier_angle_continuous ε h a W w C p b P i _ _).mul continuous_const
  have hbck := (unitary ε hε).symm.continuous.comp ((straightening ε hε).symm.continuous.comp hc)
  simpa only [T,Function.comp_def,LinearIsometryEquiv.symm_apply_apply] using hbck

theorem exponentialOutput_continuous :
    Continuous (exponentialOutput ε h a W w C p b P i hε hh ha hw hW hb) :=
  multiplierAction_angle_continuous ε h a W w C p b P i hε hh ha hw hW hb (-h) (by simp) _

theorem exponentialOutput_norm_bound (θ : ℝ) :
    ‖exponentialOutput ε h a W w C p b P i hε hh ha hw hW hb θ‖ ≤
      bound ε h a W w C p b P i*‖baselineOutput ε h a W hε hh ha hb‖ :=
  multiplierAction_norm_bound ε h a W w C p b P i hε hh ha hw hW hb θ (-h) (by simp) _

theorem secondOutput_continuous : Continuous (secondOutput ε h a W w C p b P i hε hh ha hw hW hb) :=
  (inverseL ε hε).continuous.comp (exponentialOutput_continuous ε h a W w C p b P i hε hh ha hw hW hb)

theorem secondOutput_norm_bound (θ : ℝ) :
    ‖secondOutput ε h a W w C p b P i hε hh ha hw hW hb θ‖ ≤
      (Real.sqrt ε)⁻¹*(bound ε h a W w C p b P i*‖baselineOutput ε h a W hε hh ha hb‖) := by
  exact (inverseAction_norm_bound ε hε _).trans
    (mul_le_mul_of_nonneg_left (exponentialOutput_norm_bound ε h a W w C p b P i hε hh ha hw hW hb θ)
      (inv_nonneg.mpr (Real.sqrt_nonneg ε)))

#print axioms multiplier_angle_continuous
#print axioms multiplierAction_norm_bound
#print axioms multiplierAction_angle_continuous
#print axioms exponentialOutput_continuous
#print axioms exponentialOutput_norm_bound
#print axioms secondOutput_continuous
#print axioms secondOutput_norm_bound
end
end UnifiedTheory.Audit.KFCausalSourcedWidthSymmetricContinuity
