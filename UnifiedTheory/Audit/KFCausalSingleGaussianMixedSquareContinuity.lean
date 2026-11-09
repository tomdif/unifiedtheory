/- Strong angle continuity and uniform bounds for the actual second
exponential and square outputs of the singleton Gaussian. The domination
is the proved strip multiplier bound, independent of the charge angle. -/
import UnifiedTheory.Audit.KFCausalSingleGaussianMixedSquare
import UnifiedTheory.Audit.KFCausalDominatedL2Continuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 1024

namespace UnifiedTheory.Audit.KFCausalSingleGaussianMixedSquareContinuity
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
open KFCausalSingleGaussianMixedSquare

private theorem continuous_rotation (η : ℝ → ℝ) (g : ℝ → Space)
    (hη : Continuous η) (hg : ∀ i, Continuous (fun θ => g θ i)) :
    ∀ i, Continuous (fun θ => rotate (η θ) (g θ) i) := by
  have hc := Complex.continuous_ofReal.comp (Real.continuous_cos.comp hη)
  have hs := Complex.continuous_ofReal.comp (Real.continuous_sin.comp hη)
  intro i
  fin_cases i <;> dsimp [rotate]
  · exact (hc.mul (hg 0)).sub (hs.mul (hg 2))
  · exact (hc.mul (hg 1)).sub (hs.mul (hg 3))
  · exact (hs.mul (hg 0)).add (hc.mul (hg 2))
  · exact (hs.mul (hg 1)).add (hc.mul (hg 3))
  · exact hg 4

private theorem continuous_fixed_flow (σ : ℝ) (z : ℂ) (g : ℝ → Space)
    (hg : ∀ i, Continuous (fun θ => g θ i)) :
    ∀ i, Continuous (fun θ => flow σ z (g θ) i) := by
  intro i
  fin_cases i <;> dsimp [flow]
  · exact continuous_const.mul (hg 0)
  · exact continuous_const.mul (hg 1)
  · exact continuous_const.mul (hg 2)
  · exact continuous_const.mul (hg 3)
  · exact (hg 4).add (continuous_const.mul (hg 3))

theorem holomorphic_multiplier_angle_continuous (ε h a α c : ℝ)
    (q : ℂ) (x : Joint 2 4) :
    Continuous (fun θ => KFCausalSingleGaussianHolomorphicQuotient.multiplier
      ε h a α c θ q x) := by
  have hr := continuous_rotation (fun θ => θ)
    (fun _ => KFCausalSingleGaussianHolomorphicQuotient.baselineVector ε α c q x)
    continuous_id (fun _ => continuous_const)
  have hf := continuous_fixed_flow (KFCausalPhysicalReciprocalNormalization.coupling α 1)
    (KFCausalComplexClockInverse.complexInverse ε (KFCausalTwoShearClockQuotient.shift h q)-
      KFCausalComplexClockInverse.complexInverse ε q) _ hr
  have ht : ∀ i, Continuous (fun θ =>
      KFCausalSingleGaussianHolomorphicQuotient.targetVector ε h α c θ q x i) :=
    continuous_rotation (fun θ => -θ) _ continuous_neg hf
  have hq : Continuous (fun θ => quadratic (fun i =>
      KFCausalSingleGaussianHolomorphicQuotient.targetVector ε h α c θ q x i)) := by
    unfold quadratic
    exact continuous_finset_sum _ (fun i _ => (ht i).pow 2)
  exact continuous_const.mul (hq.neg.add continuous_const).cexp

variable (ε h a : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
  (ha : 0 < a) (hb : |h| ≤ ε/10)

theorem multiplier_angle_continuous (q : ℂ) (z : KFCausalEuclideanClockSplit.TailSpace) :
    Continuous (fun θ => multiplier ε h a θ q z) :=
  holomorphic_multiplier_angle_continuous ε h a
    (KFCausalChargeGaussianGeometry.groundWidth h)
    (KFCausalNormalizedChargeFlow.momentumScale h) q
    (KFCausalMixedStripTailAttachment.tailPoint z)

include hε hh ha hb in
private theorem symbol_bound (θ y : ℝ) (hy : |y| ≤ |h|)
    (x : KFCausalEuclideanConfiguration.Space) :
    ‖symbol (multiplier ε h a θ) y x‖ ≤ bound ε h a := by
  apply KFCausalSingleGaussianHolomorphicQuotient.multiplier_bound
    ε h a _ _ θ hε hb ha.le (KFCausalChargeGaussianGeometry.groundWidth_positive h hh)
  simpa only [Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,zero_add] using hy

theorem multiplierAction_norm_bound (θ y : ℝ) (hy : |y| ≤ |h|) (f : Hilbert) :
    ‖multiplierAction ε h a hε hh ha hb θ y hy f‖ ≤ bound ε h a*‖f‖ := by
  unfold multiplierAction
  exact KFCausalMixedStripExponentialGraph.action_norm _ _ _ _ _ _ _ _ _ _ _
    (symbol_bound ε h a hε hh ha hb θ y hy) f

theorem multiplierAction_angle_continuous (y : ℝ) (hy : |y| ≤ |h|) (f : Hilbert) :
    Continuous (fun θ => multiplierAction ε h a hε hh ha hb θ y hy f) := by
  let g : FrequencyHilbert := straightening ε hε (unitary ε hε f)
  let T : ℝ → FrequencyHilbert := fun θ => straightening ε hε
    (unitary ε hε (multiplierAction ε h a hε hh ha hb θ y hy f))
  let F : ℝ → KFCausalEuclideanConfiguration.Space → ℂ :=
    fun θ x => symbol (multiplier ε h a θ) y x*g x
  have hT (θ : ℝ) : T θ =ᵐ[volume] F θ := by
    exact KFCausalMixedStripExponentialGraph.action_coe _ _ _ _ _ _ _ _ _ _ _
  have hF (θ : ℝ) : MemLp (F θ) 2 volume := (Lp.memLp (T θ)).ae_eq (hT θ)
  have he : (fun θ => (hF θ).toLp (F θ)) = T := by
    funext θ
    exact Lp.ext ((hF θ).coeFn_toLp.trans (hT θ).symm)
  have hc : Continuous T := by
    have hM : 0 ≤ bound ε h a :=
      KFCausalSingleGaussianHolomorphicQuotient.bound_nonnegative ε h a hε
    rw [← he]
    apply KFCausalDominatedL2Continuity.continuous_toLp F hF
      (fun x => (bound ε h a:ℂ)*g x) ((Lp.memLp g).const_mul _)
    · intro θ
      filter_upwards [] with x
      dsimp only [F]
      rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg hM]
      exact mul_le_mul_of_nonneg_right (symbol_bound ε h a hε hh ha hb θ y hy x) (norm_nonneg _)
    · filter_upwards [] with x
      exact (multiplier_angle_continuous ε h a _ _).mul continuous_const
  have hbck := (unitary ε hε).symm.continuous.comp ((straightening ε hε).symm.continuous.comp hc)
  simpa only [T,Function.comp_def,LinearIsometryEquiv.symm_apply_apply] using hbck

theorem exponentialOutput_continuous :
    Continuous (exponentialOutput ε h a hε hh ha hb) :=
  multiplierAction_angle_continuous ε h a hε hh ha hb (-h) (by simp) _

theorem exponentialOutput_norm_bound (θ : ℝ) :
    ‖exponentialOutput ε h a hε hh ha hb θ‖ ≤
      bound ε h a*‖baselineOutput ε h a hε hh ha hb‖ :=
  multiplierAction_norm_bound ε h a hε hh ha hb θ (-h) (by simp) _

theorem secondOutput_continuous : Continuous (secondOutput ε h a hε hh ha hb) :=
  (inverseL ε hε).continuous.comp (exponentialOutput_continuous ε h a hε hh ha hb)

theorem secondOutput_norm_bound (θ : ℝ) :
    ‖secondOutput ε h a hε hh ha hb θ‖ ≤
      (Real.sqrt ε)⁻¹*(bound ε h a*‖baselineOutput ε h a hε hh ha hb‖) := by
  exact (inverseAction_norm_bound ε hε _).trans
    (mul_le_mul_of_nonneg_left (exponentialOutput_norm_bound ε h a hε hh ha hb θ)
      (inv_nonneg.mpr (Real.sqrt_nonneg ε)))

#print axioms holomorphic_multiplier_angle_continuous
#print axioms multiplier_angle_continuous
#print axioms multiplierAction_norm_bound
#print axioms multiplierAction_angle_continuous
#print axioms exponentialOutput_continuous
#print axioms exponentialOutput_norm_bound
#print axioms secondOutput_continuous
#print axioms secondOutput_norm_bound
end
end UnifiedTheory.Audit.KFCausalSingleGaussianMixedSquareContinuity
