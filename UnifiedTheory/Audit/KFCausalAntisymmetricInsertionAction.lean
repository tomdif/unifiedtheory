/- Bounded real-line antisymmetric momentum insertions on the actual
mixed representative, with strong angle continuity for arbitrary L2 inputs. -/
import UnifiedTheory.Audit.KFCausalAntisymmetricInsertionMultiplier
import UnifiedTheory.Audit.KFCausalOuterMatterHalfField
import UnifiedTheory.Audit.KFCausalDominatedL2Continuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalAntisymmetricInsertionAction
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanConfiguration (Space FrequencyHilbert)
open KFCausalEuclideanClockSplit (TailSpace tail)
open KFCausalEuclideanProductCoordinates (Joint split)
open KFCausalPairedModeCoordinates (modeIsometry)
open KFCausalClockFloorMixedRadial (clockMixed)
open KFCausalClockFloorDefectCoordinates (straightening)
open KFCausalMixedStripExponentialGraph (unitary)
open KFCausalStripFamilyExponentialGraph (symbol)
open KFCausalMixedStripTailAttachment (family tailPoint normalize_tail family_horizontal_continuous)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)

variable (ε h a W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
  (k n : ℕ) (i : Fin 2) (hε : 0 < ε) (hh : h ≠ 0) (ha : 0 < a)
  (hw : 1 ≤ w) (hW : w ≤ W) (hb : |h| ≤ ε/10)
local notation "α" => groundWidth h

def bound : ℝ := KFCausalAntisymmetricInsertionMultiplier.bound ε h a α W w C p b P k n i

def multiplier (θ : ℝ) : ℂ → TailSpace → ℂ :=
  family (KFCausalAntisymmetricInsertionMultiplier.multiplier ε h a α W w θ C p b P k n i)

private theorem multiplier_tail (θ : ℝ) (q : ℂ) (x : Space) :
    KFCausalAntisymmetricInsertionMultiplier.multiplier ε h a α W w θ C p b P k n i q
      (tailPoint (tail x)) =
    KFCausalAntisymmetricInsertionMultiplier.multiplier ε h a α W w θ C p b P k n i q
      (modeIsometry x) := by
  simp only [KFCausalAntisymmetricInsertionMultiplier.multiplier,
    KFCausalAntisymmetricInsertionCoordinate.coefficient_tail]
  simp only [KFCausalSourcedWidthMatterMultiplier.multiplier,KFCausalMatterInsertionCoordinate.coefficient,
    KFCausalPointFieldInsertionCoordinate.neutralCoefficient,KFCausalSymmetricInsertionCoordinate.coefficient,
    KFCausalWidthGaussianNeutralMultiplier.multiplier,KFCausalWidthGaussianNeutralMultiplier.neutral,
    KFCausalWidthGaussianHolomorphicQuotient.multiplier,KFCausalWidthGaussianHolomorphicQuotient.targetVector,
    KFCausalWidthGaussianHolomorphicQuotient.baselineVector,normalize_tail]

include hε hb in
theorem horizontal_continuous (θ : ℝ) :
    ∀ y, |y| ≤ |h| → Continuous (fun z : ℝ × TailSpace =>
      multiplier ε h a W w C p b P k n i θ ((z.1:ℂ)+(y:ℂ)*Complex.I) z.2) :=
  family_horizontal_continuous _ _
    (KFCausalAntisymmetricInsertionMultiplier.multiplier_horizontal_continuous
      ε h a α W w θ C p b P k n i hε hb)

include hε hh ha hw hW hb in
private theorem multiplier_bound (θ : ℝ) :
    ∀ q, |q.im| ≤ |h| → ∀ z,
      ‖multiplier ε h a W w C p b P k n i θ q z‖ ≤ bound ε h a W w C p b P k n i := by
  intro q hq z
  exact KFCausalAntisymmetricInsertionMultiplier.multiplier_bound
    ε h a α W w θ C p b P k n i hε hb ha.le (groundWidth_positive h hh) hw hW q hq (tailPoint z)

def action (θ y : ℝ) (hy : |y| ≤ |h|) : Hilbert →L[ℂ] Hilbert :=
  KFCausalMixedStripExponentialGraph.action ε hε
    (multiplier ε h a W w C p b P k n i θ) |h| (bound ε h a W w C p b P k n i)
    (horizontal_continuous ε h a W w C p b P k n i hε hb θ)
    (KFCausalAntisymmetricInsertionMultiplier.bound_nonnegative ε h a α W w C p b P k n i
      hε (groundWidth_positive h hh) hw hW)
    (multiplier_bound ε h a W w C p b P k n i hε hh ha hw hW hb θ) y hy

theorem action_clockMixed (θ y : ℝ) (hy : |y| ≤ |h|) (f : Hilbert) :
    clockMixed ε hε (action ε h a W w C p b P k n i hε hh ha hw hW hb θ y hy f) =ᵐ[volume]
      fun x => KFCausalAntisymmetricInsertionMultiplier.multiplier ε h a α W w θ C p b P k n i
        ((x.2 0:ℂ)+(y:ℂ)*Complex.I) ((split 2 4).symm x)*(clockMixed ε hε f) x :=
  KFCausalMixedStripActionRepresentative.action_clockMixed ε hε _ _ _ _ _ _
    (multiplier_tail ε h a W w C p b P k n i θ) y hy f

omit n in
theorem action_zero_power (θ y : ℝ) (hy : |y| ≤ |h|) (f : Hilbert) :
    action ε h a W w C p b P k 0 i hε hh ha hw hW hb θ y hy f =
      KFCausalOuterMatterHalfField.multiplierAction ε h a W w C p b P k 0
        hε hh ha hw hW hb θ y hy f := by
  apply (clockMixed ε hε).injective
  apply Lp.ext
  filter_upwards [action_clockMixed ε h a W w C p b P k 0 i hε hh ha hw hW hb θ y hy f,
    KFCausalOuterMatterHalfField.multiplierAction_clockMixed ε h a W w C p b P k 0
      hε hh ha hw hW hb θ y hy f] with x hn ho
  rw [hn,ho]
  simp only [KFCausalAntisymmetricInsertionMultiplier.multiplier,
    KFCausalOuterMatterMultiplier.multiplier,pow_zero,one_mul]

theorem multiplier_angle_continuous (q : ℂ) (z : TailSpace) :
    Continuous (fun θ => multiplier ε h a W w C p b P k n i θ q z) :=
  KFCausalAntisymmetricInsertionMultiplier.multiplier_angle_continuous
    ε h a α W w C p b P k n i q (tailPoint z)

include hε hh ha hw hW hb in
private theorem symbol_bound (θ y : ℝ) (hy : |y| ≤ |h|) (x : Space) :
    ‖symbol (multiplier ε h a W w C p b P k n i θ) y x‖ ≤ bound ε h a W w C p b P k n i := by
  apply KFCausalAntisymmetricInsertionMultiplier.multiplier_bound ε h a α W w θ C p b P k n i
    hε hb ha.le (groundWidth_positive h hh) hw hW
  simpa only [Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,zero_add] using hy

theorem action_norm_bound (θ y : ℝ) (hy : |y| ≤ |h|) (f : Hilbert) :
    ‖action ε h a W w C p b P k n i hε hh ha hw hW hb θ y hy f‖ ≤
      bound ε h a W w C p b P k n i*‖f‖ := by
  unfold action
  exact KFCausalMixedStripExponentialGraph.action_norm _ _ _ _ _ _ _ _ _ _ _
    (symbol_bound ε h a W w C p b P k n i hε hh ha hw hW hb θ y hy) f

theorem action_continuous (y : ℝ) (hy : |y| ≤ |h|) (f : Hilbert) :
    Continuous (fun θ => action ε h a W w C p b P k n i hε hh ha hw hW hb θ y hy f) := by
  let g : FrequencyHilbert := straightening ε hε (unitary ε hε f)
  let T : ℝ → FrequencyHilbert := fun θ => straightening ε hε
    (unitary ε hε (action ε h a W w C p b P k n i hε hh ha hw hW hb θ y hy f))
  let F : ℝ → Space → ℂ := fun θ x => symbol (multiplier ε h a W w C p b P k n i θ) y x*g x
  have hT (θ : ℝ) : T θ =ᵐ[volume] F θ :=
    KFCausalMixedStripExponentialGraph.action_coe _ _ _ _ _ _ _ _ _ _ _
  have hF (θ : ℝ) : MemLp (F θ) 2 volume := (Lp.memLp (T θ)).ae_eq (hT θ)
  have he : (fun θ => (hF θ).toLp (F θ)) = T := by
    funext θ
    exact Lp.ext ((hF θ).coeFn_toLp.trans (hT θ).symm)
  have hc : Continuous T := by
    have hM : 0 ≤ bound ε h a W w C p b P k n i :=
      KFCausalAntisymmetricInsertionMultiplier.bound_nonnegative ε h a α W w C p b P k n i
        hε (groundWidth_positive h hh) hw hW
    rw [← he]
    apply KFCausalDominatedL2Continuity.continuous_toLp F hF
      (fun x => (bound ε h a W w C p b P k n i:ℂ)*g x) ((Lp.memLp g).const_mul _)
    · intro θ
      filter_upwards [] with x
      dsimp only [F]
      rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hM]
      exact mul_le_mul_of_nonneg_right
        (symbol_bound ε h a W w C p b P k n i hε hh ha hw hW hb θ y hy x) (norm_nonneg _)
    · filter_upwards [] with x
      exact (multiplier_angle_continuous ε h a W w C p b P k n i _ _).mul continuous_const
  have hbck := (unitary ε hε).symm.continuous.comp ((straightening ε hε).symm.continuous.comp hc)
  simpa only [T,Function.comp_def,LinearIsometryEquiv.symm_apply_apply] using hbck

#print axioms horizontal_continuous
#print axioms action_clockMixed
#print axioms action_zero_power
#print axioms multiplier_angle_continuous
#print axioms action_norm_bound
#print axioms action_continuous
end
end UnifiedTheory.Audit.KFCausalAntisymmetricInsertionAction
