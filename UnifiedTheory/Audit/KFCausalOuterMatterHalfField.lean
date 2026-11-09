/- Actual field-power graphs between the explicit half-step outputs.
The underlying strip action is shared with both exponential graph steps. -/
import UnifiedTheory.Audit.KFCausalOuterMatterRegularity
import UnifiedTheory.Audit.KFCausalClockMixedFieldGraph
import UnifiedTheory.Audit.KFCausalMixedStripActionRepresentative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalOuterMatterHalfField
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint Block split)
open KFCausalEuclideanConfiguration (Space)
open KFCausalEuclideanClockSplit (TailSpace tail)
open KFCausalPairedModeCoordinates (modeIsometry scale)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalNormalizedChargeFlow (momentumScale)
open KFCausalClockFloorMixedRadial (clockMixed)
open KFCausalClockFloorMixedChart (mixedMap)
open KFCausalClockFloorExponential (longitudinalExponential)
open KFCausalMixedStripTailAttachment (family tailPoint normalize_tail family_horizontal_continuous)
open KFCausalPhysicalField (physicalField)
open KFCausalTransverseFieldSquare (fieldSquare)
open KFCausalMatterOrderedDomain (pointField)

variable (ε h a W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
  (k m : ℕ) (hε : 0 < ε) (hh : h ≠ 0) (ha : 0 < a) (hw : 1 ≤ w)
  (hW : w ≤ W) (hb : |h| ≤ ε/10)
local notation "α" => groundWidth h
local notation "c" => momentumScale h
local notation "hα" => groundWidth_positive h hh

def bound : ℝ := KFCausalOuterMatterMultiplier.bound ε h a α W w C p b P k m

def multiplier (θ : ℝ) : ℂ → TailSpace → ℂ :=
  family (KFCausalOuterMatterMultiplier.multiplier ε h a α W w c θ C p b P k m)

theorem multiplier_tail (θ : ℝ) (q : ℂ) (x : Space) :
    KFCausalOuterMatterMultiplier.multiplier ε h a α W w c θ C p b P k m q
      (tailPoint (tail x)) =
    KFCausalOuterMatterMultiplier.multiplier ε h a α W w c θ C p b P k m q
      (modeIsometry x) := by
  simp only [KFCausalOuterMatterMultiplier.multiplier,KFCausalOuterMatterMultiplier.outerCoefficient,
    KFCausalSourcedWidthMatterMultiplier.multiplier,KFCausalMatterInsertionCoordinate.coefficient,
    KFCausalPointFieldInsertionCoordinate.coefficient,KFCausalPointFieldInsertionCoordinate.neutralCoefficient,
    KFCausalSymmetricInsertionCoordinate.coefficient,KFCausalWidthGaussianNeutralMultiplier.multiplier,
    KFCausalWidthGaussianNeutralMultiplier.neutral,KFCausalWidthGaussianHolomorphicQuotient.multiplier,
    KFCausalWidthGaussianHolomorphicQuotient.targetVector,
    KFCausalWidthGaussianHolomorphicQuotient.baselineVector,normalize_tail]

include hε hb in
theorem horizontal_continuous (θ : ℝ) :
    ∀ y, |y| ≤ |h| → Continuous (fun z : ℝ × TailSpace =>
      multiplier ε h a W w C p b P k m θ ((z.1:ℂ)+(y:ℂ)*Complex.I) z.2) :=
  family_horizontal_continuous _ _
    (KFCausalOuterMatterMultiplier.multiplier_horizontal_continuous
      ε h a α W w c θ C p b P k m hε hb)

include hε hh ha hw hW hb in
theorem multiplier_bound (θ : ℝ) :
    ∀ q, |q.im| ≤ |h| → ∀ z,
      ‖multiplier ε h a W w C p b P k m θ q z‖ ≤ bound ε h a W w C p b P k m := by
  intro q hq z
  exact KFCausalOuterMatterMultiplier.multiplier_bound
    ε h a α W w c θ C p b P k m hε hb ha.le hα hw hW q hq (tailPoint z)

def multiplierAction (θ y : ℝ) (hy : |y| ≤ |h|) : Hilbert →L[ℂ] Hilbert :=
  KFCausalMixedStripExponentialGraph.action ε hε
    (multiplier ε h a W w C p b P k m θ) |h| (bound ε h a W w C p b P k m)
    (horizontal_continuous ε h a W w C p b P k m hε hb θ)
    (KFCausalOuterMatterMultiplier.bound_nonnegative ε h a α W w C p b P k m hε hα hw hW)
    (multiplier_bound ε h a W w C p b P k m hε hh ha hw hW hb θ) y hy

theorem multiplierAction_clockMixed (θ y : ℝ) (hy : |y| ≤ |h|) (f : Hilbert) :
    clockMixed ε hε (multiplierAction ε h a W w C p b P k m hε hh ha hw hW hb θ y hy f) =ᵐ[volume]
      fun x => KFCausalOuterMatterMultiplier.multiplier ε h a α W w c θ C p b P k m
        ((x.2 0:ℂ)+(y:ℂ)*Complex.I) ((split 2 4).symm x)*(clockMixed ε hε f) x :=
  KFCausalMixedStripActionRepresentative.action_clockMixed ε hε _ _ _ _ _ _
    (multiplier_tail ε h a W w C p b P k m θ) y hy f

theorem multiplierAction_graph (θ ℓ : ℝ) (hs : |-ℓ/2| ≤ |h|) (f g : Hilbert)
    (hfg : (f,g) ∈ (longitudinalExponential ε hε ℓ (1/2)).graph) :
    (multiplierAction ε h a W w C p b P k m hε hh ha hw hW hb θ 0 (by simp) f,
      multiplierAction ε h a W w C p b P k m hε hh ha hw hW hb θ (-ℓ/2) hs g) ∈
      (longitudinalExponential ε hε ℓ (1/2)).graph := by
  apply KFCausalMixedStripExponentialGraph.graph_action ε hε _ _ _ _ _ _ _ ℓ (by simp) hs f g hfg
  intro z q hq
  exact KFCausalOuterMatterMultiplier.multiplier_analytic
    ε h a α W w c θ C p b P k m hε hb q hq (tailPoint z)

theorem half_line_bound : |-h/2| ≤ |h| := by
  rw [abs_div,abs_neg]
  rw [show |(2:ℝ)|=2 by norm_num]
  linarith [abs_nonneg h]

def halfOutput (θ : ℝ) (f : Hilbert) : Hilbert :=
  multiplierAction ε h a W w C p b P k m hε hh ha hw hW hb θ (-h/2) (half_line_bound h) f

theorem outer_half_line (q : ℝ) (x : Joint 2 4) :
    KFCausalOuterMatterMultiplier.outerCoefficient ε h α w c
      ((q:ℂ)+(-h/2:ℝ)*Complex.I) x =
      KFCausalPointFieldInsertionCoordinate.coefficient ε h α w c 0 (q:ℂ) x := by
  unfold KFCausalOuterMatterMultiplier.outerCoefficient
  congr 1
  unfold KFCausalTwoShearClockQuotient.shift
  push_cast
  ring

theorem halfOutput_clockMixed (θ : ℝ) (f : Hilbert) :
    clockMixed ε hε (halfOutput ε h a W w C p b P k m hε hh ha hw hW hb θ f) =ᵐ[volume]
      fun x =>
        KFCausalPointFieldInsertionCoordinate.coefficient ε h α w c 0 (x.2 0:ℂ)
          ((split 2 4).symm x)^m*
        (KFCausalSourcedWidthMatterMultiplier.multiplier ε h a α W w c θ C p b P k
          ((x.2 0:ℂ)+(-h/2:ℝ)*Complex.I) ((split 2 4).symm x)*(clockMixed ε hε f) x) := by
  filter_upwards [multiplierAction_clockMixed ε h a W w C p b P k m hε hh ha hw hW hb
    θ (-h/2) (half_line_bound h) f] with x hx
  rw [halfOutput,hx,KFCausalOuterMatterMultiplier.multiplier,outer_half_line]
  exact mul_assoc _ _ _

include hε hh hw in
theorem coefficient_real (x : Block 2 × Block 4) :
    KFCausalPointFieldInsertionCoordinate.coefficient ε h α w c 0 (x.2 0:ℂ)
      ((split 2 4).symm x) =
    ((2*scale*(mixedMap ε hε x).2 2+(mixedMap ε hε x).2 3:ℝ):ℂ) := by
  have he := KFCausalSourcedWidthPointFieldInsertion.coefficient_real ε hε h α w hh hα
    (zero_lt_one.trans_le hw) 0 x
  simpa only [KFCausalChargeRotatedSecondInput.rotatedPoint,KFCausalNormalizedChargeFlow.flow_zero,
    MeasurableEquiv.apply_symm_apply] using he

theorem pointField_graph (θ : ℝ) (f : Hilbert) :
    (halfOutput ε h a W w C p b P k m hε hh ha hw hW hb θ f,
      halfOutput ε h a W w C p b P k (m+1) hε hh ha hw hW hb θ f) ∈
      (physicalField pointField).graph := by
  apply (KFCausalClockMixedFieldGraph.pointField_graph_iff ε hε _ _).mpr
  filter_upwards [halfOutput_clockMixed ε h a W w C p b P k m hε hh ha hw hW hb θ f,
    halfOutput_clockMixed ε h a W w C p b P k (m+1) hε hh ha hw hW hb θ f] with x hm hn
  rw [hm,hn,← coefficient_real ε h w hε hh hw x,pow_succ]
  ring

theorem fieldSquare_graph (θ : ℝ) (f : Hilbert) :
    (halfOutput ε h a W w C p b P k m hε hh ha hw hW hb θ f,
      halfOutput ε h a W w C p b P k (m+2) hε hh ha hw hW hb θ f) ∈
      (fieldSquare pointField).graph := by
  exact KFCausalClockMixedFieldGraph.fieldSquare_of_two_fields pointField _ _ _
    (pointField_graph ε h a W w C p b P k m hε hh ha hw hW hb θ f)
    (pointField_graph ε h a W w C p b P k (m+1) hε hh ha hw hW hb θ f)

#print axioms multiplier_tail
#print axioms horizontal_continuous
#print axioms multiplier_bound
#print axioms multiplierAction_clockMixed
#print axioms multiplierAction_graph
#print axioms half_line_bound
#print axioms outer_half_line
#print axioms halfOutput_clockMixed
#print axioms coefficient_real
#print axioms pointField_graph
#print axioms fieldSquare_graph
end
end UnifiedTheory.Audit.KFCausalOuterMatterHalfField
