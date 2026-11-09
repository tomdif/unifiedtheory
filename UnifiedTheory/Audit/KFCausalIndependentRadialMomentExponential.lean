/- Actual exponential half and full steps for the bare radial moment
inputs. All multipliers act on an explicit broad Gaussian baseline. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialMomentRegularity
import UnifiedTheory.Audit.KFCausalIndependentRadialBaseline
import UnifiedTheory.Audit.KFCausalMixedStripActionRepresentative
import UnifiedTheory.Audit.KFCausalMatterHalfStepAssembly

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalIndependentRadialMomentExponential
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint split)
open KFCausalEuclideanClockSplit (TailSpace tail)
open KFCausalPairedModeCoordinates (modeIsometry)
open KFCausalClockFloorBoundedInverse (inverseL ordered_graph_iff)
open KFCausalClockFloorExponential (longitudinalExponential)
open KFCausalClockFloorVacuumSquare (square square_graph exponential_rescale)
open KFCausalClockFloorMixedRadial (clockMixed)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive groundWidth_matching)
open KFCausalNormalizedChargeFlow (momentumScale)
open KFCausalMixedStripTailAttachment (family tailPoint family_horizontal_continuous)
open KFCausalIndependentRadialPacketMoments (momentState)
open KFCausalSingleGaussianMixedSquare (original_strip doubled_strip)

variable (ε h a W wL wR : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
  (m n : ℕ) (hε : 0 < ε) (hh : h ≠ 0) (ha : 0 < a) (hL : 1 ≤ wL)
  (hR : 1 ≤ wR) (hW : wL ≤ W) (hb : |h| ≤ ε/10)
local notation "α" => groundWidth h
local notation "c" => momentumScale h
local notation "hα" => groundWidth_positive h hh
local notation "hW₀" => lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hL) hW

def bound (k : ℕ) : ℝ :=
  KFCausalIndependentRadialMomentMultiplier.bound h a α W wL wR C p b P m n k

def multiplier (k : ℕ) : ℂ → TailSpace → ℂ :=
  family (KFCausalIndependentRadialMomentMultiplier.multiplier ε h a α W wL wR c C p b P m n k)

private theorem independent_normalize_tail (α₀ wL wR c₀ : ℝ)
    (x : KFCausalEuclideanConfiguration.Space) :
    KFCausalIndependentRadialNormalization.normalize α₀ wL wR c₀ (tailPoint (tail x))=
      KFCausalIndependentRadialNormalization.normalize α₀ wL wR c₀ (modeIsometry x) := by
  ext i
  fin_cases i <;> rfl

private theorem multiplier_tail (k : ℕ) (q : ℂ) (x : KFCausalEuclideanConfiguration.Space) :
    KFCausalIndependentRadialMomentMultiplier.multiplier ε h a α W wL wR c C p b P m n k q
      (tailPoint (tail x)) =
    KFCausalIndependentRadialMomentMultiplier.multiplier ε h a α W wL wR c C p b P m n k q
      (modeIsometry x) := by
  simp only [KFCausalIndependentRadialMomentMultiplier.multiplier,
    KFCausalIndependentRadialShiftedField.coefficient,KFCausalIndependentRadialShiftedField.point,
    KFCausalIndependentRadialMomentInput.left,KFCausalIndependentRadialMomentInput.right,
    KFCausalIndependentRadialMomentInput.neutral,KFCausalIndependentRadialBareMultiplier.multiplier,
    KFCausalIndependentRadialHolomorphicQuotient.baselineVector,independent_normalize_tail]

include hε hb in
private theorem horizontal_continuous (k : ℕ) :
    ∀ y, |y| ≤ |h| → Continuous (fun z : ℝ × TailSpace =>
      multiplier ε h a W wL wR C p b P m n k ((z.1:ℂ)+(y:ℂ)*Complex.I) z.2) :=
  family_horizontal_continuous _ _
    (KFCausalIndependentRadialMomentMultiplier.multiplier_horizontal_continuous
      ε h a α W wL wR c C p b P m n k hε hb)

include hε hh ha hL hR hW hb in
private theorem multiplier_bound (k : ℕ) :
    ∀ q, |q.im| ≤ |h| → ∀ z,
      ‖multiplier ε h a W wL wR C p b P m n k q z‖ ≤ bound h a W wL wR C p b P m n k := by
  intro q hq z
  exact KFCausalIndependentRadialMomentMultiplier.multiplier_bound
    ε h a α W wL wR c C p b P m n k hε hb ha.le hα hL hR hW q hq (tailPoint z)

def multiplierAction (k : ℕ) (y : ℝ) (hy : |y| ≤ |h|) : Hilbert →L[ℂ] Hilbert :=
  KFCausalMixedStripExponentialGraph.action ε hε
    (multiplier ε h a W wL wR C p b P m n k) |h| (bound h a W wL wR C p b P m n k)
    (horizontal_continuous ε h a W wL wR C p b P m n hε hb k)
    (KFCausalIndependentRadialMomentMultiplier.bound_nonnegative h a α W wL wR C p b P m n k hα hL hR hW)
    (multiplier_bound ε h a W wL wR C p b P m n hε hh ha hL hR hW hb k) y hy

theorem multiplierAction_clockMixed (k : ℕ) (y : ℝ) (hy : |y| ≤ |h|) (f : Hilbert) :
    clockMixed ε hε (multiplierAction ε h a W wL wR C p b P m n hε hh ha hL hR hW hb k y hy f) =ᵐ[volume]
      fun x => KFCausalIndependentRadialMomentMultiplier.multiplier ε h a α W wL wR c C p b P m n k
        ((x.2 0:ℂ)+(y:ℂ)*Complex.I) ((split 2 4).symm x)*(clockMixed ε hε f) x :=
  KFCausalMixedStripActionRepresentative.action_clockMixed ε hε _ _ _ _ _ _
    (multiplier_tail ε h a W wL wR C p b P m n k) y hy f

theorem multiplierAction_graph (k : ℕ) (ℓ : ℝ) (hs : |-ℓ/2| ≤ |h|) (f g : Hilbert)
    (hfg : (f,g) ∈ (longitudinalExponential ε hε ℓ (1/2)).graph) :
    (multiplierAction ε h a W wL wR C p b P m n hε hh ha hL hR hW hb k 0 (by simp) f,
      multiplierAction ε h a W wL wR C p b P m n hε hh ha hL hR hW hb k (-ℓ/2) hs g) ∈
      (longitudinalExponential ε hε ℓ (1/2)).graph := by
  apply KFCausalMixedStripExponentialGraph.graph_action ε hε _ _ _ _ _ _ _ ℓ (by simp) hs f g hfg
  intro z q hq
  exact KFCausalIndependentRadialMomentMultiplier.multiplier_analytic
    ε h a α W wL wR c C p b P m n k hε hb q hq (tailPoint z)

private theorem half_line_bound (h : ℝ) : |-h/2| ≤ |h| := by
  rw [abs_div,abs_neg,show |(2:ℝ)|=2 by norm_num]
  linarith [abs_nonneg h]

include hε hb in
private theorem half_baseline_strip : |h| ≤ 2*Real.pi*ε/3 := by
  have hs := original_strip ε h hε hb
  have hp := mul_pos Real.pi_pos hε
  linarith

def baseline : Hilbert := KFCausalBroadPairedGaussian.state ε (a/2) α (1/(4*W))
  hε (by positivity) hα (by have := hW₀; positivity)

def baselineHalfOutput : Hilbert :=
  KFCausalBroadPairedGaussian.output ε (a/2) α (1/(4*W)) hε (by positivity) hα h
    (half_baseline_strip ε h hε hb)

def baselineOutput : Hilbert :=
  KFCausalBroadPairedGaussian.output ε (a/2) α (1/(4*W)) hε (by positivity) hα (2*h)
    (doubled_strip ε h hε hb)

def halfState (k : ℕ) : Hilbert :=
  multiplierAction ε h a W wL wR C p b P m n hε hh ha hL hR hW hb k (-h/2) (half_line_bound h)
    (baselineHalfOutput ε h a W hε hh ha hb)

def fullState (k : ℕ) : Hilbert :=
  multiplierAction ε h a W wL wR C p b P m n hε hh ha hL hR hW hb k (-h) (by simp)
    (baselineOutput ε h a W hε hh ha hb)

theorem half_graph (k : ℕ) :
    (multiplierAction ε h a W wL wR C p b P m n hε hh ha hL hR hW hb k 0 (by simp)
      (inverseL ε hε (baseline ε h a W wL hε hh ha hL hW)),
      halfState ε h a W wL wR C p b P m n hε hh ha hL hR hW hb k) ∈
      (longitudinalExponential ε hε h (1/2)).graph := by
  apply multiplierAction_graph
  exact (ordered_graph_iff ε hε h _ _).mp
    (KFCausalBroadPairedGaussian.output_graph ε (a/2) α (1/(4*W)) hε
      (by positivity) hα (by have := hW₀; positivity) h (half_baseline_strip ε h hε hb))

theorem full_graph (k : ℕ) :
    (multiplierAction ε h a W wL wR C p b P m n hε hh ha hL hR hW hb k 0 (by simp)
      (inverseL ε hε (baseline ε h a W wL hε hh ha hL hW)),
      fullState ε h a W wL wR C p b P m n hε hh ha hL hR hW hb k) ∈
      (longitudinalExponential ε hε h 1).graph := by
  have hg := multiplierAction_graph ε h a W wL wR C p b P m n hε hh ha hL hR hW hb k (2*h)
    (by rw [show -(2*h)/2=-h by ring,abs_neg]) _ _
    ((ordered_graph_iff ε hε (2*h) _ _).mp
      (KFCausalBroadPairedGaussian.output_graph ε (a/2) α (1/(4*W)) hε
        (by positivity) hα (by have := hW₀; positivity) (2*h) (doubled_strip ε h hε hb)))
  have he := (exponential_rescale ε hε h 2 (1/2) _ _).mp hg
  simpa only [show -(2*h)/2=-h by ring,show (1/2:ℝ)*2=1 by norm_num] using he

theorem second_half_graph (k : ℕ) :
    (halfState ε h a W wL wR C p b P m n hε hh ha hL hR hW hb k,
      fullState ε h a W wL wR C p b P m n hε hh ha hL hR hW hb k) ∈
      (longitudinalExponential ε hε h (1/2)).graph :=
  KFCausalMatterHalfStepAssembly.second_half_graph ε hε h _ _ _
    (half_graph ε h a W wL wR C p b P m n hε hh ha hL hR hW hb k)
    (full_graph ε h a W wL wR C p b P m n hε hh ha hL hR hW hb k)

theorem actual_input :
    multiplierAction ε h a W wL wR C p b P m n hε hh ha hL hR hW hb 0 0 (by simp)
      (inverseL ε hε (baseline ε h a W wL hε hh ha hL hW)) =
      inverseL ε hε (momentState ε a h wL wR C p b P hε ha hh hL hR m n) := by
  apply (clockMixed ε hε).injective
  apply Lp.ext
  filter_upwards [multiplierAction_clockMixed ε h a W wL wR C p b P m n hε hh ha hL hR hW hb
    0 0 (by simp) (inverseL ε hε (baseline ε h a W wL hε hh ha hL hW)),
    KFCausalIndependentRadialBaseline.baseline_second_input_coe ε a α W wL wR c
      hε ha hα (zero_lt_one.trans_le hL) (zero_lt_one.trans_le hR) hW₀ (groundWidth_matching h hh),
    KFCausalIndependentRadialMomentInput.moment_input_coe ε a h wL wR C p b P hε ha hh hL hR m n]
    with x hx hbase hi
  rw [hx,hi,baseline,hbase]
  simp only [Complex.ofReal_zero,zero_mul,add_zero]
  rw [KFCausalIndependentRadialMomentMultiplier.multiplier_mul_baseline
    ε h a α W wL wR c C p b P m n 0 (ne_of_gt hW₀),pow_zero,one_mul]

theorem actual_half_graph :
    (inverseL ε hε (momentState ε a h wL wR C p b P hε ha hh hL hR m n),
      halfState ε h a W wL wR C p b P m n hε hh ha hL hR hW hb 0) ∈
      (longitudinalExponential ε hε h (1/2)).graph := by
  have hg := half_graph ε h a W wL wR C p b P m n hε hh ha hL hR hW hb 0
  rwa [actual_input ε h a W wL wR C p b P m n hε hh ha hL hR hW hb] at hg

theorem actual_full_graph :
    (inverseL ε hε (momentState ε a h wL wR C p b P hε ha hh hL hR m n),
      fullState ε h a W wL wR C p b P m n hε hh ha hL hR hW hb 0) ∈
      (longitudinalExponential ε hε h 1).graph := by
  have hg := full_graph ε h a W wL wR C p b P m n hε hh ha hL hR hW hb 0
  rwa [actual_input ε h a W wL wR C p b P m n hε hh ha hL hR hW hb] at hg

theorem vacuum_graph :
    (momentState ε a h wL wR C p b P hε ha hh hL hR m n,
      inverseL ε hε (fullState ε h a W wL wR C p b P m n hε hh ha hL hR hW hb 0)) ∈
      (square ε hε h).graph :=
  (square_graph ε hε h _ _).mpr
    ⟨_,actual_full_graph ε h a W wL wR C p b P m n hε hh ha hL hR hW hb,rfl⟩

#print axioms multiplierAction_clockMixed
#print axioms multiplierAction_graph
#print axioms half_graph
#print axioms full_graph
#print axioms second_half_graph
#print axioms actual_input
#print axioms actual_half_graph
#print axioms actual_full_graph
#print axioms vacuum_graph
end
end UnifiedTheory.Audit.KFCausalIndependentRadialMomentExponential
