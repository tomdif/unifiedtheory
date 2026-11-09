/- Bounded real clock weights of the original strip actions. Factoring
the clock Gaussian makes the extra action independent of the charge angle. -/
import UnifiedTheory.Audit.KFCausalOuterMatterClockWeights
import UnifiedTheory.Audit.KFCausalOuterMatterActionContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalClockWeightedMatterAction
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint split)
open KFCausalEuclideanClockSplit (TailSpace)
open KFCausalClockFloorMixedRadial (clockMixed)
open KFCausalMixedStripTailAttachment (family)
open KFCausalOuterMatterClockDecay (splitFactor)
open KFCausalOuterMatterClockWeights (clockWeight scalarCap)
open KFCausalChargeGaussianGeometry (groundWidth)
open KFCausalNormalizedChargeFlow (momentumScale)

def factorSymbol (ε h a : ℝ) (n : ℕ) (hε : 0 < ε) (q : ℂ) (_x : Joint 2 4) : ℂ :=
  (clockWeight ε hε n q.re:ℂ)*splitFactor a h q

def factorCap (ε h a : ℝ) (n : ℕ) : ℝ := scalarCap ε a n*Real.exp (7*a*h^2/4)

private theorem factor_continuous (ε h a : ℝ) (n : ℕ) (hε : 0 < ε) :
    ∀ y, |y| ≤ |h| → Continuous (fun z : ℝ × TailSpace =>
      family (factorSymbol ε h a n hε) ((z.1:ℂ)+(y:ℂ)*Complex.I) z.2) := by
  intro y _
  unfold family factorSymbol
  have hq : Continuous (fun z : ℝ × TailSpace => (z.1:ℂ)+(y:ℂ)*Complex.I) := by fun_prop
  exact (Complex.continuous_ofReal.comp
    ((KFCausalOuterMatterClockWeights.clockWeight_continuous ε hε n).comp
      (Complex.continuous_re.comp hq))).mul
        ((KFCausalOuterMatterClockDecay.splitFactor_continuous a h).comp hq)

private theorem factor_cap_nonnegative (ε h a : ℝ) (n : ℕ) (hε : 0 < ε) :
    0 ≤ factorCap ε h a n :=
  mul_nonneg (KFCausalOuterMatterClockWeights.scalarCap_nonnegative ε a n hε) (Real.exp_pos _).le

private theorem factor_bound (ε h a : ℝ) (n : ℕ) (hε : 0 < ε) (ha : 0 < a) :
    ∀ q, |q.im| ≤ |h| → ∀ z,
      ‖family (factorSymbol ε h a n hε) q z‖ ≤ factorCap ε h a n := by
  intro q hq _
  exact KFCausalOuterMatterClockWeights.weighted_splitFactor_bound ε h a n hε ha q hq

def factorAction (ε h a : ℝ) (n : ℕ) (hε : 0 < ε) (ha : 0 < a)
    (y : ℝ) (hy : |y| ≤ |h|) : Hilbert →L[ℂ] Hilbert :=
  KFCausalMixedStripExponentialGraph.action ε hε (family (factorSymbol ε h a n hε)) |h|
    (factorCap ε h a n) (factor_continuous ε h a n hε) (factor_cap_nonnegative ε h a n hε)
    (factor_bound ε h a n hε ha) y hy

theorem factorAction_clockMixed (ε h a : ℝ) (n : ℕ) (hε : 0 < ε) (ha : 0 < a)
    (y : ℝ) (hy : |y| ≤ |h|) (f : Hilbert) :
    clockMixed ε hε (factorAction ε h a n hε ha y hy f) =ᵐ[volume]
      fun x => factorSymbol ε h a n hε ((x.2 0:ℂ)+(y:ℂ)*Complex.I)
        ((split 2 4).symm x)*(clockMixed ε hε f) x :=
  KFCausalMixedStripActionRepresentative.action_clockMixed ε hε _ _ _ _ _ _
    (fun _ _ => rfl) y hy f

theorem factorAction_norm_bound (ε h a : ℝ) (n : ℕ) (hε : 0 < ε) (ha : 0 < a)
    (y : ℝ) (hy : |y| ≤ |h|) (f : Hilbert) :
    ‖factorAction ε h a n hε ha y hy f‖ ≤ factorCap ε h a n*‖f‖ := by
  apply KFCausalMixedStripExponentialGraph.action_norm
  intro x
  apply KFCausalOuterMatterClockWeights.weighted_splitFactor_bound ε h a n hε ha
  simpa only [Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,zero_add] using hy

variable (ε h a W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
  (k m n : ℕ) (hε : 0 < ε) (hh : h ≠ 0) (ha : 0 < a) (hw : 1 ≤ w)
  (hW : w ≤ W) (hb : |h| ≤ ε/10)

def action (θ y : ℝ) (hy : |y| ≤ |h|) : Hilbert →L[ℂ] Hilbert :=
  (factorAction ε h a n hε ha y hy).comp
    (KFCausalOuterMatterHalfField.multiplierAction ε h (a/2) W w C p b P k m
      hε hh (by positivity) hw hW hb θ y hy)

theorem action_clockMixed (θ y : ℝ) (hy : |y| ≤ |h|) (f : Hilbert) :
    clockMixed ε hε (action ε h a W w C p b P k m n hε hh ha hw hW hb θ y hy f) =ᵐ[volume]
      fun x => (clockWeight ε hε n (x.2 0):ℂ)*
        KFCausalOuterMatterMultiplier.multiplier ε h a (groundWidth h) W w (momentumScale h)
          θ C p b P k m ((x.2 0:ℂ)+(y:ℂ)*Complex.I) ((split 2 4).symm x)*
          (clockMixed ε hε f) x := by
  filter_upwards [factorAction_clockMixed ε h a n hε ha y hy
    (KFCausalOuterMatterHalfField.multiplierAction ε h (a/2) W w C p b P k m
      hε hh (by positivity) hw hW hb θ y hy f),
    KFCausalOuterMatterHalfField.multiplierAction_clockMixed ε h (a/2) W w C p b P k m
      hε hh (by positivity) hw hW hb θ y hy f] with x hx hi
  change (clockMixed ε hε (factorAction ε h a n hε ha y hy
    (KFCausalOuterMatterHalfField.multiplierAction ε h (a/2) W w C p b P k m
      hε hh (by positivity) hw hW hb θ y hy f))) x = _
  rw [hx,hi,factorSymbol,KFCausalOuterMatterClockDecay.multiplier_split
    ε h a (groundWidth h) W w (momentumScale h) θ C p b P k m]
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_I_re,Complex.ofReal_im,neg_zero,add_zero]
  ring

theorem action_zero_weight (θ y : ℝ) (hy : |y| ≤ |h|) (f : Hilbert) :
    action ε h a W w C p b P k m 0 hε hh ha hw hW hb θ y hy f =
      KFCausalOuterMatterHalfField.multiplierAction ε h a W w C p b P k m
        hε hh ha hw hW hb θ y hy f := by
  apply (clockMixed ε hε).injective
  apply Lp.ext
  filter_upwards [action_clockMixed ε h a W w C p b P k m 0 hε hh ha hw hW hb θ y hy f,
    KFCausalOuterMatterHalfField.multiplierAction_clockMixed ε h a W w C p b P k m
      hε hh ha hw hW hb θ y hy f] with x hx hi
  simpa only [KFCausalOuterMatterClockWeights.clockWeight_zero,Complex.ofReal_one,one_mul,hi] using hx

theorem action_continuous (y : ℝ) (hy : |y| ≤ |h|) (f : Hilbert) :
    Continuous (fun θ => action ε h a W w C p b P k m n hε hh ha hw hW hb θ y hy f) :=
  (factorAction ε h a n hε ha y hy).continuous.comp
    (KFCausalOuterMatterActionContinuity.action_continuous ε h (a/2) W w C p b P k m
      hε hh (by positivity) hw hW hb y hy f)

theorem action_norm_bound (θ y : ℝ) (hy : |y| ≤ |h|) (f : Hilbert) :
    ‖action ε h a W w C p b P k m n hε hh ha hw hW hb θ y hy f‖ ≤
      factorCap ε h a n * (KFCausalOuterMatterHalfField.bound ε h (a/2) W w C p b P k m * ‖f‖) :=
  (factorAction_norm_bound ε h a n hε ha y hy _).trans
    (mul_le_mul_of_nonneg_left (KFCausalOuterMatterActionContinuity.action_norm_bound
      ε h (a/2) W w C p b P k m hε hh (by positivity) hw hW hb θ y hy f)
      (factor_cap_nonnegative ε h a n hε))

#print axioms factorAction_clockMixed
#print axioms factorAction_norm_bound
#print axioms action_clockMixed
#print axioms action_zero_weight
#print axioms action_continuous
#print axioms action_norm_bound
end
end UnifiedTheory.Audit.KFCausalClockWeightedMatterAction
