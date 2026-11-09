/- Bounded real-line derivative multipliers on the actual mixed Hilbert
coordinates, with strongly continuous angle dependence and exact full
numerator representatives on the established broad Gaussian baseline. -/
import UnifiedTheory.Audit.KFCausalSymmetricPhysicalJetMultiplier
import UnifiedTheory.Audit.KFCausalSymmetricPhysicalJetRegularity
import UnifiedTheory.Audit.KFCausalBoundedLpMultiplier
import UnifiedTheory.Audit.KFCausalDominatedL2Continuity
import UnifiedTheory.Audit.KFCausalOuterMatterHalfField
import UnifiedTheory.Audit.KFCausalSourcedWidthMatterSquare

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalSymmetricJetAction
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Block Joint ProductHilbert split)
open KFCausalClockFloorMixedRadial (clockMixed)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive groundWidth_matching)
open KFCausalNormalizedChargeFlow (momentumScale)
open KFCausalSourcedWidthMatterSquare (baseline)

private theorem multiplier_strong_continuous
    (m : ℝ → Block 2 × Block 4 → ℂ) (hm : ∀ θ, Measurable (m θ))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ θ x, ‖m θ x‖ ≤ M)
    (hc : ∀ x, Continuous (fun θ => m θ x)) (g : ProductHilbert 2 4) :
    Continuous (fun θ => KFCausalBoundedLpMultiplier.operator (m θ) (hm θ) M hM (hb θ) g) := by
  let T : ℝ → ProductHilbert 2 4 := fun θ =>
    KFCausalBoundedLpMultiplier.operator (m θ) (hm θ) M hM (hb θ) g
  let F : ℝ → Block 2 × Block 4 → ℂ := fun θ x => m θ x*g x
  have hT (θ : ℝ) : T θ =ᵐ[volume] F θ :=
    KFCausalBoundedLpMultiplier.operator_coe (m θ) (hm θ) M hM (hb θ) g
  have hF (θ : ℝ) : MemLp (F θ) 2 := (Lp.memLp (T θ)).ae_eq (hT θ)
  have he : (fun θ => (hF θ).toLp (F θ))=T := by
    funext θ
    exact Lp.ext ((hF θ).coeFn_toLp.trans (hT θ).symm)
  change Continuous T
  rw [← he]
  apply KFCausalDominatedL2Continuity.continuous_toLp F hF
    (fun x => (M:ℂ)*g x) ((Lp.memLp g).const_mul _)
  · intro θ
    filter_upwards [] with x
    dsimp only [F]
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hM]
    exact mul_le_mul_of_nonneg_right (hb θ x) (norm_nonneg _)
  · filter_upwards [] with x
    exact (hc x).mul continuous_const

variable (ε h a W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
  (k : ℕ) (i : Fin 2) (order : Fin 3) (hε : 0 < ε) (hh : h ≠ 0) (ha : 0 < a)
  (hw : 1 ≤ w) (hW : w ≤ W) (hb : |h| ≤ ε/10)
local notation "α" => groundWidth h
local notation "c" => momentumScale h
local notation "hα" => groundWidth_positive h hh

def bound : ℝ :=
  KFCausalSymmetricPhysicalJetMultiplier.bound ε h a α W w C p b (Polynomial.X^k) P i order

def symbol (θ : ℝ) (x : Block 2 × Block 4) : ℂ :=
  KFCausalSymmetricPhysicalJets.multiplier ε h a α W w c θ C p b (Polynomial.X^k) P i order
    (x.2 0:ℂ) ((split 2 4).symm x)

include hε hb in
private theorem symbol_measurable (θ : ℝ) : Measurable (symbol ε h a W w C p b P k i order θ) := by
  let F : ℝ × Joint 2 4 → ℂ := fun v => KFCausalSymmetricPhysicalJets.multiplier
    ε h a α W w c θ C p b (Polynomial.X^k) P i order (v.1:ℂ) v.2
  have hm : Measurable F := (KFCausalSymmetricPhysicalJetRegularity.multiplier_real_continuous
    ε h a α W w c θ C p b (Polynomial.X^k) P i order hε hb).measurable
  have hg : Measurable (fun x : Block 2 × Block 4 => (x.2 0,(split 2 4).symm x)) :=
    ((PiLp.continuous_apply 2 _ (0:Fin 4)).comp continuous_snd).measurable.prodMk
      (split 2 4).symm.measurable
  change Measurable (F ∘ fun x : Block 2 × Block 4 => (x.2 0,(split 2 4).symm x))
  exact hm.comp hg


include hε hh ha hw hW hb in
private theorem bound_nonnegative : 0 ≤ bound ε h a W w C p b P k i order :=
  KFCausalSymmetricPhysicalJetMultiplier.bound_nonnegative ε h a α W w C p b
    (Polynomial.X^k) P i order hε hb ha.le hα hw hW

include hε hh ha hw hW hb in
private theorem symbol_bound (θ : ℝ) (x : Block 2 × Block 4) :
    ‖symbol ε h a W w C p b P k i order θ x‖ ≤ bound ε h a W w C p b P k i order :=
  KFCausalSymmetricPhysicalJetMultiplier.multiplier_bound ε h a α W w c θ C p b
    (Polynomial.X^k) P i order hε hb ha.le hα hw hW _ (by simp) _


def action (θ : ℝ) : Hilbert →L[ℂ] Hilbert :=
  ((clockMixed ε hε).symm : ProductHilbert 2 4 →L[ℂ] Hilbert) ∘L
    (KFCausalBoundedLpMultiplier.operator (symbol ε h a W w C p b P k i order θ)
      (symbol_measurable ε h a W w C p b P k i order hε hb θ)
      (bound ε h a W w C p b P k i order)
      (bound_nonnegative ε h a W w C p b P k i order hε hh ha hw hW hb)
      (symbol_bound ε h a W w C p b P k i order hε hh ha hw hW hb θ)) ∘L
        (clockMixed ε hε : Hilbert →L[ℂ] ProductHilbert 2 4)


theorem action_clockMixed (θ : ℝ) (f : Hilbert) :
    clockMixed ε hε (action ε h a W w C p b P k i order hε hh ha hw hW hb θ f) =ᵐ[volume]
      fun x => symbol ε h a W w C p b P k i order θ x*(clockMixed ε hε f) x := by
  simp only [action,ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_coe'',
    LinearIsometryEquiv.apply_symm_apply]
  exact KFCausalBoundedLpMultiplier.operator_coe _ _ _ _ _ _


theorem action_norm_bound (θ : ℝ) (f : Hilbert) :
    ‖action ε h a W w C p b P k i order hε hh ha hw hW hb θ f‖ ≤
      bound ε h a W w C p b P k i order*‖f‖ := by
  simp only [action,ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_coe'',
    LinearIsometryEquiv.norm_map]
  exact (KFCausalBoundedLpMultiplier.operator_norm _ _ _ _ _ _).trans_eq
    (congrArg (fun r => bound ε h a W w C p b P k i order*r) ((clockMixed ε hε).norm_map f))


theorem action_continuous (f : Hilbert) :
    Continuous (fun θ => action ε h a W w C p b P k i order hε hh ha hw hW hb θ f) := by
  have hm := multiplier_strong_continuous
    (symbol ε h a W w C p b P k i order)
    (symbol_measurable ε h a W w C p b P k i order hε hb)
    (bound ε h a W w C p b P k i order)
    (bound_nonnegative ε h a W w C p b P k i order hε hh ha hw hW hb)
    (symbol_bound ε h a W w C p b P k i order hε hh ha hw hW hb)
    (fun x => KFCausalSymmetricPhysicalJetRegularity.multiplier_angle_continuous
      ε h a α W w c C p b (Polynomial.X^k) P i order (x.2 0:ℂ) ((split 2 4).symm x))
    (clockMixed ε hε f)
  simpa only [action,ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_coe'',Function.comp_apply] using
    (clockMixed ε hε).symm.continuous.comp hm

omit order in
theorem action_zero_order (θ : ℝ) (f : Hilbert) :
    action ε h a W w C p b P k i 0 hε hh ha hw hW hb θ f=
      KFCausalOuterMatterHalfField.multiplierAction ε h a W w C p b P k 0
        hε hh ha hw hW hb θ 0 (by simp) f := by
  apply (clockMixed ε hε).injective
  apply Lp.ext
  filter_upwards [action_clockMixed ε h a W w C p b P k i 0 hε hh ha hw hW hb θ f,
    KFCausalOuterMatterHalfField.multiplierAction_clockMixed ε h a W w C p b P k 0
      hε hh ha hw hW hb θ 0 (by simp) f] with x hn ho
  rw [hn,ho]
  simp only [symbol,KFCausalSymmetricPhysicalJets.multiplier_zero_order,
    KFCausalOuterMatterMultiplier.multiplier,pow_zero,one_mul,Complex.ofReal_zero,zero_mul,add_zero]

def output (θ : ℝ) : Hilbert := action ε h a W w C p b P k i order hε hh ha hw hW hb θ
  (inverseL ε hε (baseline ε h a W w hε hh ha hw hW))

theorem output_clockMixed (θ : ℝ) :
    clockMixed ε hε (output ε h a W w C p b P k i order hε hh ha hw hW hb θ) =ᵐ[volume]
      fun x => KFCausalSymmetricPhysicalJets.numerator ε h a α w c θ C p b (Polynomial.X^k) P i order
        (x.2 0:ℂ) ((split 2 4).symm x) := by
  have hw₀ : 0 < w := zero_lt_one.trans_le hw
  have hW₀ : 0 < W := hw₀.trans_le hW
  filter_upwards [action_clockMixed ε h a W w C p b P k i order hε hh ha hw hW hb θ
      (inverseL ε hε (baseline ε h a W w hε hh ha hw hW)),
    KFCausalBroadWidthHolomorphicBaseline.baseline_second_input_coe
      ε a α W w c hε ha hα hw₀ hW₀ (groundWidth_matching h hh)] with x hx hg
  change clockMixed ε hε (output ε h a W w C p b P k i order hε hh ha hw hW hb θ) x=_ at hx
  rw [hx]
  change symbol ε h a W w C p b P k i order θ x*
    clockMixed ε hε (KFCausalClockFloorBoundedInverse.inverseL ε hε
      (KFCausalBroadPairedGaussian.state ε (a/2) α (1/(4*W)) hε _ hα _)) x=_
  rw [hg]
  exact KFCausalSymmetricPhysicalJets.multiplier_mul_baseline ε h a α W w c θ C p b
    (Polynomial.X^k) P i order _ _ hW₀.ne'

theorem output_continuous :
    Continuous (output ε h a W w C p b P k i order hε hh ha hw hW hb) :=
  action_continuous ε h a W w C p b P k i order hε hh ha hw hW hb _

#print axioms action_clockMixed
#print axioms action_norm_bound
#print axioms action_continuous
#print axioms action_zero_order
#print axioms output_clockMixed
#print axioms output_continuous
end
end UnifiedTheory.Audit.KFCausalSymmetricJetAction
