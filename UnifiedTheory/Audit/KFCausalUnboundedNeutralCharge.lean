/- Maximal measurable neutral-coordinate multiplication relations are
preserved by charge rotations and zero-charge projection. Unbounded
weights are reduced to two contractive multipliers using a nonzero
reciprocal; no boundedness of the original weight is assumed. -/
import UnifiedTheory.Audit.KFCausalNeutralMultiplierCharge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalUnboundedNeutralCharge
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalNeutralMultiplierCharge
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalStandingChargeOperator (zeroProjection)

def reciprocal (w : ℝ → ℂ) (s : ℝ) : ℂ := ((1+‖w s‖:ℝ):ℂ)⁻¹
def normalized (w : ℝ → ℂ) (s : ℝ) : ℂ := reciprocal w s*w s

theorem reciprocal_measurable (w : ℝ → ℂ) (hw : Measurable w) :
    Measurable (reciprocal w) := by
  unfold reciprocal
  exact (Complex.measurable_ofReal.comp (measurable_const.add hw.norm)).inv

theorem normalized_measurable (w : ℝ → ℂ) (hw : Measurable w) :
    Measurable (normalized w) := (reciprocal_measurable w hw).mul hw

theorem reciprocal_ne_zero (w : ℝ → ℂ) (s : ℝ) : reciprocal w s ≠ 0 := by
  apply inv_ne_zero
  exact Complex.ofReal_ne_zero.mpr (by positivity)

theorem reciprocal_bound (w : ℝ → ℂ) (s : ℝ) : ‖reciprocal w s‖ ≤ 1 := by
  rw [reciprocal,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity)]
  exact inv_le_one_of_one_le₀ (by linarith [norm_nonneg (w s)])

theorem normalized_bound (w : ℝ → ℂ) (s : ℝ) : ‖normalized w s‖ ≤ 1 := by
  rw [normalized,norm_mul,reciprocal,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (by positivity),mul_comm,← div_eq_mul_inv]
  exact (div_le_one (by positivity)).mpr (by linarith [norm_nonneg (w s)])

def relation (w : ℝ → ℂ) (f g : Hilbert) : Prop :=
  g =ᵐ[volume] fun x : Configuration => w (x.2 4)*f x

theorem relation_iff_bounded (w : ℝ → ℂ) (hw : Measurable w) (f g : Hilbert) :
    relation w f g ↔
      multiplier (reciprocal w) (reciprocal_measurable w hw) (reciprocal_bound w) g =
        multiplier (normalized w) (normalized_measurable w hw) (normalized_bound w) f := by
  constructor
  · intro hg
    apply Lp.ext
    filter_upwards [hg,
      multiplier_coe (reciprocal w) (reciprocal_measurable w hw) (reciprocal_bound w) g,
      multiplier_coe (normalized w) (normalized_measurable w hw) (normalized_bound w) f]
      with x hx hu hv
    rw [hu,hv,hx]
    exact (mul_assoc _ _ _).symm
  · intro he
    filter_upwards [
      multiplier_coe (reciprocal w) (reciprocal_measurable w hw) (reciprocal_bound w) g,
      multiplier_coe (normalized w) (normalized_measurable w hw) (normalized_bound w) f]
      with x hu hv
    have hx := congrArg (fun u : Hilbert => u x) he
    dsimp only at hx
    rw [hu,hv] at hx
    exact mul_left_cancel₀ (reciprocal_ne_zero w _) (hx.trans (mul_assoc _ _ _))

theorem relation_map (w : ℝ → ℂ) (hw : Measurable w) (L : Hilbert →L[ℂ] Hilbert)
    (hc : ∀ (v : ℝ → ℂ) (hv : Measurable v) (hb : ∀ s, ‖v s‖ ≤ 1) (f : Hilbert),
      multiplier v hv hb (L f) = L (multiplier v hv hb f))
    (f g : Hilbert) (hg : relation w f g) : relation w (L f) (L g) := by
  apply (relation_iff_bounded w hw _ _).mpr
  rw [hc,hc,(relation_iff_bounded w hw f g).mp hg]

theorem relation_action (w : ℝ → ℂ) (hw : Measurable w)
    (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (f g : Hilbert) (hg : relation w f g) :
    relation w (action h hh θ f) (action h hh θ g) :=
  relation_map w hw (action h hh θ) (fun v hv hb u => multiplier_action v hv hb h hh θ u) f g hg

theorem relation_projection (w : ℝ → ℂ) (hw : Measurable w)
    (h : ℝ) (hh : h ≠ 0) (f g : Hilbert) (hg : relation w f g) :
    relation w (zeroProjection h hh f) (zeroProjection h hh g) :=
  relation_map w hw (zeroProjection h hh) (fun v hv hb u => multiplier_projection v hv hb h hh u) f g hg

theorem domain_action (w : ℝ → ℂ) (hw : Measurable w)
    (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (f : Hilbert)
    (hf : MemLp (fun x : Configuration => w (x.2 4)*f x) 2 volume) :
    MemLp (fun x : Configuration => w (x.2 4)*action h hh θ f x) 2 volume := by
  have hg := relation_action w hw h hh θ f (hf.toLp _) hf.coeFn_toLp
  exact (Lp.memLp (action h hh θ (hf.toLp _))).ae_eq hg

theorem domain_projection (w : ℝ → ℂ) (hw : Measurable w)
    (h : ℝ) (hh : h ≠ 0) (f : Hilbert)
    (hf : MemLp (fun x : Configuration => w (x.2 4)*f x) 2 volume) :
    MemLp (fun x : Configuration => w (x.2 4)*zeroProjection h hh f x) 2 volume := by
  have hg := relation_projection w hw h hh f (hf.toLp _) hf.coeFn_toLp
  exact (Lp.memLp (zeroProjection h hh (hf.toLp _))).ae_eq hg

#print axioms reciprocal_measurable
#print axioms normalized_measurable
#print axioms reciprocal_ne_zero
#print axioms reciprocal_bound
#print axioms normalized_bound
#print axioms relation_iff_bounded
#print axioms relation_map
#print axioms relation_action
#print axioms relation_projection
#print axioms domain_action
#print axioms domain_projection
end
end UnifiedTheory.Audit.KFCausalUnboundedNeutralCharge
