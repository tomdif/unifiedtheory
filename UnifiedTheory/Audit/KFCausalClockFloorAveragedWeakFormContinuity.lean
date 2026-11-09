/- The constructed weak solution is weakly continuous in the reference
form space. Its mass-dual curve is locally Lipschitz and has the weak
derivative dictated by the averaged form Hamiltonian. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakIntegralEquation
import UnifiedTheory.Audit.KFCausalMassGram
import UnifiedTheory.Audit.KFCausalLocalWeakContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity
noncomputable section
open Filter MeasureTheory
open scoped Topology
open UnifiedTheory.Audit.KFCausalBoundedFormCurve
open UnifiedTheory.Audit.KFCausalShiftedForm
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormGeometry
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedSmoothedTrajectory
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormWindowBound
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakPairing
open UnifiedTheory.Audit.KFCausalClockFloorAveragedCountableLimit
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakTrajectory
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakIntegralEquation
open UnifiedTheory.Audit.KFCausalWeakLimitTransport
open UnifiedTheory.Audit.KFCausalMassGram
open UnifiedTheory.Audit.KFCausalLocalWeakContinuity

def massOperator (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum : ℝ) :
    FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0 →L[ℂ] FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0 :=
  gram (E := FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (H := Hilbert) (embedding ε hε hbar hh hbound mass2 quartic vacuum 0)

theorem mass_left_pairing (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum : ℝ)
    (x y : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) :
    inner ℂ (massOperator ε hε hbar hh hbound mass2 quartic vacuum x) y =
      inner ℂ (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 x) (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 y) :=
  gram_left_pairing _ x y

theorem mass_dense (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum : ℝ) :
    DenseRange (massOperator ε hε hbar hh hbound mass2 quartic vacuum) :=
  gram_dense _ (embedding_injective ε hε hbar hh hbound mass2 quartic vacuum 0)

theorem formState_window_bound (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (V : WeakTrajectory ε hε hbar hh hbound mass2 quartic vacuum s w)
    (T t : ℝ) (hT : 0 ≤ T) (ht : |t| ≤ T) :
    ‖V.formState t‖ ≤ windowRadius ε hε hbar hh hbound mass2 quartic vacuum s T w := by
  exact weak_norm_le (H := FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0)
    (fun n => smoothed_window_norm ε hε hbar hh hbound mass2 quartic vacuum (cutoff (V.subsequence n))
      (cutoff_pos (V.subsequence n)) s T t hT ht w) (V.formConvergence t)

theorem formState_weakly_continuous (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (V : WeakTrajectory ε hε hbar hh hbound mass2 quartic vacuum s w) :
    ∀ y, Continuous (fun t => inner ℂ (V.formState t) y) := by
  apply weak_continuous_of_locally_bounded_dense_tests (massOperator ε hε hbar hh hbound mass2 quartic vacuum)
    (mass_dense ε hε hbar hh hbound mass2 quartic vacuum) V.formState (fun T => windowRadius ε hε hbar hh hbound mass2 quartic vacuum s T w)
  · exact formState_window_bound ε hε hbar hh hbound mass2 quartic vacuum s w V
  · intro y
    have he : (fun t => inner ℂ (V.formState t) (massOperator ε hε hbar hh hbound mass2 quartic vacuum y)) =
        (fun t => inner ℂ (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 (V.formState t))
          (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 y)) := by
      funext t
      exact gram_right_pairing _ _ _
    rw [he]
    exact weak_trajectory_form_pairing_continuous ε hε hbar hh hbound mass2 quartic vacuum s w V y

theorem limitSlope_continuous (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (V : WeakTrajectory ε hε hbar hh hbound mass2 quartic vacuum s w)
    (y : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) :
    Continuous (fun t => limitSlope ε hε hbar hh hbound mass2 quartic vacuum s w V t y) := by
  have hf : Continuous (fun t => referenceFormOperator ε hε hbar hh hbound mass2 quartic vacuum t y) :=
    (continuous_iff_continuousAt.mpr (fun t =>
      (referenceForm_derivative ε hε hbar hh hbound mass2 quartic vacuum t).continuousAt)).clm_apply continuous_const
  have hpair := weak_strong_pairing_continuous V.formState
    (fun t => referenceFormOperator ε hε hbar hh hbound mass2 quartic vacuum t y)
    (fun T => windowRadius ε hε hbar hh hbound mass2 quartic vacuum s T w)
    (formState_window_bound ε hε hbar hh hbound mass2 quartic vacuum s w V)
    (formState_weakly_continuous ε hε hbar hh hbound mass2 quartic vacuum s w V) hf
  exact continuous_const.mul hpair

def massState (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (V : WeakTrajectory ε hε hbar hh hbound mass2 quartic vacuum s w)
    (t : ℝ) : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0 := massOperator ε hε hbar hh hbound mass2 quartic vacuum (V.formState t)

def massSlope (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (V : WeakTrajectory ε hε hbar hh hbound mass2 quartic vacuum s w)
    (t : ℝ) : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0 :=
  (-Complex.I*((1/hbar:ℝ):ℂ)) • referenceFormOperator ε hε hbar hh hbound mass2 quartic vacuum t (V.formState t)

theorem massSlope_pairing (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (V : WeakTrajectory ε hε hbar hh hbound mass2 quartic vacuum s w)
    (t : ℝ) (y : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) :
    inner ℂ (massSlope ε hε hbar hh hbound mass2 quartic vacuum s w V t) y = limitSlope ε hε hbar hh hbound mass2 quartic vacuum s w V t y := by
  unfold massSlope limitSlope
  have hs := formOperator_inner_symm (E := FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (H := KFCausalAveragedOutputRescaling.EnergyOutputSpace)
    (staticMap ε hε hbar hh hbound mass2 quartic vacuum) (growingMap ε hε hbar hh hbound mass2 quartic vacuum) t (V.formState t) y
  change inner ℂ (referenceFormOperator ε hε hbar hh hbound mass2 quartic vacuum t (V.formState t)) y =
    inner ℂ (V.formState t) (referenceFormOperator ε hε hbar hh hbound mass2 quartic vacuum t y) at hs
  have hscale := inner_smul_left (𝕜 := ℂ) (E := FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0)
    (referenceFormOperator ε hε hbar hh hbound mass2 quartic vacuum t (V.formState t)) y
    (-Complex.I*((1/hbar:ℝ):ℂ))
  simp only [map_mul,map_neg,Complex.conj_I,neg_neg,Complex.conj_ofReal] at hscale
  exact hscale.trans (congrArg (fun z : ℂ => (Complex.I*((1/hbar:ℝ):ℂ))*z) hs)

theorem mass_pairing_derivative (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (V : WeakTrajectory ε hε hbar hh hbound mass2 quartic vacuum s w)
    (t : ℝ) (y : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) :
    HasDerivAt (fun z => inner ℂ (massState ε hε hbar hh hbound mass2 quartic vacuum s w V z) y)
      (inner ℂ (massSlope ε hε hbar hh hbound mass2 quartic vacuum s w V t) y) t := by
  have hc := limitSlope_continuous ε hε hbar hh hbound mass2 quartic vacuum s w V y
  have hd := intervalIntegral.integral_hasDerivAt_right
    (limitSlope_intervalIntegrable ε hε hbar hh hbound mass2 quartic vacuum s w V s t y)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  have he : (fun z => inner ℂ (massState ε hε hbar hh hbound mass2 quartic vacuum s w V z) y) =
      (fun z => (∫ r in s..z, limitSlope ε hε hbar hh hbound mass2 quartic vacuum s w V r y)+
        inner ℂ (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 w) (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 y)) := by
    funext z
    have hp := mass_left_pairing ε hε hbar hh hbound mass2 quartic vacuum (V.formState z) y
    have hi := weak_trajectory_integral_initial ε hε hbar hh hbound mass2 quartic vacuum s w V z y
    have hi' := (congrArg (fun u : ℂ => u + inner ℂ
      (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 w)
      (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 y)) hi).trans (sub_add_cancel _ _)
    exact hp.trans hi'.symm
  exact (congrArg₂ (fun (f : ℝ → ℂ) (d : ℂ) => HasDerivAt f d t) he
    (massSlope_pairing ε hε hbar hh hbound mass2 quartic vacuum s w V t y)).mpr (hd.add_const _)

def massLipschitzBound (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s T : ℝ)
    (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) : ℝ :=
  |1/hbar| * windowRadius ε hε hbar hh hbound mass2 quartic vacuum s T w * (1+Real.exp (2*T))

theorem massLipschitzBound_nonneg (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s T : ℝ)
    (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) : 0 ≤ massLipschitzBound ε hε hbar hh hbound mass2 quartic vacuum s T w := by
  unfold massLipschitzBound windowRadius
  positivity

theorem massState_window_lipschitz (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (V : WeakTrajectory ε hε hbar hh hbound mass2 quartic vacuum s w)
    (T x y : ℝ) (hT : 0 ≤ T) (hx : |x| ≤ T) (hy : |y| ≤ T) :
    ‖massState ε hε hbar hh hbound mass2 quartic vacuum s w V y-massState ε hε hbar hh hbound mass2 quartic vacuum s w V x‖ ≤
      massLipschitzBound ε hε hbar hh hbound mass2 quartic vacuum s T w * |y-x| := by
  apply norm_le_of_inner_bound _ _ (mul_nonneg (massLipschitzBound_nonneg ε hε hbar hh hbound mass2 quartic vacuum s T w) (abs_nonneg _))
  intro v
  have hpair := weak_trajectory_pairing_lipschitz ε hε hbar hh hbound mass2 quartic vacuum s w V T x y hT hx hy v
  have hi := (inner_sub_left (𝕜 := ℂ)
    (massState ε hε hbar hh hbound mass2 quartic vacuum s w V y)
    (massState ε hε hbar hh hbound mass2 quartic vacuum s w V x) v).trans
      (congrArg₂ (fun a b : ℂ => a-b)
        (mass_left_pairing ε hε hbar hh hbound mass2 quartic vacuum (V.formState y) v)
        (mass_left_pairing ε hε hbar hh hbound mass2 quartic vacuum (V.formState x) v))
  have hn := (congrArg norm hi).le.trans hpair
  have hs : pairingBound ε hε hbar hh hbound mass2 quartic vacuum s T w v * |y-x| =
      (massLipschitzBound ε hε hbar hh hbound mass2 quartic vacuum s T w * |y-x|) * ‖v‖ := by
    unfold pairingBound massLipschitzBound
    exact mul_right_comm _ _ _
  exact hn.trans hs.le

theorem massState_continuous (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (V : WeakTrajectory ε hε hbar hh hbound mass2 quartic vacuum s w) :
    Continuous (massState ε hε hbar hh hbound mass2 quartic vacuum s w V) :=
  continuous_of_window_lipschitz _ (fun T => massLipschitzBound ε hε hbar hh hbound mass2 quartic vacuum s T w)
    (fun T _ => massLipschitzBound_nonneg ε hε hbar hh hbound mass2 quartic vacuum s T w)
    (massState_window_lipschitz ε hε hbar hh hbound mass2 quartic vacuum s w V)

#print axioms mass_dense
#print axioms formState_window_bound
#print axioms formState_weakly_continuous
#print axioms limitSlope_continuous
#print axioms mass_pairing_derivative
#print axioms massState_window_lipschitz
#print axioms massState_continuous

end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity
