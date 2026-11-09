/- The constructed weak solution is weakly continuous in the reference
form space. Its mass-dual curve is locally Lipschitz and has the weak
derivative dictated by the original form Hamiltonian. -/
import UnifiedTheory.Audit.KFCausalRegularizedWeakIntegralEquation
import UnifiedTheory.Audit.KFCausalMassGram
import UnifiedTheory.Audit.KFCausalLocalWeakContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalRegularizedWeakFormContinuity
noncomputable section
open Filter MeasureTheory
open scoped Topology
open UnifiedTheory.Audit.KFCausalBoundedFormCurve
open UnifiedTheory.Audit.KFCausalShiftedForm
open UnifiedTheory.Audit.KFCausalRegularizedMomentumClosure
open UnifiedTheory.Audit.KFCausalRegularizedFormEmbedding
open UnifiedTheory.Audit.KFCausalRegularizedFormRegularity
open UnifiedTheory.Audit.KFCausalRegularizedSmoothedTrajectory
open UnifiedTheory.Audit.KFCausalRegularizedFormWindowBound
open UnifiedTheory.Audit.KFCausalRegularizedWeakPairing
open UnifiedTheory.Audit.KFCausalRegularizedCountableLimit
open UnifiedTheory.Audit.KFCausalRegularizedWeakTrajectory
open UnifiedTheory.Audit.KFCausalRegularizedWeakIntegralEquation
open UnifiedTheory.Audit.KFCausalWeakLimitTransport
open UnifiedTheory.Audit.KFCausalMassGram
open UnifiedTheory.Audit.KFCausalLocalWeakContinuity

def massOperator (ε : ℝ) (hε : 0 < ε) (hbar coupling : ℝ) :
    FormSpace ε hε hbar coupling 0 →L[ℂ] FormSpace ε hε hbar coupling 0 :=
  gram (E := FormSpace ε hε hbar coupling 0) (H := Hilbert) (embedding ε hε hbar coupling 0)

theorem mass_left_pairing (ε : ℝ) (hε : 0 < ε) (hbar coupling : ℝ)
    (x y : FormSpace ε hε hbar coupling 0) :
    inner ℂ (massOperator ε hε hbar coupling x) y =
      inner ℂ (embedding ε hε hbar coupling 0 x) (embedding ε hε hbar coupling 0 y) :=
  gram_left_pairing _ x y

theorem mass_dense (ε : ℝ) (hε : 0 < ε) (hbar coupling : ℝ) :
    DenseRange (massOperator ε hε hbar coupling) :=
  gram_dense _ (embedding_injective ε hε hbar coupling 0)

theorem formState_window_bound (ε : ℝ) (hε : 0 < ε) (hbar coupling s : ℝ)
    (w : FormSpace ε hε hbar coupling 0) (V : WeakTrajectory ε hε hbar coupling s w)
    (T t : ℝ) (hT : 0 ≤ T) (ht : |t| ≤ T) :
    ‖V.formState t‖ ≤ windowRadius ε hε hbar coupling s T w := by
  exact weak_norm_le (H := FormSpace ε hε hbar coupling 0)
    (fun n => smoothed_window_norm ε hε hbar coupling (cutoff (V.subsequence n))
      (cutoff_pos (V.subsequence n)) s T t hT ht w) (V.formConvergence t)

theorem formState_weakly_continuous (ε : ℝ) (hε : 0 < ε) (hbar coupling s : ℝ)
    (w : FormSpace ε hε hbar coupling 0) (V : WeakTrajectory ε hε hbar coupling s w) :
    ∀ y, Continuous (fun t => inner ℂ (V.formState t) y) := by
  apply weak_continuous_of_locally_bounded_dense_tests (massOperator ε hε hbar coupling)
    (mass_dense ε hε hbar coupling) V.formState (fun T => windowRadius ε hε hbar coupling s T w)
  · exact formState_window_bound ε hε hbar coupling s w V
  · intro y
    have he : (fun t => inner ℂ (V.formState t) (massOperator ε hε hbar coupling y)) =
        (fun t => inner ℂ (embedding ε hε hbar coupling 0 (V.formState t))
          (embedding ε hε hbar coupling 0 y)) := by
      funext t
      exact gram_right_pairing _ _ _
    rw [he]
    exact weak_trajectory_form_pairing_continuous ε hε hbar coupling s w V y

theorem limitSlope_continuous (ε : ℝ) (hε : 0 < ε) (hbar coupling s : ℝ)
    (w : FormSpace ε hε hbar coupling 0) (V : WeakTrajectory ε hε hbar coupling s w)
    (y : FormSpace ε hε hbar coupling 0) :
    Continuous (fun t => limitSlope ε hε hbar coupling s w V t y) := by
  have hf : Continuous (fun t => referenceFormOperator ε hε hbar coupling t y) :=
    (continuous_iff_continuousAt.mpr (fun t =>
      (referenceForm_derivative ε hε hbar coupling t).continuousAt)).clm_apply continuous_const
  have hh := weak_strong_pairing_continuous V.formState
    (fun t => referenceFormOperator ε hε hbar coupling t y)
    (fun T => windowRadius ε hε hbar coupling s T w)
    (formState_window_bound ε hε hbar coupling s w V)
    (formState_weakly_continuous ε hε hbar coupling s w V) hf
  exact continuous_const.mul hh

def massState (ε : ℝ) (hε : 0 < ε) (hbar coupling s : ℝ)
    (w : FormSpace ε hε hbar coupling 0) (V : WeakTrajectory ε hε hbar coupling s w)
    (t : ℝ) : FormSpace ε hε hbar coupling 0 := massOperator ε hε hbar coupling (V.formState t)

def massSlope (ε : ℝ) (hε : 0 < ε) (hbar coupling s : ℝ)
    (w : FormSpace ε hε hbar coupling 0) (V : WeakTrajectory ε hε hbar coupling s w)
    (t : ℝ) : FormSpace ε hε hbar coupling 0 :=
  (-Complex.I*((1/hbar:ℝ):ℂ)) • referenceFormOperator ε hε hbar coupling t (V.formState t)

theorem massSlope_pairing (ε : ℝ) (hε : 0 < ε) (hbar coupling s : ℝ)
    (w : FormSpace ε hε hbar coupling 0) (V : WeakTrajectory ε hε hbar coupling s w)
    (t : ℝ) (y : FormSpace ε hε hbar coupling 0) :
    inner ℂ (massSlope ε hε hbar coupling s w V t) y = limitSlope ε hε hbar coupling s w V t y := by
  unfold massSlope limitSlope
  have hs := formOperator_inner_symm (E := FormSpace ε hε hbar coupling 0) (H := Hilbert)
    (clockMap ε hε hbar coupling) (momentumMap ε hε hbar coupling) t (V.formState t) y
  change inner ℂ (referenceFormOperator ε hε hbar coupling t (V.formState t)) y =
    inner ℂ (V.formState t) (referenceFormOperator ε hε hbar coupling t y) at hs
  have hscale := inner_smul_left (𝕜 := ℂ) (E := FormSpace ε hε hbar coupling 0)
    (referenceFormOperator ε hε hbar coupling t (V.formState t)) y
    (-Complex.I*((1/hbar:ℝ):ℂ))
  rw [hs] at hscale
  simpa only [map_mul,map_neg,Complex.conj_I,neg_neg,Complex.conj_ofReal] using hscale

theorem mass_pairing_derivative (ε : ℝ) (hε : 0 < ε) (hbar coupling s : ℝ)
    (w : FormSpace ε hε hbar coupling 0) (V : WeakTrajectory ε hε hbar coupling s w)
    (t : ℝ) (y : FormSpace ε hε hbar coupling 0) :
    HasDerivAt (fun z => inner ℂ (massState ε hε hbar coupling s w V z) y)
      (inner ℂ (massSlope ε hε hbar coupling s w V t) y) t := by
  have hc := limitSlope_continuous ε hε hbar coupling s w V y
  have hd := intervalIntegral.integral_hasDerivAt_right
    (limitSlope_intervalIntegrable ε hε hbar coupling s w V s t y)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  have he : (fun z => inner ℂ (massState ε hε hbar coupling s w V z) y) =
      (fun z => (∫ r in s..z, limitSlope ε hε hbar coupling s w V r y)+
        inner ℂ (embedding ε hε hbar coupling 0 w) (embedding ε hε hbar coupling 0 y)) := by
    funext z
    rw [massState,mass_left_pairing,weak_trajectory_integral_initial,sub_add_cancel]
  rw [he,massSlope_pairing]
  exact hd.add_const _

def massLipschitzBound (ε : ℝ) (hε : 0 < ε) (hbar coupling s T : ℝ)
    (w : FormSpace ε hε hbar coupling 0) : ℝ :=
  |1/hbar| * windowRadius ε hε hbar coupling s T w * (1+Real.exp (2*T))

theorem massLipschitzBound_nonneg (ε : ℝ) (hε : 0 < ε) (hbar coupling s T : ℝ)
    (w : FormSpace ε hε hbar coupling 0) : 0 ≤ massLipschitzBound ε hε hbar coupling s T w := by
  unfold massLipschitzBound windowRadius
  positivity

theorem massState_window_lipschitz (ε : ℝ) (hε : 0 < ε) (hbar coupling s : ℝ)
    (w : FormSpace ε hε hbar coupling 0) (V : WeakTrajectory ε hε hbar coupling s w)
    (T x y : ℝ) (hT : 0 ≤ T) (hx : |x| ≤ T) (hy : |y| ≤ T) :
    ‖massState ε hε hbar coupling s w V y-massState ε hε hbar coupling s w V x‖ ≤
      massLipschitzBound ε hε hbar coupling s T w * |y-x| := by
  apply norm_le_of_inner_bound _ _ (mul_nonneg (massLipschitzBound_nonneg _ _ _ _ _ _ _) (abs_nonneg _))
  intro v
  have hh := weak_trajectory_pairing_lipschitz ε hε hbar coupling s w V T x y hT hx hy v
  rw [inner_sub_left,massState,massState,mass_left_pairing,mass_left_pairing]
  unfold pairingBound at hh
  unfold massLipschitzBound
  convert hh using 1
  ring

theorem massState_continuous (ε : ℝ) (hε : 0 < ε) (hbar coupling s : ℝ)
    (w : FormSpace ε hε hbar coupling 0) (V : WeakTrajectory ε hε hbar coupling s w) :
    Continuous (massState ε hε hbar coupling s w V) :=
  continuous_of_window_lipschitz _ (fun T => massLipschitzBound ε hε hbar coupling s T w)
    (fun T _ => massLipschitzBound_nonneg _ _ _ _ _ T _)
    (massState_window_lipschitz ε hε hbar coupling s w V)

#print axioms mass_dense
#print axioms formState_window_bound
#print axioms formState_weakly_continuous
#print axioms limitSlope_continuous
#print axioms mass_pairing_derivative
#print axioms massState_window_lipschitz
#print axioms massState_continuous

end
end UnifiedTheory.Audit.KFCausalRegularizedWeakFormContinuity
