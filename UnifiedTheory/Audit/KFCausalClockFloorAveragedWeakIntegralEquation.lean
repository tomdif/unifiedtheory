/- The constructed all-time weak trajectory satisfies the integrated
averaged Schrodinger form equation. Passage to the limit uses the actual
cutoff sequence and dominated convergence. This does not yet establish
uniqueness, norm conservation, or a unitary unbounded propagator. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedFormGeometry
import UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakTrajectory
import UnifiedTheory.Audit.KFCausalWeakIntegralLimit
import UnifiedTheory.Audit.KFCausalWeakContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakIntegralEquation
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormGeometry
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosida
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosidaDynamics
open UnifiedTheory.Audit.KFCausalClockFloorAveragedSmoothedTrajectory
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakPairing
open UnifiedTheory.Audit.KFCausalClockFloorAveragedCountableLimit
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakTrajectory
open UnifiedTheory.Audit.KFCausalWeakIntegralLimit
open UnifiedTheory.Audit.KFCausalWeakContinuity

theorem weakSlope_continuous (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum a : ℝ) (ha : 0 < a)
    (s : ℝ) (f : Hilbert) (v : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) :
    Continuous (fun t => weakSlope ε hε hbar hh hbound mass2 quartic vacuum a ha s t f v) := by
  have hp : Continuous (fun t => dynamics ε hε hbar hh hbound mass2 quartic vacuum a ha s t f) :=
    continuous_iff_continuousAt.mpr (fun t => (dynamics_state_derivative ε hε hbar hh hbound mass2 quartic vacuum a ha s t f).continuousAt)
  have hpair := ((averagedYosida_continuous ε hε hbar hh hbound mass2 quartic vacuum a ha).clm_apply hp).inner
    (𝕜 := ℂ) (continuous_const (y := embedding ε hε hbar hh hbound mass2 quartic vacuum 0 v))
  simpa only [weakSlope,smoothed_weak_pairing] using (continuous_const (y := Complex.I*((1/hbar:ℝ):ℂ))).mul hpair

def limitSlope (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (V : WeakTrajectory ε hε hbar hh hbound mass2 quartic vacuum s w)
    (t : ℝ) (v : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) : ℂ :=
  (Complex.I*((1/hbar:ℝ):ℂ))*inner ℂ (V.formState t) (referenceFormOperator ε hε hbar hh hbound mass2 quartic vacuum t v)

theorem weakSlope_tendsto (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (V : WeakTrajectory ε hε hbar hh hbound mass2 quartic vacuum s w)
    (t : ℝ) (v : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) :
    Tendsto (fun n => weakSlope ε hε hbar hh hbound mass2 quartic vacuum (cutoff (V.subsequence n))
      (cutoff_pos (V.subsequence n)) s t (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 w) v) atTop
      (𝓝 (limitSlope ε hε hbar hh hbound mass2 quartic vacuum s w V t v)) :=
  (V.formConvergence t (referenceFormOperator ε hε hbar hh hbound mass2 quartic vacuum t v)).const_mul _

theorem abs_le_window_of_mem_uIcc (r t z : ℝ) (hz : z ∈ uIcc r t) : |z| ≤ max |r| |t| := by
  have hr := le_max_left |r| |t|
  have ht := le_max_right |r| |t|
  rcases mem_uIcc.mp hz with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
    exact abs_le.mpr ⟨by linarith [neg_abs_le r,neg_abs_le t],by linarith [le_abs_self r,le_abs_self t]⟩

theorem weak_trajectory_integral_equation (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (V : WeakTrajectory ε hε hbar hh hbound mass2 quartic vacuum s w)
    (r t : ℝ) (v : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) :
    (∫ z in r..t, limitSlope ε hε hbar hh hbound mass2 quartic vacuum s w V z v) =
      inner ℂ (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 (V.formState t)) (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 v)-
      inner ℂ (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 (V.formState r)) (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 v) := by
  apply integral_derivative_limit
    (fun n z => inner ℂ (dynamics ε hε hbar hh hbound mass2 quartic vacuum (cutoff (V.subsequence n))
      (cutoff_pos (V.subsequence n)) s z (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 w))
      (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 v))
    (fun n z => weakSlope ε hε hbar hh hbound mass2 quartic vacuum (cutoff (V.subsequence n))
      (cutoff_pos (V.subsequence n)) s z (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 w) v)
    _ _ r t (pairingBound ε hε hbar hh hbound mass2 quartic vacuum s (max |r| |t|) w v)
  · intro n z
    exact weak_pairing_derivative ε hε hbar hh hbound mass2 quartic vacuum _ (cutoff_pos (V.subsequence n)) s z _ v
  · intro n
    exact weakSlope_continuous ε hε hbar hh hbound mass2 quartic vacuum _ (cutoff_pos (V.subsequence n)) s _ v
  · intro n z hz
    exact weakSlope_window_bound ε hε hbar hh hbound mass2 quartic vacuum _ (cutoff_pos (V.subsequence n)) s
      (max |r| |t|) z (le_max_of_le_left (abs_nonneg r)) (abs_le_window_of_mem_uIcc r t z hz) w v
  · intro z
    exact V.physicalConvergence z (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 v)
  · intro z
    exact weakSlope_tendsto ε hε hbar hh hbound mass2 quartic vacuum s w V z v

theorem weak_trajectory_integral_initial (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (V : WeakTrajectory ε hε hbar hh hbound mass2 quartic vacuum s w)
    (t : ℝ) (v : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) :
    (∫ z in s..t, limitSlope ε hε hbar hh hbound mass2 quartic vacuum s w V z v) =
      inner ℂ (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 (V.formState t)) (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 v)-
      inner ℂ (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 w) (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 v) := by
  have he := weak_trajectory_integral_equation ε hε hbar hh hbound mass2 quartic vacuum s w V s t v
  have hi := weak_trajectory_initial ε hε hbar hh hbound mass2 quartic vacuum s w V
  exact he.trans (congrArg (fun u : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0 =>
    inner ℂ (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 (V.formState t))
      (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 v) -
    inner ℂ (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 u)
      (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 v)) hi)

theorem limitSlope_intervalIntegrable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (V : WeakTrajectory ε hε hbar hh hbound mass2 quartic vacuum s w)
    (r t : ℝ) (v : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) :
    IntervalIntegrable (fun z => limitSlope ε hε hbar hh hbound mass2 quartic vacuum s w V z v) volume r t := by
  apply intervalIntegrable_limit
    (fun n z => weakSlope ε hε hbar hh hbound mass2 quartic vacuum (cutoff (V.subsequence n))
      (cutoff_pos (V.subsequence n)) s z (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 w) v)
    _ r t (pairingBound ε hε hbar hh hbound mass2 quartic vacuum s (max |r| |t|) w v)
  · intro n
    exact weakSlope_continuous ε hε hbar hh hbound mass2 quartic vacuum _ (cutoff_pos (V.subsequence n)) s _ v
  · intro n z hz
    exact weakSlope_window_bound ε hε hbar hh hbound mass2 quartic vacuum _ (cutoff_pos (V.subsequence n)) s
      (max |r| |t|) z (le_max_of_le_left (abs_nonneg r)) (abs_le_window_of_mem_uIcc r t z hz) w v
  · intro z
    exact weakSlope_tendsto ε hε hbar hh hbound mass2 quartic vacuum s w V z v

theorem weak_trajectory_form_pairing_continuous (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (V : WeakTrajectory ε hε hbar hh hbound mass2 quartic vacuum s w)
    (v : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) :
    Continuous (fun t => inner ℂ (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 (V.formState t))
      (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 v)) := by
  have hc := intervalIntegral.continuous_primitive
    (fun r t => limitSlope_intervalIntegrable ε hε hbar hh hbound mass2 quartic vacuum s w V r t v) s
  have he : (fun t => inner ℂ (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 (V.formState t))
      (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 v)) =
      (fun t => (∫ z in s..t, limitSlope ε hε hbar hh hbound mass2 quartic vacuum s w V z v)+
        inner ℂ (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 w) (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 v)) := by
    funext t
    rw [weak_trajectory_integral_initial,sub_add_cancel]
  rw [he]
  exact hc.add continuous_const

theorem weak_trajectory_weakly_continuous (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (V : WeakTrajectory ε hε hbar hh hbound mass2 quartic vacuum s w) :
    ∀ y : Hilbert, Continuous (fun t => inner ℂ
      (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 (V.formState t)) y) := by
  exact weak_continuous_of_dense_tests (embedding ε hε hbar hh hbound mass2 quartic vacuum 0)
    (embedding_dense ε hε hbar hh hbound mass2 quartic vacuum 0) _ ‖embedding ε hε hbar hh hbound mass2 quartic vacuum 0 w‖
    (weak_trajectory_norm_bound ε hε hbar hh hbound mass2 quartic vacuum s w V)
    (weak_trajectory_form_pairing_continuous ε hε hbar hh hbound mass2 quartic vacuum s w V)

/-- Nonzero hbar gives the integrated equation in the original form pairing.
The minus sign reflects conjugate-linearity in the first inner-product slot. -/
theorem weak_trajectory_schrodinger_integral (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s : ℝ)
    (hhbar : hbar ≠ 0) (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0)
    (V : WeakTrajectory ε hε hbar hh hbound mass2 quartic vacuum s w) (r t : ℝ)
    (v : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) :
    (∫ z in r..t, inner ℂ (V.formState z) (referenceFormOperator ε hε hbar hh hbound mass2 quartic vacuum z v)) =
      (-Complex.I*(hbar:ℂ)) *
      (inner ℂ (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 (V.formState t)) (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 v)-
       inner ℂ (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 (V.formState r)) (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 v)) := by
  have he := weak_trajectory_integral_equation ε hε hbar hh hbound mass2 quartic vacuum s w V r t v
  simp only [limitSlope,intervalIntegral.integral_const_mul] at he
  have hz : (hbar:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hhbar
  have hc : (-Complex.I*(hbar:ℂ))*(Complex.I*((1/hbar:ℝ):ℂ)) = 1 := by
    rw [Complex.ofReal_div,Complex.ofReal_one]
    calc
      _ = (-Complex.I*Complex.I)*((hbar:ℂ)/(hbar:ℂ)) := by ring
      _ = 1 := by rw [div_self hz]; simp
  let z : ℂ := ∫ u in r..t, inner ℂ (V.formState u)
    (referenceFormOperator ε hε hbar hh hbound mass2 quartic vacuum u v)
  have hz' : (-Complex.I*(hbar:ℂ))*((Complex.I*((1/hbar:ℝ):ℂ))*z) = z := by
    rw [← mul_assoc,hc,one_mul]
  exact hz'.symm.trans (congrArg (fun u : ℂ => (-Complex.I*(hbar:ℂ))*u) he)

#print axioms weakSlope_continuous
#print axioms weakSlope_tendsto
#print axioms weak_trajectory_integral_equation
#print axioms weak_trajectory_integral_initial
#print axioms limitSlope_intervalIntegrable
#print axioms weak_trajectory_form_pairing_continuous
#print axioms weak_trajectory_weakly_continuous
#print axioms weak_trajectory_schrodinger_integral

end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakIntegralEquation
