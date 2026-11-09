/- Joint removal of Hamiltonian smoothing and pure-momentum cutoffs.
The quantitative remainder vanishes with a=b^(-4). Endpoint moment
regularity is explicit; its propagation is not assumed as a theorem. -/
import UnifiedTheory.Audit.KFCausalPureMomentumCutoffDynamics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalPureMomentumJointLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalPureMomentumCutoff
open UnifiedTheory.Audit.KFCausalPureMomentumFirstMoment
open UnifiedTheory.Audit.KFCausalPureMomentumCutoffDynamics
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution (evolution)
open UnifiedTheory.Audit.KFCausalClockFloorResolventBalance (expectation)
open UnifiedTheory.Audit.KFCausalClockFloorMovingResolventEhrenfest (boundedRate)
open UnifiedTheory.Audit.KFCausalClockFloorMovingResolventWindow (residual)

def smoothingScale (b : ℝ) : ℝ := (b⁻¹)^4

theorem smoothingScale_positive (b : ℝ) (hb : 0 < b) : 0 < smoothingScale b := by
  unfold smoothingScale
  positivity

theorem smoothingScale_tendsto (b : ℕ → ℝ) (hb : ∀ n, 0 < b n)
    (hz : Tendsto b atTop (𝓝 0)) : Tendsto (fun n => smoothingScale (b n)) atTop atTop := by
  have ht : Tendsto b atTop (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hz,Filter.Eventually.of_forall hb⟩
  exact (tendsto_pow_atTop (by norm_num : (4:ℕ) ≠ 0)).comp (tendsto_inv_nhdsGT_zero.comp ht)

theorem scaled_error (B L b : ℝ) (hb : 0 < b) :
    b⁻¹*error B L (smoothingScale b) = 2*b*Real.sqrt B*(1+|L|) := by
  have h1 : B/smoothingScale b = (b^2)^2*B := by unfold smoothingScale; field_simp
  have h4 : B/(4*smoothingScale b) = (b^2/2)^2*B := by unfold smoothingScale; field_simp; ring
  have h2 := Real.sqrt_mul (sq_nonneg (b^2)) B
  have h3 := Real.sqrt_mul (sq_nonneg (b^2/2)) B
  rw [Real.sqrt_sq (sq_nonneg b)] at h2
  rw [Real.sqrt_sq (by positivity : 0 ≤ b^2/2)] at h3
  unfold error
  rw [h1,h4,h2,h3]
  field_simp
  ring

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "U" => evolution ε hε h hne hh m g k
local notation "X" => expectation ε hε h hne hh m g k
local notation "R" => boundedRate ε hε h hne hh m g k
local notation "Z" => KFCausalClockFloorMovingResolventWindow.residual ε hε h hne hh m g k

def remainderConstant (s r t : ℝ) (v : V) : ℝ :=
  2*‖J v‖*Real.sqrt (budget ε hε h hne hh m g k s (|r-s|+|t-s|) v)*(1+|t-r|)

theorem remainderConstant_nonnegative (s r t : ℝ) (v : V) :
    0 ≤ remainderConstant ε hε h hne hh m g k s r t v := by
  unfold remainderConstant
  positivity

theorem joint_remainder_bound (b : ℝ) (hb : 0 < b) (D : Hilbert →L[ℂ] Hilbert)
    (hD : ‖D‖ ≤ b⁻¹) (s r t : ℝ) (v : V) :
    ‖Z (smoothingScale b) D s r t v‖ ≤ b*remainderConstant ε hε h hne hh m g k s r t v := by
  let T := |r-s|+|t-s|
  have hr : |r-s| ≤ T := le_add_of_nonneg_right (abs_nonneg _)
  have ht : |t-s| ≤ T := le_add_of_nonneg_left (abs_nonneg _)
  calc
    _ ≤ ‖D‖*‖J v‖*error (budget ε hε h hne hh m g k s T v) (t-r) (smoothingScale b) :=
      residual_window ε hε h hne hh m g k _ (smoothingScale_positive b hb) D s T r t v hr ht
    _ ≤ b⁻¹*‖J v‖*error (budget ε hε h hne hh m g k s T v) (t-r) (smoothingScale b) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
        (error_nonnegative _ _ _)
    _ = _ := by
      rw [mul_right_comm,scaled_error _ _ b hb]
      unfold remainderConstant
      dsimp only [T]
      ring

theorem joint_remainder_tendsto (b : ℕ → ℝ) (hb : ∀ n, 0 < b n)
    (hz : Tendsto b atTop (𝓝 0)) (D : ℕ → Hilbert →L[ℂ] Hilbert)
    (hD : ∀ n, ‖D n‖ ≤ (b n)⁻¹) (s r t : ℝ) (v : V) :
    Tendsto (fun n => Z (smoothingScale (b n)) (D n) s r t v) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => joint_remainder_bound ε hε h hne hh m g k
    (b n) (hb n) (D n) (hD n) s r t v)
  simpa only [zero_mul] using hz.mul_const (remainderConstant ε hε h hne hh m g k s r t v)

theorem joint_signed_response_limit (b : ℕ → ℝ) (hb : ∀ n, 0 < b n)
    (hz : Tendsto b atTop (𝓝 0)) (s r t : ℝ) (v : V)
    (hr : U s r (J v) ∈ (momentumHalf ε hε h).domain)
    (ht : U s t (J v) ∈ (momentumHalf ε hε h).domain) :
    Tendsto (fun n => (∫ z in r..t, R (smoothingScale (b n))
      (momentumCutoff ε hε h (b n) (hb n)) s z v).re) atTop
      (𝓝 ((∫ k, KFCausalClockFloorFourierMultiplier.symbol h k*‖(spectralCoordinates ε hε (U s t (J v))) k‖^2)-
        (∫ k, KFCausalClockFloorFourierMultiplier.symbol h k*‖(spectralCoordinates ε hε (U s r (J v))) k‖^2))) := by
  have he := (Complex.continuous_re.tendsto _).comp
    (joint_remainder_tendsto ε hε h hne hh m g k b hb hz
      (fun n => momentumCutoff ε hε h (b n) (hb n))
      (fun n => operator_opNorm _ _ _ (b n) (hb n)) s r t v)
  have hd := (momentum_expectation_tendsto ε hε h _ ht b hb hz).sub
    (momentum_expectation_tendsto ε hε h _ hr b hb hz)
  have ha := he.add hd
  simpa only [KFCausalClockFloorMovingResolventWindow.residual,expectation,
    Function.comp_def,Complex.sub_re,Complex.zero_re,zero_add,sub_add_cancel] using ha

theorem joint_absolute_response_limit (b : ℕ → ℝ) (hb : ∀ n, 0 < b n)
    (hz : Tendsto b atTop (𝓝 0)) (s r t : ℝ) (v : V)
    (hr : U s r (J v) ∈ (momentumHalf ε hε h).domain)
    (ht : U s t (J v) ∈ (momentumHalf ε hε h).domain) :
    Tendsto (fun n => (∫ z in r..t, R (smoothingScale (b n))
      (absoluteCutoff ε hε h (b n) (hb n)) s z v).re) atTop
      (𝓝 (‖momentumHalf ε hε h ⟨U s t (J v),ht⟩‖^2-
        ‖momentumHalf ε hε h ⟨U s r (J v),hr⟩‖^2)) := by
  have he := (Complex.continuous_re.tendsto _).comp
    (joint_remainder_tendsto ε hε h hne hh m g k b hb hz
      (fun n => absoluteCutoff ε hε h (b n) (hb n))
      (fun n => operator_opNorm _ _ _ (b n) (hb n)) s r t v)
  have hd := (absolute_expectation_tendsto ε hε h _ ht b hb hz).sub
    (absolute_expectation_tendsto ε hε h _ hr b hb hz)
  have ha := he.add hd
  simpa only [KFCausalClockFloorMovingResolventWindow.residual,expectation,
    Function.comp_def,Complex.sub_re,Complex.zero_re,zero_add,sub_add_cancel] using ha

theorem joint_graph_response_limit (b : ℕ → ℝ) (hb : ∀ n, 0 < b n)
    (hz : Tendsto b atTop (𝓝 0)) (s r t : ℝ) (v : V) (br bt : Hilbert)
    (hr : (U s r (J v),br) ∈ (KFCausalClockFloorPureClockMomentum.pureMomentum ε hε h).graph)
    (ht : (U s t (J v),bt) ∈ (KFCausalClockFloorPureClockMomentum.pureMomentum ε hε h).graph) :
    Tendsto (fun n => (∫ z in r..t, R (smoothingScale (b n))
      (momentumCutoff ε hε h (b n) (hb n)) s z v).re) atTop
      (𝓝 ((inner ℂ (U s t (J v)) bt).re-(inner ℂ (U s r (J v)) br).re)) := by
  rw [graph_expectation_integral ε hε h hne _ _ ht,
    graph_expectation_integral ε hε h hne _ _ hr]
  exact joint_signed_response_limit ε hε h hne hh m g k b hb hz s r t v
    (momentum_graph_domain ε hε h hne _ _ hr) (momentum_graph_domain ε hε h hne _ _ ht)

#print axioms smoothingScale_positive
#print axioms smoothingScale_tendsto
#print axioms scaled_error
#print axioms remainderConstant_nonnegative
#print axioms joint_remainder_bound
#print axioms joint_remainder_tendsto
#print axioms joint_signed_response_limit
#print axioms joint_absolute_response_limit
#print axioms joint_graph_response_limit
end
end UnifiedTheory.Audit.KFCausalPureMomentumJointLimit
