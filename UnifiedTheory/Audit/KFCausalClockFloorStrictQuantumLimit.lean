/- The strictly decreasing quantum expectation has a nonnegative long-time
limit and an exact accumulated-drop limit. Zero is not identified as that
limit; equivalence to decay of the physical defect norm is proved. -/
import UnifiedTheory.Audit.KFCausalClockFloorStrictQuantumDecay
import UnifiedTheory.Audit.KFCausalClockFloorInitialDriftPairing
import Mathlib.Topology.Order.MonotoneConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorStrictQuantumLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph (l2_norm_square)
open UnifiedTheory.Audit.KFCausalClockFloorInitialDriftPairing (real_multiplier_pairing)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution (evolution evolution_norm)
open UnifiedTheory.Audit.KFCausalClockFloorExactEhrenfest
open UnifiedTheory.Audit.KFCausalClockFloorStrictQuantumDecay

variable (ε : ℝ) (hε : 0 < ε)
local notation "D" => defectOperator ε hε

theorem expectation_bounds (f : Hilbert) :
    ‖D f‖^2 ≤ (inner ℂ f (D f)).re ∧ (inner ℂ f (D f)).re ≤ ‖f‖*‖D f‖ := by
  refine ⟨?_,re_inner_le_norm (𝕜 := ℂ) f (D f)⟩
  have he : (fun x : Configuration => (inner ℂ (f x) ((D f) x)).re) =ᵐ[volume]
      fun x => defect ε x.1*‖f x‖^2 := by
    filter_upwards [defectOperator_coe ε hε f] with x hx
    rw [hx]
    change (inner ℂ (f x) ((defect ε x.1:ℂ) • f x)).re = _
    rw [inner_smul_right,inner_self_eq_norm_sq_to_K]
    change ((defect ε x.1:ℂ)*(‖f x‖:ℂ)^2).re = _
    rw [← Complex.ofReal_pow,← Complex.ofReal_mul,Complex.ofReal_re]
  have hi := (L2.integrable_inner (𝕜 := ℂ) f (D f)).re.congr he
  rw [l2_norm_square,real_multiplier_pairing volume _ _ _ (defectOperator_coe ε hε f)]
  apply integral_mono_ae
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (D f))).mp (Lp.memLp (D f))) hi
  filter_upwards [defectOperator_coe ε hε f] with x hx
  have hd := defect_positive ε x.1 hε
  have hr := (response_bounds ε x.1 hε).1
  have hs := response_add_defect ε x.1 hε.le
  have hb : (defect ε x.1)^2 ≤ defect ε x.1 := by nlinarith
  rw [hx,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd,mul_pow]
  exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)

theorem expectation_nonnegative (f : Hilbert) : 0 ≤ (inner ℂ f (D f)).re :=
  (sq_nonneg _).trans (expectation_bounds ε hε f).1

theorem expectation_positive (f : Hilbert) (hf : f ≠ 0) : 0 < (inner ℂ f (D f)).re :=
  (sq_pos_of_pos (norm_pos_iff.mpr (defectOperator_ne_zero ε hε f hf))).trans_le
    (expectation_bounds ε hε f).1

variable (hbar : ℝ) (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum : ℝ)
local notation "V₀" => FormSpace ε hε hbar hh hb mass2 quartic vacuum 0
local notation "J" => embedding ε hε hbar hh hb mass2 quartic vacuum 0
local notation "U" => evolution ε hε hbar hh hb mass2 quartic vacuum

theorem expectation_limit (hv : 0 < vacuum) (s : ℝ) (w : V₀) (hw : J w ≠ 0) :
    ∃ ℓ : ℝ, 0 ≤ ℓ ∧
      (∀ t, ℓ < (inner ℂ (U s t (J w)) (D (U s t (J w)))).re) ∧
      Tendsto (fun t => (inner ℂ (U s t (J w)) (D (U s t (J w)))).re) atTop (𝓝 ℓ) := by
  let F : ℝ → ℝ := fun t => (inner ℂ (U s t (J w)) (D (U s t (J w)))).re
  have hs : StrictAnti F := expectation_strictAnti ε hε hbar hh hb mass2 quartic vacuum hv s w hw
  have h0 (t : ℝ) : 0 ≤ F t := expectation_nonnegative ε hε _
  have hbd : BddBelow (Set.range F) := ⟨0,by rintro _ ⟨t,rfl⟩; exact h0 t⟩
  refine ⟨⨅ t, F t,le_ciInf h0,?_,tendsto_atTop_ciInf hs.antitone hbd⟩
  intro t
  exact (ciInf_le hbd (t+1)).trans_lt (hs (by linarith : t < t+1))

theorem accumulated_drop_limit (hv : 0 < vacuum) (s r : ℝ) (w : V₀) (hw : J w ≠ 0) :
    ∃ ℓ : ℝ, 0 ≤ ℓ ∧ ℓ < (inner ℂ (U s r (J w)) (D (U s r (J w)))).re ∧
      Tendsto (fun t => ∫ z in r..t, -exactRate ε hε hbar hh hb mass2 quartic vacuum s z w)
        atTop (𝓝 ((inner ℂ (U s r (J w)) (D (U s r (J w)))).re-ℓ)) := by
  have hex := expectation_limit ε hε hbar hh hb mass2 quartic vacuum hv s w hw
  let ℓ := Classical.choose hex
  have hp := Classical.choose_spec hex
  refine ⟨ℓ,hp.1,hp.2.1 r,?_⟩
  have he (t : ℝ) : (∫ z in r..t, -exactRate ε hε hbar hh hb mass2 quartic vacuum s z w) =
      (inner ℂ (U s r (J w)) (D (U s r (J w)))).re-
        (inner ℂ (U s t (J w)) (D (U s t (J w)))).re := by
    exact intervalIntegral.integral_neg.trans
      ((congrArg Neg.neg (expectation_integral ε hε hbar hh hb mass2 quartic vacuum s r t w)).trans (neg_sub _ _))
  exact (tendsto_const_nhds.sub hp.2.2).congr' (Filter.Eventually.of_forall (fun t => (he t).symm))

theorem zero_limit_iff_defect_norm (s : ℝ) (f : Hilbert) :
    Tendsto (fun t => (inner ℂ (U s t f) (D (U s t f))).re) atTop (𝓝 0) ↔
      Tendsto (fun t => ‖D (U s t f)‖) atTop (𝓝 0) := by
  constructor
  · intro h
    have hs : Tendsto (fun t => ‖D (U s t f)‖^2) atTop (𝓝 0) :=
      squeeze_zero (fun _ => sq_nonneg _) (fun t => (expectation_bounds ε hε (U s t f)).1) h
    have ht := (Real.continuous_sqrt.tendsto 0).comp hs
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),Real.sqrt_zero] using ht
  · intro h
    have hs : Tendsto (fun t => ‖f‖*‖D (U s t f)‖) atTop (𝓝 0) := by
      simpa only [mul_zero] using h.const_mul ‖f‖
    apply squeeze_zero (fun t => expectation_nonnegative ε hε (U s t f)) _ hs
    intro t
    simpa only [evolution_norm] using (expectation_bounds ε hε (U s t f)).2

#print axioms expectation_bounds
#print axioms expectation_nonnegative
#print axioms expectation_positive
#print axioms expectation_limit
#print axioms accumulated_drop_limit
#print axioms zero_limit_iff_defect_norm

end
end UnifiedTheory.Audit.KFCausalClockFloorStrictQuantumLimit
