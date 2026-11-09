/- Two-sided log-clock Born tails control the actual canonical clock
position phase. The eventual bound is uniform over finite forward time
windows; no clock-position second moment is assumed. -/
import UnifiedTheory.Audit.KFCausalL2PhaseTailBound
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockTightness
import UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockTestControl
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (Frequency characteristic operator operator_coe scalar)
open UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics (positionFrequency)
open UnifiedTheory.Audit.KFCausalLpPhaseTranslation (modulation modulation_coe)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail (evolvedState evolvedState_norm)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockTightness (evolved_clock_compact_tail)
open UnifiedTheory.Audit.KFCausalClockFloorClockPositionMass (outsideMass)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

def frequency (u : ℝ) : Frequency (X := Configuration) := (positionFrequency u 0,0)
def clockTest (h u : ℝ) : Hilbert ≃ₗᵢ[ℂ] Hilbert := operator volume h (frequency u)

theorem clockTest_modulation (h u : ℝ) (f : Hilbert) :
    clockTest h u f = modulation volume (fun x : Configuration => u*x.1)
      (measurable_const.mul measurable_fst) f := by
  apply Lp.ext
  filter_upwards [operator_coe volume h (frequency u) f,
    modulation_coe volume (fun x : Configuration => u*x.1) (measurable_const.mul measurable_fst) f] with x ho hm
  change (clockTest h u f) x = _ at ho
  rw [ho,hm]
  simp [frequency,positionFrequency,KFCausalPhysicalGaussianConcentration.dot,scalar,KFCausalLpPhaseTranslation.phase]

def radialTail (R : ℝ) (f : Hilbert) : ℝ := ∫ x : Configuration in {x | R^2 ≤ x.1^2}, ‖f x‖^2

theorem radialTail_le_outside (S R L : ℝ) (hLS : -L < S) (hRL : R < L) (f : Hilbert) :
    radialTail L f ≤ outsideMass S R f := by
  have hf := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  apply setIntegral_mono_set hf.integrableOn (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
  filter_upwards [] with x hx hi
  have ha : |x.1| < L := abs_lt.mpr ⟨hLS.trans_le hi.1,hi.2.trans_lt hRL⟩
  have hs : x.1^2 < L^2 := by nlinarith [sq_abs x.1,abs_nonneg x.1]
  exact (not_lt_of_ge hx) hs

theorem clockTest_tail_bound (h u R : ℝ) (hR : 0 ≤ R) (f : Hilbert) :
    ‖clockTest h u f-f‖^2 ≤ u^2*R^2*‖f‖^2+4*radialTail R f := by
  rw [clockTest_modulation]
  exact KFCausalL2PhaseTailBound.phase_difference_square_tail (fun x : Configuration => x.1)
    (fun x => x.1^2) measurable_fst (by fun_prop) (fun _ => le_refl _) u R hR f

theorem characteristic_difference (h u : ℝ) (f : Hilbert) (hf : ‖f‖ = 1) :
    ‖characteristic volume h f (frequency u)-1‖ ≤ ‖clockTest h u f-f‖ := by
  have hi : inner ℂ f f = 1 := by rw [inner_self_eq_norm_sq_to_K,hf]; norm_num
  change ‖inner ℂ f (clockTest h u f)-1‖ ≤ _
  rw [← hi,← inner_sub_right]
  simpa only [hf,one_mul] using norm_inner_le_norm (𝕜 := ℂ) f (clockTest h u f-f)

theorem evolved_test_uniform (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (m g κ s : ℝ) (p : Configuration) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Set.Icc s (s+T),
      ∀ u : ℝ, |u| ≤ ρ →
      ‖clockTest (h n) u (evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p t)-
        evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p t‖ < δ := by
  obtain ⟨S,R,hS,hR,N,hN⟩ := evolved_clock_compact_tail ε a hε ha m g κ s p hm hg hκ
    h hh hb hz T (δ^2/16) (by positivity)
  let L := max (-S) R+1
  have hL : 0 < L := by dsimp [L]; linarith [le_max_right (-S) R]
  have hLS : -L < S := by dsimp [L]; linarith [le_max_left (-S) R]
  have hRL : R < L := by dsimp [L]; linarith [le_max_right (-S) R]
  refine ⟨δ/(2*L),by positivity,N,fun n hn t ht u hu => ?_⟩
  let f := evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p t
  have hnorm : ‖f‖ = 1 := evolvedState_norm ε a (h n) hε ha (hh n) (hb n) m g κ s p t
  have htail : radialTail L f < δ^2/16 :=
    (radialTail_le_outside S R L hLS hRL f).trans_lt (hN n hn t ht)
  have hp : |u| * L ≤ δ/2 := by
    have he := (le_div_iff₀ (by positivity : 0 < 2*L)).mp hu
    nlinarith
  have hs : u^2*L^2 ≤ δ^2/4 := by
    have he := pow_le_pow_left₀ (mul_nonneg (abs_nonneg u) hL.le) hp 2
    simpa only [mul_pow,sq_abs,div_pow,show (2:ℝ)^2 = 4 by norm_num] using he
  have he := clockTest_tail_bound (h n) u L hL.le f
  rw [hnorm,one_pow,mul_one] at he
  change ‖clockTest (h n) u f-f‖ < δ
  nlinarith [norm_nonneg (clockTest (h n) u f-f)]

theorem evolved_characteristic_uniform (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (m g κ s : ℝ) (p : Configuration) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Set.Icc s (s+T),
      ∀ u : ℝ, |u| ≤ ρ →
      ‖characteristic volume (h n) (evolvedState ε a (h n) hε ha (hh n) (hb n) m g κ s p t)
        (frequency u)-1‖ < δ := by
  obtain ⟨ρ,hρ,N,hN⟩ := evolved_test_uniform ε a hε ha m g κ s p hm hg hκ h hh hb hz T δ hδ
  refine ⟨ρ,hρ,N,fun n hn t ht u hu => ?_⟩
  exact (characteristic_difference (h n) u _
    (evolvedState_norm ε a (h n) hε ha (hh n) (hb n) m g κ s p t)).trans_lt (hN n hn t ht u hu)

#print axioms clockTest_modulation
#print axioms radialTail_le_outside
#print axioms clockTest_tail_bound
#print axioms characteristic_difference
#print axioms evolved_test_uniform
#print axioms evolved_characteristic_uniform

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockTestControl
