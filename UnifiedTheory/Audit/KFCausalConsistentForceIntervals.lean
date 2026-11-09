/- An additive family of finite interval forces with a local mass budget.
The actual dynamics constructs this structure in the successor module. -/
import UnifiedTheory.Audit.KFCausalLocalForceConsistency

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalConsistentForceIntervals
noncomputable section
open MeasureTheory BoundedContinuousFunction
open UnifiedTheory.Audit.KFCausalNeutralForceMeasure (FluxPair evaluate_bound)
open UnifiedTheory.Audit.KFCausalCompactifiedForceMeasure (Spectrum)
open UnifiedTheory.Audit.KFCausalLocalForceMeasure (finitePair finitePart)
open UnifiedTheory.Audit.KFCausalLocalForceConsistency

structure Family {K : Type*} (b c : K → ℝ) (s : ℝ) (budget : ℝ → ℝ) where
  positive : K → FiniteMeasure Spectrum
  negative : K → FiniteMeasure Spectrum
  additive : ∀ i j l, b i = b l → c i = b j → c j = c l →
    positive l = positive i+positive j ∧ negative l = negative i+negative j
  mass_bound : ∀ T i, |b i-s| ≤ T → |c i-s| ≤ T →
    ((positive i).mass:ℝ)+((negative i).mass:ℝ) ≤ (c i-b i)*budget T

variable {K : Type*} {b c : K → ℝ} {s : ℝ} {budget : ℝ → ℝ}
  (F : Family b c s budget)

def Family.local (i : K) : FluxPair := finitePair (F.positive i) (F.negative i)

theorem local_add (i j l : K) (hl : b i = b l) (hm : c i = b j) (hr : c j = c l) :
    (F.local l).positive = (F.local i).positive+(F.local j).positive ∧
    (F.local l).negative = (F.local i).negative+(F.local j).negative := by
  obtain ⟨hp,hn⟩ := F.additive i j l hl hm hr
  constructor
  · change (finitePart (F.positive l) : Measure ℝ) = _
    rw [hp,finitePart_add]
    rfl
  · change (finitePart (F.negative l) : Measure ℝ) = _
    rw [hn,finitePart_add]
    rfl

theorem local_evaluate_add (i j l : K) (hl : b i = b l) (hm : c i = b j) (hr : c j = c l)
    (q : ℝ →ᵇ ℂ) :
    (F.local l).evaluate q = (F.local i).evaluate q+(F.local j).evaluate q := by
  obtain ⟨hp,hn⟩ := F.additive i j l hl hm hr
  change (finitePair (F.positive l) (F.negative l)).evaluate q = _
  rw [hp,hn]
  exact finitePair_add_evaluate _ _ _ _ q

theorem local_mass_bound (T : ℝ) (i : K) (hb : |b i-s| ≤ T) (hc : |c i-s| ≤ T) :
    (F.local i).mass ≤ (c i-b i)*budget T :=
  (finitePair_mass_bound _ _).trans (F.mass_bound T i hb hc)

theorem point_interval_zero (i : K) (hi : b i = c i) : F.positive i = 0 ∧ F.negative i = 0 := by
  have hb := F.mass_bound |b i-s| i le_rfl (by rw [← hi])
  rw [← hi,sub_self,zero_mul] at hb
  have hp : ((F.positive i).mass:ℝ) = 0 := by
    have := NNReal.coe_nonneg (F.negative i).mass
    have := NNReal.coe_nonneg (F.positive i).mass
    linarith
  have hn : ((F.negative i).mass:ℝ) = 0 := by
    have := NNReal.coe_nonneg (F.negative i).mass
    linarith
  exact ⟨(FiniteMeasure.mass_zero_iff _).mp (by exact_mod_cast hp),
    (FiniteMeasure.mass_zero_iff _).mp (by exact_mod_cast hn)⟩

theorem local_test_bound (T : ℝ) (i : K) (hb : |b i-s| ≤ T) (hc : |c i-s| ≤ T)
    (q : ℝ →ᵇ ℂ) :
    ‖(F.local i).evaluate q‖ ≤ ((c i-b i)*budget T)/2*‖q‖ := by
  apply (evaluate_bound (F.local i) q).trans
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
    (local_mass_bound F T i hb hc) (by norm_num)) (norm_nonneg q)

theorem local_increment_bound (i j l : K) (hl : b i = b l) (hm : c i = b j) (hr : c j = c l)
    (T : ℝ) (hb : |b j-s| ≤ T) (hc : |c j-s| ≤ T) (q : ℝ →ᵇ ℂ) :
    ‖(F.local l).evaluate q-(F.local i).evaluate q‖ ≤ ((c j-b j)*budget T)/2*‖q‖ := by
  rw [local_evaluate_add F i j l hl hm hr,add_sub_cancel_left]
  exact local_test_bound F T j hb hc q

#print axioms local_add
#print axioms local_evaluate_add
#print axioms local_mass_bound
#print axioms point_interval_zero
#print axioms local_test_bound
#print axioms local_increment_bound
end
end UnifiedTheory.Audit.KFCausalConsistentForceIntervals
