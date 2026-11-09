/- Strict clock-defect decrease along actual matter canonical trajectories.
This does not assert their global existence or a zero long-time limit. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterClock

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClassicalMatterDefect
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalMatterSymbols
open UnifiedTheory.Audit.KFCausalClassicalMatterHamiltonian
open UnifiedTheory.Audit.KFCausalClassicalMatterODE
open UnifiedTheory.Audit.KFCausalClassicalMatterClock
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth (q p TimePhase)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (clock_positive defect)

theorem clock_derivative (ε m g κ : ℝ) (hε : 0 ≤ ε) (γ : ℝ → TimePhase) (t : ℝ)
    (hγ : HasDerivAt γ (field ε m g κ (γ t)) t) :
    HasDerivAt (fun u => q (.inr 0) (γ u).2)
      (clockRate ε m g κ (γ t).1 (γ t).2 (q (.inr 0) (γ t).2) (p (.inr 0) (γ t).2)) t := by
  have h : HasDerivAt (fun u => q (.inr 0) (γ u).2) (q (.inr 0) (field ε m g κ (γ t)).2) t :=
    (q (.inr 0)).hasFDerivAt.comp_hasDerivAt t hγ.snd
  simpa only [field_clock ε m g κ hε] using h

theorem clockMomentum_derivative (ε m g κ : ℝ) (hε : 0 ≤ ε) (γ : ℝ → TimePhase) (t : ℝ)
    (hγ : HasDerivAt γ (field ε m g κ (γ t)) t) :
    HasDerivAt (fun u => p (.inr 0) (γ u).2)
      (momentumRate ε m g κ (γ t).1 (γ t).2 (q (.inr 0) (γ t).2) (p (.inr 0) (γ t).2)) t := by
  have h : HasDerivAt (fun u => p (.inr 0) (γ u).2) (p (.inr 0) (field ε m g κ (γ t)).2) t :=
    (p (.inr 0)).hasFDerivAt.comp_hasDerivAt t hγ.snd
  simpa only [field_clockMomentum ε m g κ hε] using h

theorem clockRate_positive (ε m g κ t s r : ℝ) (hε : 0 ≤ ε)
    (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 < κ) (z : Phase) :
    0 < clockRate ε m g κ t z s r := by
  apply lt_of_lt_of_le _ (clockRate_lower ε m g κ t hm hg hκ.le z s r)
  exact div_pos (mul_pos hκ (Real.exp_pos _)) (sq_pos_of_pos (clock_positive ε s hε))

theorem defect_derivative (ε m g κ : ℝ) (hε : 0 ≤ ε) (γ : ℝ → TimePhase) (t : ℝ)
    (hγ : HasDerivAt γ (field ε m g κ (γ t)) t) :
    HasDerivAt (fun u => defect ε (q (.inr 0) (γ u).2))
      (-ε*Real.exp (q (.inr 0) (γ t).2)*
        clockRate ε m g κ (γ t).1 (γ t).2 (q (.inr 0) (γ t).2) (p (.inr 0) (γ t).2)/
          (clock ε (q (.inr 0) (γ t).2))^2) t := by
  have hd := ((clock_derivative ε m g κ hε γ t hγ).exp).add_const ε
  have h := (hasDerivAt_const t ε).div hd (clock_positive ε _ hε).ne'
  convert h using 1
  simp only [zero_mul,zero_sub,clock]
  ring

theorem defect_strictAntiOn (ε m g κ : ℝ) (hε : 0 < ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 < κ)
    (γ : ℝ → TimePhase) (a b : ℝ)
    (hγ : ∀ t ∈ Icc a b, HasDerivAt γ (field ε m g κ (γ t)) t) :
    StrictAntiOn (fun t => defect ε (q (.inr 0) (γ t).2)) (Icc a b) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc a b)
    (fun t ht => (defect_derivative ε m g κ hε.le γ t (hγ t ht)).continuousAt.continuousWithinAt)
  intro t ht
  rw [(defect_derivative ε m g κ hε.le γ t (hγ t (interior_subset ht))).deriv]
  have hr := clockRate_positive ε m g κ (γ t).1 (q (.inr 0) (γ t).2) (p (.inr 0) (γ t).2)
    hε.le hm hg hκ (γ t).2
  have hc := clock_positive ε (q (.inr 0) (γ t).2) hε.le
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (neg_neg_of_pos hε) (Real.exp_pos _)) hr) (sq_pos_of_pos hc)

#print axioms clock_derivative
#print axioms clockMomentum_derivative
#print axioms clockRate_positive
#print axioms defect_derivative
#print axioms defect_strictAntiOn

end
end UnifiedTheory.Audit.KFCausalClassicalMatterDefect
