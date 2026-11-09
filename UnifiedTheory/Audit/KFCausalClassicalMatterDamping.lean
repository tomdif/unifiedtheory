/- Phase damping is an auxiliary device for constructing solutions. It
preserves the exact work law because canonical phase motion is tangent to
the instantaneous energy levels. No damping is added to the physical model. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterEnergy
import UnifiedTheory.Audit.KFCausalClassicalMatterClock

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClassicalMatterDamping
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalMatterSmooth
open UnifiedTheory.Audit.KFCausalClassicalMatterODE
open UnifiedTheory.Audit.KFCausalClassicalMatterEnergy
open UnifiedTheory.Audit.KFCausalClassicalMatterHamiltonian
open UnifiedTheory.Audit.KFCausalClassicalMatterClock

open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth (q p TimePhase)
open UnifiedTheory.Audit.KFCausalCanonicalPhaseODE (poisson stateInclusion dual_poisson_zero)

def dampedField (ε m g κ c : ℝ) (x : TimePhase) : TimePhase := (1,c • (field ε m g κ x).2)

theorem dampedField_one (ε m g κ : ℝ) (x : TimePhase) : dampedField ε m g κ 1 x = field ε m g κ x := by
  simp [dampedField,field]

theorem dampedField_contDiff (ε m g κ : ℝ) (hε : 0 ≤ ε) (χ : TimePhase → ℝ)
    (hχ : ContDiff ℝ 1 χ) : ContDiff ℝ 1 (fun x => dampedField ε m g κ (χ x) x) :=
  contDiff_const.prodMk (hχ.smul (field_contDiff ε m g κ hε).snd)

theorem hamiltonian_damped (ε m g κ c : ℝ) (x : TimePhase) :
    fderiv ℝ (fullHamiltonian ε m g κ) x (dampedField ε m g κ c x) =
      fderiv ℝ (fullHamiltonian ε m g κ) x (1,0) := by
  let l := fderiv ℝ (fullHamiltonian ε m g κ) x
  change l (1,c • poisson (l.comp stateInclusion)) = l (1,0)
  rw [show (1,c • poisson (l.comp stateInclusion)) =
    (1,0)+c • stateInclusion (poisson (l.comp stateInclusion)) by simp [stateInclusion], map_add,map_smul]
  have h : l (stateInclusion (poisson (l.comp stateInclusion))) = 0 :=
    dual_poisson_zero (l.comp stateInclusion)
  rw [h,smul_zero,add_zero]

theorem damped_clock (ε m g κ c : ℝ) (hε : 0 ≤ ε) (x : TimePhase) :
    q (.inr 0) (dampedField ε m g κ c x).2 =
      c*clockRate ε m g κ x.1 x.2 (q (.inr 0) x.2) (p (.inr 0) x.2) := by
  simp only [dampedField,map_smul,smul_eq_mul,field_clock ε m g κ hε]

theorem damped_clockMomentum (ε m g κ c : ℝ) (hε : 0 ≤ ε) (x : TimePhase) :
    p (.inr 0) (dampedField ε m g κ c x).2 =
      c*momentumRate ε m g κ x.1 x.2 (q (.inr 0) x.2) (p (.inr 0) x.2) := by
  simp only [dampedField,map_smul,smul_eq_mul,field_clockMomentum ε m g κ hε]

theorem energy_derivative (ε m g κ : ℝ) (hε : 0 ≤ ε) (c : ℝ → ℝ) (γ : ℝ → TimePhase) (t : ℝ)
    (hγ : HasDerivAt γ (dampedField ε m g κ (c t) (γ t)) t) :
    HasDerivAt (fun u => fullHamiltonian ε m g κ (γ u)) (2*growingEnergy ε m g κ (γ t)) t := by
  have h := (((fullHamiltonian_contDiff ε m g κ hε 1).differentiable (by norm_num)) (γ t)).hasFDerivAt.comp_hasDerivAt t hγ
  simpa only [hamiltonian_damped, time_differential ε m g κ hε] using h

theorem weighted_energy_derivative (ε m g κ : ℝ) (hε : 0 ≤ ε) (c : ℝ → ℝ) (γ : ℝ → TimePhase) (t : ℝ)
    (hγ : HasDerivAt γ (dampedField ε m g κ (c t) (γ t)) t) :
    HasDerivAt (fun u => Real.exp (-2*u)*fullHamiltonian ε m g κ (γ u))
      (Real.exp (-2*t)*2*(growingEnergy ε m g κ (γ t)-fullHamiltonian ε m g κ (γ t))) t := by
  convert (((hasDerivAt_id t).const_mul (-2)).exp).mul (energy_derivative ε m g κ hε c γ t hγ) using 1
  simp only [id_eq]
  ring

theorem energy_forward_bound (ε m g κ : ℝ) (hε : 0 ≤ ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (c : ℝ → ℝ) (γ : ℝ → TimePhase) (a b : ℝ) (hab : a ≤ b)
    (hγ : ∀ t ∈ Icc a b, HasDerivAt γ (dampedField ε m g κ (c t) (γ t)) t) :
    fullHamiltonian ε m g κ (γ b) ≤ Real.exp (2*(b-a))*fullHamiltonian ε m g κ (γ a) := by
  have hm : AntitoneOn (fun t => Real.exp (-2*t)*fullHamiltonian ε m g κ (γ t)) (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
      (fun t ht => (weighted_energy_derivative ε m g κ hε c γ t (hγ t ht)).continuousAt.continuousWithinAt)
      (fun t ht => (weighted_energy_derivative ε m g κ hε c γ t (hγ t (interior_subset ht))).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(weighted_energy_derivative ε m g κ hε c γ t (hγ t (interior_subset ht))).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (sub_nonpos.mpr (energy_bounds ε m g κ hε hm hg hκ (γ t)).2)
  have hb := mul_le_mul_of_nonneg_left (hm ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab) (Real.exp_pos (2*b)).le
  have hcancel : Real.exp (2*b)*Real.exp (-2*b) = 1 := by
    rw [← Real.exp_add, show 2*b+-2*b = 0 by ring, Real.exp_zero]
  have htimes : Real.exp (2*b)*Real.exp (-2*a) = Real.exp (2*(b-a)) := by
    rw [← Real.exp_add]; congr 1; ring
  simpa only [← mul_assoc,hcancel,htimes,one_mul] using hb

theorem energy_monotoneOn (ε m g κ : ℝ) (hε : 0 ≤ ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (c : ℝ → ℝ) (γ : ℝ → TimePhase) (a b : ℝ)
    (hγ : ∀ t ∈ Icc a b, HasDerivAt γ (dampedField ε m g κ (c t) (γ t)) t) :
    MonotoneOn (fun t => fullHamiltonian ε m g κ (γ t)) (Icc a b) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    (fun t ht => (energy_derivative ε m g κ hε c γ t (hγ t ht)).continuousAt.continuousWithinAt)
    (fun t ht => (energy_derivative ε m g κ hε c γ t (hγ t (interior_subset ht))).differentiableAt.differentiableWithinAt)
  intro t ht
  rw [(energy_derivative ε m g κ hε c γ t (hγ t (interior_subset ht))).deriv]
  exact mul_nonneg (by norm_num) (growingEnergy_nonnegative ε m g κ hε hm hg hκ (γ t))

theorem energy_interval_bound (ε m g κ : ℝ) (hε : 0 ≤ ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (c : ℝ → ℝ) (γ : ℝ → TimePhase) (T : ℝ) (hT : 0 ≤ T)
    (hγ : ∀ t ∈ Icc (-T) T, HasDerivAt γ (dampedField ε m g κ (c t) (γ t)) t)
    (t : ℝ) (ht : t ∈ Icc (-T) T) :
    fullHamiltonian ε m g κ (γ t) ≤ Real.exp (2*T)*fullHamiltonian ε m g κ (γ 0) := by
  have hH := (energy_bounds ε m g κ hε hm hg hκ (γ 0)).1.le
  by_cases h0 : 0 ≤ t
  · have h := energy_forward_bound ε m g κ hε hm hg hκ c γ 0 t h0
      (fun u hu => hγ u ⟨by linarith [hu.1],hu.2.trans ht.2⟩)
    simp only [sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [ht.2])) hH)
  · have h := energy_monotoneOn ε m g κ hε hm hg hκ c γ (-T) T hγ ht ⟨by linarith,hT⟩ (le_of_not_ge h0)
    exact h.trans (le_mul_of_one_le_left hH (Real.one_le_exp (by positivity)))

#print axioms dampedField_one
#print axioms dampedField_contDiff
#print axioms hamiltonian_damped
#print axioms damped_clock
#print axioms damped_clockMomentum
#print axioms energy_derivative
#print axioms weighted_energy_derivative
#print axioms energy_forward_bound
#print axioms energy_monotoneOn
#print axioms energy_interval_bound

end
end UnifiedTheory.Audit.KFCausalClassicalMatterDamping
