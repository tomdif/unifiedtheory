/- The exact work identity and finite-window energy bound persist for the
full nonnegative mass and quartic candidate under its derived canonical ODE. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterODE
import UnifiedTheory.Audit.KFCausalClassicalVacuumEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClassicalMatterEnergy
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalMatterSymbols
open UnifiedTheory.Audit.KFCausalClassicalMatterHamiltonian
open UnifiedTheory.Audit.KFCausalClassicalMatterSmooth
open UnifiedTheory.Audit.KFCausalClassicalMatterODE
open UnifiedTheory.Audit.KFCausalClassicalAveragedVacuum (kineticMean_eq)
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth (q p q_apply p_apply TimePhase)
open UnifiedTheory.Audit.KFCausalClassicalVacuumEnergy (staticKinetic growingKinetic staticKinetic_nonnegative growingKinetic_nonnegative)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (clock_positive)

def growingCoefficient (ε m g κ : ℝ) (z : Phase) : ℝ :=
  (growingKinetic z+Real.exp (p (.inr 0) z/clock ε (q (.inr 0) z))*
    weightedMean m g κ (clock ε (q (.inr 0) z)) z)/clock ε (q (.inr 0) z)

def growingEnergy (ε m g κ : ℝ) (x : TimePhase) : ℝ := Real.exp (2*x.1)*growingCoefficient ε m g κ x.2

theorem hamiltonian_split (ε m g κ : ℝ) (x : TimePhase) :
    fullHamiltonian ε m g κ x = clock ε (q (.inr 0) x.2)/2+
      staticKinetic x.2/clock ε (q (.inr 0) x.2)+growingEnergy ε m g κ x := by
  unfold fullHamiltonian hamiltonian
  rw [kineticMean_eq]
  simp only [growingEnergy, growingCoefficient, growingKinetic, staticKinetic,
    amplitude, q_apply, p_apply, Real.exp_add]
  ring

theorem growingEnergy_nonnegative (ε m g κ : ℝ) (hε : 0 ≤ ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ) (x : TimePhase) :
    0 ≤ growingEnergy ε m g κ x := by
  have hc := (clock_positive ε (q (.inr 0) x.2) hε).le
  have hk := growingKinetic_nonnegative x.2
  have hf : 0 ≤ weightedMean m g κ (clock ε (q (.inr 0) x.2)) x.2 :=
    le_trans hκ (weightedMean_lower m g κ _ hm hg hκ _)
  unfold growingEnergy growingCoefficient
  positivity

theorem energy_bounds (ε m g κ : ℝ) (hε : 0 ≤ ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ) (x : TimePhase) :
    0 < fullHamiltonian ε m g κ x ∧ growingEnergy ε m g κ x ≤ fullHamiltonian ε m g κ x := by
  rw [hamiltonian_split]
  have hc := clock_positive ε (q (.inr 0) x.2) hε
  have hk := div_nonneg (staticKinetic_nonnegative x.2) hc.le
  have hg := growingEnergy_nonnegative ε m g κ hε hm hg hκ x
  constructor <;> linarith

theorem hamiltonian_time_derivative (ε m g κ t : ℝ) (z : Phase) :
    HasDerivAt (fun u => fullHamiltonian ε m g κ (u,z)) (2*growingEnergy ε m g κ (t,z)) t := by
  have h := ((((hasDerivAt_id t).const_mul 2).exp).mul_const (growingCoefficient ε m g κ z)).const_add
    (clock ε (q (.inr 0) z)/2+staticKinetic z/clock ε (q (.inr 0) z))
  simp_rw [hamiltonian_split]
  convert h using 1
  simp only [growingEnergy, id_eq]
  ring

theorem time_differential (ε m g κ : ℝ) (hε : 0 ≤ ε) (x : TimePhase) :
    fderiv ℝ (fullHamiltonian ε m g κ) x (1,0) = 2*growingEnergy ε m g κ x := by
  have hd := (fullHamiltonian_contDiff ε m g κ hε 1).differentiable (by norm_num)
  have ht : HasDerivAt (fun u : ℝ => (u,x.2)) (1,0) x.1 :=
    (hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2)
  have hdx : HasFDerivAt (fullHamiltonian ε m g κ) (fderiv ℝ (fullHamiltonian ε m g κ) x) x :=
    (hd x).hasFDerivAt
  have hcomp : HasDerivAt (fun u => fullHamiltonian ε m g κ (u,x.2))
      (fderiv ℝ (fullHamiltonian ε m g κ) x (1,0)) x.1 :=
    HasFDerivAt.comp_hasDerivAt (f := fun u : ℝ => (u,x.2))
      (l := fullHamiltonian ε m g κ) (l' := fderiv ℝ (fullHamiltonian ε m g κ) x) x.1 hdx ht
  exact hcomp.unique (hamiltonian_time_derivative ε m g κ x.1 x.2)

theorem energy_derivative (ε m g κ : ℝ) (hε : 0 ≤ ε) (γ : ℝ → TimePhase) (t : ℝ)
    (hγ : HasDerivAt γ (field ε m g κ (γ t)) t) :
    HasDerivAt (fun u => fullHamiltonian ε m g κ (γ u)) (2*growingEnergy ε m g κ (γ t)) t := by
  have h := (((fullHamiltonian_contDiff ε m g κ hε 1).differentiable (by norm_num)) (γ t)).hasFDerivAt.comp_hasDerivAt t hγ
  simpa only [hamiltonian_field, time_differential ε m g κ hε] using h

theorem weighted_energy_derivative (ε m g κ : ℝ) (hε : 0 ≤ ε) (γ : ℝ → TimePhase) (t : ℝ)
    (hγ : HasDerivAt γ (field ε m g κ (γ t)) t) :
    HasDerivAt (fun u => Real.exp (-2*u)*fullHamiltonian ε m g κ (γ u))
      (Real.exp (-2*t)*2*(growingEnergy ε m g κ (γ t)-fullHamiltonian ε m g κ (γ t))) t := by
  convert (((hasDerivAt_id t).const_mul (-2)).exp).mul (energy_derivative ε m g κ hε γ t hγ) using 1
  simp only [id_eq]
  ring

theorem energy_forward_bound (ε m g κ : ℝ) (hε : 0 ≤ ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (γ : ℝ → TimePhase) (a b : ℝ) (hab : a ≤ b)
    (hγ : ∀ t ∈ Icc a b, HasDerivAt γ (field ε m g κ (γ t)) t) :
    fullHamiltonian ε m g κ (γ b) ≤ Real.exp (2*(b-a))*fullHamiltonian ε m g κ (γ a) := by
  have hm : AntitoneOn (fun t => Real.exp (-2*t)*fullHamiltonian ε m g κ (γ t)) (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
      (fun t ht => (weighted_energy_derivative ε m g κ hε γ t (hγ t ht)).continuousAt.continuousWithinAt)
      (fun t ht => (weighted_energy_derivative ε m g κ hε γ t (hγ t (interior_subset ht))).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(weighted_energy_derivative ε m g κ hε γ t (hγ t (interior_subset ht))).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (sub_nonpos.mpr (energy_bounds ε m g κ hε hm hg hκ (γ t)).2)
  have hb := mul_le_mul_of_nonneg_left (hm ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab) (Real.exp_pos (2*b)).le
  have hcancel : Real.exp (2*b)*Real.exp (-2*b) = 1 := by
    rw [← Real.exp_add, show 2*b+-2*b = 0 by ring, Real.exp_zero]
  have htimes : Real.exp (2*b)*Real.exp (-2*a) = Real.exp (2*(b-a)) := by
    rw [← Real.exp_add]; congr 1; ring
  simpa only [← mul_assoc,hcancel,htimes,one_mul] using hb

theorem energy_monotoneOn (ε m g κ : ℝ) (hε : 0 ≤ ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (γ : ℝ → TimePhase) (a b : ℝ)
    (hγ : ∀ t ∈ Icc a b, HasDerivAt γ (field ε m g κ (γ t)) t) :
    MonotoneOn (fun t => fullHamiltonian ε m g κ (γ t)) (Icc a b) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    (fun t ht => (energy_derivative ε m g κ hε γ t (hγ t ht)).continuousAt.continuousWithinAt)
    (fun t ht => (energy_derivative ε m g κ hε γ t (hγ t (interior_subset ht))).differentiableAt.differentiableWithinAt)
  intro t ht
  rw [(energy_derivative ε m g κ hε γ t (hγ t (interior_subset ht))).deriv]
  exact mul_nonneg (by norm_num) (growingEnergy_nonnegative ε m g κ hε hm hg hκ (γ t))

theorem energy_interval_bound (ε m g κ : ℝ) (hε : 0 ≤ ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (γ : ℝ → TimePhase) (T : ℝ) (hT : 0 ≤ T)
    (hγ : ∀ t ∈ Icc (-T) T, HasDerivAt γ (field ε m g κ (γ t)) t)
    (t : ℝ) (ht : t ∈ Icc (-T) T) :
    fullHamiltonian ε m g κ (γ t) ≤ Real.exp (2*T)*fullHamiltonian ε m g κ (γ 0) := by
  have hH := (energy_bounds ε m g κ hε hm hg hκ (γ 0)).1.le
  by_cases h0 : 0 ≤ t
  · have h := energy_forward_bound ε m g κ hε hm hg hκ γ 0 t h0
      (fun u hu => hγ u ⟨by linarith [hu.1],hu.2.trans ht.2⟩)
    simp only [sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [ht.2])) hH)
  · have h := energy_monotoneOn ε m g κ hε hm hg hκ γ (-T) T hγ ht ⟨by linarith,hT⟩ (le_of_not_ge h0)
    exact h.trans (le_mul_of_one_le_left hH (Real.one_le_exp (by positivity)))

#print axioms hamiltonian_split
#print axioms growingEnergy_nonnegative
#print axioms energy_bounds
#print axioms hamiltonian_time_derivative
#print axioms time_differential
#print axioms energy_derivative
#print axioms weighted_energy_derivative
#print axioms energy_forward_bound
#print axioms energy_monotoneOn
#print axioms energy_interval_bound

end
end UnifiedTheory.Audit.KFCausalClassicalMatterEnergy
