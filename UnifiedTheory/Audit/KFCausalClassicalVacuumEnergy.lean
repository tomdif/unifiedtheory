/- The exact work identity for the full canonical vacuum vector field, with
positive energy and a forward exponential bound on any existence interval.
The energy law follows from the derived Hamiltonian, not a trajectory axiom. -/
import UnifiedTheory.Audit.KFCausalCanonicalPhaseODE

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClassicalVacuumEnergy
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalChargeMean
open UnifiedTheory.Audit.KFCausalClassicalAveragedVacuum
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth
open UnifiedTheory.Audit.KFCausalCanonicalPhaseODE
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (clock_positive)

def staticKinetic (z : Phase) : ℝ :=
  (p (.inr 1) z^2+q (.inl 0) z^2+p (.inr 2) z^2+q (.inl 1) z^2+p (.inr 3) z^2)/2

def growingKinetic (z : Phase) : ℝ :=
  (p (.inl 0) z^2+q (.inr 1) z^2+p (.inl 1) z^2+q (.inr 2) z^2)/2

def growingCoefficient (ε κ : ℝ) (z : Phase) : ℝ :=
  (growingKinetic z+κ*Real.exp (p (.inr 0) z/clock ε (q (.inr 0) z))*
    exponentialMean (clock ε (q (.inr 0) z)) z)/clock ε (q (.inr 0) z)

def growingEnergy (ε κ : ℝ) (x : TimePhase) : ℝ := Real.exp (2*x.1)*growingCoefficient ε κ x.2

theorem hamiltonian_split (ε κ : ℝ) (x : TimePhase) :
    fullHamiltonian ε κ x = clock ε (q (.inr 0) x.2)/2+
      staticKinetic x.2/clock ε (q (.inr 0) x.2)+growingEnergy ε κ x := by
  unfold fullHamiltonian hamiltonian
  rw [kineticMean_eq]
  simp only [growingEnergy, growingCoefficient, growingKinetic, staticKinetic,
    amplitude, q_apply, p_apply, Real.exp_add]
  ring

theorem staticKinetic_nonnegative (z : Phase) : 0 ≤ staticKinetic z := by
  unfold staticKinetic
  positivity

theorem growingKinetic_nonnegative (z : Phase) : 0 ≤ growingKinetic z := by
  unfold growingKinetic
  positivity

theorem growingEnergy_nonnegative (ε κ : ℝ) (hε : 0 ≤ ε) (hκ : 0 ≤ κ) (x : TimePhase) :
    0 ≤ growingEnergy ε κ x := by
  have hc := (clock_positive ε (q (.inr 0) x.2) hε).le
  have hk := growingKinetic_nonnegative x.2
  have hf : 0 ≤ exponentialMean (clock ε (q (.inr 0) x.2)) x.2 :=
    le_trans (by norm_num) (exponentialMean_ge_one _ _)
  unfold growingEnergy growingCoefficient
  positivity

theorem energy_bounds (ε κ : ℝ) (hε : 0 ≤ ε) (hκ : 0 ≤ κ) (x : TimePhase) :
    0 < fullHamiltonian ε κ x ∧ growingEnergy ε κ x ≤ fullHamiltonian ε κ x := by
  rw [hamiltonian_split]
  have hc := clock_positive ε (q (.inr 0) x.2) hε
  have hk := div_nonneg (staticKinetic_nonnegative x.2) hc.le
  have hg := growingEnergy_nonnegative ε κ hε hκ x
  constructor <;> linarith

theorem hamiltonian_time_derivative (ε κ t : ℝ) (z : Phase) :
    HasDerivAt (fun u => fullHamiltonian ε κ (u,z)) (2*growingEnergy ε κ (t,z)) t := by
  have h := ((((hasDerivAt_id t).const_mul 2).exp).mul_const (growingCoefficient ε κ z)).const_add
    (clock ε (q (.inr 0) z)/2+staticKinetic z/clock ε (q (.inr 0) z))
  simp_rw [hamiltonian_split]
  convert h using 1
  simp only [growingEnergy, id_eq]
  ring

theorem time_differential (ε κ : ℝ) (hε : 0 ≤ ε) (x : TimePhase) :
    fderiv ℝ (fullHamiltonian ε κ) x (1,0) = 2*growingEnergy ε κ x := by
  have hd := (fullHamiltonian_contDiff ε κ hε 1).differentiable (by norm_num)
  have ht : HasDerivAt (fun u : ℝ => (u,x.2)) (1,0) x.1 :=
    (hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2)
  have hdx : HasFDerivAt (fullHamiltonian ε κ) (fderiv ℝ (fullHamiltonian ε κ) x) x :=
    (hd x).hasFDerivAt
  have hcomp : HasDerivAt (fun u => fullHamiltonian ε κ (u,x.2))
      (fderiv ℝ (fullHamiltonian ε κ) x (1,0)) x.1 :=
    HasFDerivAt.comp_hasDerivAt (f := fun u : ℝ => (u,x.2))
      (l := fullHamiltonian ε κ) (l' := fderiv ℝ (fullHamiltonian ε κ) x) x.1 hdx ht
  exact hcomp.unique (hamiltonian_time_derivative ε κ x.1 x.2)

theorem energy_derivative (ε κ : ℝ) (hε : 0 ≤ ε) (γ : ℝ → TimePhase) (t : ℝ)
    (hγ : HasDerivAt γ (field ε κ (γ t)) t) :
    HasDerivAt (fun u => fullHamiltonian ε κ (γ u)) (2*growingEnergy ε κ (γ t)) t := by
  have h := (((fullHamiltonian_contDiff ε κ hε 1).differentiable (by norm_num)) (γ t)).hasFDerivAt.comp_hasDerivAt t hγ
  simpa only [hamiltonian_field, time_differential ε κ hε] using h

theorem weighted_energy_derivative (ε κ : ℝ) (hε : 0 ≤ ε) (γ : ℝ → TimePhase) (t : ℝ)
    (hγ : HasDerivAt γ (field ε κ (γ t)) t) :
    HasDerivAt (fun u => Real.exp (-2*u)*fullHamiltonian ε κ (γ u))
      (Real.exp (-2*t)*2*(growingEnergy ε κ (γ t)-fullHamiltonian ε κ (γ t))) t := by
  convert (((hasDerivAt_id t).const_mul (-2)).exp).mul (energy_derivative ε κ hε γ t hγ) using 1
  simp only [id_eq]
  ring

theorem energy_forward_bound (ε κ : ℝ) (hε : 0 ≤ ε) (hκ : 0 ≤ κ)
    (γ : ℝ → TimePhase) (a b : ℝ) (hab : a ≤ b)
    (hγ : ∀ t ∈ Icc a b, HasDerivAt γ (field ε κ (γ t)) t) :
    fullHamiltonian ε κ (γ b) ≤ Real.exp (2*(b-a))*fullHamiltonian ε κ (γ a) := by
  have hm : AntitoneOn (fun t => Real.exp (-2*t)*fullHamiltonian ε κ (γ t)) (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
      (fun t ht => (weighted_energy_derivative ε κ hε γ t (hγ t ht)).continuousAt.continuousWithinAt)
      (fun t ht => (weighted_energy_derivative ε κ hε γ t (hγ t (interior_subset ht))).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(weighted_energy_derivative ε κ hε γ t (hγ t (interior_subset ht))).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (sub_nonpos.mpr (energy_bounds ε κ hε hκ (γ t)).2)
  have hb := mul_le_mul_of_nonneg_left (hm ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab) (Real.exp_pos (2*b)).le
  have hcancel : Real.exp (2*b)*Real.exp (-2*b) = 1 := by
    rw [← Real.exp_add, show 2*b+-2*b = 0 by ring, Real.exp_zero]
  have htimes : Real.exp (2*b)*Real.exp (-2*a) = Real.exp (2*(b-a)) := by
    rw [← Real.exp_add]; congr 1; ring
  simpa only [← mul_assoc,hcancel,htimes,one_mul] using hb

theorem energy_monotoneOn (ε κ : ℝ) (hε : 0 ≤ ε) (hκ : 0 ≤ κ)
    (γ : ℝ → TimePhase) (a b : ℝ)
    (hγ : ∀ t ∈ Icc a b, HasDerivAt γ (field ε κ (γ t)) t) :
    MonotoneOn (fun t => fullHamiltonian ε κ (γ t)) (Icc a b) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    (fun t ht => (energy_derivative ε κ hε γ t (hγ t ht)).continuousAt.continuousWithinAt)
    (fun t ht => (energy_derivative ε κ hε γ t (hγ t (interior_subset ht))).differentiableAt.differentiableWithinAt)
  intro t ht
  rw [(energy_derivative ε κ hε γ t (hγ t (interior_subset ht))).deriv]
  exact mul_nonneg (by norm_num) (growingEnergy_nonnegative ε κ hε hκ (γ t))

theorem energy_interval_bound (ε κ : ℝ) (hε : 0 ≤ ε) (hκ : 0 ≤ κ)
    (γ : ℝ → TimePhase) (T : ℝ) (hT : 0 ≤ T)
    (hγ : ∀ t ∈ Icc (-T) T, HasDerivAt γ (field ε κ (γ t)) t)
    (t : ℝ) (ht : t ∈ Icc (-T) T) :
    fullHamiltonian ε κ (γ t) ≤ Real.exp (2*T)*fullHamiltonian ε κ (γ 0) := by
  have hH := (energy_bounds ε κ hε hκ (γ 0)).1.le
  by_cases h0 : 0 ≤ t
  · have h := energy_forward_bound ε κ hε hκ γ 0 t h0
      (fun u hu => hγ u ⟨by linarith [hu.1],hu.2.trans ht.2⟩)
    simp only [sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [ht.2])) hH)
  · have h := energy_monotoneOn ε κ hε hκ γ (-T) T hγ ht ⟨by linarith,hT⟩ (le_of_not_ge h0)
    exact h.trans (le_mul_of_one_le_left hH (Real.one_le_exp (by positivity)))

#print axioms hamiltonian_split
#print axioms staticKinetic_nonnegative
#print axioms growingKinetic_nonnegative
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
end UnifiedTheory.Audit.KFCausalClassicalVacuumEnergy
