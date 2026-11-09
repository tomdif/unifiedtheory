/- A constructive free-sector candidate for the occupation/energy bridge.
The canonical rescaling below is proved for the existing charge-averaged
classical Hamiltonian. Quantizing this normal form and intertwining the
closed quantum operator are further obligations, not assumptions here. -/
import UnifiedTheory.Audit.KFCausalClassicalAveragedVacuum
import UnifiedTheory.Audit.KFCausalOccupationSeries

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalFreeChargedNormalForm
noncomputable section
open KFCausalClassicalChargePhase KFCausalClassicalAveragedVacuum
open KFCausalOccupationSeries
open UnifiedTheory.QSeries PowerSeries

/-- Opposite canonical rescalings of the two charged coordinate pairs.
Clock and homogeneous neutral position/momentum are unchanged. -/
def squeeze (u : ℝ) (z : Phase) : Phase :=
  (WithLp.toLp 2 (fun
    | .inl i => Real.exp (-u) * z.1 (.inl i)
    | .inr i => ![z.1 (.inr 0), Real.exp u * z.1 (.inr 1),
        Real.exp u * z.1 (.inr 2), z.1 (.inr 3)] i),
   WithLp.toLp 2 (fun
    | .inl i => Real.exp u * z.2 (.inl i)
    | .inr i => ![z.2 (.inr 0), Real.exp (-u) * z.2 (.inr 1),
        Real.exp (-u) * z.2 (.inr 2), z.2 (.inr 3)] i))

theorem squeeze_inverse (u : ℝ) (z : Phase) : squeeze (-u) (squeeze u z) = z := by
  ext i <;> rcases i with i | i <;> fin_cases i <;>
    simp [squeeze, ← mul_assoc, ← Real.exp_add]

theorem squeeze_symplectic (u : ℝ) (z w : Phase) :
    symplectic (squeeze u z) (squeeze u w) = symplectic z w := by
  have he (a b v : ℝ) : (Real.exp (-v) * a) * (Real.exp v * b) = a * b := by
    rw [mul_mul_mul_comm, ← Real.exp_add]
    simp
  have he' (a b v : ℝ) : (Real.exp v * a) * (Real.exp (-v) * b) = a * b := by
    simpa only [neg_neg] using he a b (-v)
  simp [symplectic, PiLp.inner_apply, Fintype.sum_sum_type, Fin.sum_univ_succ,
    squeeze, RCLike.inner_apply, he, he']

/-- The canonical transformation respects the existing translation-charge action. -/
theorem squeeze_charge_equivariant (u θ : ℝ) (z : Phase) :
    squeeze u (rotate θ z) = rotate θ (squeeze u z) := by
  ext i <;> rcases i with i | i <;> fin_cases i <;> simp [squeeze, rotate] <;> ring

/-- Four unit-frequency oscillator actions, with neither the clock nor the
neutral homogeneous mode included in the discrete count. -/
def chargedAction (z : Phase) : ℝ :=
  (z.1 (.inl 0)^2 + z.2 (.inl 0)^2 + z.1 (.inl 1)^2 + z.2 (.inl 1)^2 +
    z.1 (.inr 1)^2 + z.2 (.inr 1)^2 + z.1 (.inr 2)^2 + z.2 (.inr 2)^2) / 2

/-- The exact, already charge-averaged free kinetic symbol has an oscillator
normal form after a canonical squeeze. -/
theorem kinetic_normal_form (t : ℝ) (z : Phase) :
    kineticMean t z = Real.exp t * chargedAction (squeeze (t / 2) z) +
      z.2 (.inr 3)^2 / 2 := by
  rw [kineticMean_eq]
  have hp : Real.exp (t / 2)^2 = Real.exp t := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hm : Real.exp (-(t / 2))^2 = Real.exp (-t) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have ht : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  have h2 : Real.exp (2 * t) = Real.exp t ^ 2 := Real.exp_nat_mul t 2
  dsimp [chargedAction, squeeze]
  simp only [mul_pow, hp, hm, h2]
  linear_combination -(z.1 (.inl 0)^2 + z.1 (.inl 1)^2 +
    z.2 (.inr 1)^2 + z.2 (.inr 2)^2) / 2 * ht

/-- In the free classical model the energy is affine in the charged action
at fixed clock and neutral momentum. The spacing depends on the clock. -/
theorem free_hamiltonian_normal_form (ε t s p : ℝ) (z : Phase) :
    hamiltonian ε 0 t z s p = KFCausalClockFloorFlow.clock ε s / 2 +
      (Real.exp t * chargedAction (squeeze (t / 2) z) + z.2 (.inr 3)^2 / 2) /
        KFCausalClockFloorFlow.clock ε s := by
  simp only [hamiltonian, amplitude, zero_mul, add_zero]
  rw [kinetic_normal_form]

/-- The clock is a conserved classical coordinate in this free parameter regime;
fixing it is not a harmonic approximation to an interacting clock. -/
theorem free_clock_rate_zero (ε t s p : ℝ) (z : Phase) :
    clockRate ε 0 t z s p = 0 := by
  simp [clockRate, amplitude]

theorem free_hamiltonian_independent_clock_momentum (ε t s p p' : ℝ) (z : Phase) :
    hamiltonian ε 0 t z s p = hamiltonian ε 0 t z s p' := by
  rw [free_hamiltonian_normal_form, free_hamiltonian_normal_form]

/-- Two positive-charge modes with total occupation p, and two negative-charge
modes with the same total. This is the neutral charged oscillator basis. -/
abbrev BalancedCharged (p : ℕ) :=
  KFCausalOccupationSeries.Shell 2 p p × KFCausalOccupationSeries.Shell 2 p p

theorem balanced_charged_count (p : ℕ) : Fintype.card (BalancedCharged p) = (p + 1)^2 := by
  rw [Fintype.card_prod, card_shell 2 p p (by omega) le_rfl]
  simp [Nat.choose_one_right, pow_two, Nat.add_comm]

/-- The pair-occupation generating function, before any energy interpretation. -/
def chargedPairSeries : PowerSeries ℤ := (1 + X) * (invOneSubPow ℤ 3).val

theorem chargedPairSeries_euler :
    chargedPairSeries = (1 + X) * weightedEuler (occupationMultiplicity 3) := by
  rw [occupation_euler]
  rfl

private theorem adjacent_choose_two (n : ℕ) :
    (n + 2).choose 2 + (n + 1).choose 2 = (n + 1)^2 := by
  have h1 := Nat.add_one_mul_choose_eq (n + 1) 1
  have h0 := Nat.add_one_mul_choose_eq n 1
  simp only [Nat.choose_one_right] at h1 h0
  nlinarith

/-- The neutral charged sector has the exact series `(1+u)/(1-u)^3`,
where `u` counts a positive/negative pair, not an assigned unit of energy. -/
theorem coeff_chargedPairSeries (n : ℕ) :
    coeff n chargedPairSeries = (Fintype.card (BalancedCharged n) : ℤ) := by
  have hc (k : ℕ) : coeff k (invOneSubPow ℤ 3).val = ((k + 2).choose 2 : ℤ) := by
    rw [invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos ℤ 3 (by omega), coeff_mk]
    simp [Nat.add_comm]
  rw [chargedPairSeries, add_mul, one_mul, map_add, balanced_charged_count]
  cases n with
  | zero => simp [hc, coeff_zero_eq_constantCoeff]
  | succ n =>
    rw [mul_comm X, show X = (X : PowerSeries ℤ)^1 from (pow_one _).symm,
      coeff_mul_X_pow, hc, hc]
    exact_mod_cast adjacent_choose_two (n + 1)

end
end UnifiedTheory.Audit.KFCausalFreeChargedNormalForm
