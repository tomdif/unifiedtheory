/- Counting the actual zero-charge sector, and identifying the constraint kernel.
These are occupation characters; no identification with thermal energy is assumed. -/
import UnifiedTheory.Audit.KFCausalOccupationSeries
import UnifiedTheory.Audit.KFCausalReducedSpinHamiltonian
import Mathlib.Data.Fin.Tuple.NatAntidiagonal

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalOccupationConstraintSeries
noncomputable section
open scoped BigOperators
open Matrix PowerSeries
open KFCausalFiniteOccupationLadders KFCausalOccupationSeries
open KFCausalSpinSourceIdentity KFCausalQuantumConstraintReduction
open KFCausalConcreteClockConstraint

abbrev NeutralShell (R n : ℕ) := {v : State R // total v.val = n ∧ charge v = 0}
abbrev NeutralState (R : ℕ) := {v : State R // charge v = 0}

/-- Translation charge of an unbounded occupation tuple, with the model's signs. -/
def tupleCharge (v : Fin 6 → ℕ) : ℤ := (v 1 : ℤ) - v 2 + v 3 - v 4

/-- Computable enumeration at every degree, independent of the capacity. -/
def neutralTuples (n : ℕ) : Finset (Fin 6 → ℕ) :=
  (Finset.Nat.antidiagonalTuple 6 n).filter (fun v => tupleCharge v = 0)

def neutralCoefficient (n : ℕ) : ℕ := (neutralTuples n).card

def neutralShellEquivTuples (R n : ℕ) (hn : n ≤ R) :
    NeutralShell R n ≃ ↥(neutralTuples n) where
  toFun v := ⟨fun a => (v.val.val a : ℕ), by
    simp only [neutralTuples, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]
    exact v.property⟩
  invFun v :=
    let s := (shellEquivNatSum 6 R n hn).symm
      ⟨v.val, (Finset.Nat.mem_antidiagonalTuple.mp (Finset.mem_filter.mp v.property).1)⟩
    ⟨s.val, s.property, (Finset.mem_filter.mp v.property).2⟩
  left_inv v := rfl
  right_inv v := rfl

theorem card_neutralShell (R n : ℕ) (hn : n ≤ R) :
    Fintype.card (NeutralShell R n) = neutralCoefficient n := by
  rw [Fintype.card_congr (neutralShellEquivTuples R n hn), Fintype.card_coe]
  rfl

/-- The capacity-independent series obtained by enumerating actual neutral tuples. -/
def neutralSeries : PowerSeries ℤ := mk (fun n => (neutralCoefficient n : ℤ))

def neutralCharacter (R : ℕ) : PowerSeries ℤ :=
  ∑ v : State R, if charge v = 0 then X ^ total v.val else 0

theorem coeff_neutralCharacter (R n : ℕ) :
    coeff n (neutralCharacter R) = (Fintype.card (NeutralShell R n) : ℤ) := by
  classical
  simp only [neutralCharacter, map_sum, apply_ite, coeff_X_pow, map_zero,
    NeutralShell, Fintype.card_subtype, Finset.card_eq_sum_ones, Nat.cast_sum,
    Nat.cast_one, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hq : charge v = 0
  · by_cases hn : total v.val = n
    · simp [hq, hn]
    · simp [hq, hn, Ne.symm hn]
  · simp [hq]

theorem neutralCharacter_matches_series (R n : ℕ) (hn : n ≤ R) :
    coeff n (neutralCharacter R) = coeff n neutralSeries := by
  rw [coeff_neutralCharacter, card_neutralShell R n hn]
  simp [neutralSeries]

theorem neutral_shell_dimension (R n : ℕ) (hn : n ≤ R) :
    (Module.finrank ℂ (NeutralShell R n → ℂ) : ℤ) = coeff n neutralSeries := by
  rw [Module.finrank_fintype_fun_eq_card, card_neutralShell R n hn]
  simp [neutralSeries]

/-- Unit radial weights make the diagonal constraint coefficient nonzero,
including at the capacity boundary. Degenerate radial weights need not do so. -/
theorem unit_coefficient_ne_zero (R : ℕ) (hbar : ℝ) (hh : hbar ≠ 0) (v : State R) :
    coefficient (fun _ => 1) hbar v ≠ 0 := by
  have hc : (hbar : ℂ) ≠ 0 := by exact_mod_cast hh
  by_cases ht : total v.val + 1 ≤ R <;>
    simp [coefficient, weight, v.property, ht, hc]

/-- Exact kernel membership for the existing reconstructed constraint.
The nonvanishing hypothesis rules out extra kernel states from zero radial weights. -/
theorem constraint_kernel_iff (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ)
    (hc : ∀ v : State R, coefficient r hbar v ≠ 0) (f : State R → ℂ) :
    (constraint R r hbar).mulVec f = 0 ↔ ∀ v, charge v ≠ 0 → f v = 0 := by
  rw [concrete_constraint_identity, source_mean]
  simp only [funext_iff, mulVec_diagonal, Pi.zero_apply]
  constructor
  · intro hf v hv
    have hz : (charge v : ℂ) ≠ 0 := by exact_mod_cast hv
    exact (mul_eq_zero.mp (hf v)).resolve_left (mul_ne_zero (hc v) hz)
  · intro hf v
    by_cases hv : charge v = 0
    · simp [hv]
    · simp [hf v hv]

/-- Extension by zero identifies neutral amplitudes with the actual constraint kernel. -/
def neutralEquivKernel (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ)
    (hc : ∀ v : State R, coefficient r hbar v ≠ 0) :
    (NeutralState R → ℂ) ≃ₗ[ℂ] LinearMap.ker (Matrix.mulVecLin (constraint R r hbar)) where
  toFun f := ⟨fun v => if h : charge v = 0 then f ⟨v, h⟩ else 0, by
    apply (constraint_kernel_iff R r hbar hc _).mpr
    intro v hv
    simp [hv]⟩
  invFun f v := f.val v.val
  left_inv f := by funext v; simp [v.property]
  right_inv f := by
    apply Subtype.ext
    funext v
    by_cases hv : charge v = 0
    · simp [hv]
    · simp [hv, (constraint_kernel_iff R r hbar hc f.val).mp f.property v hv]
  map_add' f g := by
    apply Subtype.ext
    funext v
    by_cases hv : charge v = 0 <;> simp [hv]
  map_smul' c f := by
    apply Subtype.ext
    funext v
    by_cases hv : charge v = 0 <;> simp [hv]

theorem constraint_kernel_dimension (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ)
    (hc : ∀ v : State R, coefficient r hbar v ≠ 0) :
    Module.finrank ℂ (LinearMap.ker (Matrix.mulVecLin (constraint R r hbar))) =
      Fintype.card (NeutralState R) := by
  rw [← (neutralEquivKernel R r hbar hc).finrank_eq, Module.finrank_fintype_fun_eq_card]

def neutralStateEquivShells (R : ℕ) :
    NeutralState R ≃ Σ n : Fin (R + 1), NeutralShell R n.val where
  toFun v := ⟨⟨total v.val.val, Nat.lt_succ_of_le v.val.property⟩,
    v.val, rfl, v.property⟩
  invFun v := ⟨v.2.val, v.2.property.2⟩
  left_inv v := rfl
  right_inv v := by
    rcases v with ⟨⟨n, hn⟩, v, hs, hc⟩
    dsimp at hs
    subst n
    rfl

/-- A computable all-capacity formula for the actual kernel dimension,
under the explicit nondegeneracy condition. -/
theorem constraint_kernel_dimension_series (R : ℕ) (r : ℕ → ℝ) (hbar : ℝ)
    (hc : ∀ v : State R, coefficient r hbar v ≠ 0) :
    Module.finrank ℂ (LinearMap.ker (Matrix.mulVecLin (constraint R r hbar))) =
      ∑ n : Fin (R + 1), neutralCoefficient n.val := by
  rw [constraint_kernel_dimension R r hbar hc,
    Fintype.card_congr (neutralStateEquivShells R), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro n _
  exact card_neutralShell R n.val (Nat.le_of_lt_succ n.isLt)

/-- The constraint commutes with every occupation-shell projector. -/
theorem constraint_commutes_occupation (R n : ℕ) (r : ℕ → ℝ) (hbar : ℝ) :
    Commute (constraint R r hbar)
      (diagonal (fun v : State R => if total v.val = n then (1 : ℂ) else 0)) := by
  rw [concrete_constraint_identity, source_mean]
  exact Matrix.commute_diagonal _ _

/-- The actual polynomial Hamiltonian preserves translation charge.
This does not assert preservation of total occupation. -/
theorem hamiltonian_preserves_neutral (R : ℕ) (r : ℕ → ℝ)
    (hbar mass2 quartic vacuum t : ℝ) :
    Commute (KFCausalReducedSpinHamiltonian.hamiltonian R r hbar mass2 quartic vacuum t)
      (sector charge 0) :=
  dephase_commutes_sector charge _ 0

/-- Exact coefficients from enumeration, not a supplied degeneracy table. -/
theorem neutral_coefficients_through_four :
    neutralCoefficient 0 = 1 ∧ neutralCoefficient 1 = 2 ∧
    neutralCoefficient 2 = 7 ∧ neutralCoefficient 3 = 12 ∧ neutralCoefficient 4 = 26 := by
  decide

end
end UnifiedTheory.Audit.KFCausalOccupationConstraintSeries
