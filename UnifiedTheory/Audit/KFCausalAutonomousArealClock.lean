/-
  Explicit positive autonomous completion of the canonical areal target.
  H = Pc²/(2M) + (v²+omega² u²+u²/(4T²))/2, T>0.
  The u²/(8T²) interaction is a stated change of the free parent, selected
  by the previously derived areal equation. It is not claimed to be an
  emergent interaction of the original spin Hamiltonian.

  Proves clock backreaction, total-energy conservation along solutions,
  and an explicit relational vector-field error on an energy band.
  Finite-spin realization, locality, solution existence and quantum limits
  are separate obligations.
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalAutonomousArealClock
noncomputable section

def waveEnergy (ω2 T u v : ℝ) : ℝ := (v^2+ω2*u^2+u^2/(4*T^2))/2
def totalEnergy (M ω2 T pc u v : ℝ) : ℝ := pc^2/(2*M)+waveEnergy ω2 T u v

theorem autonomous_energy_nonnegative (M ω2 T pc u v : ℝ) (hM : 0 < M) (hω : 0 ≤ ω2) :
    0 ≤ totalEnergy M ω2 T pc u v := by
  unfold totalEnergy waveEnergy
  positivity

/-- This force is part of the autonomous model, not an externally fixed
clock trajectory. It accelerates the positive clock branch. -/
theorem clock_force (M ω2 T pc u v : ℝ) (hT : T ≠ 0) :
    HasDerivAt (fun x => totalEnergy M ω2 x pc u v) (-(u^2/(4*T^3))) T := by
  have hd := (hasDerivAt_const T (u^2)).div
    (((hasDerivAt_id T).pow 2).const_mul 4) (by dsimp; positivity)
  have hd2 := ((hasDerivAt_const T (v^2+ω2*u^2)).add hd).div_const 2
  convert hd2.const_add (pc^2/(2*M)) using 1
  dsimp
  field_simp
  ring

/-- Wave energy decreases by precisely the work delivered to the clock. -/
theorem autonomous_wave_energy_derivative
    (T pc u v : ℝ → ℝ) (M ω2 s : ℝ) (hT0 : T s ≠ 0) (hM : M ≠ 0)
    (hT : HasDerivAt T (pc s/M) s)
    (hu : HasDerivAt u (v s) s)
    (hv : HasDerivAt v (-ω2*u s-u s/(4*(T s)^2)) s) :
    HasDerivAt (fun t => waveEnergy ω2 (T t) (u t) (v t))
      (-(u s)^2*pc s/(4*M*(T s)^3)) s := by
  have hd := ((hv.pow 2).add ((hu.pow 2).const_mul ω2)).add
    ((hu.pow 2).div ((hT.pow 2).const_mul 4) (by dsimp; positivity))
  convert hd.div_const 2 using 1
  dsimp
  field_simp
  ring

theorem autonomous_total_energy_derivative
    (T pc u v : ℝ → ℝ) (M ω2 s : ℝ) (hT0 : T s ≠ 0) (hM : M ≠ 0)
    (hT : HasDerivAt T (pc s/M) s)
    (hpc : HasDerivAt pc ((u s)^2/(4*(T s)^3)) s)
    (hu : HasDerivAt u (v s) s)
    (hv : HasDerivAt v (-ω2*u s-u s/(4*(T s)^2)) s) :
    HasDerivAt (fun t => totalEnergy M ω2 (T t) (pc t) (u t) (v t)) 0 s := by
  have hd := ((hpc.pow 2).div_const (2*M)).add
    (autonomous_wave_energy_derivative T pc u v M ω2 s hT0 hM hT hu hv)
  convert hd using 1
  dsimp
  field_simp
  ring

theorem energy_shell_clock_speed (M ω2 T pc u v : ℝ) (hM : M ≠ 0)
    (hE : totalEnergy M ω2 T pc u v = M/2) :
    (pc/M)^2 = 1-2*waveEnergy ω2 T u v/M := by
  unfold totalEnergy at hE
  field_simp at hE ⊢
  nlinarith

/-- The actual clock's reciprocal speed approaches one uniformly on a
fixed wave-energy band, including its backreaction. -/
theorem relational_clock_rate_bound (M energy e w : ℝ)
    (hM : 0 < M) (henergy : 0 ≤ energy) (he : energy ≤ e)
    (heM : e ≤ 3*M/8) (hw : 0 < w)
    (hshell : w^2 = 1-2*energy/M) :
    1/2 ≤ w ∧ w ≤ 1 ∧ 0 ≤ 1/w-1 ∧ 1/w-1 ≤ 4*e/M := by
  have hid : M*w^2 = M-2*energy := by
    field_simp at hshell
    nlinarith
  have hs1 : w^2 ≤ 1 := by
    rw [hshell]
    have hn : 0 ≤ 2*energy/M := by positivity
    linarith
  have hs2 : 1/4 ≤ w^2 := by
    have hb : 2*energy/M ≤ 3/4 := (div_le_iff₀ hM).mpr (by linarith)
    rw [hshell]
    linarith
  have hw1 : w ≤ 1 := by nlinarith
  have hw2 : 1/2 ≤ w := by nlinarith
  have hpos : 0 ≤ 1/w-1 := by
    apply sub_nonneg.mpr
    exact (le_div_iff₀ hw).mpr (by simpa using hw1)
  refine ⟨hw2, hw1, hpos, ?_⟩
  rw [show 1/w-1 = (1-w)/w by field_simp]
  apply (div_le_div_iff₀ hw hM).mpr
  have he0 : 0 ≤ e := henergy.trans he
  have hprod : 0 ≤ M*w*(1-w) := mul_nonneg (mul_pos hM hw).le (sub_nonneg.mpr hw1)
  nlinarith [mul_nonneg he0 (sub_nonneg.mpr hw2)]

/-- Each relational Hamilton component differs from the desired areal
component by a controlled multiplicative error. -/
theorem relational_vector_field_error (M e w X : ℝ)
    (hlo : 0 ≤ 1/w-1) (hhi : 1/w-1 ≤ 4*e/M) :
    |X/w-X| ≤ (4*e/M)*|X| := by
  rw [show X/w-X = (1/w-1)*X by ring, abs_mul, abs_of_nonneg hlo]
  exact mul_le_mul_of_nonneg_right hhi (abs_nonneg X)

#print axioms autonomous_energy_nonnegative
#print axioms clock_force
#print axioms autonomous_wave_energy_derivative
#print axioms autonomous_total_energy_derivative
#print axioms energy_shell_clock_speed
#print axioms relational_clock_rate_bound
#print axioms relational_vector_field_error

end
end UnifiedTheory.Audit.KFCausalAutonomousArealClock
