/- The fixed second-degree half-exponential used by the finite model
has a classical chart error independent of finite spin capacity. These
theorems calculate derivatives of the actual commuting clock/vacuum
formulas. The exponential replacement repairs this classical subproblem;
it does not remove the finite-matrix commutator boundary or prove a TOE. -/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalPolynomialClockObstruction
noncomputable section
open Filter
open scoped Topology

def half (s : ℝ) : ℝ := 1+s/2+s^2/8
def clock (s : ℝ) : ℝ := half s^2
def longitudinal (s p : ℝ) : ℝ := half (-s)^2*p
def vacuumPotential (s p : ℝ) : ℝ := half (longitudinal s p)^2*half (-s)^2
def vacuumHamiltonian (s p : ℝ) : ℝ := clock s/2+vacuumPotential s p
def chartJacobian (s : ℝ) : ℝ := deriv clock s*half (-s)^2
def clockForce (s p : ℝ) : ℝ := deriv clock s*deriv (vacuumHamiltonian s) p

theorem half_floor (s : ℝ) : 1/2 ≤ half s := by
  unfold half
  nlinarith [sq_nonneg (s+2)]

theorem clock_floor (s : ℝ) : 1/4 ≤ clock s := by
  have h := half_floor s
  unfold clock
  nlinarith

theorem clock_misses_positive_value : ∀ s, clock s ≠ 1/8 := by
  intro s hs
  have h := clock_floor s
  linarith

/-- Changing the regulator or the sampled point cannot recover clock
values below the fixed polynomial's floor. The functional approximation
must also be changed if the whole positive branch is the target. -/
theorem clock_limit_floor (s : ℕ → ℝ) (c : ℝ)
    (hc : Tendsto (fun R => clock (s R)) atTop (𝓝 c)) : 1/4 ≤ c :=
  ge_of_tendsto hc (Filter.Eventually.of_forall (fun R => clock_floor (s R)))

theorem half_derivative (s : ℝ) : HasDerivAt half (1/2+s/4) s := by
  have h := (((hasDerivAt_id s).div_const 2).const_add 1).add
    (((hasDerivAt_id s).pow 2).div_const 8)
  convert h using 1
  dsimp [half]
  ring

theorem clock_derivative (s : ℝ) : HasDerivAt clock (half s*(1+s/2)) s := by
  convert (half_derivative s).pow 2 using 1
  dsimp [clock]
  ring

theorem longitudinal_momentum_derivative (s p : ℝ) :
    HasDerivAt (longitudinal s) (half (-s)^2) p := by
  simpa [longitudinal] using (hasDerivAt_id p).const_mul (half (-s)^2)

theorem vacuum_momentum_derivative (s p : ℝ) :
    HasDerivAt (vacuumHamiltonian s)
      (half (longitudinal s p)*(1+longitudinal s p/2)*half (-s)^4) p := by
  have h := (((half_derivative (longitudinal s p)).comp p
    (longitudinal_momentum_derivative s p)).pow 2).mul_const (half (-s)^2)
  convert h.const_add (clock s/2) using 1
  dsimp [vacuumHamiltonian,vacuumPotential]
  ring

theorem chart_jacobian_error (s : ℝ) :
    chartJacobian s-1=s^2*(s^5-2*s^4+16*s^2+64*s-128)/1024 := by
  rw [chartJacobian,(clock_derivative s).deriv]
  simp only [half]
  ring

theorem polynomial_inverse_error (s : ℝ) : half s*half (-s)-1=s^4/64 := by
  unfold half
  ring

theorem chart_degenerate : deriv clock (-2)=0 ∧ chartJacobian (-2)=0 := by
  rw [chartJacobian,(clock_derivative (-2)).deriv]
  norm_num [half]

theorem vacuum_force_at_one :
    vacuumPotential 1 0=25/64 ∧ clockForce 1 0=24375/65536 ∧
      clockForce 1 0-vacuumPotential 1 0= -1225/65536 := by
  rw [clockForce,(clock_derivative 1).deriv,(vacuum_momentum_derivative 1 0).deriv]
  norm_num [vacuumPotential,longitudinal,half]

/-- The classical target requires clock rate = potential energy on this
vacuum-only, homogeneous subfamily. The fixed polynomial fails exactly. -/
theorem polynomial_vacuum_clock_law_fails :
    ¬∀ s p, clockForce s p=vacuumPotential s p := by
  intro h
  have h1 := h 1 0
  have hc := vacuum_force_at_one
  linarith [hc.1,hc.2.1]

theorem vacuum_force_degenerate :
    clockForce (-2) 0=0 ∧ vacuumPotential (-2) 0=25/4 := by
  simp [clockForce,chart_degenerate.1,vacuumPotential,longitudinal,half]
  norm_num

def exactClock (s : ℝ) : ℝ := Real.exp s
def exactLongitudinal (s p : ℝ) : ℝ := Real.exp (-s)*p
def exactVacuumPotential (s p : ℝ) : ℝ := Real.exp (exactLongitudinal s p)*Real.exp (-s)
def exactVacuumHamiltonian (s p : ℝ) : ℝ := exactClock s/2+exactVacuumPotential s p

theorem exact_vacuum_momentum_derivative (s p : ℝ) :
    HasDerivAt (exactVacuumHamiltonian s)
      (Real.exp (exactLongitudinal s p)*Real.exp (-s)*Real.exp (-s)) p := by
  have h := (((hasDerivAt_id p).const_mul (Real.exp (-s))).exp).mul_const (Real.exp (-s))
  convert h.const_add (exactClock s/2) using 1
  simp [exactLongitudinal]

/-- Exact exponentials repair the classical vacuum clock law at every
point of the positive branch. This is not a finite-dimensional CCR claim. -/
theorem exact_vacuum_clock_law (s p : ℝ) :
    deriv exactClock s*deriv (exactVacuumHamiltonian s) p=exactVacuumPotential s p := by
  rw [show deriv exactClock s=Real.exp s from (Real.hasDerivAt_exp s).deriv,
    (exact_vacuum_momentum_derivative s p).deriv]
  have he : Real.exp s*Real.exp (-s)=1 := by rw [← Real.exp_add]; simp
  dsimp [exactVacuumPotential]
  calc
    _ = (Real.exp s*Real.exp (-s))*(Real.exp (exactLongitudinal s p)*Real.exp (-s)) := by ring
    _ = _ := by rw [he,one_mul]

#print axioms clock_floor
#print axioms clock_misses_positive_value
#print axioms clock_limit_floor
#print axioms clock_derivative
#print axioms vacuum_momentum_derivative
#print axioms chart_jacobian_error
#print axioms polynomial_inverse_error
#print axioms chart_degenerate
#print axioms vacuum_force_at_one
#print axioms polynomial_vacuum_clock_law_fails
#print axioms vacuum_force_degenerate
#print axioms exact_vacuum_clock_law

end
end UnifiedTheory.Audit.KFCausalPolynomialClockObstruction
