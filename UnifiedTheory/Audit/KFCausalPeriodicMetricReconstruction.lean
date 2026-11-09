/-
  Constructed longitudinal metric on a finite periodic chain, including
  its global compatibility condition and exact discrete time evolution.
  This solves the stated reduced momentum constraint from wave data;
  it does not derive that constraint from the spin Hamiltonian.
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalPeriodicMetricReconstruction
noncomputable section
open scoped BigOperators

def reconstruct (base : ℝ) (source : ℕ → ℝ) (n : ℕ) : ℝ :=
  base + ∑ i ∈ Finset.range n, source i

theorem reconstruct_zero (base : ℝ) (source : ℕ → ℝ) : reconstruct base source 0 = base := by
  simp [reconstruct]

theorem reconstruct_succ (base : ℝ) (source : ℕ → ℝ) (n : ℕ) :
    reconstruct base source (n+1) = reconstruct base source n + source n := by
  simp [reconstruct, Finset.sum_range_succ, add_assoc]

theorem reconstructed_constraint (base : ℝ) (source : ℕ → ℝ) (n : ℕ) :
    reconstruct base source (n+1)-reconstruct base source n = source n := by
  rw [reconstruct_succ]
  ring

/-- The global momentum condition is necessary and sufficient for closure
of the reconstructed chain; it is not discarded as a zero-mode convention. -/
theorem periodic_iff_total_source_zero (base : ℝ) (source : ℕ → ℝ) (N : ℕ) :
    reconstruct base source N = reconstruct base source 0 ↔
      ∑ i ∈ Finset.range N, source i = 0 := by
  simp [reconstruct]

/-- Exact flux compatibility gives the time derivative of the constructed
metric at every site, after retaining its homogeneous datum. -/
theorem reconstruction_evolves
    (base : ℝ → ℝ) (source flux : ℕ → ℝ → ℝ) (t : ℝ)
    (hbase : HasDerivAt base (flux 0 t) t)
    (hsource : ∀ i, HasDerivAt (source i) (flux (i+1) t-flux i t) t) (n : ℕ) :
    HasDerivAt (fun s => reconstruct (base s) (fun i => source i s) n) (flux n t) t := by
  induction n with
  | zero => simpa [reconstruct] using hbase
  | succ n ih =>
      have he : (fun s => reconstruct (base s) (fun i => source i s) (n+1)) =
          (fun s => reconstruct (base s) (fun i => source i s) n+source n s) := by
        funext s
        exact reconstruct_succ _ _ _
      rw [he]
      convert ih.add (hsource n) using 1
      ring

def momentumSource (c p qprev qnext : ℝ) : ℝ := p*(qnext-qprev)/(2*c)
def metricFlux (c k q qnext p pnext : ℝ) : ℝ :=
  (k*(qnext-q)^2+p*pnext)/(2*c^2)-1/2

/-- Exact nearest-neighbor identity, rather than applying a continuum
product rule to finite differences. The instantaneous k can vary in time. -/
theorem lattice_source_continuity
    (qprev q qnext pprev p pnext : ℝ → ℝ) (c k t : ℝ) (hc : c ≠ 0)
    (hp : HasDerivAt p (k*(qnext t-2*q t+qprev t)/c) t)
    (hqp : HasDerivAt qprev (pprev t/c) t)
    (hqn : HasDerivAt qnext (pnext t/c) t) :
    HasDerivAt (fun s => momentumSource c (p s) (qprev s) (qnext s))
      (metricFlux c k (q t) (qnext t) (p t) (pnext t)-
        metricFlux c k (qprev t) (q t) (pprev t) (p t)) t := by
  convert (hp.mul (hqn.sub hqp)).div_const (2*c) using 1
  dsimp [momentumSource, metricFlux]
  field_simp
  ring

def cellEnergy (c speed p dq : ℝ) : ℝ := (p^2+speed^2*dq^2)/(2*c)

theorem source_energy_bound (c speed p dq : ℝ) (hc : 0 < c) (hs : 0 < speed) :
    |p*dq/c| ≤ cellEnergy c speed p dq/speed := by
  rw [abs_le]
  dsimp [cellEnergy]
  constructor
  · have hy : -(p*dq/c) ≤ (p^2+speed^2*dq^2)/(2*c)/speed := by
      apply (le_div_iff₀ hs).mpr
      field_simp
      nlinarith [sq_nonneg (p+speed*dq)]
    linarith
  · apply (le_div_iff₀ hs).mpr
    field_simp
    nlinarith [sq_nonneg (p-speed*dq)]

/-- A global reconstruction bound in terms of total energy, with no
additional number-of-sites factor. The spacing is explicit. -/
theorem reconstruction_energy_bound (p dq : ℕ → ℝ) (base c speed spacing : ℝ)
    (hc : 0 < c) (hs : 0 < speed) (hspacing : 0 ≤ spacing) (n : ℕ) :
    |reconstruct base (fun i => spacing*(p i*dq i/c)) n-base| ≤
      (∑ i ∈ Finset.range n, spacing*cellEnergy c speed (p i) (dq i))/speed := by
  simp only [reconstruct, add_sub_cancel_left]
  calc
    _ ≤ ∑ i ∈ Finset.range n, |spacing*(p i*dq i/c)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, spacing*(cellEnergy c speed (p i) (dq i)/speed) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg hspacing]
      exact mul_le_mul_of_nonneg_left (source_energy_bound c speed (p i) (dq i) hc hs) hspacing
    _ = _ := by simp [Finset.sum_div, mul_div_assoc]

theorem reconstructed_metric_positive (base : ℝ) (source : ℕ → ℝ) (n : ℕ) :
    0 < Real.exp (reconstruct base source n) := Real.exp_pos _

#print axioms reconstructed_constraint
#print axioms periodic_iff_total_source_zero
#print axioms reconstruction_evolves
#print axioms lattice_source_continuity
#print axioms source_energy_bound
#print axioms reconstruction_energy_bound
#print axioms reconstructed_metric_positive

end
end UnifiedTheory.Audit.KFCausalPeriodicMetricReconstruction
