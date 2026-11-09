/-
  Supporting finite inequalities for a supplied local geometry template.
  Hamiltonian spectral bounds, graph recognition, cycle counting, and the
  external regular-graph estimate are explicit analytic suppliers.
-/
import UnifiedTheory.Audit.KFCausalAutonomousGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalPatchGeometry
noncomputable section
open scoped BigOperators
open Filter Topology

/-- Applies to a variational ground energy or a conserved initial energy. -/
theorem defect_fraction_bound (defects energy J n budget : ℝ)
    (hJ : 0 < J) (hn : 0 < n)
    (hlower : J * defects ≤ energy) (hupper : energy ≤ budget * n) :
    defects / n ≤ budget / J := by
  apply (div_le_div_iff₀ hn hJ).mpr
  nlinarith

/-- A uniform graph input has zero initial kinetic energy. A bounded
kinetic reservoir cannot absorb arbitrarily much defect energy. -/
theorem uniform_quench_bound (before after kinetic J rho n cap : ℝ)
    (hJ : 0 < J) (hn : 0 < n) (hr : 0 ≤ rho)
    (hconserve : J * before = J * after + rho * kinetic)
    (hcap : kinetic ≤ cap * n) :
    before / n - rho * cap / J ≤ after / n := by
  have h := mul_le_mul_of_nonneg_left hcap hr
  have hd : before - after ≤ (rho * cap / J) * n := by
    calc
      before - after ≤ rho * cap * n / J := (le_div_iff₀ hJ).mpr (by nlinarith)
      _ = (rho * cap / J) * n := by ring
  have hf : before / n - after / n ≤ rho * cap / J := by
    rw [← sub_div]
    exact (div_le_iff₀ hn).mpr hd
  linarith

/-- A necessary per-site energy capacity for a proposed matter reservoir. -/
theorem reservoir_budget (initial final J rho bath coupling : ℝ)
    (henergy : J * initial - coupling ≤ 600 * rho + J * final + bath + coupling) :
    J * (initial - final) ≤ 600 * rho + bath + 2 * coupling := by linarith

/-- A maximal packing gives a cover by bounded intersection neighborhoods. -/
theorem finite_cover_bound {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (family : Finset X) (selected : Finset Y) (cover : Y → Finset X) (bound : ℕ)
    (hc : family ⊆ selected.biUnion cover)
    (hb : ∀ y ∈ selected, (cover y).card ≤ bound) :
    family.card ≤ selected.card * bound := by
  calc
    family.card ≤ (selected.biUnion cover).card := Finset.card_le_card hc
    _ ≤ ∑ y ∈ selected, (cover y).card := Finset.card_biUnion_le
    _ ≤ ∑ _y ∈ selected, bound := Finset.sum_le_sum hb
    _ = selected.card * bound := by simp

/-- Twelve squares per good root and at most 300 intersections per packed
square give a linear number of vertex-disjoint squares. -/
theorem packed_square_capacity (good squares packed : ℝ)
    (hincidence : 12 * good ≤ 4 * squares) (hcover : squares ≤ 300 * packed) :
    good ≤ 100 * packed := by linarith

/-- Small probability of every positive-threshold event implies a small
mean for an observable valued in [0,1]; commutation with H is not needed. -/
theorem threshold_mean_bound {X : Type*} [Fintype X]
    (weight value : X → ℝ) (alpha : ℝ) (ha : 0 ≤ alpha)
    (hw : ∀ x, 0 ≤ weight x) (hnorm : ∑ x, weight x = 1)
    (hv : ∀ x, value x ≤ 1) :
    (∑ x, weight x * value x) ≤
      alpha + ∑ x, weight x * (if alpha ≤ value x then 1 else 0) := by
  have hpoint : ∀ x, value x ≤ alpha + (if alpha ≤ value x then 1 else 0) := by
    intro x
    split_ifs with h
    · linarith [hv x]
    · have hh : value x < alpha := lt_of_not_ge h
      linarith
  calc
    _ ≤ ∑ x, weight x * (alpha + (if alpha ≤ value x then 1 else 0)) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hpoint x) (hw x))
    _ = _ := by simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hnorm, one_mul]

/-- Lower-bound each denominator factor in the cited regular-graph edge
probability estimate for a collection of vertex-disjoint squares. -/
theorem moment_denominator_bound (n j : ℝ) (hn : 144 ≤ n) (hj : j ≤ n - 1) :
    3 * n ≤ 2 * (3 * n - 72 - j) := by linarith

theorem vanishing_defect_density (defects ratio : ℕ → ℝ)
    (hd : ∀ n, 0 ≤ defects n) (hb : ∀ n, defects n ≤ 300 * ratio n)
    (hr : Tendsto ratio atTop (𝓝 0)) : Tendsto defects atTop (𝓝 0) := by
  have hlim : Tendsto (fun n => 300 * ratio n) atTop (𝓝 0) := by
    simpa using hr.const_mul 300
  exact squeeze_zero hd hb hlim

#print axioms defect_fraction_bound
#print axioms uniform_quench_bound
#print axioms reservoir_budget
#print axioms finite_cover_bound
#print axioms packed_square_capacity
#print axioms threshold_mean_bound
#print axioms moment_denominator_bound
#print axioms vanishing_defect_density

end
end UnifiedTheory.Audit.KFCausalPatchGeometry
