/-
Identify the existing Poisson heat series with a bounded operator exponential
on every finite additive grid. This supplies its time derivative and semigroup
law without assuming an unrelated evolution. The continuum Fourier argument
and non-Abelian/quantum extensions are separate.
-/
import UnifiedTheory.LayerA.AbelianCurvatureHeat
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.ODE.Gronwall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerA.AbelianCurvatureHeatDynamics
noncomputable section
open UnifiedTheory.LayerA.AbelianCurvatureHeat

variable {V : Type*} [AddCommGroup V] [Fintype V]

def stepOperator (ex ey : V) : (V → ℝ) →L[ℝ] (V → ℝ) :=
  (1 / 4 : ℝ) • ContinuousLinearMap.pi (fun p =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : V => ℝ) (p + ex) +
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : V => ℝ) (p - ex) +
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : V => ℝ) (p + ey) +
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : V => ℝ) (p - ey))

theorem stepOperator_apply (ex ey : V) (f : V → ℝ) (p : V) :
    stepOperator ex ey f p = step ex ey f p := by
  simp [stepOperator, step, div_eq_mul_inv, mul_comm]

theorem stepOperator_pow_apply (ex ey : V) (k : ℕ) (f : V → ℝ) (p : V) :
    (stepOperator ex ey ^ k) f p = walk ex ey f k p := by
  induction k generalizing p with
  | zero => simp [walk]
  | succ k ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, stepOperator_apply]
    simp only [walk, step, ih]

def evolution (ex ey : V) (s : ℝ) : (V → ℝ) →L[ℝ] (V → ℝ) :=
  Real.exp (-s) • NormedSpace.exp (s • stepOperator ex ey)

/-- The previously defined infinite series is exactly this operator evolution. -/
theorem evolution_eq_heat (ex ey : V) (s : ℝ) (f : V → ℝ) (p : V) :
    evolution ex ey s f p = heat ex ey s f p := by
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (s • stepOperator ex ey)
  have hf := (ContinuousLinearMap.apply ℝ (V → ℝ) f).hasSum h
  have hp := (ContinuousLinearMap.proj (R := ℝ) p).hasSum hf
  have hs := hp.mul_left (Real.exp (-s))
  have ht : HasSum (fun k => poissonWeight s k * walk ex ey f k p)
      (evolution ex ey s f p) := by
    convert hs using 1
    · ext k
      simp [poissonWeight, smul_pow, stepOperator_pow_apply, div_eq_mul_inv,
        mul_assoc, mul_left_comm, mul_comm]
  exact ht.tsum_eq.symm

theorem evolution_derivative (ex ey : V) (s : ℝ) (f : V → ℝ) :
    HasDerivAt (fun t => evolution ex ey t f)
      (stepOperator ex ey (evolution ex ey s f) - evolution ex ey s f) s := by
  have he := (hasDerivAt_exp_smul_const' (stepOperator ex ey) s).clm_apply
    (hasDerivAt_const s f)
  have hr : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-s)) s := by
    convert (Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_id s).neg using 1 <;> simp
  have h := hr.smul he
  convert h using 1
  ext p
  simp [evolution, map_smul, ContinuousLinearMap.mul_apply, sub_eq_add_neg]

theorem heat_hasDerivAt (ex ey : V) (s : ℝ) (f : V → ℝ) :
    HasDerivAt (fun t => heat ex ey t f)
      (fun p => step ex ey (heat ex ey s f) p - heat ex ey s f p) s := by
  have h := evolution_derivative ex ey s f
  simpa only [show (fun t => evolution ex ey t f) = (fun t => heat ex ey t f) by
    funext t p; exact evolution_eq_heat ex ey t f p,
    show evolution ex ey s f = heat ex ey s f by
      funext p; exact evolution_eq_heat ex ey s f p,
    show stepOperator ex ey (heat ex ey s f) = step ex ey (heat ex ey s f) by
      funext p; exact stepOperator_apply ex ey _ p] using h

theorem evolution_add (ex ey : V) (s t : ℝ) :
    evolution ex ey (s + t) = evolution ex ey s * evolution ex ey t := by
  letI : NormedAlgebra ℚ ((V → ℝ) →L[ℝ] (V → ℝ)) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  have hc : Commute (s • stepOperator ex ey) (t • stepOperator ex ey) :=
    ((Commute.refl (stepOperator ex ey)).smul_left s).smul_right t
  simp only [evolution, neg_add, Real.exp_add, add_smul,
    NormedSpace.exp_add_of_commute hc]
  simp [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm]

theorem heat_add (ex ey : V) (s t : ℝ) (f : V → ℝ) (p : V) :
    heat ex ey (s + t) f p = heat ex ey s (heat ex ey t f) p := by
  have ht : evolution ex ey t f = heat ex ey t f := by
    funext q
    exact evolution_eq_heat ex ey t f q
  rw [← evolution_eq_heat, evolution_add, ContinuousLinearMap.mul_apply, ht,
    evolution_eq_heat]

/-- The actual n-by-n Poisson series solves the displayed lattice heat ODE. -/
theorem gridHeat_hasDerivAt (n : ℕ) [NeZero n] (t : ℝ) (f : Grid n → ℝ) :
    HasDerivAt (fun s => gridHeat n s f) (generator n (gridHeat n t f)) t := by
  have h := (heat_hasDerivAt (1, 0) (0, 1) (4 * (n : ℝ)^2 * t) f).scomp t
    ((hasDerivAt_id t).const_mul (4 * (n : ℝ)^2))
  convert h using 1
  ext p
  simp [generator_uniformization, gridHeat]

theorem gridHeat_add (n : ℕ) [NeZero n] (s t : ℝ) (f : Grid n → ℝ) (p : Grid n) :
    gridHeat n (s + t) f p = gridHeat n s (gridHeat n t f) p := by
  simp only [gridHeat, mul_add, heat_add]

/-- Initial-data differentiation is the actual evolution operator itself. -/
theorem heat_initial_hasFDerivAt (ex ey : V) (s : ℝ) (f : V → ℝ) :
    HasFDerivAt (heat ex ey s) (evolution ex ey s) f := by
  have he : (heat ex ey s) = (evolution ex ey s : (V → ℝ) → (V → ℝ)) := by
    funext g p
    exact (evolution_eq_heat ex ey s g p).symm
  rw [he]
  exact (evolution ex ey s).hasFDerivAt

/-- The initial-data derivative has norm at most one, uniformly in grid size and time. -/
theorem evolution_opNorm_le_one (ex ey : V) (s : ℝ) (hs : 0 ≤ s) :
    ‖evolution ex ey s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 1)
  intro f
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg f)).mpr
  intro p
  rw [Real.norm_eq_abs, evolution_eq_heat]
  exact heat_bound ex ey s hs f ‖f‖
    (fun q => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm f q) p

theorem step_sum (ex ey : V) (f : V → ℝ) :
    ∑ p, step ex ey f p = ∑ p, f p := by
  have hx : (∑ p, f (p + ex)) = ∑ p, f p :=
    Equiv.sum_comp (Equiv.addRight ex) f
  have hy : (∑ p, f (p + ey)) = ∑ p, f p :=
    Equiv.sum_comp (Equiv.addRight ey) f
  have hnx : (∑ p, f (p - ex)) = ∑ p, f p := by
    simpa only [sub_eq_add_neg] using Equiv.sum_comp (Equiv.addRight (-ex)) f
  have hny : (∑ p, f (p - ey)) = ∑ p, f p := by
    simpa only [sub_eq_add_neg] using Equiv.sum_comp (Equiv.addRight (-ey)) f
  simp only [step, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [hx, hy, hnx, hny]
  ring

theorem walk_sum (ex ey : V) (f : V → ℝ) (k : ℕ) :
    ∑ p, walk ex ey f k p = ∑ p, f p := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [walk, step_sum] using ih

theorem heat_sum (ex ey : V) (s : ℝ) (hs : 0 ≤ s) (f : V → ℝ)
    (M : ℝ) (hf : ∀ p, |f p| ≤ M) :
    ∑ p, heat ex ey s f p = ∑ p, f p := by
  have htot := hasSum_sum (s := Finset.univ)
    (f := fun p k => poissonWeight s k * walk ex ey f k p)
    (a := fun p => heat ex ey s f p)
    (fun p _ => (heat_series_summable ex ey s hs f M hf p).hasSum)
  simp only [← Finset.mul_sum, walk_sum] at htot
  exact htot.unique (by simpa only [one_mul] using
    (poissonWeight_hasSum s).mul_right (∑ p, f p))

/-- Uniqueness for global differentiable solutions of this finite-grid ODE. -/
theorem heat_unique (ex ey : V) (initial : V → ℝ) (u : ℝ → V → ℝ)
    (hu : ∀ t, HasDerivAt u (stepOperator ex ey (u t) - u t) t)
    (hzero : u 0 = initial) : u = fun t => heat ex ey t initial := by
  let L : (V → ℝ) →L[ℝ] (V → ℝ) := stepOperator ex ey - 1
  apply ODE_solution_unique_univ (v := fun _ : ℝ => L)
    (s := fun _ => Set.univ) (t₀ := 0)
    (fun _ => L.lipschitz.lipschitzOnWith)
  · intro t
    exact ⟨by simpa [L] using hu t, Set.mem_univ _⟩
  · intro t
    refine ⟨?_, Set.mem_univ _⟩
    simpa only [L, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      show stepOperator ex ey (heat ex ey t initial) = step ex ey (heat ex ey t initial) by
        funext p; exact stepOperator_apply ex ey _ p] using heat_hasDerivAt ex ey t initial
  · rw [hzero]
    funext p
    exact (heat_zero ex ey initial p).symm

end
end UnifiedTheory.LayerA.AbelianCurvatureHeatDynamics
