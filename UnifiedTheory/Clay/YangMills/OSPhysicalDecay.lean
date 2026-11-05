/-
A common exponential decay rate for diagonal connected canonical kernels is
enough for the sharp finite-quadratic-form decay of the actual OS semigroup.
The prefactor and the large-time threshold may depend on each canonical label.
Linearity first bounds the scaled orbit of every finite sum. The self-adjoint
semigroup doubling inequality then removes every vector-dependent prefactor,
producing all cross-term bounds without assuming them. The actual contraction
controls the remaining finite-time portion of each orbit.

This reduces the physical decay input in the existing full Schwartz spectral
package. It does not prove that exponential clustering holds for a physical
Yang--Mills hierarchy, construct a nonzero continuum state, construct local
fields or a Lorentz representation, or establish every compact simple group.
-/

import UnifiedTheory.Clay.YangMills.OSFiniteExcitation
import UnifiedTheory.Clay.YangMills.OSBoundedOrbitContraction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.OSPhysicalDecay
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4 OSPositiveTimeKernel
open KernelHilbertCompletion OSScalarDynamics OSLaplaceResolvent OSFormGapResolvent
open scoped NNReal BigOperators

variable {W : Hierarchy} {plane : Plane} {hp : Positive W plane}
  (D : Evolution W plane hp)

/-- A common physical exponent, but no common prefactor, is required for the
diagonal connected kernel of each actual canonical label. -/
def DiagonalDecay (m : ℝ) : Prop :=
  ∀ i : Label, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ≥0,
    (kernel W plane (i, shift (t+t) i)).re -
      ‖inner ℂ (OSVacuumSector.vacuum W plane hp)
        (canonical (positiveKernel W plane hp) i)‖ ^ 2 ≤
      C * Real.exp (-2 * m * (t : ℝ))

/-- Boundedness of a scaled orbit. The bound may depend on the vector. -/
def ScaledOrbitBound (m : ℝ) (x : State (hp := hp)) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ≥0, Real.exp (m * (t : ℝ)) * ‖D.operator t x‖ ≤ C

theorem exp_weight_sq (m s : ℝ) : Real.exp (m*s) ^ 2 = Real.exp (2*m*s) := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

theorem scaledOrbitBound_zero (m : ℝ) : ScaledOrbitBound D m 0 := by
  refine ⟨0, le_rfl, ?_⟩
  intro t
  simp only [map_zero, norm_zero, mul_zero, le_refl]

theorem scaledOrbitBound_add (m : ℝ) (x y : State (hp := hp))
    (hx : ScaledOrbitBound D m x) (hy : ScaledOrbitBound D m y) :
    ScaledOrbitBound D m (x+y) := by
  obtain ⟨C, hC, hx⟩ := hx
  obtain ⟨B, hB, hy⟩ := hy
  refine ⟨C+B, add_nonneg hC hB, fun t => ?_⟩
  rw [map_add]
  calc
    _ ≤ Real.exp (m * (t : ℝ)) * (‖D.operator t x‖ + ‖D.operator t y‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.exp_pos _).le
    _ = Real.exp (m * (t : ℝ)) * ‖D.operator t x‖ +
        Real.exp (m * (t : ℝ)) * ‖D.operator t y‖ := mul_add _ _ _
    _ ≤ C+B := add_le_add (hx t) (hy t)

theorem scaledOrbitBound_smul (m : ℝ) (c : ℂ) (x : State (hp := hp))
    (hx : ScaledOrbitBound D m x) : ScaledOrbitBound D m (c • x) := by
  obtain ⟨C, hC, hx⟩ := hx
  refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg _) hC, fun t => ?_⟩
  rw [map_smul, norm_smul]
  calc
    _ = ‖c‖ * (Real.exp (m * (t : ℝ)) * ‖D.operator t x‖) := by ring
    _ ≤ ‖c‖ * C := mul_le_mul_of_nonneg_left (hx t) (norm_nonneg _)

theorem canonical_scaledOrbitBound
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (m : ℝ) (hdecay : DiagonalDecay (W := W) (plane := plane) (hp := hp) m)
    (i : Label) : ScaledOrbitBound D m
      (center (canonical (positiveKernel W plane hp) i)) := by
  obtain ⟨C, hC, hbound⟩ := hdecay i
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, fun t => ?_⟩
  have h := hbound t
  rw [← OSFixedSector.centered_canonical_norm_sq D hn] at h
  have he : Real.exp (2*m*(t : ℝ)) * Real.exp (-2*m*(t : ℝ)) = 1 := by
    rw [← Real.exp_add]
    have hz : 2*m*(t : ℝ) + -2*m*(t : ℝ) = 0 := by ring
    rw [hz, Real.exp_zero]
  have hs : (Real.exp (m*(t : ℝ)) * ‖D.operator t
      (center (canonical (positiveKernel W plane hp) i))‖) ^ 2 ≤ C := by
    rw [mul_pow, exp_weight_sq]
    calc
      _ ≤ Real.exp (2*m*(t : ℝ)) * (C * Real.exp (-2*m*(t : ℝ))) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = C := by rw [mul_left_comm, he, mul_one]
  nlinarith [Real.sq_sqrt hC, Real.sqrt_nonneg C,
    mul_nonneg (Real.exp_pos (m*(t : ℝ))).le
      (norm_nonneg (D.operator t (center (canonical (positiveKernel W plane hp) i))))]

/-- Finite linear combinations acquire a finite prefactor by linearity and the
triangle inequality; no cross-kernel decay is assumed. -/
theorem span_scaledOrbitBound
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (m : ℝ) (hdecay : DiagonalDecay (W := W) (plane := plane) (hp := hp) m)
    (x : State (hp := hp))
    (hx : x ∈ Submodule.span ℂ (Set.range (canonical (positiveKernel W plane hp)))) :
    ScaledOrbitBound D m (center x) := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, rfl⟩ := hz
    exact canonical_scaledOrbitBound D hn m hdecay i
  | zero =>
    rw [map_zero]
    exact scaledOrbitBound_zero D m
  | add x y hx hy ihx ihy =>
    rw [map_add]
    exact scaledOrbitBound_add D m _ _ ihx ihy
  | smul c x hx ih =>
    rw [map_smul]
    exact scaledOrbitBound_smul D m c _ ih

/-- Self-adjoint semigroup doubling, proved on the actual Hilbert space. -/
theorem norm_sq_doubling (x : State (hp := hp)) (t : ℝ≥0) :
    (‖D.operator t x‖ ^ 2) ^ 2 ≤ ‖x‖ ^ 2 * ‖D.operator (t+t) x‖ ^ 2 := by
  have h : ‖D.operator t x‖ ^ 2 ≤ ‖x‖ * ‖D.operator (t+t) x‖ := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), D.symmetric, D.add]
    exact re_inner_le_norm (𝕜 := ℂ) x (D.operator (t+t) x)
  have hs := pow_le_pow_left₀ (sq_nonneg ‖D.operator t x‖) h 2
  simpa only [mul_pow] using hs

/-- The doubling argument removes the vector-dependent prefactor completely. -/
theorem decay_of_scaledOrbitBound (m : ℝ) (x : State (hp := hp))
    (hx : ScaledOrbitBound D m x) (t : ℝ≥0) :
    ‖D.operator t x‖ ^ 2 ≤ Real.exp (-2*m*(t : ℝ)) * ‖x‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := hx
  let f : ℕ → ℝ := fun n => Real.exp (2*m*↑((n : ℝ≥0)*t)) *
    ‖D.operator ((n : ℝ≥0)*t) x‖ ^ 2
  have hf (n : ℕ) : 0 ≤ f n := mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hb : BddAbove (Set.range f) := by
    refine ⟨C^2, ?_⟩
    rintro z ⟨n, rfl⟩
    have h := pow_le_pow_left₀ (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
      (hbound ((n : ℝ≥0)*t)) 2
    simpa only [f, mul_pow, exp_weight_sq] using h
  have hd (n : ℕ) : f n ^ 2 ≤ ‖x‖ ^ 2 * f (2*n) := by
    have htime : ((2*n : ℕ) : ℝ≥0)*t = (n : ℝ≥0)*t + (n : ℝ≥0)*t := by
      push_cast
      ring
    have he : Real.exp (2*m*↑((n : ℝ≥0)*t)) ^ 2 =
        Real.exp (2*m*↑((n : ℝ≥0)*t + (n : ℝ≥0)*t)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      push_cast
      ring
    change (Real.exp (2*m*↑((n : ℝ≥0)*t)) * ‖D.operator ((n : ℝ≥0)*t) x‖ ^ 2) ^ 2 ≤
      ‖x‖ ^ 2 * (Real.exp (2*m*↑(((2*n : ℕ) : ℝ≥0)*t)) *
        ‖D.operator (((2*n : ℕ) : ℝ≥0)*t) x‖ ^ 2)
    rw [mul_pow, he, htime]
    calc
      _ ≤ Real.exp (2*m*↑((n : ℝ≥0)*t + (n : ℝ≥0)*t)) *
          (‖x‖ ^ 2 * ‖D.operator ((n : ℝ≥0)*t + (n : ℝ≥0)*t) x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (norm_sq_doubling D x _) (Real.exp_pos _).le
      _ = _ := by ring
  have h := OSBoundedOrbitContraction.bounded_doubling f (fun n => 2*n)
    (‖x‖ ^ 2) (sq_nonneg _) hf hb hd 1
  have hs : Real.exp (2*m*(t : ℝ)) * ‖D.operator t x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    simpa only [f, Nat.cast_one, one_mul] using h
  have he : Real.exp (-2*m*(t : ℝ)) * Real.exp (2*m*(t : ℝ)) = 1 := by
    rw [← Real.exp_add]
    have hz : -2*m*(t : ℝ) + 2*m*(t : ℝ) = 0 := by ring
    rw [hz, Real.exp_zero]
  calc
    _ = Real.exp (-2*m*(t : ℝ)) *
        (Real.exp (2*m*(t : ℝ)) * ‖D.operator t x‖ ^ 2) := by
      rw [← mul_assoc, he, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le

include D

/-- Every cross term and every finite quadratic form now has the sharp common
prefactor required by the existing spectral reconstruction theorem. -/
theorem quadraticDecay_of_diagonalDecay
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (m : ℝ) (hdecay : DiagonalDecay (W := W) (plane := plane) (hp := hp) m) :
    OSClusteringGap.QuadraticDecay (W := W) (plane := plane) m := by
  intro c t
  rw [OSClusteringGap.connectedQuadratic_eq_norm_sq D hn,
    OSClusteringGap.connectedQuadratic_eq_norm_sq D hn, D.zero]
  exact decay_of_scaledOrbitBound D m _
    (span_scaledOrbitBound D hn m hdecay _ (embed_mem_canonical_span _ c)) t

theorem diagonalDecay_of_quadraticDecay
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (m : ℝ) (hdecay : OSClusteringGap.QuadraticDecay (W := W) (plane := plane) m) :
    DiagonalDecay (W := W) (plane := plane) (hp := hp) m := by
  intro i
  refine ⟨‖center (canonical (positiveKernel W plane hp) i)‖ ^ 2, sq_nonneg _, fun t => ?_⟩
  have h := OSClusteringGap.centered_norm_sq_decay D hn m hdecay t
    (canonical (positiveKernel W plane hp) i)
  rw [OSFixedSector.centered_canonical_norm_sq D hn] at h
  simpa only [center_apply, mul_comm] using h

theorem diagonalDecay_iff_quadraticDecay
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x) (m : ℝ) :
    DiagonalDecay (W := W) (plane := plane) (hp := hp) m ↔
      OSClusteringGap.QuadraticDecay (W := W) (plane := plane) m :=
  ⟨quadraticDecay_of_diagonalDecay D hn m, diagonalDecay_of_quadraticDecay D hn m⟩

omit D in
/-- Only large-time exponential clustering is required, and both the time
threshold and the prefactor may depend on the actual canonical label. -/
def EventualDiagonalDecay (m : ℝ) : Prop :=
  ∀ i : Label, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t : ℝ≥0 in Filter.atTop,
    (kernel W plane (i, shift (t+t) i)).re -
      ‖inner ℂ (OSVacuumSector.vacuum W plane hp)
        (canonical (positiveKernel W plane hp) i)‖ ^ 2 ≤
      C * Real.exp (-2*m*(t : ℝ))

/-- The already proved contraction controls the finite-time portion of each
orbit, so eventual diagonal clustering suffices without a uniform threshold. -/
theorem diagonalDecay_of_eventual
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (m : ℝ) (hm : 0 ≤ m)
    (hdecay : EventualDiagonalDecay (W := W) (plane := plane) (hp := hp) m) :
    DiagonalDecay (W := W) (plane := plane) (hp := hp) m := by
  intro i
  obtain ⟨C, hC, hbound⟩ := hdecay i
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hbound
  let v := center (hp := hp) (canonical (positiveKernel W plane hp) i)
  refine ⟨max C (‖v‖ ^ 2 * Real.exp (2*m*(T : ℝ))),
    hC.trans (le_max_left _ _), fun t => ?_⟩
  by_cases ht : T ≤ t
  · exact (hT t ht).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · have htt : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast (le_of_not_ge ht)
    have he : 1 ≤ Real.exp (2*m*(T : ℝ)) * Real.exp (-2*m*(t : ℝ)) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      nlinarith
    have hc : (kernel W plane (i, shift (t+t) i)).re -
        ‖inner ℂ (OSVacuumSector.vacuum W plane hp)
          (canonical (positiveKernel W plane hp) i)‖ ^ 2 ≤ ‖v‖ ^ 2 := by
      rw [← OSFixedSector.centered_canonical_norm_sq D hn]
      exact pow_le_pow_left₀ (norm_nonneg _) (D.contraction t v) 2
    calc
      _ ≤ ‖v‖ ^ 2 := hc
      _ = ‖v‖ ^ 2 * 1 := (mul_one _).symm
      _ ≤ ‖v‖ ^ 2 * (Real.exp (2*m*(T : ℝ)) * Real.exp (-2*m*(t : ℝ))) :=
        mul_le_mul_of_nonneg_left he (sq_nonneg _)
      _ = (‖v‖ ^ 2 * Real.exp (2*m*(T : ℝ))) * Real.exp (-2*m*(t : ℝ)) :=
        (mul_assoc _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

theorem quadraticDecay_of_eventualDiagonalDecay
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (m : ℝ) (hm : 0 ≤ m)
    (hdecay : EventualDiagonalDecay (W := W) (plane := plane) (hp := hp) m) :
    OSClusteringGap.QuadraticDecay (W := W) (plane := plane) m :=
  quadraticDecay_of_diagonalDecay D hn m (diagonalDecay_of_eventual D hn m hm hdecay)

/-- All actual full Schwartz spectral requirements now need only diagonal
large-time clustering with label-dependent constants, plus a nonzero state. -/
theorem full_spectralRequirements_of_eventualDiagonalDecay
    (hfull : FullPositiveTimeReflection.Positive W plane)
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (m : ℝ) (hm : 0 < m)
    (hdecay : EventualDiagonalDecay (W := W) (plane := plane) (hp := hp) m)
    (w : FullSchwartzHamiltonian.State W plane hfull) (hw : w ≠ 0)
    (ho : inner ℂ (RenormalizedFullOSLimit.fullVacuum W plane hfull) w = 0) :
    SpectralGap.SpectralRequirements
      (FullSchwartzHamiltonian.hamiltonian W plane hp hfull D)
      (RenormalizedFullOSLimit.fullVacuum W plane hfull) m :=
  OSFiniteExcitation.full_spectralRequirements_of_quadraticDecay D hfull hn m hm
    (quadraticDecay_of_eventualDiagonalDecay D hn m hm.le hdecay) w hw ho

end
end UnifiedTheory.Clay.YangMills.OSPhysicalDecay
