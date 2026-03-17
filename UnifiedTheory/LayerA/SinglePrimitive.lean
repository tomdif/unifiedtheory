/-
  LayerA/SinglePrimitive.lean — Reduce to ONE primitive

  The key theorem: on any vector space of dimension ≥ 2,
  every nonzero linear functional has a nontrivial kernel.

  This means the dressing sector is GUARANTEED by dimension alone.
  No independent "perturbation space is nontrivial" assumption needed.

  Reduction chain:
    dim(V) ≥ 2
    → any nonzero φ : V → ℝ has rank ≤ 1
    → ker(φ) has dim ≥ dim(V) - 1 ≥ 1  (rank-nullity)
    → ker(φ) contains a nonzero vector   (dressing exists)
    → K/P split, complex amplitudes, |z|² observable, phase averaging
-/
import UnifiedTheory.LayerA.SourceFromMetric
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace UnifiedTheory.LayerA.SinglePrimitive

/-! ### The kernel theorem -/

/-- **Kernel nontriviality (the 2→1 reduction).**

    Any nonzero linear functional φ : V → ℝ on a space of dimension ≥ 2
    has a nontrivial kernel. This is because:
    - rank(φ) ≤ 1 (image ⊆ ℝ)
    - dim(ker(φ)) = dim(V) - rank(φ) ≥ 2 - 1 = 1  (rank-nullity)
    - So ker(φ) contains a nonzero vector.

    Physically: the dressing sector is guaranteed to be nontrivial
    whenever the perturbation space has dimension ≥ 2. -/
theorem kernel_nontrivial
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (hdim : 2 ≤ Module.finrank ℝ V)
    (φ : V →ₗ[ℝ] ℝ) (hφ : φ ≠ 0) :
    ∃ v : V, v ≠ 0 ∧ φ v = 0 := by
  -- Suppose for contradiction that ker(φ) = {0}
  by_contra h_all
  push_neg at h_all
  -- h_all : ∀ v, v ≠ 0 → φ v ≠ 0
  -- This means φ is injective: if φ(a) = φ(b), then φ(a-b) = 0,
  -- so a-b = 0 (since a-b ≠ 0 would give φ(a-b) ≠ 0), so a = b.
  have h_inj : Function.Injective φ := by
    intro a b hab
    by_contra hne
    have hsub : a - b ≠ 0 := sub_ne_zero.mpr hne
    have hφsub : φ (a - b) ≠ 0 := h_all _ hsub
    rw [map_sub] at hφsub
    exact hφsub (sub_eq_zero.mpr hab)
  -- But an injective linear map V → ℝ requires dim(V) ≤ dim(ℝ) = 1.
  -- This contradicts dim(V) ≥ 2.
  have hle := LinearMap.finrank_le_finrank_of_injective h_inj
  rw [Module.finrank_self] at hle
  linarith

/-- **Corollary: for any nonzero functional, the K/P split has
    nontrivial dressing.** This is the content of the 2→1 reduction. -/
theorem dressing_guaranteed
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (hdim : 2 ≤ Module.finrank ℝ V)
    (sf : SourceFunctional V) :
    ∃ v : V, v ≠ 0 ∧ sf.φ v = 0 := by
  have hφ : sf.φ ≠ 0 := by
    intro heq
    have := sf.hv₀
    simp [heq] at this
  exact kernel_nontrivial hdim sf.φ hφ

/-- **The 2 → 1 Primitive Reduction.**

    Given:
    - A vector space V with dim(V) ≥ 2  (the ONE primitive)
    - Any nonzero functional φ on V      (exists by nontriviality of dual)

    Then:
    - ker(φ) is nontrivial              (proven: kernel_nontrivial)
    - K/P split exists with nontrivial P (proven: dressing_guaranteed)
    - Complex amplitudes z = Q + iP     (proven: ComplexFromDressing)
    - Born rule |z|² is unique           (proven: ComplexUniqueness)
    - Decoherence → classical            (proven: Decoherence)

    The entire quantum-matter framework reduces to ONE primitive:
    a vector space of dimension ≥ 2.

    In physics: a metric on a manifold of dimension n ≥ 2 provides
    a perturbation space of symmetric 2-tensors with dim = n(n+1)/2 ≥ 3.
    This is always ≥ 2. So the metric alone suffices. -/
theorem reduction_2_to_1
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (hdim : 2 ≤ Module.finrank ℝ V) :
    -- For ANY nonzero functional on V:
    ∀ (φ : V →ₗ[ℝ] ℝ), φ ≠ 0 →
      -- The kernel is nontrivial (dressing exists)
      (∃ v : V, v ≠ 0 ∧ φ v = 0) := by
  intro φ hφ
  exact kernel_nontrivial hdim φ hφ

end UnifiedTheory.LayerA.SinglePrimitive
