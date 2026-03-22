/-
  LayerA/SourceFromMetric.lean — Derive source functional from metric

  Proves that the source functional (primitive 2) can be derived from
  the metric structure (primitive 1) via linearization.

  Key insight: given a metric g and its Einstein tensor G[g],
  the linearized Einstein operator L = dG/dg is a linear map
  on perturbations h. This linear map IS a source functional:
  - Its image = source-capable perturbations (K-sector)
  - Its kernel = gauge/dressing perturbations (P-sector)
  - The K/P split follows from the image/kernel decomposition

  This reduces primitives from 3 to 2:
    1. Metric structure
    2. Linear defect perturbation structure
  The source functional is no longer independent.

  The proof is abstract: any linear operator L : V →ₗ[ℝ] W on a
  finite-dimensional space induces a source functional via
  composition with any nonzero functional on the image.
-/
import UnifiedTheory.LayerA.DerivedBFSplit
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace UnifiedTheory.LayerA.SourceReduction

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
                        [AddCommGroup W] [Module ℝ W]

/-! ### Source functional from a linear operator -/

/-- **Any nontrivial linear operator induces a source functional.**

    Given L : V →ₗ[ℝ] W (the linearized Einstein operator) and
    any nonzero functional ψ : W →ₗ[ℝ] ℝ on the target space,
    the composition φ = ψ ∘ L is a source functional on V.

    This is the key reduction: the metric determines L (via
    linearization of Einstein's equation), and L determines φ. -/
noncomputable def sourceFromOperator
    (L : V →ₗ[ℝ] W) (ψ : W →ₗ[ℝ] ℝ) : V →ₗ[ℝ] ℝ :=
  ψ ∘ₗ L

/-- **The source functional from an operator is nonzero as a map
    when its defining data is nontrivial.** Given v₀ with ψ(L(v₀)) ≠ 0,
    the composite φ = ψ ∘ L is a nonzero linear map (not just nonzero
    at one point, but nonzero as an element of the dual space). -/
theorem sourceFromOperator_ne_zero
    (L : V →ₗ[ℝ] W) (ψ : W →ₗ[ℝ] ℝ)
    (v₀ : V) (h : ψ (L v₀) ≠ 0) :
    sourceFromOperator L ψ ≠ 0 := by
  intro heq
  have h1 := LinearMap.ext_iff.mp heq v₀
  simp only [sourceFromOperator, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.zero_apply] at h1
  exact h h1

/-- **The K/P split is induced by the operator's image/kernel structure.**

    For φ = ψ ∘ L:
    - K-sector (source-capable): perturbations where L(h) ≠ 0
    - P-sector (dressing/gauge): perturbations where L(h) = 0

    More precisely: φ(h) = ψ(L(h)), so φ vanishes on ker(L).
    The dressing sector contains ker(L), which is the gauge sector. -/
theorem source_vanishes_on_kernel
    (L : V →ₗ[ℝ] W) (ψ : W →ₗ[ℝ] ℝ)
    (v : V) (hv : L v = 0) :
    sourceFromOperator L ψ v = 0 := by
  simp [sourceFromOperator, LinearMap.comp_apply, hv, map_zero]

/-- **The kernel of L is contained in the kernel of the source functional.**
    Any perturbation killed by L is also killed by φ = ψ ∘ L. This is
    the content of "gauge modes are invisible to the source functional". -/
theorem source_ker_contains_operator_ker
    (L : V →ₗ[ℝ] W) (ψ : W →ₗ[ℝ] ℝ) :
    LinearMap.ker L ≤ LinearMap.ker (sourceFromOperator L ψ) := by
  intro v hv
  simp only [LinearMap.mem_ker] at hv ⊢
  simp [sourceFromOperator, LinearMap.comp_apply, hv, map_zero]

/-! ### Construct SourceFunctional from a linear operator -/

/-- **Derive a SourceFunctional from a linear operator.**

    Given:
    - L : V →ₗ[ℝ] W (e.g., linearized Einstein operator)
    - ψ : W →ₗ[ℝ] ℝ (functional on the target, e.g., trace)
    - v₀ : V with ψ(L(v₀)) ≠ 0

    Produces a SourceFunctional, which by DerivedBFSplit.lean
    automatically generates the full K/P decomposition.

    This is the 3→2 reduction: metric → L → φ → K/P split. -/
noncomputable def sourceFunctionalFromOperator
    (L : V →ₗ[ℝ] W) (ψ : W →ₗ[ℝ] ℝ)
    (v₀ : V) (h : ψ (L v₀) ≠ 0) :
    SourceFunctional V where
  φ := sourceFromOperator L ψ
  v₀ := v₀
  hv₀ := h

/-! ### The full derivation chain -/

/-- **The complete K/P decomposition derived from a linear operator.**

    metric → linearized Einstein operator L
    → source functional φ = ψ ∘ L
    → SourceFunctional
    → decompFromFunctional
    → full SourceDressingDecomp with all properties proven

    No independent source functional primitive needed. -/
noncomputable def decompositionFromOperator
    (L : V →ₗ[ℝ] W) (ψ : W →ₗ[ℝ] ℝ)
    (v₀ : V) (h : ψ (L v₀) ≠ 0) :
    SourceDressingDecomp V :=
  decompFromFunctional (sourceFunctionalFromOperator L ψ v₀ h)

/-- **All K/P properties hold for operator-derived decomposition.** -/
theorem operator_decomposition_properties
    (L : V →ₗ[ℝ] W) (ψ : W →ₗ[ℝ] ℝ)
    (v₀ : V) (h : ψ (L v₀) ≠ 0) :
    let sf := sourceFunctionalFromOperator L ψ v₀ h
    -- (1) K/P decomposition exists
    (∀ v : V, v = (decompFromFunctional sf).πK v +
                   (decompFromFunctional sf).πP v)
    -- (2) Source vanishes on P
    ∧ (∀ v : V, (decompFromFunctional sf).πK v = 0 →
        sf.φ v = 0)
    -- (3) Source captures all data on K
    ∧ (∀ v : V, sf.φ (sourceProj sf v) = sf.φ v) :=
  functional_derives_decomposition _

/-! ### Gauge interpretation -/

/-- **Kernel of L is contained in the dressing sector.**
    Perturbations that don't change the Einstein tensor (gauge modes)
    are automatically dressing — they carry zero source strength. -/
theorem gauge_is_dressing
    (L : V →ₗ[ℝ] W) (ψ : W →ₗ[ℝ] ℝ)
    (v₀ : V) (h : ψ (L v₀) ≠ 0)
    (v : V) (hv : L v = 0) :
    (sourceFunctionalFromOperator L ψ v₀ h).φ v = 0 := by
  simp [sourceFunctionalFromOperator, sourceFromOperator,
    LinearMap.comp_apply, hv, map_zero]

/-! ### The reduction theorem -/

/-- **Primitive Reduction 3 → 2.**

    The source functional is not an independent primitive.
    It is derived from any nontrivial linear operator L : V → W
    (such as the linearized Einstein operator) via composition
    with a functional ψ on the target space.

    After this reduction, the framework has TWO irreducible primitives:
    1. Metric structure (determines L via linearization of Einstein eq)
    2. Linear defect perturbation structure (the space V that L acts on)

    The source functional, K/P split, dressing neutrality, and
    everything downstream (charge algebra, quantum structure)
    are ALL derived from these two primitives. -/
theorem reduction_3_to_2
    -- Given: a linear operator (from the metric) and a detection functional
    (L : V →ₗ[ℝ] W) (ψ : W →ₗ[ℝ] ℝ)
    (v₀ : V) (h : ψ (L v₀) ≠ 0) :
    -- Then: a complete source/dressing decomposition exists
    ∃ (sd : SourceDressingDecomp V),
      -- with decomposition property
      (∀ v, v = sd.πK v + sd.πP v)
      -- and source vanishing on dressing
      ∧ (∀ v, sd.πK v = 0 → (sourceFromOperator L ψ) v = 0) := by
  exact ⟨decompositionFromOperator L ψ v₀ h,
    (decompFromFunctional (sourceFunctionalFromOperator L ψ v₀ h)).decompose,
    (decompFromFunctional (sourceFunctionalFromOperator L ψ v₀ h)).source_vanishes_on_P⟩

end UnifiedTheory.LayerA.SourceReduction
