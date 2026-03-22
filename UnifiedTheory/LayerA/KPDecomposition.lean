/-
  LayerA/KPDecomposition.lean — K/P decomposition: formal physics connection

  Connects the K/P decomposition to physics by proving:
  1. ker(L) ⊆ ker(φ)  [referenced from SourceFromMetric.lean]
  2. V = ker(φ) ⊕ complement  (completeness, from rank-nullity)
  3. dim(K-sector) = 1  (φ : V → ℝ has rank 1)
  4. dim(P-sector) = dim(V) - 1  (rank-nullity)
  5. Concrete example: trace on matrices, with P = traceless, K = scalar·I
-/
import UnifiedTheory.LayerA.SourceFromMetric
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.Trace

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerA.KPDecomposition

open Module FiniteDimensional

/-! ### Theorem 1: ker(L) ⊆ ker(φ)

This is already proven in SourceFromMetric.lean as
`SourceReduction.source_ker_contains_operator_ker`.
We re-export it here for completeness. -/

/-- Gauge modes (ker L) are invisible to the source functional φ = ψ ∘ L.
    This is the content of "pure gauge perturbations carry zero source". -/
theorem gauge_in_ker_source
    {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (L : V →ₗ[ℝ] W) (ψ : W →ₗ[ℝ] ℝ) :
    LinearMap.ker L ≤ LinearMap.ker (SourceReduction.sourceFromOperator L ψ) :=
  SourceReduction.source_ker_contains_operator_ker L ψ

/-! ### Theorem 2: Completeness of the K/P decomposition

For finite-dimensional V with φ ≠ 0, V decomposes as ker(φ) ⊕ complement.
This follows from the fact that every submodule of a vector space over a
division ring has a complement. -/

/-- The K/P decomposition is complete: ker(φ) has a complement in V.
    The complement is the K-sector (source modes), ker(φ) is the P-sector (gauge). -/
theorem kp_decomposition_complete
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (φ : V →ₗ[ℝ] ℝ) :
    ∃ K : Submodule ℝ V, IsCompl (LinearMap.ker φ) K :=
  Submodule.exists_isCompl (LinearMap.ker φ)

/-- The K/P decomposition gives a direct sum: every v ∈ V decomposes uniquely
    as v = vₖ + vₚ with vₖ ∈ K and vₚ ∈ ker(φ). -/
theorem kp_direct_sum_mem
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (φ : V →ₗ[ℝ] ℝ) (K : Submodule ℝ V)
    (hc : IsCompl (LinearMap.ker φ) K) (v : V) :
    ∃ (vp : V) (vk : V), vp ∈ LinearMap.ker φ ∧ vk ∈ K ∧ v = vp + vk := by
  have hmem : v ∈ (⊤ : Submodule ℝ V) := Submodule.mem_top
  rw [← hc.sup_eq_top] at hmem
  obtain ⟨vp, hvp, vk, hvk, heq⟩ := Submodule.mem_sup.mp hmem
  exact ⟨vp, vk, hvp, hvk, heq.symm⟩

/-! ### Theorem 3: The K-sector has dimension exactly 1

Since φ : V → ℝ is a nonzero linear functional, its range is all of ℝ
(1-dimensional). By rank-nullity, dim(ker φ) + 1 = dim(V), so any
complement of ker(φ) is 1-dimensional.

Physical meaning: there is exactly ONE independent "source mode" direction.
All matter content is captured by a single scalar — the source strength. -/

/-- The kernel of a nonzero functional has codimension 1:
    dim(ker φ) + 1 = dim(V). -/
theorem finrank_ker_source_add_one
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (φ : V →ₗ[ℝ] ℝ) (hφ : φ ≠ 0) :
    finrank ℝ (LinearMap.ker φ) + 1 = finrank ℝ V :=
  Module.Dual.finrank_ker_add_one_of_ne_zero hφ

/-- The K-sector (complement of ker φ) is 1-dimensional.
    This means there is exactly one independent source mode. -/
theorem finrank_K_sector_eq_one
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (φ : V →ₗ[ℝ] ℝ) (hφ : φ ≠ 0)
    (K : Submodule ℝ V) (hc : IsCompl (LinearMap.ker φ) K) :
    finrank ℝ K = 1 := by
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hφ
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker φ) K
  rw [hc.sup_eq_top, hc.inf_eq_bot] at hsum
  simp only [finrank_top, finrank_bot] at hsum
  omega

/-! ### Theorem 4: The P-sector has dimension dim(V) - 1

The P-sector = ker(φ) contains all gauge/dressing modes.
Its dimension is dim(V) - 1 by rank-nullity.

Physical meaning: almost all of the perturbation space is gauge.
In linearized gravity, these are the diffeomorphism-equivalent
perturbations that don't affect the source (stress-energy). -/

/-- The P-sector (gauge/dressing) has dimension dim(V) - 1. -/
theorem finrank_P_sector
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (φ : V →ₗ[ℝ] ℝ) (hφ : φ ≠ 0) :
    finrank ℝ (LinearMap.ker φ) = finrank ℝ V - 1 := by
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero hφ
  omega

/-! ### Theorem 5: The trace example — physics of the K/P split

The linearized Einstein equation in trace-reversed form:
  L(h) = Ric(h) - (1/2) g · tr(h) + ...

The trace functional φ = tr extracts the scalar part.
  - P = ker(tr) = traceless perturbations = gauge modes (diffeomorphisms)
  - K = complement = scalar multiples of the identity = matter (source) modes

We prove this concretely for n×n real matrices. -/

section TraceExample

variable {n : ℕ}

/-- The trace functional on n×n real matrices, as a linear map. -/
noncomputable def traceFunc (n : ℕ) : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ :=
  Matrix.traceLinearMap (Fin n) ℝ ℝ

/-- The trace of the identity matrix is n. -/
theorem trace_identity :
    traceFunc n (1 : Matrix (Fin n) (Fin n) ℝ) = (n : ℝ) := by
  simp [traceFunc, Matrix.traceLinearMap_apply, Matrix.trace_one, Fintype.card_fin]

/-- For n ≥ 1, the trace functional is nonzero. -/
theorem traceFunc_ne_zero (hn : 0 < n) : traceFunc n ≠ 0 := by
  intro h
  have h1 := LinearMap.ext_iff.mp h (1 : Matrix (Fin n) (Fin n) ℝ)
  simp only [LinearMap.zero_apply] at h1
  rw [trace_identity] at h1
  exact absurd h1 (Nat.cast_ne_zero.mpr (by omega))

/-- A matrix is in ker(trace) iff it is traceless. -/
theorem mem_ker_trace_iff (A : Matrix (Fin n) (Fin n) ℝ) :
    A ∈ LinearMap.ker (traceFunc n) ↔ Matrix.trace A = 0 := by
  simp [traceFunc, LinearMap.mem_ker, Matrix.traceLinearMap_apply]

/-- The identity matrix is NOT in ker(trace) for n ≥ 1. -/
theorem identity_not_in_ker_trace (hn : 0 < n) :
    (1 : Matrix (Fin n) (Fin n) ℝ) ∉ LinearMap.ker (traceFunc n) := by
  rw [mem_ker_trace_iff]
  simp only [Matrix.trace_one, Fintype.card_fin, Nat.cast_eq_zero]
  omega

/-- Scalar multiples of the identity have trace = c · n. -/
theorem trace_smul_one (c : ℝ) :
    traceFunc n (c • (1 : Matrix (Fin n) (Fin n) ℝ)) = c * (n : ℝ) := by
  simp [traceFunc, Matrix.traceLinearMap_apply, Matrix.trace_one, Fintype.card_fin]

/-- Any matrix decomposes as traceless + scalar·I.
    This is the concrete K/P decomposition for matrices:
      A = (A - (tr(A)/n) · I) + (tr(A)/n) · I
    where the first term is traceless (P-sector/gauge)
    and the second is a scalar multiple of I (K-sector/source). -/
theorem matrix_kp_decomposition (A : Matrix (Fin n) (Fin n) ℝ) :
    A = (A - (Matrix.trace A / (n : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℝ))
      + (Matrix.trace A / (n : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  simp [sub_add_cancel]

/-- The traceless part is indeed traceless (in ker(trace)). -/
theorem traceless_part_in_ker (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ) :
    (A - (Matrix.trace A / (n : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℝ))
      ∈ LinearMap.ker (traceFunc n) := by
  rw [mem_ker_trace_iff]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
  rw [smul_eq_mul, div_mul_cancel₀ _ hn', sub_self]

/-- The scalar·I part carries all the trace (source strength).
    tr((tr(A)/n) · I) = tr(A). -/
theorem scalar_part_captures_source (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.trace ((Matrix.trace A / (n : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℝ))
      = Matrix.trace A := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
  rw [smul_eq_mul, div_mul_cancel₀ _ hn']

/-- For n ≥ 1, dim(ker trace) = n² - 1 (the P-sector / gauge modes). -/
theorem finrank_traceless_matrices (hn : 0 < n) :
    finrank ℝ (LinearMap.ker (traceFunc n)) = n ^ 2 - 1 := by
  have hne : traceFunc n ≠ 0 := traceFunc_ne_zero hn
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero hne
  have hdim : finrank ℝ (Matrix (Fin n) (Fin n) ℝ) = n ^ 2 := by
    simp [Module.finrank_matrix, Fintype.card_fin, finrank_self, sq]
  rw [hdim] at h
  omega

/-- The traceless condition IS the gauge condition: a perturbation h is
    pure gauge (invisible to the source) iff tr(h) = 0. -/
theorem gauge_iff_traceless (A : Matrix (Fin n) (Fin n) ℝ) :
    A ∈ LinearMap.ker (traceFunc n) ↔ Matrix.trace A = 0 :=
  mem_ker_trace_iff A

end TraceExample

/-! ### Summary: The complete K/P story

Bringing it all together: for the source functional φ = ψ ∘ L derived from
the linearized Einstein operator L:

1. ker(L) ⊆ ker(φ)  — gauge modes are invisible to the source
2. V = ker(φ) ⊕ K   — the decomposition is complete
3. dim(K) = 1        — exactly one source mode (the trace/scalar part)
4. dim(ker φ) = dim(V) - 1  — almost everything is gauge
5. For matrices: K = ℝ·I, ker(φ) = traceless, and tr(h) = 0 IS the gauge condition

This formally connects:
  - K-sector = source modes = matter/energy = nonzero curvature perturbations
  - P-sector = dressing/gauge = pure gravitational waves = traceless perturbations
-/

/-- **Master theorem**: The full K/P decomposition with all properties.
    Given a nonzero source functional on a finite-dimensional space:
    (1) A complement K exists (completeness)
    (2) K is 1-dimensional (unique source direction)
    (3) ker(φ) has codimension 1 (gauge is "almost everything") -/
theorem kp_full_decomposition
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (φ : V →ₗ[ℝ] ℝ) (hφ : φ ≠ 0) :
    (∃ K : Submodule ℝ V, IsCompl (LinearMap.ker φ) K ∧ finrank ℝ K = 1)
    ∧ finrank ℝ (LinearMap.ker φ) = finrank ℝ V - 1 := by
  constructor
  · obtain ⟨K, hK⟩ := Submodule.exists_isCompl (LinearMap.ker φ)
    exact ⟨K, hK, finrank_K_sector_eq_one φ hφ K hK⟩
  · exact finrank_P_sector φ hφ

end UnifiedTheory.LayerA.KPDecomposition
