/-
  UnifiedTheory/LayerC/PeresHorodecki.lean
  ────────────────────────────────────────

  **The Peres–Horodecki PPT (positive partial transpose) separability
  criterion.**

  A. Peres, "Separability Criterion for Density Matrices,"
  Phys. Rev. Lett. 77, 1413 (1996), arXiv:quant-ph/9604005.
  M., P. & R. Horodecki, "Separability of mixed states: necessary and
  sufficient conditions," Phys. Lett. A 223, 1 (1996),
  arXiv:quant-ph/9605038.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  CONTEXT

  A bipartite operator ρ on ℂ^{d_A} ⊗ ℂ^{d_B} is indexed by pairs
  (i,k),(j,l) with i,j ∈ Fin d_A and k,l ∈ Fin d_B.  The **partial
  transpose over the second factor** transposes only the B–indices:

      (ρ^{T_B})_{(i,k),(j,l)} = ρ_{(i,l),(j,k)}.

  PERES (1996, the "easy" but historically pivotal direction):
  if ρ is *separable*, ρ = Σ_a p_a σ_a ⊗ τ_a with p_a ≥ 0 and each
  σ_a, τ_a positive semidefinite, then ρ^{T_B} ⪰ 0.  Equivalently:
  if ρ^{T_B} is **not** PSD, ρ is *entangled*.  This is because a
  product state partial-transposes to σ ⊗ τᵀ — and transpose preserves
  positive semidefiniteness — so each summand stays PSD, and a
  nonnegative sum of PSD matrices is PSD.

  HORODECKI (1996): in dimensions 2×2 and 2×3 the criterion is *exact*:
  PPT ⟺ separable.  In higher dimension there exist PPT entangled
  states (bound entanglement).  The maximally entangled Bell state
  violates PPT (its partial transpose has eigenvalue −1/2), which is the
  canonical entanglement witness.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  WHAT IS PROVED UNCONDITIONALLY HERE

  • `partialTransposeB`               — the partial transpose, explicit;
  • `partialTransposeB_involutive`    — it is an involution;
  • `partialTransposeB_add` / `_smul` / `_zero` / `_sum` — linearity;
  • `partialTransposeB_trace`         — trace-preserving;
  • `partialTransposeB_isHermitian`   — Hermiticity-preserving;
  • `partialTransposeB_product`       — (σ ⊗ τ)^{T_B} = σ ⊗ τᵀ;
  • `partialTransposeB_product_posSemidef`
                                      — a PSD product state is PPT;
  • `peres_separable_isPPT`           — **Peres**: every separable state
                                        is PPT (proved, unconditional);
  • `peres_not_PPT_entangled`         — contrapositive witness form.

  Named targets (require eigenvalue computation / the full exactness
  proof, beyond the convexity core): `Bell_violates_PPT_Target`,
  `Horodecki_2x2_Target`, `Horodecki_2x3_Target`.

  Master bundle: `peres_horodecki_master`.

  Zero `sorry`, zero custom `axiom`.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Matrix.Order

namespace UnifiedTheory.LayerC.PeresHorodecki

open Matrix
open scoped Kronecker BigOperators ComplexOrder

/-! ## The partial transpose over the second tensor factor -/

/-- Partial transpose over the second (B) factor.  Transposes only the
B-indices:  `(ρ^{T_B})_{(i,k),(j,l)} = ρ_{(i,l),(j,k)}`. -/
def partialTransposeB {dA dB : ℕ}
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :
    Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ :=
  fun ik jl => ρ (ik.1, jl.2) (jl.1, ik.2)

@[simp] theorem partialTransposeB_apply {dA dB : ℕ}
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (i j : Fin dA) (k l : Fin dB) :
    partialTransposeB ρ (i, k) (j, l) = ρ (i, l) (j, k) := rfl

/-! ### Involution -/

/-- Partial transpose is an involution: `(ρ^{T_B})^{T_B} = ρ`. -/
theorem partialTransposeB_involutive {dA dB : ℕ}
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :
    partialTransposeB (partialTransposeB ρ) = ρ := by
  funext ik jl
  rfl

/-! ### Linearity -/

@[simp] theorem partialTransposeB_zero {dA dB : ℕ} :
    partialTransposeB (0 : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) = 0 := by
  funext ik jl; rfl

theorem partialTransposeB_add {dA dB : ℕ}
    (ρ σ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :
    partialTransposeB (ρ + σ) = partialTransposeB ρ + partialTransposeB σ := by
  funext ik jl; rfl

theorem partialTransposeB_smul {dA dB : ℕ} (c : ℂ)
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :
    partialTransposeB (c • ρ) = c • partialTransposeB ρ := by
  funext ik jl; rfl

theorem partialTransposeB_sum {dA dB : ℕ} {ι : Type*} (s : Finset ι)
    (ρ : ι → Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :
    partialTransposeB (∑ a ∈ s, ρ a) = ∑ a ∈ s, partialTransposeB (ρ a) := by
  funext ik jl
  simp only [partialTransposeB, Matrix.sum_apply]

/-! ### Trace preservation -/

/-- Partial transpose preserves the trace.  The diagonal entry at
`(i,k)` of `ρ^{T_B}` is `ρ (i,k) (i,k)`, so the diagonals coincide. -/
theorem partialTransposeB_trace {dA dB : ℕ}
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :
    (partialTransposeB ρ).trace = ρ.trace := by
  simp only [Matrix.trace, Matrix.diag]
  apply Finset.sum_congr rfl
  intro ik _
  rcases ik with ⟨i, k⟩
  rfl

/-! ### Hermiticity preservation -/

/-- Partial transpose preserves Hermiticity.  Writing the Hermiticity
condition entrywise, `(ρ^{T_B})^*_{(j,l),(i,k)} = ρ^*_{(j,k),(i,l)} =
ρ_{(i,l),(j,k)} = (ρ^{T_B})_{(i,k),(j,l)}`. -/
theorem partialTransposeB_isHermitian {dA dB : ℕ}
    {ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ} (hρ : ρ.IsHermitian) :
    (partialTransposeB ρ).IsHermitian := by
  ext ik jl
  rcases ik with ⟨i, k⟩
  rcases jl with ⟨j, l⟩
  have h := congrFun (congrFun hρ (i, l)) (j, k)
  simp only [conjTranspose_apply, partialTransposeB_apply]
  simpa [conjTranspose_apply] using h

/-! ## The product-state partial transpose formula -/

/-- For a product state, the partial transpose acts only on the second
factor:  `(σ ⊗ τ)^{T_B} = σ ⊗ τᵀ`. -/
theorem partialTransposeB_product {dA dB : ℕ}
    (σ : Matrix (Fin dA) (Fin dA) ℂ) (τ : Matrix (Fin dB) (Fin dB) ℂ) :
    partialTransposeB (σ ⊗ₖ τ) = σ ⊗ₖ τᵀ := by
  funext ik jl
  rcases ik with ⟨i, k⟩
  rcases jl with ⟨j, l⟩
  simp only [partialTransposeB_apply, kronecker_apply, transpose_apply]

/-- A product of positive-semidefinite states is PPT:
`(σ ⊗ τ)^{T_B} = σ ⊗ τᵀ ⪰ 0`, since transpose preserves PSD and the
Kronecker product of PSD matrices is PSD. -/
theorem partialTransposeB_product_posSemidef {dA dB : ℕ}
    {σ : Matrix (Fin dA) (Fin dA) ℂ} {τ : Matrix (Fin dB) (Fin dB) ℂ}
    (hσ : σ.PosSemidef) (hτ : τ.PosSemidef) :
    (partialTransposeB (σ ⊗ₖ τ)).PosSemidef := by
  rw [partialTransposeB_product]
  exact hσ.kronecker hτ.transpose

/-! ## PPT and separability predicates -/

/-- A bipartite state is **PPT** (positive partial transpose) if its
partial transpose over the B factor is positive semidefinite. -/
def IsPPT {dA dB : ℕ}
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) : Prop :=
  (partialTransposeB ρ).PosSemidef

/-- A bipartite state is **separable** if it is a finite nonnegative
combination of product states ρ = Σ_a p_a (σ_a ⊗ τ_a) with p_a ≥ 0 and
each σ_a, τ_a positive semidefinite. -/
def IsSeparable {dA dB : ℕ}
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) : Prop :=
  ∃ (n : ℕ) (p : Fin n → ℝ)
    (σ : Fin n → Matrix (Fin dA) (Fin dA) ℂ)
    (τ : Fin n → Matrix (Fin dB) (Fin dB) ℂ),
    (∀ a, 0 ≤ p a) ∧ (∀ a, (σ a).PosSemidef) ∧ (∀ a, (τ a).PosSemidef) ∧
    ρ = ∑ a : Fin n, (p a : ℂ) • (σ a ⊗ₖ τ a)

/-! ## The Peres direction (proved unconditionally) -/

/-- **Peres (1996).**  Every separable state is PPT.

The partial transpose is linear, so it distributes over the separable
decomposition; each product summand transposes to `p_a • (σ_a ⊗ τ_aᵀ)`,
which is positive semidefinite (transpose and Kronecker preserve PSD,
and `p_a ≥ 0`).  A finite nonnegative sum of PSD matrices is PSD. -/
theorem peres_separable_isPPT {dA dB : ℕ}
    {ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ}
    (hρ : IsSeparable ρ) : IsPPT ρ := by
  obtain ⟨n, p, σ, τ, hp, hσ, hτ, hdecomp⟩ := hρ
  unfold IsPPT
  rw [hdecomp, partialTransposeB_sum]
  apply Matrix.posSemidef_sum
  intro a _
  rw [partialTransposeB_smul, partialTransposeB_product]
  -- p a • (σ a ⊗ τ aᵀ) with p a ≥ 0 and σ a ⊗ τ aᵀ PSD
  have hpsd : (σ a ⊗ₖ (τ a)ᵀ).PosSemidef := (hσ a).kronecker (hτ a).transpose
  have : ((p a : ℂ) • (σ a ⊗ₖ (τ a)ᵀ)) = (p a : ℝ) • (σ a ⊗ₖ (τ a)ᵀ) := by
    rw [Complex.coe_smul]
  rw [this]
  exact hpsd.smul (hp a)

/-- **Contrapositive (the entanglement witness form).**  If the partial
transpose of ρ fails to be positive semidefinite, then ρ is entangled
(not separable).  This is how a non-PSD partial transpose certifies
entanglement. -/
theorem peres_not_PPT_entangled {dA dB : ℕ}
    {ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ}
    (h : ¬ (partialTransposeB ρ).PosSemidef) : ¬ IsSeparable ρ :=
  fun hsep => h (peres_separable_isPPT hsep)

/-! ## The Bell state and its partial transpose (explicit witness) -/

/-- The (unnormalized) two-qubit maximally entangled state
`|Φ⟩ = |00⟩ + |11⟩`, as the rank-one density `|Φ⟩⟨Φ|` on
ℂ² ⊗ ℂ² = ℂ^{Fin 2 × Fin 2}.  Entries are `1` on the four positions
`(i,k),(j,l)` with `i=k` and `j=l`, else `0`. -/
def bellState : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun ik jl => if ik.1 = ik.2 ∧ jl.1 = jl.2 then 1 else 0

/-- The Bell state is positive semidefinite (it is a rank-one
projector-type Gram matrix `vᵀ v` with `v_{(i,k)} = [i=k]`). -/
theorem bellState_posSemidef : bellState.PosSemidef := by
  -- bellState = vecMulVec v (star v) with v (i,k) = if i = k then 1 else 0
  have hv : bellState =
      Matrix.vecMulVec (fun ik => if ik.1 = ik.2 then (1 : ℂ) else 0)
        (fun jl => star (if jl.1 = jl.2 then (1 : ℂ) else 0)) := by
    funext ik jl
    simp only [bellState, Matrix.vecMulVec_apply]
    by_cases hik : ik.1 = ik.2 <;> by_cases hjl : jl.1 = jl.2 <;>
      simp [hik, hjl]
  rw [hv]
  exact Matrix.posSemidef_vecMulVec_self_star _

/-- The partial transpose of the Bell state: it has entry `1` at
`(i,k),(j,l)` whenever `i=l` and `j=k`.  Concretely this swaps the
`|01⟩⟨10|` and `|10⟩⟨01|` coherences onto the diagonal block, producing
the SWAP-like matrix whose `−1/2` eigenvalue witnesses entanglement. -/
theorem bellState_partialTransposeB_apply (i j k l : Fin 2) :
    partialTransposeB bellState (i, k) (j, l) =
      (if i = l ∧ j = k then (1 : ℂ) else 0) := by
  simp only [partialTransposeB_apply, bellState]

/-- The partial transpose of the Bell state is **not** positive
semidefinite — the canonical entanglement witness.  Tested on the
vector `e_{(0,1)} − e_{(1,0)}`: the quadratic form evaluates to `−2 < 0`.
(In the normalized state this is the eigenvalue `−1/2`.) -/
theorem bellState_not_PPT : ¬ (partialTransposeB bellState).PosSemidef := by
  intro h
  -- the antisymmetric test vector v = e_{(0,1)} − e_{(1,0)}
  let v : (Fin 2 × Fin 2) → ℂ :=
    fun x => if x = (0, 1) then 1 else if x = (1, 0) then -1 else 0
  have hquad := h.dotProduct_mulVec_nonneg v
  -- compute star v ⬝ᵥ (M *ᵥ v) = -2, contradicting 0 ≤ ·
  have hval : (star v ⬝ᵥ (partialTransposeB bellState *ᵥ v)) = (-2 : ℂ) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two,
      bellState_partialTransposeB_apply, v]
    norm_num
  rw [hval] at hquad
  -- 0 ≤ -2 in the complex order forces 0 ≤ (-2).re = -2, false.
  have hre : (0 : ℝ) ≤ ((-2 : ℂ)).re := (Complex.nonneg_iff.mp hquad).1
  norm_num [Complex.neg_re] at hre

/-! ## Named targets: Bell witness and Horodecki exactness -/

/-- **Bell-violates-PPT target** (now a *theorem*, discharged above):
the maximally entangled state is PSD yet its partial transpose is not,
exhibiting an entangled PPT-violating state. -/
def Bell_violates_PPT_Target : Prop :=
  bellState.PosSemidef ∧ ¬ (partialTransposeB bellState).PosSemidef

theorem bell_violates_PPT : Bell_violates_PPT_Target :=
  ⟨bellState_posSemidef, bellState_not_PPT⟩

/-- **Horodecki 2×2 exactness target.**  In dimension 2×2 the PPT
criterion is *necessary and sufficient*: a state is PPT iff separable.
The forward (Peres) direction is `peres_separable_isPPT`; the converse
requires the Horodecki positive-map argument (Størmer–Woronowicz: all
positive maps on 2×2/2×3 are decomposable), stated here as a target. -/
def Horodecki_2x2_Target : Prop :=
  ∀ ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
    ρ.PosSemidef → (IsPPT ρ ↔ IsSeparable ρ)

/-- **Horodecki 2×3 exactness target.**  Likewise PPT ⟺ separable in
dimension 2×3 (the other case where all positive maps are
decomposable). -/
def Horodecki_2x3_Target : Prop :=
  ∀ ρ : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ,
    ρ.PosSemidef → (IsPPT ρ ↔ IsSeparable ρ)

/-! ## Master bundle -/

/-- **Peres–Horodecki master bundle.**

Unconditional facts:
  • partial transpose is an involution, linear, trace- and
    Hermiticity-preserving, and sends `σ ⊗ τ ↦ σ ⊗ τᵀ`;
  • **Peres**: every separable state is PPT (proved);
  • the maximally entangled Bell state is PSD yet PPT-violating
    (entanglement witness, proved explicitly).

Named targets carried forward:
  • Horodecki exactness in 2×2 and 2×3 (PPT ⟺ separable). -/
theorem peres_horodecki_master :
    -- algebra of the partial transpose
    (∀ {dA dB : ℕ} (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ),
      partialTransposeB (partialTransposeB ρ) = ρ) ∧
    (∀ {dA dB : ℕ} (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ),
      (partialTransposeB ρ).trace = ρ.trace) ∧
    (∀ {dA dB : ℕ} (σ : Matrix (Fin dA) (Fin dA) ℂ)
        (τ : Matrix (Fin dB) (Fin dB) ℂ),
      partialTransposeB (σ ⊗ₖ τ) = σ ⊗ₖ τᵀ) ∧
    -- Peres: separable ⟹ PPT
    (∀ {dA dB : ℕ} {ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ},
      IsSeparable ρ → IsPPT ρ) ∧
    -- Bell witness
    Bell_violates_PPT_Target ∧
    -- Horodecki exactness targets
    (Horodecki_2x2_Target → Horodecki_2x3_Target →
      (Horodecki_2x2_Target ∧ Horodecki_2x3_Target)) :=
  ⟨fun ρ => partialTransposeB_involutive ρ,
   fun ρ => partialTransposeB_trace ρ,
   fun σ τ => partialTransposeB_product σ τ,
   fun hsep => peres_separable_isPPT hsep,
   bell_violates_PPT,
   fun h2 h3 => ⟨h2, h3⟩⟩

end UnifiedTheory.LayerC.PeresHorodecki
