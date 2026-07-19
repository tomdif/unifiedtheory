/-
  UnifiedTheory/LayerC/CHSHMonogamy.lean
  ───────────────────────────────────────

  **CHSH-monogamy phenomenon for the 3-qubit GHZ state.**

  A three-qubit pure state `|ψ⟩_{ABC} ∈ ℂ⁸` has two bipartite-marginal
  density matrices `ρ_{AB}` and `ρ_{AC}` obtained by tracing out one of
  the three qubits.  The Toner–Verstraete monogamy inequality
  (Phys. Rev. Lett. 102, 110506 (2009)) asserts

      S_{AB}² + S_{AC}² ≤ 8

  where `S_{XY}` is the maximum CHSH value extractable from `ρ_{XY}`
  over bipartite observables.  In particular, if Alice and Bob saturate
  Tsirelson with `S_{AB} = 2√2 ⇒ S_{AB}² = 8`, then `S_{AC}² ≤ 0` and
  Alice–Charlie correlations cannot CHSH-violate.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT THIS FILE FORMALIZES — HONEST SCOPE

  The full Toner–Verstraete inequality requires Pauli/Bloch
  parametrization of arbitrary 3-qubit states and is out of scope
  (multi-session work).  This file ships a tractable subset that
  captures the *operationally meaningful* monogamy phenomenon, anchored
  on the 3-qubit GHZ state `|GHZ⟩ = (|000⟩ + |111⟩)/√2`.

  Headline results:

  • `ThreeQubitPureState` — a normalized wavefunction `ψ : Fin 8 → ℂ`.

  • `ρAB`, `ρAC` — the two bipartite marginals, defined directly
    via the partial-trace formula on the wavefunction.

  • `ghzCDM_AB`, `ghzCDM_AC` — both reduce to the *same* classically
    correlated state `½(|00⟩⟨00| + |11⟩⟨11|)` (a diagonal density
    matrix `diag(½, 0, 0, ½)`).

  • `ghz_marginal_correlation_factorizes` — for the GHZ AB-marginal,
    `⟨(eq θa) ⊗ (eq θb)⟩_{ρ_{AB}} = cos θa · cos θb`.  The correlation
    function is FACTORIZABLE — Alice and Bob's outcomes look classically
    independent at the level of equator-observable correlations.

  • `ghz_marginal_chsh_classical_bound` — applying
    `LayerB.SeparableCHSH.chsh_factorizable_bound` to the factorized
    correlation, every CHSH expression evaluated on `ρ_{AB}^{GHZ}` over
    equator observables satisfies `|S| ≤ 2`, the *classical* bound.
    Identically for `ρ_{AC}^{GHZ}` by left/right symmetry of the GHZ
    state.

  • `ghz_marginal_chsh_saturates_classical` — at angles `(0, π/2; 0, 0)`,
    the GHZ marginal CHSH equals `2` exactly, saturating the classical
    bound.

  • `ghz_canonical_singlet_angles_value` — at the *singlet's* Tsirelson-
    saturating angles `(0, π/2; π/4, -π/4)`, the GHZ marginal yields
    `S = √2`, a factor of `2` weaker than the singlet's `2√2`.  This is
    the quantitative monogamy footprint at the canonical CHSH angles.

  • `ghz_tripartite_but_pairwise_classical` — the headline statement:
    the GHZ state is tripartite-entangled (cf. `MerminGHZ.ghz_is_entangled`,
    real-amplitude version) yet every bipartite marginal has a CHSH
    expression bounded by the *classical* limit `2` over equator
    observables.  Tripartite entanglement does NOT distribute as pairwise
    CHSH violation — the Toner–Verstraete saturation regime.

  • `weak_chsh_monogamy_via_factorizability` — for the GHZ state,
    `S_{AB}² + S_{AC}² ≤ 8` directly (each `≤ 4`).  Saturates the
    true Toner–Verstraete bound at the classical-classical extreme
    (`S_{AB} = S_{AC} = 2` ⇒ `4 + 4 = 8`).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS *NOT* PROVED HERE

  • The full Toner–Verstraete inequality `S² + S'² ≤ 8` for arbitrary
    3-qubit pure states.  The proof requires explicit Bloch-vector
    parametrization of the AB and AC marginals plus a delicate sum-
    of-squares argument over the Bloch coefficients (Toner 2009 §III).
    We expose the GHZ corner of the inequality (which saturates it)
    rather than the full envelope.

  • The Tsirelson bound `S ≤ 2√2` for arbitrary 2-qubit density matrices
    over arbitrary observables.  Only the singlet/equator special case
    is covered upstream in `LayerB.TsirelsonBound`.

  • `chshValue ρ := sup over observables` — we do NOT define the
    supremum, only the CHSH expression at specific angle choices and
    a bound for ALL equator-observable angle choices via
    `chsh_factorizable_bound`.

  Zero `sorry`. Zero custom `axiom`.  Only Lean's `propext`,
  `Classical.choice`, and `Quot.sound`.
-/

import UnifiedTheory.LayerC.BipartiteQubitCHSH
import UnifiedTheory.LayerB.PartialTrace
import UnifiedTheory.LayerB.SeparableCHSH
import UnifiedTheory.LayerB.TsirelsonBound

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.CHSHMonogamy

open Matrix Complex
open scoped BigOperators ComplexOrder Kronecker
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.PartialTrace
open UnifiedTheory.LayerC.LocalRealisticAxioms
open UnifiedTheory.LayerB.TsirelsonBound
open UnifiedTheory.LayerC.BipartiteQubitCHSH

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THREE-QUBIT PURE STATE + TRIPLE INDEXING
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Fin 8 is decomposed as Fin 2 × Fin 2 × Fin 2 via the explicit
    bit-encoding  i = 4·a + 2·b + c  (the "big-endian" 3-qubit
    computational basis):

       index   (a, b, c)
       ────────────────
         0     (0, 0, 0)   = |000⟩
         1     (0, 0, 1)   = |001⟩
         2     (0, 1, 0)   = |010⟩
         3     (0, 1, 1)   = |011⟩
         4     (1, 0, 0)   = |100⟩
         5     (1, 0, 1)   = |101⟩
         6     (1, 1, 0)   = |110⟩
         7     (1, 1, 1)   = |111⟩

    This matches the existing `finProdFinEquiv (m:=2) (n:=2)` convention
    `(i, j) ↦ j + 2·i` for the Fin 4 = AB grouping.  The Fin 8 = AB ⊗ C
    grouping uses `finProdFinEquiv (m:=4) (n:=2)`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The bit-encoding map `Fin 2 × Fin 2 × Fin 2 → Fin 8`. -/
def triple (a b c : Fin 2) : Fin 8 :=
  finProdFinEquiv (m := 4) (n := 2)
    (finProdFinEquiv (m := 2) (n := 2) (a, b), c)

/-- The 8 explicit triple-to-Fin-8 evaluations. -/
private lemma triple_table :
    triple 0 0 0 = 0 ∧ triple 0 0 1 = 1
  ∧ triple 0 1 0 = 2 ∧ triple 0 1 1 = 3
  ∧ triple 1 0 0 = 4 ∧ triple 1 0 1 = 5
  ∧ triple 1 1 0 = 6 ∧ triple 1 1 1 = 7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- A normalized three-qubit pure state vector `ψ ∈ ℂ⁸`. -/
structure ThreeQubitPureState where
  /-- The wavefunction. -/
  ψ : Fin 8 → ℂ
  /-- Normalization `∑_i |ψ_i|² = 1`. -/
  normalized : (∑ i, Complex.normSq (ψ i)) = 1

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: BIPARTITE MARGINALS ρ_AB AND ρ_AC

    Defined directly via the partial-trace formula on the wavefunction:

       (ρ_AB)[(a,b),(a',b')] := Σ_c ψ(a,b,c) · star(ψ(a',b',c))
       (ρ_AC)[(a,c),(a',c')] := Σ_b ψ(a,b,c) · star(ψ(a',b,c'))

    Both are 4×4 matrices indexed by Fin 4 ≅ Fin 2 × Fin 2.  The Fin 4
    index `i ∈ {0,1,2,3}` decomposes as `(i/2, i%2) = (a, b)` or
    `(a, c)` via `finProdFinEquiv (m := 2) (n := 2)`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The "first qubit" projection of a Fin 4 index (matches
    `finProdFinEquiv (m:=2) (n:=2)).symm`'s first component). -/
def fin4_first (i : Fin 4) : Fin 2 := if i.val < 2 then 0 else 1

/-- The "second qubit" projection of a Fin 4 index. -/
def fin4_second (i : Fin 4) : Fin 2 := if i.val % 2 = 0 then 0 else 1

/-- Explicit table for fin4_first. -/
private lemma fin4_first_table :
    fin4_first 0 = 0 ∧ fin4_first 1 = 0
  ∧ fin4_first 2 = 1 ∧ fin4_first 3 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- Explicit table for fin4_second. -/
private lemma fin4_second_table :
    fin4_second 0 = 0 ∧ fin4_second 1 = 1
  ∧ fin4_second 2 = 0 ∧ fin4_second 3 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- The Alice–Bob reduced state: trace out Charlie's qubit. -/
noncomputable def ρAB (s : ThreeQubitPureState) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  fun ab1 ab2 =>
    ∑ c : Fin 2,
      s.ψ (triple (fin4_first ab1) (fin4_second ab1) c)
        * star (s.ψ (triple (fin4_first ab2) (fin4_second ab2) c))

/-- The Alice–Charlie reduced state: trace out Bob's qubit. -/
noncomputable def ρAC (s : ThreeQubitPureState) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  fun ac1 ac2 =>
    ∑ b : Fin 2,
      s.ψ (triple (fin4_first ac1) b (fin4_second ac1))
        * star (s.ψ (triple (fin4_first ac2) b (fin4_second ac2)))

/-! ### Local copy of `eq_entries` (which is `private`
    in `BipartiteQubitCHSH`). -/

private lemma eq_entries (θ : ℝ) :
    equatorObservable θ 0 0 = (Real.cos θ : ℂ)
  ∧ equatorObservable θ 0 1 = (Real.sin θ : ℂ)
  ∧ equatorObservable θ 1 0 = (Real.sin θ : ℂ)
  ∧ equatorObservable θ 1 1 = -(Real.cos θ : ℂ) := by
  unfold equatorObservable σz σx
  refine ⟨?_, ?_, ?_, ?_⟩
    <;> simp [Matrix.add_apply, smul_eq_mul]

/-! ### Structural properties of the marginals. -/

/-- `ρAB` is Hermitian: each entry is the conjugate of the transposed
    entry, because `star ∘ star = id` and `star` distributes over `*`
    and `+`. -/
theorem ρAB_isHermitian (s : ThreeQubitPureState) :
    (ρAB s).IsHermitian := by
  ext ab1 ab2
  change star (ρAB s ab2 ab1) = ρAB s ab1 ab2
  unfold ρAB
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [show star
        (s.ψ (triple (fin4_first ab2) (fin4_second ab2) c) *
         star (s.ψ (triple (fin4_first ab1) (fin4_second ab1) c)))
      = star (star (s.ψ (triple (fin4_first ab1) (fin4_second ab1) c))) *
        star (s.ψ (triple (fin4_first ab2) (fin4_second ab2) c))
      from StarMul.star_mul _ _]
  rw [star_star]

/-- `ρAC` is Hermitian. -/
theorem ρAC_isHermitian (s : ThreeQubitPureState) :
    (ρAC s).IsHermitian := by
  ext ac1 ac2
  change star (ρAC s ac2 ac1) = ρAC s ac1 ac2
  unfold ρAC
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [show star
        (s.ψ (triple (fin4_first ac2) b (fin4_second ac2)) *
         star (s.ψ (triple (fin4_first ac1) b (fin4_second ac1))))
      = star (star (s.ψ (triple (fin4_first ac1) b (fin4_second ac1)))) *
        star (s.ψ (triple (fin4_first ac2) b (fin4_second ac2)))
      from StarMul.star_mul _ _]
  rw [star_star]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: THE 3-QUBIT GHZ STATE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    |GHZ⟩ = (|000⟩ + |111⟩) / √2  has nonzero amplitudes at Fin 8
    indices 0 and 7 only, each equal to 1/√2. -/

/-- The GHZ wavefunction values, indexed by `Fin 8`. -/
noncomputable def ghzVec : Fin 8 → ℂ := fun i =>
  if i = 0 then ((1 : ℂ) / (Real.sqrt 2 : ℂ))
  else if i = 7 then ((1 : ℂ) / (Real.sqrt 2 : ℂ))
  else 0

/-- Eight explicit table values. -/
private lemma ghzVec_table :
    ghzVec 0 = (1 : ℂ) / (Real.sqrt 2 : ℂ)
  ∧ ghzVec 1 = 0 ∧ ghzVec 2 = 0 ∧ ghzVec 3 = 0
  ∧ ghzVec 4 = 0 ∧ ghzVec 5 = 0 ∧ ghzVec 6 = 0
  ∧ ghzVec 7 = (1 : ℂ) / (Real.sqrt 2 : ℂ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold ghzVec
  · rw [if_pos rfl]
  · rw [if_neg (by decide), if_neg (by decide)]
  · rw [if_neg (by decide), if_neg (by decide)]
  · rw [if_neg (by decide), if_neg (by decide)]
  · rw [if_neg (by decide), if_neg (by decide)]
  · rw [if_neg (by decide), if_neg (by decide)]
  · rw [if_neg (by decide), if_neg (by decide)]
  · rw [if_neg (by decide), if_pos rfl]

/-- `star (ghzVec)` at each index — real amplitudes so star = id. -/
private lemma star_ghzVec_table :
    star (ghzVec 0) = (1 : ℂ) / (Real.sqrt 2 : ℂ)
  ∧ star (ghzVec 1) = 0 ∧ star (ghzVec 2) = 0 ∧ star (ghzVec 3) = 0
  ∧ star (ghzVec 4) = 0 ∧ star (ghzVec 5) = 0 ∧ star (ghzVec 6) = 0
  ∧ star (ghzVec 7) = (1 : ℂ) / (Real.sqrt 2 : ℂ) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := ghzVec_table
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h0]; rw [star_div₀, star_one, Complex.star_def, Complex.conj_ofReal]
  · rw [h1, star_zero]
  · rw [h2, star_zero]
  · rw [h3, star_zero]
  · rw [h4, star_zero]
  · rw [h5, star_zero]
  · rw [h6, star_zero]
  · rw [h7]; rw [star_div₀, star_one, Complex.star_def, Complex.conj_ofReal]

/-- `(Real.sqrt 2 : ℂ)·(Real.sqrt 2 : ℂ) = 2`.  Re-derived locally to
    avoid a private-lemma import. -/
private lemma sqrt_two_sq_complex' :
    (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = (2 : ℂ) := by
  have h : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)
         = ((Real.sqrt 2 * Real.sqrt 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [h, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- ‖ghzVec‖² = 1. -/
private lemma ghzVec_norm_one :
    (∑ i, Complex.normSq (ghzVec i)) = 1 := by
  rw [show (Finset.univ : Finset (Fin 8))
        = {0, 1, 2, 3, 4, 5, 6, 7} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := ghzVec_table
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  simp only [Complex.normSq_zero, add_zero, zero_add]
  -- ‖1/√2‖² + ‖1/√2‖² = 1/2 + 1/2 = 1
  have hsq : Complex.normSq ((1 : ℂ) / (Real.sqrt 2 : ℂ)) = 1 / 2 := by
    rw [Complex.normSq_div]
    rw [show Complex.normSq (1 : ℂ) = 1 from Complex.normSq_one]
    rw [show Complex.normSq ((Real.sqrt 2 : ℂ)) = 2 from by
      rw [Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]]
  rw [hsq]
  ring

/-- The 3-qubit GHZ state as a `ThreeQubitPureState`. -/
noncomputable def ghzState : ThreeQubitPureState where
  ψ := ghzVec
  normalized := ghzVec_norm_one

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: EXPLICIT FORM OF GHZ MARGINALS

    ρ_{AB}^{GHZ} = ρ_{AC}^{GHZ} = ½·diag(1, 0, 0, 1)
    = ½(|00⟩⟨00| + |11⟩⟨11|), a classically correlated state.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The 4-index decompositions for Fin 4 via finProdFinEquiv.symm.  This
    just mirrors `BipartiteQubitCHSH.fin4_decompose`. -/
private lemma fin4_decomp :
    ((finProdFinEquiv (m := 2) (n := 2)).symm 0 = ((0 : Fin 2), (0 : Fin 2)))
  ∧ ((finProdFinEquiv (m := 2) (n := 2)).symm 1 = ((0 : Fin 2), (1 : Fin 2)))
  ∧ ((finProdFinEquiv (m := 2) (n := 2)).symm 2 = ((1 : Fin 2), (0 : Fin 2)))
  ∧ ((finProdFinEquiv (m := 2) (n := 2)).symm 3 = ((1 : Fin 2), (1 : Fin 2))) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- Auxiliary: `(1 / √2 : ℂ) * (1 / √2 : ℂ) = 1/2`. -/
private lemma one_div_sqrt2_sq :
    ((1 : ℂ) / (Real.sqrt 2 : ℂ)) * ((1 : ℂ) / (Real.sqrt 2 : ℂ)) = (1/2 : ℂ) := by
  rw [div_mul_div_comm, one_mul, sqrt_two_sq_complex']

/-- Auxiliary (inverse form, after simp normalization):
    `(√2 : ℂ)⁻¹ * (√2 : ℂ)⁻¹ = 2⁻¹`. -/
private lemma inv_sqrt2_sq :
    ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = (2 : ℂ)⁻¹ := by
  rw [← mul_inv, sqrt_two_sq_complex']

/-- Define the target diagonal matrix to share between AB and AC proofs. -/
noncomputable def ghzDiagonal : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(1/2 : ℂ), 0, 0, 0;
       0, 0, 0, 0;
       0, 0, 0, 0;
       0, 0, 0, (1/2 : ℂ)]

/-- The diagonal matrix is `1/2` at (0,0), (3,3) and `0` elsewhere. -/
private lemma ghzDiagonal_apply (i j : Fin 4) :
    ghzDiagonal i j =
      if (i = 0 ∧ j = 0) ∨ (i = 3 ∧ j = 3) then (1/2 : ℂ) else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [ghzDiagonal, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_fin_one, Matrix.head_fin_const]

/-- Helper: an entry of `ρAB ghzState` at indices `(a1,b1)` and `(a2,b2)`
    expressed as a sum of two products with literal Fin 8 lookups. -/
private lemma ρAB_at_abc (a1 b1 a2 b2 : Fin 2) :
    ρAB ghzState
        (finProdFinEquiv (m := 2) (n := 2) (a1, b1))
        (finProdFinEquiv (m := 2) (n := 2) (a2, b2))
      = ghzVec (triple a1 b1 0) * star (ghzVec (triple a2 b2 0))
      + ghzVec (triple a1 b1 1) * star (ghzVec (triple a2 b2 1)) := by
  show (∑ c : Fin 2,
          ghzVec (triple (fin4_first (finProdFinEquiv (a1, b1)))
                         (fin4_second (finProdFinEquiv (a1, b1))) c) *
            star (ghzVec (triple (fin4_first (finProdFinEquiv (a2, b2)))
                                 (fin4_second (finProdFinEquiv (a2, b2))) c)))
       = _
  rw [Fin.sum_univ_two]
  -- Need to reduce fin4_first (finProdFinEquiv (a, b)) = a, similarly for second.
  have h_first : ∀ a b : Fin 2,
      fin4_first (finProdFinEquiv (m := 2) (n := 2) (a, b)) = a := by
    intro a b
    fin_cases a <;> fin_cases b <;> rfl
  have h_second : ∀ a b : Fin 2,
      fin4_second (finProdFinEquiv (m := 2) (n := 2) (a, b)) = b := by
    intro a b
    fin_cases a <;> fin_cases b <;> rfl
  rw [h_first a1 b1, h_second a1 b1, h_first a2 b2, h_second a2 b2]

/-- Same helper for ρAC. -/
private lemma ρAC_at_abc (a1 c1 a2 c2 : Fin 2) :
    ρAC ghzState
        (finProdFinEquiv (m := 2) (n := 2) (a1, c1))
        (finProdFinEquiv (m := 2) (n := 2) (a2, c2))
      = ghzVec (triple a1 0 c1) * star (ghzVec (triple a2 0 c2))
      + ghzVec (triple a1 1 c1) * star (ghzVec (triple a2 1 c2)) := by
  show (∑ b : Fin 2,
          ghzVec (triple (fin4_first (finProdFinEquiv (a1, c1))) b
                         (fin4_second (finProdFinEquiv (a1, c1)))) *
            star (ghzVec (triple (fin4_first (finProdFinEquiv (a2, c2))) b
                                 (fin4_second (finProdFinEquiv (a2, c2))))))
       = _
  rw [Fin.sum_univ_two]
  have h_first : ∀ a b : Fin 2,
      fin4_first (finProdFinEquiv (m := 2) (n := 2) (a, b)) = a := by
    intro a b
    fin_cases a <;> fin_cases b <;> rfl
  have h_second : ∀ a b : Fin 2,
      fin4_second (finProdFinEquiv (m := 2) (n := 2) (a, b)) = b := by
    intro a b
    fin_cases a <;> fin_cases b <;> rfl
  rw [h_first a1 c1, h_second a1 c1, h_first a2 c2, h_second a2 c2]

/-- Every index `i : Fin 4` factors as `finProdFinEquiv (a, b)` for unique
    `a, b ∈ Fin 2`.  This packages the per-case 16-fold enumeration. -/
private lemma ρAB_ghz_entry (ab1 ab2 : Fin 4) :
    ρAB ghzState ab1 ab2 = ghzDiagonal ab1 ab2 := by
  -- Surface (a1, b1) and (a2, b2).
  obtain ⟨⟨a1, b1⟩, rfl⟩ := (finProdFinEquiv (m := 2) (n := 2)).surjective ab1
  obtain ⟨⟨a2, b2⟩, rfl⟩ := (finProdFinEquiv (m := 2) (n := 2)).surjective ab2
  rw [ρAB_at_abc, ghzDiagonal_apply]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := ghzVec_table
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7⟩ := star_ghzVec_table
  obtain ⟨t000, t001, t010, t011, t100, t101, t110, t111⟩ := triple_table
  -- 16 cases. For each, both triple_table lookups, both ghz lookups close it.
  fin_cases a1 <;> fin_cases b1 <;> fin_cases a2 <;> fin_cases b2 <;>
    simp [t000, t001, t010, t011, t100, t101, t110, t111,
          h0, h1, h2, h3, h4, h5, h6, h7,
          s0, s1, s2, s3, s4, s5, s6, s7,
          one_div_sqrt2_sq, inv_sqrt2_sq,
          show (finProdFinEquiv (m := 2) (n := 2)) (0, 0) = (0 : Fin 4) from rfl,
          show (finProdFinEquiv (m := 2) (n := 2)) (0, 1) = (1 : Fin 4) from rfl,
          show (finProdFinEquiv (m := 2) (n := 2)) (1, 0) = (2 : Fin 4) from rfl,
          show (finProdFinEquiv (m := 2) (n := 2)) (1, 1) = (3 : Fin 4) from rfl]

private lemma ρAC_ghz_entry (ac1 ac2 : Fin 4) :
    ρAC ghzState ac1 ac2 = ghzDiagonal ac1 ac2 := by
  obtain ⟨⟨a1, c1⟩, rfl⟩ := (finProdFinEquiv (m := 2) (n := 2)).surjective ac1
  obtain ⟨⟨a2, c2⟩, rfl⟩ := (finProdFinEquiv (m := 2) (n := 2)).surjective ac2
  rw [ρAC_at_abc, ghzDiagonal_apply]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := ghzVec_table
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7⟩ := star_ghzVec_table
  obtain ⟨t000, t001, t010, t011, t100, t101, t110, t111⟩ := triple_table
  fin_cases a1 <;> fin_cases c1 <;> fin_cases a2 <;> fin_cases c2 <;>
    simp [t000, t001, t010, t011, t100, t101, t110, t111,
          h0, h1, h2, h3, h4, h5, h6, h7,
          s0, s1, s2, s3, s4, s5, s6, s7,
          one_div_sqrt2_sq, inv_sqrt2_sq,
          show (finProdFinEquiv (m := 2) (n := 2)) (0, 0) = (0 : Fin 4) from rfl,
          show (finProdFinEquiv (m := 2) (n := 2)) (0, 1) = (1 : Fin 4) from rfl,
          show (finProdFinEquiv (m := 2) (n := 2)) (1, 0) = (2 : Fin 4) from rfl,
          show (finProdFinEquiv (m := 2) (n := 2)) (1, 1) = (3 : Fin 4) from rfl]

/-- The 4×4 GHZ AB-marginal: diagonal `(1/2, 0, 0, 1/2)`. -/
theorem ρAB_ghz_diagonal : ρAB ghzState = ghzDiagonal := by
  ext ab1 ab2; exact ρAB_ghz_entry ab1 ab2

/-- The 4×4 GHZ AC-marginal: same as AB by left-right symmetry of the
    GHZ state under swap of the B and C qubits. -/
theorem ρAC_ghz_diagonal : ρAC ghzState = ghzDiagonal := by
  ext ac1 ac2; exact ρAC_ghz_entry ac1 ac2

/-! ### Properties of `ghzDiagonal`. -/

/-- `ghzDiagonal` has trace 1. -/
private theorem ghzDiagonal_trace_one : ghzDiagonal.trace = 1 := by
  rw [Matrix.trace]
  rw [show (Finset.univ : Finset (Fin 4))
        = {0, 1, 2, 3} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [Matrix.diag_apply]
  simp [ghzDiagonal_apply]
  norm_num

/-- `ghzDiagonal = ½·diag(1,0,0,1)` is positive semidefinite.  Proof: it
    equals `V · V†` where `V : Fin 4 → Fin 2 → ℂ` is the 4×2 matrix with
    `V[0,0] = 1/√2`, `V[3,1] = 1/√2`, all other entries 0. -/
private theorem ghzDiagonal_posSemidef : ghzDiagonal.PosSemidef := by
  set V : Matrix (Fin 4) (Fin 2) ℂ :=
    Matrix.of (fun i j =>
      if i = 0 ∧ j = 0 then ((1 : ℂ) / (Real.sqrt 2 : ℂ))
      else if i = 3 ∧ j = 1 then ((1 : ℂ) / (Real.sqrt 2 : ℂ))
      else 0) with hV_def
  have hVVt : V * V.conjTranspose = ghzDiagonal := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    rw [Matrix.conjTranspose_apply, Matrix.conjTranspose_apply]
    simp only [V, Matrix.of_apply]
    rw [ghzDiagonal_apply]
    fin_cases i <;> fin_cases j <;>
      simp [star_one, Complex.star_def, Complex.conj_ofReal,
            one_div_sqrt2_sq, inv_sqrt2_sq]
  rw [← hVVt]
  exact Matrix.posSemidef_self_mul_conjTranspose V

/-! ### The GHZ marginal as a `ComplexDensityMatrix 4`. -/

/-- The classically-correlated state `½·diag(1, 0, 0, 1)` is Hermitian. -/
private theorem ghzMarginal_isHermitian :
    (ρAB ghzState).IsHermitian := ρAB_isHermitian ghzState

/-- The classically-correlated state has trace 1. -/
private theorem ghzMarginal_trace_one :
    (ρAB ghzState).trace = 1 := by
  rw [ρAB_ghz_diagonal]; exact ghzDiagonal_trace_one

/-- The AB marginal of the GHZ state is positive semidefinite. -/
private theorem ghzMarginal_posSemidef :
    (ρAB ghzState).PosSemidef := by
  rw [ρAB_ghz_diagonal]
  exact ghzDiagonal_posSemidef

/-- The GHZ AB-marginal packaged as a `ComplexDensityMatrix 4`. -/
noncomputable def ghzCDM_AB : ComplexDensityMatrix 4 :=
  UnitaryQuantum.ofPosSemidef 4
    (ρAB ghzState)
    ghzMarginal_isHermitian
    ghzMarginal_trace_one
    ghzMarginal_posSemidef

/-- The GHZ AC-marginal as a `ComplexDensityMatrix 4`.  By
    `ρAC_ghz_diagonal` the underlying matrix is the same as `ρAB`. -/
private theorem ghzMarginal_AC_isHermitian :
    (ρAC ghzState).IsHermitian := ρAC_isHermitian ghzState

private theorem ghzMarginal_AC_trace_one :
    (ρAC ghzState).trace = 1 := by
  rw [ρAC_ghz_diagonal]; exact ghzDiagonal_trace_one

private theorem ghzMarginal_AC_posSemidef :
    (ρAC ghzState).PosSemidef := by
  rw [ρAC_ghz_diagonal]; exact ghzDiagonal_posSemidef

noncomputable def ghzCDM_AC : ComplexDensityMatrix 4 :=
  UnitaryQuantum.ofPosSemidef 4
    (ρAC ghzState)
    ghzMarginal_AC_isHermitian
    ghzMarginal_AC_trace_one
    ghzMarginal_AC_posSemidef

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: THE GHZ MARGINAL CORRELATION FACTORIZES

    For equator-plane observables on each side,
       ⟨(eq θa) ⊗ (eq θb)⟩_{ρ_{AB}^{GHZ}}
        = (½)·(A[0,0]·B[0,0] + A[1,1]·B[1,1])
        = (½)·(cos θa · cos θb + (-cos θa) · (-cos θb))
        = cos θa · cos θb.

    The correlation is a product f(θa)·g(θb) — the classical Bell-
    locality fingerprint, despite the underlying tripartite entanglement.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Trace of `ghzDiagonal · M` reduces to `(1/2)·(M[0,0] + M[3,3])`. -/
private lemma trace_ghzDiagonal_mul (M : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix.trace (ghzDiagonal * M)
      = (1/2 : ℂ) * (M 0 0 + M 3 3) := by
  rw [Matrix.trace]
  rw [show (Finset.univ : Finset (Fin 4))
        = {0, 1, 2, 3} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  -- Each (ghzDiagonal·M)[i,i] = ∑_k ghzDiagonal[i,k] M[k,i]
  -- ghzDiagonal[i,k] nonzero only for (i,k)=(0,0) or (3,3).
  have h_row : ∀ i : Fin 4, (∑ k, ghzDiagonal i k * M k i)
              = (if i = 0 then (1/2 : ℂ) * M 0 0 else 0)
              + (if i = 3 then (1/2 : ℂ) * M 3 3 else 0) := by
    intro i
    rw [show (Finset.univ : Finset (Fin 4))
          = {0, 1, 2, 3} from by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton]
    rw [ghzDiagonal_apply, ghzDiagonal_apply, ghzDiagonal_apply, ghzDiagonal_apply]
    fin_cases i <;> simp
  rw [h_row 0, h_row 1, h_row 2, h_row 3]
  simp
  ring

/-- Trace of `ρAB ghzState · M` reduces to `(1/2)·(M[0,0] + M[3,3])`. -/
private lemma trace_ghzAB_mul (M : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix.trace (ρAB ghzState * M)
      = (1/2 : ℂ) * (M 0 0 + M 3 3) := by
  rw [ρAB_ghz_diagonal]; exact trace_ghzDiagonal_mul M

/-- Analog for AC marginal. -/
private lemma trace_ghzAC_mul (M : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix.trace (ρAC ghzState * M)
      = (1/2 : ℂ) * (M 0 0 + M 3 3) := by
  rw [ρAC_ghz_diagonal]; exact trace_ghzDiagonal_mul M

/-- Entry (0,0) of `kroneckerReindexed A B` is `A[0,0] · B[0,0]`. -/
private lemma kron_00 (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    kroneckerReindexed A B 0 0 = A 0 0 * B 0 0 := by
  unfold kroneckerReindexed
  rw [Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
  obtain ⟨h0, _, _, _⟩ := fin4_decomp
  rw [h0]

/-- Entry (3,3) of `kroneckerReindexed A B` is `A[1,1] · B[1,1]`. -/
private lemma kron_33 (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    kroneckerReindexed A B 3 3 = A 1 1 * B 1 1 := by
  unfold kroneckerReindexed
  rw [Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
  obtain ⟨_, _, _, h3⟩ := fin4_decomp
  rw [h3]

/-- **THE FACTORIZATION THEOREM.**  For the GHZ AB-marginal and equator-
    plane observables, the correlation is `cos θa · cos θb`. -/
theorem ghz_marginal_AB_correlation_factorizes (θa θb : ℝ) :
    correlation ghzCDM_AB (equatorObservable θa) (equatorObservable θb)
      = Real.cos θa * Real.cos θb := by
  unfold correlation
  -- ghzCDM_AB.M is definitionally ρAB ghzState
  have hρM : ghzCDM_AB.M = ρAB ghzState := rfl
  rw [hρM]
  rw [trace_ghzAB_mul]
  -- Now the goal involves (1/2) * (M[0,0] + M[3,3]) with M = kron(eq θa, eq θb)
  rw [kron_00, kron_33]
  -- A[0,0] = cos θa, A[1,1] = -cos θa, similarly B.
  obtain ⟨hA00, _, _, hA11⟩ := eq_entries θa
  obtain ⟨hB00, _, _, hB11⟩ := eq_entries θb
  rw [hA00, hA11, hB00, hB11]
  -- (1/2) * (cos θa · cos θb + (-cos θa) · (-cos θb)) = cos θa · cos θb
  have h_real :
      ((1/2 : ℝ) *
          (Real.cos θa * Real.cos θb
           + (-Real.cos θa) * (-Real.cos θb)))
        = Real.cos θa * Real.cos θb := by ring
  have h_cast :
      (((1/2 : ℝ) *
          (Real.cos θa * Real.cos θb
           + (-Real.cos θa) * (-Real.cos θb)) : ℝ) : ℂ)
        = (1/2 : ℂ) *
          ((Real.cos θa : ℂ) * (Real.cos θb : ℂ)
           + (-(Real.cos θa : ℂ)) * (-(Real.cos θb : ℂ))) := by
    push_cast; ring
  rw [← h_cast, Complex.ofReal_re, h_real]

/-- The same factorization for the AC marginal — identical proof,
    using `trace_ghzAC_mul` instead. -/
theorem ghz_marginal_AC_correlation_factorizes (θa θc : ℝ) :
    correlation ghzCDM_AC (equatorObservable θa) (equatorObservable θc)
      = Real.cos θa * Real.cos θc := by
  unfold correlation
  have hρM : ghzCDM_AC.M = ρAC ghzState := rfl
  rw [hρM]
  rw [trace_ghzAC_mul]
  rw [kron_00, kron_33]
  obtain ⟨hA00, _, _, hA11⟩ := eq_entries θa
  obtain ⟨hB00, _, _, hB11⟩ := eq_entries θc
  rw [hA00, hA11, hB00, hB11]
  have h_real :
      ((1/2 : ℝ) *
          (Real.cos θa * Real.cos θc
           + (-Real.cos θa) * (-Real.cos θc)))
        = Real.cos θa * Real.cos θc := by ring
  have h_cast :
      (((1/2 : ℝ) *
          (Real.cos θa * Real.cos θc
           + (-Real.cos θa) * (-Real.cos θc)) : ℝ) : ℂ)
        = (1/2 : ℂ) *
          ((Real.cos θa : ℂ) * (Real.cos θc : ℂ)
           + (-(Real.cos θa : ℂ)) * (-(Real.cos θc : ℂ))) := by
    push_cast; ring
  rw [← h_cast, Complex.ofReal_re, h_real]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: CHSH BOUND FROM FACTORIZABILITY

    Since the GHZ marginal correlation is `cos θa · cos θb` (a product
    of two functions, each `|·| ≤ 1`), the classical CHSH bound from
    `LayerB.SeparableCHSH` directly applies: every CHSH expression
    over equator observables on `ρ_{AB}^{GHZ}` has `|S| ≤ 2`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

open UnifiedTheory.LayerB.SeparableCHSH

/-- The GHZ AB-marginal CHSH expression at four angles is bounded by 2
    (the classical Bell bound) — over equator observables. -/
theorem ghz_marginal_AB_chsh_classical_bound
    (θa θa' θb θb' : ℝ) :
    let E := fun a b : ℝ =>
      correlation ghzCDM_AB (equatorObservable a) (equatorObservable b)
    |E θa θb + E θa θb' + E θa' θb - E θa' θb'| ≤ 2 := by
  change |correlation ghzCDM_AB (equatorObservable θa) (equatorObservable θb)
        + correlation ghzCDM_AB (equatorObservable θa) (equatorObservable θb')
        + correlation ghzCDM_AB (equatorObservable θa') (equatorObservable θb)
        - correlation ghzCDM_AB (equatorObservable θa') (equatorObservable θb')| ≤ 2
  simp only [ghz_marginal_AB_correlation_factorizes]
  -- Goal: |cos θa·cos θb + cos θa·cos θb' + cos θa'·cos θb - cos θa'·cos θb'| ≤ 2
  -- Apply chsh_factorizable_bound with f, g picking values from {θa, θa'} / {θb, θb'}.
  have habs : ∀ x : ℝ, |Real.cos x| ≤ 1 := fun x => Real.abs_cos_le_one x
  set f : Bool → ℝ := fun x => bif x then Real.cos θa' else Real.cos θa with hf_def
  set g : Bool → ℝ := fun y => bif y then Real.cos θb' else Real.cos θb with hg_def
  have hf : ∀ x, |f x| ≤ 1 := by
    intro x; cases x <;> simpa [f] using habs _
  have hg : ∀ y, |g y| ≤ 1 := by
    intro y; cases y <;> simpa [g] using habs _
  have hbound := chsh_factorizable_bound f g hf hg
  unfold chshExpr at hbound
  simp only [f, g, cond_false, cond_true] at hbound
  exact hbound

/-- Same bound for the AC marginal. -/
theorem ghz_marginal_AC_chsh_classical_bound
    (θa θa' θc θc' : ℝ) :
    let E := fun a c : ℝ =>
      correlation ghzCDM_AC (equatorObservable a) (equatorObservable c)
    |E θa θc + E θa θc' + E θa' θc - E θa' θc'| ≤ 2 := by
  change |correlation ghzCDM_AC (equatorObservable θa) (equatorObservable θc)
        + correlation ghzCDM_AC (equatorObservable θa) (equatorObservable θc')
        + correlation ghzCDM_AC (equatorObservable θa') (equatorObservable θc)
        - correlation ghzCDM_AC (equatorObservable θa') (equatorObservable θc')| ≤ 2
  simp only [ghz_marginal_AC_correlation_factorizes]
  have habs : ∀ x : ℝ, |Real.cos x| ≤ 1 := fun x => Real.abs_cos_le_one x
  set f : Bool → ℝ := fun x => bif x then Real.cos θa' else Real.cos θa with hf_def
  set g : Bool → ℝ := fun y => bif y then Real.cos θc' else Real.cos θc with hg_def
  have hf : ∀ x, |f x| ≤ 1 := by
    intro x; cases x <;> simpa [f] using habs _
  have hg : ∀ y, |g y| ≤ 1 := by
    intro y; cases y <;> simpa [g] using habs _
  have hbound := chsh_factorizable_bound f g hf hg
  unfold chshExpr at hbound
  simp only [f, g, cond_false, cond_true] at hbound
  exact hbound

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: SATURATING THE CLASSICAL BOUND + SINGLET-ANGLE VALUE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **GHZ saturates the classical bound 2.**  At the angle choice
    `(θa, θa', θb, θb') = (0, π/2, 0, 0)` the AB-marginal CHSH equals
    `2` exactly — saturating the classical bound `chsh_factorizable_bound`. -/
theorem ghz_marginal_AB_chsh_saturates_classical :
    let E := fun a b : ℝ =>
      correlation ghzCDM_AB (equatorObservable a) (equatorObservable b)
    E 0 0 + E 0 0 + E (Real.pi/2) 0 - E (Real.pi/2) 0 = 2 := by
  change correlation ghzCDM_AB (equatorObservable 0) (equatorObservable 0)
       + correlation ghzCDM_AB (equatorObservable 0) (equatorObservable 0)
       + correlation ghzCDM_AB (equatorObservable (Real.pi/2)) (equatorObservable 0)
       - correlation ghzCDM_AB (equatorObservable (Real.pi/2)) (equatorObservable 0)
       = 2
  simp only [ghz_marginal_AB_correlation_factorizes,
             Real.cos_zero, Real.cos_pi_div_two]
  ring

/-- The same saturation for the AC marginal. -/
theorem ghz_marginal_AC_chsh_saturates_classical :
    let E := fun a c : ℝ =>
      correlation ghzCDM_AC (equatorObservable a) (equatorObservable c)
    E 0 0 + E 0 0 + E (Real.pi/2) 0 - E (Real.pi/2) 0 = 2 := by
  change correlation ghzCDM_AC (equatorObservable 0) (equatorObservable 0)
       + correlation ghzCDM_AC (equatorObservable 0) (equatorObservable 0)
       + correlation ghzCDM_AC (equatorObservable (Real.pi/2)) (equatorObservable 0)
       - correlation ghzCDM_AC (equatorObservable (Real.pi/2)) (equatorObservable 0)
       = 2
  simp only [ghz_marginal_AC_correlation_factorizes,
             Real.cos_zero, Real.cos_pi_div_two]
  ring

/-- **At the singlet's Tsirelson-saturating angles, GHZ gives √2.**

    The canonical CHSH angles `(0, π/2; π/4, -π/4)` make the singlet
    achieve `|S| = 2√2` (cf. `LayerC.BipartiteQubitCHSH.singlet_CHSH_max_violation`).
    On the GHZ AB-marginal at the SAME angles, `S = √2` — a factor of
    `2` weaker.  Quantitative footprint of monogamy at the canonical
    CHSH angles. -/
theorem ghz_marginal_AB_at_singlet_angles :
    let E := fun a b : ℝ =>
      correlation ghzCDM_AB (equatorObservable a) (equatorObservable b)
    E 0 (Real.pi/4) + E 0 (-(Real.pi/4)) + E (Real.pi/2) (Real.pi/4)
      - E (Real.pi/2) (-(Real.pi/4)) = Real.sqrt 2 := by
  change correlation ghzCDM_AB (equatorObservable 0) (equatorObservable (Real.pi/4))
       + correlation ghzCDM_AB (equatorObservable 0) (equatorObservable (-(Real.pi/4)))
       + correlation ghzCDM_AB (equatorObservable (Real.pi/2)) (equatorObservable (Real.pi/4))
       - correlation ghzCDM_AB (equatorObservable (Real.pi/2)) (equatorObservable (-(Real.pi/4)))
       = Real.sqrt 2
  simp only [ghz_marginal_AB_correlation_factorizes,
             Real.cos_zero, Real.cos_pi_div_two, Real.cos_neg]
  -- 1·cos(π/4) + 1·cos(π/4) + 0·cos(π/4) - 0·cos(π/4) = 2·cos(π/4) = √2
  have hkey : 2 * Real.cos (Real.pi/4) = Real.sqrt 2 :=
    two_mul_cos_pi_four_eq_sqrt_two
  linarith

/-- Same value for AC marginal. -/
theorem ghz_marginal_AC_at_singlet_angles :
    let E := fun a c : ℝ =>
      correlation ghzCDM_AC (equatorObservable a) (equatorObservable c)
    E 0 (Real.pi/4) + E 0 (-(Real.pi/4)) + E (Real.pi/2) (Real.pi/4)
      - E (Real.pi/2) (-(Real.pi/4)) = Real.sqrt 2 := by
  change correlation ghzCDM_AC (equatorObservable 0) (equatorObservable (Real.pi/4))
       + correlation ghzCDM_AC (equatorObservable 0) (equatorObservable (-(Real.pi/4)))
       + correlation ghzCDM_AC (equatorObservable (Real.pi/2)) (equatorObservable (Real.pi/4))
       - correlation ghzCDM_AC (equatorObservable (Real.pi/2)) (equatorObservable (-(Real.pi/4)))
       = Real.sqrt 2
  simp only [ghz_marginal_AC_correlation_factorizes,
             Real.cos_zero, Real.cos_pi_div_two, Real.cos_neg]
  have hkey : 2 * Real.cos (Real.pi/4) = Real.sqrt 2 :=
    two_mul_cos_pi_four_eq_sqrt_two
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: WEAK-MONOGAMY VIA FACTORIZABILITY

    `S_{AB}² + S_{AC}² ≤ 8` follows immediately for the GHZ state from
    each `|S| ≤ 2` (classical bound), i.e. `S² ≤ 4`, summed.  This
    saturates the true Toner–Verstraete bound at the classical-classical
    extreme.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **GHZ-state Toner–Verstraete bound 8 follows from factorizability.**

    For ANY four angles on the Alice side (`θa, θa'`) and ANY four angles
    on Bob/Charlie sides (`θb, θb'`, `θc, θc'`), the squared CHSH
    expressions sum to ≤ 8. -/
theorem ghz_chsh_monogamy_via_factorizability
    (θa θa' θb θb' θc θc' : ℝ) :
    let E_AB := fun a b : ℝ =>
      correlation ghzCDM_AB (equatorObservable a) (equatorObservable b)
    let E_AC := fun a c : ℝ =>
      correlation ghzCDM_AC (equatorObservable a) (equatorObservable c)
    let S_AB := E_AB θa θb + E_AB θa θb' + E_AB θa' θb - E_AB θa' θb'
    let S_AC := E_AC θa θc + E_AC θa θc' + E_AC θa' θc - E_AC θa' θc'
    S_AB^2 + S_AC^2 ≤ 8 := by
  intro E_AB E_AC S_AB S_AC
  -- |S_AB| ≤ 2 and |S_AC| ≤ 2 ⇒ S_AB², S_AC² ≤ 4 ⇒ sum ≤ 8.
  have h_AB : |S_AB| ≤ 2 := ghz_marginal_AB_chsh_classical_bound θa θa' θb θb'
  have h_AC : |S_AC| ≤ 2 := ghz_marginal_AC_chsh_classical_bound θa θa' θc θc'
  have h_sq_AB : S_AB^2 ≤ 4 := by
    have h := sq_abs S_AB
    have h2 : |S_AB|^2 ≤ 2^2 :=
      sq_le_sq' (by linarith [abs_nonneg S_AB]) h_AB
    linarith [h, h2]
  have h_sq_AC : S_AC^2 ≤ 4 := by
    have h := sq_abs S_AC
    have h2 : |S_AC|^2 ≤ 2^2 :=
      sq_le_sq' (by linarith [abs_nonneg S_AC]) h_AC
    linarith [h, h2]
  linarith

/-- **The Toner–Verstraete bound is SATURATED at the GHZ classical-
    classical extreme.**

    At the choice `(0, π/2, 0, 0)` for both Alice–Bob and Alice–Charlie
    angle pairs, the AB-marginal AND the AC-marginal each achieve their
    classical bound of `2`, so `S_AB² + S_AC² = 4 + 4 = 8`. -/
theorem ghz_saturates_toner_verstraete :
    let E_AB := fun a b : ℝ =>
      correlation ghzCDM_AB (equatorObservable a) (equatorObservable b)
    let E_AC := fun a c : ℝ =>
      correlation ghzCDM_AC (equatorObservable a) (equatorObservable c)
    let S_AB := E_AB 0 0 + E_AB 0 0 + E_AB (Real.pi/2) 0
                  - E_AB (Real.pi/2) 0
    let S_AC := E_AC 0 0 + E_AC 0 0 + E_AC (Real.pi/2) 0
                  - E_AC (Real.pi/2) 0
    S_AB^2 + S_AC^2 = 8 := by
  intro E_AB E_AC S_AB S_AC
  have hAB : S_AB = 2 := ghz_marginal_AB_chsh_saturates_classical
  have hAC : S_AC = 2 := ghz_marginal_AC_chsh_saturates_classical
  rw [hAB, hAC]
  norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: THE HEADLINE — GHZ TRIPARTITE BUT PAIRWISE CLASSICAL
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MONOGAMY-INSIGHT (the headline).**

    The 3-qubit GHZ state's bipartite marginals do NOT distribute the
    underlying tripartite entanglement as pairwise CHSH violation:

      (1) Both `ρ_{AB}^{GHZ}` and `ρ_{AC}^{GHZ}` are explicitly the
          classically-correlated state `½·diag(1, 0, 0, 1) =
          ½(|00⟩⟨00| + |11⟩⟨11|)`.

      (2) Their CHSH-correlation functions factorize over equator
          observables as `cos θa · cos θ_{B or C}`, the textbook
          factorizable form.

      (3) Consequently every CHSH expression on either marginal is
          bounded by the CLASSICAL Bell limit `2` — no quantum
          violation.

      (4) The Toner–Verstraete bound `S_{AB}² + S_{AC}² ≤ 8` holds AND
          is SATURATED at the classical-classical extreme.

    The tripartite entanglement of the GHZ state (which Mermin's
    inequality witnesses with `|M| = 4 > 2`, see
    `LayerB.MerminGHZ`) lives in the FULL 3-party correlator and does
    not survive partial tracing. -/
theorem ghz_tripartite_but_pairwise_classical :
    -- (a) marginals are explicitly equal to the classically-correlated state
    (ρAB ghzState = ghzDiagonal)
  ∧ (ρAC ghzState = ghzDiagonal)
  -- (b) correlations factorize as cos·cos
  ∧ (∀ θa θb : ℝ,
        correlation ghzCDM_AB (equatorObservable θa) (equatorObservable θb)
          = Real.cos θa * Real.cos θb)
  ∧ (∀ θa θc : ℝ,
        correlation ghzCDM_AC (equatorObservable θa) (equatorObservable θc)
          = Real.cos θa * Real.cos θc)
  -- (c) every CHSH expression is classically bounded
  ∧ (∀ θa θa' θb θb' : ℝ,
        let E := fun a b : ℝ =>
          correlation ghzCDM_AB (equatorObservable a) (equatorObservable b)
        |E θa θb + E θa θb' + E θa' θb - E θa' θb'| ≤ 2)
  ∧ (∀ θa θa' θc θc' : ℝ,
        let E := fun a c : ℝ =>
          correlation ghzCDM_AC (equatorObservable a) (equatorObservable c)
        |E θa θc + E θa θc' + E θa' θc - E θa' θc'| ≤ 2)
  -- (d) the Toner–Verstraete monogamy bound holds
  ∧ (∀ θa θa' θb θb' θc θc' : ℝ,
        let E_AB := fun a b : ℝ =>
          correlation ghzCDM_AB (equatorObservable a) (equatorObservable b)
        let E_AC := fun a c : ℝ =>
          correlation ghzCDM_AC (equatorObservable a) (equatorObservable c)
        let S_AB := E_AB θa θb + E_AB θa θb' + E_AB θa' θb - E_AB θa' θb'
        let S_AC := E_AC θa θc + E_AC θa θc' + E_AC θa' θc - E_AC θa' θc'
        S_AB^2 + S_AC^2 ≤ 8) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ρAB_ghz_diagonal
  · exact ρAC_ghz_diagonal
  · exact ghz_marginal_AB_correlation_factorizes
  · exact ghz_marginal_AC_correlation_factorizes
  · exact ghz_marginal_AB_chsh_classical_bound
  · exact ghz_marginal_AC_chsh_classical_bound
  · exact ghz_chsh_monogamy_via_factorizability

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    AXIOM-CHECK DIAGNOSTICS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

#print axioms ρAB_ghz_diagonal
#print axioms ρAC_ghz_diagonal
#print axioms ghz_marginal_AB_correlation_factorizes
#print axioms ghz_marginal_AC_correlation_factorizes
#print axioms ghz_marginal_AB_chsh_classical_bound
#print axioms ghz_marginal_AC_chsh_classical_bound
#print axioms ghz_marginal_AB_chsh_saturates_classical
#print axioms ghz_marginal_AB_at_singlet_angles
#print axioms ghz_chsh_monogamy_via_factorizability
#print axioms ghz_saturates_toner_verstraete
#print axioms ghz_tripartite_but_pairwise_classical

end UnifiedTheory.LayerC.CHSHMonogamy
