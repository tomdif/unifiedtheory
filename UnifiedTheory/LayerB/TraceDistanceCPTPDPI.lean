/-
  LayerB/TraceDistanceCPTPDPI.lean
  ─────────────────────────────────

  **The full CPTP trace-distance data-processing inequality, made
  UNCONDITIONAL via the Stinespring factorization.**

      `traceDistance (Φ ρ) (Φ σ)  ≤  traceDistance ρ σ`.

  Every CPTP map factors (Stinespring) as

      `Φ(X)  =  Tr_E (V · X · V†)`,        `V† V = I`  (`V` an ISOMETRY).

  The DPI then assembles from two structural pieces, BOTH now
  unconditional:

    1. **Isometric invariance — EQUALITY.**  Conjugation by an isometry
       `V` (`V† V = I`, but `V` need not be square/unitary) PRESERVES the
       trace distance:
           `traceDistance (V ρ V†) (V σ V†) = traceDistance ρ σ`.
       This is the genuinely NEW content of this file (the unitary
       special case is `traceDistance_unitaryConjugate` in
       `TraceDistanceContractivity.lean`).  It rests on the operator
       identity
           `|V X V†|  =  V |X| V†`     (`X` Hermitian, `V` isometric),
       proved via UNIQUENESS of the positive square root
       (`CFC.sqrt_unique`):  both `|V X V†|` and `V |X| V†` are PSD and
       square to `V X² V† = (V X V†)·(V X V†)` — the cross term collapses
       through `V† V = I`.  Tracing and using cyclicity with `V† V = I`
       gives `Tr|V X V†| = Tr|X|`, hence the equality of trace distances.

    2. **Partial-trace contractivity — CONTRACTIVE (UNCONDITIONAL).**
       `traceDistance (Tr_E ω) (Tr_E τ) ≤ traceDistance ω τ`, imported as
       `traceDistance_partialTrace_contractive_unconditional` from
       `TraceNormDualAttainment.lean` (NO hypotheses — the trace-norm
       dual attainment is discharged there by the spectral sign
       construction).

  Composing 1 then 2 gives the full CPTP trace-distance DPI for any
  Stinespring-presented channel.  Since (finite-dimensionally) every CPTP
  map is a Kraus map and `StinespringDilation.stinespringOfKraus` builds
  the isometry `V` and the partial-trace recovery `Φ = Tr_E ∘ (V · V†)`
  UNCONDITIONALLY from a Kraus family, the DPI is unconditional for KRAUS
  maps — the operational definition of a CPTP channel.

  **Honest residual.**  Nothing here is threaded as a `Prop` hypothesis.
  The only scoping is that the channel is presented either by an explicit
  isometry (`traceDistance_cptp_dpi_of_isometricDilation`) or by a Kraus
  family (`traceDistance_cptp_dpi_kraus`); the abstract "every CP map has
  a dilation" direction is the finite-dimensional Choi–Kraus theorem,
  already shipped in its engineering form as
  `StinespringDilation.stinespring_existence` (a theorem, not an axiom).

  STANDING CONSTRAINT: zero `sorry`, zero custom `axiom`.

  ## Build

      lake build UnifiedTheory.LayerB.TraceDistanceCPTPDPI
-/

import UnifiedTheory.LayerB.TraceNormDualAttainment
import UnifiedTheory.LayerB.StinespringDilation

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.TraceDistanceCPTPDPI

open Matrix Complex
open scoped ComplexOrder MatrixOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.QuantumChernoff
open UnifiedTheory.LayerB.PartialTrace
open UnifiedTheory.LayerB.PartialTraceDPI
open UnifiedTheory.LayerB.TraceDistanceContractivity
open UnifiedTheory.LayerB.TraceNormDualAttainment

/-- Re-declare the matrix `CStarAlgebra` instance (mirrors the pattern in
    the sibling files), needed for `CFC.abs` / `CFC.sqrt`.  Parametric in
    the dimension, so it covers BOTH the small space `Fin n` and the
    dilated space `Fin n'`. -/
noncomputable scoped instance matrixCStarAlgebra {k : ℕ} :
    CStarAlgebra (Matrix (Fin k) (Fin k) ℂ) where

/-! ## 1.  Isometric conjugation of the absolute value.

The keystone operator identity, the isometric analogue of
`TraceDistanceContractivity.cfcAbs_unitary_conj`.  Unlike the unitary
case, an isometry `V : Matrix (Fin n') (Fin n) ℂ` is NOT square, so
conjugation by `V` is not a `*`-algebra automorphism and the naturality
route (`cfc_unitary_conj`) is unavailable.  We use UNIQUENESS of the PSD
square root instead. -/

variable {n n' : ℕ}

/-- **Isometric naturality of `CFC.abs`.**

      `|V X V†|  =  V |X| V†`     for Hermitian `X` and an isometry `V`
                                  (`V† V = I`).

    Proof via `CFC.sqrt_unique`: the candidate `b := V |X| V†` is PSD
    (conjugation by `V` preserves PSD) and satisfies `b · b =
    V X² V† = (V X V†)·(V X V†) = star(VXV†) · (VXV†)`, the radicand of
    `CFC.abs (V X V†) = CFC.sqrt (star · · )`.  The cross term `V† V`
    collapses to `I`. -/
theorem cfcAbs_isometric_conj
    {V : Matrix (Fin n') (Fin n) ℂ} (hV : V.conjTranspose * V = 1)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : IsSelfAdjoint X) :
    CFC.abs (V * X * V.conjTranspose)
      = V * (CFC.abs X) * V.conjTranspose := by
  -- The candidate square root.
  set b : Matrix (Fin n') (Fin n') ℂ := V * (CFC.abs X) * V.conjTranspose with hb
  -- (a) b is PSD, i.e. 0 ≤ b in the matrix order.
  have hbPSD : b.PosSemidef := by
    have hAbsPSD : (CFC.abs X).PosSemidef := by
      rw [Matrix.nonneg_iff_posSemidef.symm] at *
      exact CFC.abs_nonneg X
    -- V * |X| * V† PSD via conjugation.
    simpa [hb] using hAbsPSD.mul_mul_conjTranspose_same V
  have hb_nonneg : (0 : Matrix (Fin n') (Fin n') ℂ) ≤ b :=
    Matrix.nonneg_iff_posSemidef.mpr hbPSD
  -- (b) The radicand: star (V X V†) * (V X V†) = V (X*X) V†.
  --     W := V X V† is self-adjoint (X self-adjoint).
  have hXstar : star X = X := hX
  have hWsa : star (V * X * V.conjTranspose) = V * X * V.conjTranspose := by
    change (V * X * V.conjTranspose).conjTranspose = V * X * V.conjTranspose
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
        show X.conjTranspose = X from hXstar, Matrix.mul_assoc]
  -- |X| * |X| = star X * X = X * X.
  have hAbsSq : CFC.abs X * CFC.abs X = X * X := by
    have h := CFC.abs_mul_abs X
    rw [hXstar] at h
    exact h
  -- The sandwich-collapse identity: (V A V†)(V B V†) = V (A B) V†, using V† V = I.
  have hcollapse : ∀ A B : Matrix (Fin n) (Fin n) ℂ,
      (V * A * V.conjTranspose) * (V * B * V.conjTranspose)
        = V * (A * B) * V.conjTranspose := by
    intro A B
    -- Right-associate to expose the inner V† V, collapse it, reassemble.
    have h1 : (V * A * V.conjTranspose) * (V * B * V.conjTranspose)
            = (V * A) * (V.conjTranspose * V) * (B * V.conjTranspose) := by
      simp only [Matrix.mul_assoc]
    rw [h1, hV, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  -- b * b = V (|X| |X|) V† = V (X X) V†.
  have hbb : b * b = V * (X * X) * V.conjTranspose := by
    rw [hb, hcollapse (CFC.abs X) (CFC.abs X), hAbsSq]
  -- star (V X V†) * (V X V†) = (V X V†)(V X V†) = V (X X) V†.
  have hradicand :
      star (V * X * V.conjTranspose) * (V * X * V.conjTranspose)
        = V * (X * X) * V.conjTranspose := by
    rw [hWsa, hcollapse X X]
  -- Conclude by uniqueness of the PSD square root.
  rw [CFC.abs, hradicand]
  exact CFC.sqrt_unique hbb hb_nonneg

/-! ## 2.  Isometric invariance of the trace distance.

Package `V ρ V†` as a `ComplexDensityMatrix` (the isometric analogue of
`UnitaryInvariance.unitaryConjugate`), then prove
`traceDistance (V ρ V†) (V σ V†) = traceDistance ρ σ` from
`cfcAbs_isometric_conj` + trace cyclicity with `V† V = I`. -/

/-- The isometric conjugate `V ρ V†` of a density matrix, packaged as a
    `ComplexDensityMatrix` on the larger space `Fin n'`.

    Requires `V` to be an isometry (`V† V = I`); then trace-1 and
    trace-PSD are preserved by the cyclicity `Tr(V ρ V† · ·) = Tr(ρ · ·)`
    and PSD-conjugation respectively. -/
noncomputable def isometricConjugate
    {V : Matrix (Fin n') (Fin n) ℂ} (hV : V.conjTranspose * V = 1)
    (ρ : ComplexDensityMatrix n) : ComplexDensityMatrix n' where
  M := V * ρ.M * V.conjTranspose
  hHerm := by
    change (V * ρ.M * V.conjTranspose).conjTranspose = V * ρ.M * V.conjTranspose
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
        ρ.hHerm.eq, Matrix.mul_assoc]
  hTrace := by
    -- Tr(V ρ V†) = Tr(V† V ρ) = Tr(ρ) = 1.
    have h : Matrix.trace (V * ρ.M * V.conjTranspose)
           = Matrix.trace (V.conjTranspose * V * ρ.M) := by
      rw [Matrix.trace_mul_cycle]
    rw [h, hV, Matrix.one_mul, ρ.hTrace]
  hTracePSD := by
    -- V ρ V† is PSD; the trace-PSD field then follows by cyclicity.
    have hρPSD : ρ.M.PosSemidef :=
      UnifiedTheory.LayerB.OperatorEntropy.posSemidef_of_ComplexDensityMatrix ρ
    have hconjPSD : (V * ρ.M * V.conjTranspose).PosSemidef :=
      hρPSD.mul_mul_conjTranspose_same V
    intro X
    -- 0 ≤ Re Tr((V ρ V†) X† X) = Re Tr(X (V ρ V†) X†), PSD sandwich.
    have hcyc :
        Matrix.trace (V * ρ.M * V.conjTranspose * X.conjTranspose * X)
          = Matrix.trace (X * (V * ρ.M * V.conjTranspose) * X.conjTranspose) := by
      rw [show V * ρ.M * V.conjTranspose * X.conjTranspose * X
              = (V * ρ.M * V.conjTranspose * X.conjTranspose) * X from by
            simp only [Matrix.mul_assoc]]
      rw [Matrix.trace_mul_comm (V * ρ.M * V.conjTranspose * X.conjTranspose) X]
      simp only [Matrix.mul_assoc]
    rw [hcyc]
    have h_sandwich : (X * (V * ρ.M * V.conjTranspose) * X.conjTranspose).PosSemidef :=
      hconjPSD.mul_mul_conjTranspose_same X
    have := (Complex.le_def.mp h_sandwich.trace_nonneg).1
    simpa using this

/-- Unfolding: the matrix underlying `isometricConjugate hV ρ`. -/
@[simp]
theorem isometricConjugate_M
    {V : Matrix (Fin n') (Fin n) ℂ} (hV : V.conjTranspose * V = 1)
    (ρ : ComplexDensityMatrix n) :
    (isometricConjugate hV ρ).M = V * ρ.M * V.conjTranspose := rfl

/-- The Hermitian difference of two isometric conjugates is the isometric
    conjugate of the difference:  `V ρ V† − V σ V† = V (ρ − σ) V†`. -/
theorem diff_isometricConjugate
    {V : Matrix (Fin n') (Fin n) ℂ} (hV : V.conjTranspose * V = 1)
    (ρ σ : ComplexDensityMatrix n) :
    diff (isometricConjugate hV ρ) (isometricConjugate hV σ)
      = V * (diff ρ σ) * V.conjTranspose := by
  unfold diff
  simp only [isometricConjugate_M]
  rw [Matrix.mul_sub, Matrix.sub_mul]

/-- **Isometric invariance of the trace distance (EQUALITY).**

      `traceDistance (V ρ V†) (V σ V†)  =  traceDistance ρ σ`

    for an isometry `V` (`V† V = I`).  The isometric extension of
    `TraceDistanceContractivity.traceDistance_unitaryConjugate`.

    Tracing the natural identity `|V Δ V†| = V |Δ| V†`
    (`cfcAbs_isometric_conj`) and using cyclicity `Tr(V |Δ| V†) =
    Tr(V† V |Δ|) = Tr(|Δ|)`. -/
theorem traceDistance_isometricConjugate
    {V : Matrix (Fin n') (Fin n) ℂ} (hV : V.conjTranspose * V = 1)
    (ρ σ : ComplexDensityMatrix n) :
    traceDistance (isometricConjugate hV ρ) (isometricConjugate hV σ)
      = traceDistance ρ σ := by
  unfold traceDistance
  rw [diff_isometricConjugate hV ρ σ,
      cfcAbs_isometric_conj hV (diff_isSelfAdjoint ρ σ)]
  congr 1
  -- Tr(V |Δ| V†) = Tr(V† V |Δ|) = Tr(|Δ|).
  have h_cyc :
      Matrix.trace (V * CFC.abs (diff ρ σ) * V.conjTranspose)
        = Matrix.trace (V.conjTranspose * V * CFC.abs (diff ρ σ)) := by
    rw [Matrix.trace_mul_cycle]
  rw [h_cyc, hV, Matrix.one_mul]

/-! ## 3.  The full CPTP trace-distance DPI, assembled.

Compose §2 (isometric equality) with the UNCONDITIONAL partial-trace
contractivity.  A Stinespring-presented channel is `Φ = Tr_E ∘ (V · V†)`;
the DPI is the composite. -/

variable {n_A n_B : ℕ}

/-- **CPTP trace-distance DPI from an explicit isometric dilation,
    UNCONDITIONAL.**

    Suppose the channel `Φ` acts on density matrices of the dilated,
    bipartite shape `Fin (n_A * n_B)` as `Φ ρ = Tr_E (V ρ V†)`, i.e.
    `Φρ = partialTraceDensity_right (isometricConjugate hV ρ)` for an
    isometry `V : Matrix (Fin (n_A * n_B)) (Fin n) ℂ`.  Then

        `traceDistance (Φ ρ) (Φ σ)  ≤  traceDistance ρ σ`.

    Both structural pieces are unconditional:
      • isometric stage  — EQUALITY     (`traceDistance_isometricConjugate`);
      • partial-trace    — CONTRACTIVE  (the now-unconditional
        `traceDistance_partialTrace_contractive_unconditional`). -/
theorem traceDistance_cptp_dpi_of_isometricDilation
    {V : Matrix (Fin (n_A * n_B)) (Fin n) ℂ} (hV : V.conjTranspose * V = 1)
    (ρ σ : ComplexDensityMatrix n) :
    traceDistance
        (partialTraceDensity_right (isometricConjugate hV ρ))
        (partialTraceDensity_right (isometricConjugate hV σ))
      ≤ traceDistance ρ σ := by
  calc traceDistance
          (partialTraceDensity_right (isometricConjugate hV ρ))
          (partialTraceDensity_right (isometricConjugate hV σ))
      ≤ traceDistance (isometricConjugate hV ρ) (isometricConjugate hV σ) :=
        traceDistance_partialTrace_contractive_unconditional
          (isometricConjugate hV ρ) (isometricConjugate hV σ)
    _ = traceDistance ρ σ :=
        traceDistance_isometricConjugate hV ρ σ

/-! ## 4.  Discharging the conditional `traceDistance_cptp_contractive_of_stinespring`.

`TraceDistanceContractivity.traceDistance_cptp_contractive_of_stinespring`
took the two structural facts (`hEmbed` equality, `hContract` contraction)
as HYPOTHESES.  We now SUPPLY both from the unconditional lemmas above,
turning that conditional assembly into an unconditional theorem for any
isometric dilation. -/

/-- **General-CPTP target discharged for an isometric dilation.**

    The named `TraceDistance_Contractive_Target` of
    `TraceDistanceContractivity.lean` holds UNCONDITIONALLY for a channel
    given by an explicit isometric dilation, by feeding
    `traceDistance_cptp_contractive_of_stinespring` the equality
    (`traceDistance_isometricConjugate`) and contraction
    (`traceDistance_partialTrace_contractive_unconditional`) it requires. -/
theorem cptp_contractive_target_of_isometricDilation
    {V : Matrix (Fin (n_A * n_B)) (Fin n) ℂ} (hV : V.conjTranspose * V = 1)
    (ρ σ : ComplexDensityMatrix n) :
    TraceDistance_Contractive_Target
      (partialTraceDensity_right (isometricConjugate hV ρ))
      (partialTraceDensity_right (isometricConjugate hV σ))
      ρ σ :=
  traceDistance_cptp_contractive_of_stinespring
    (partialTraceDensity_right (isometricConjugate hV ρ))
    (partialTraceDensity_right (isometricConjugate hV σ))
    ρ σ
    (isometricConjugate hV ρ) (isometricConjugate hV σ)
    (traceDistance_isometricConjugate hV ρ σ)
    (traceDistance_partialTrace_contractive_unconditional
      (isometricConjugate hV ρ) (isometricConjugate hV σ))

/-! ## 4½.  The KRAUS-map trace-distance DPI (UNCONDITIONAL).

A finite Kraus family `K : Fin d → Matrix (Fin n) (Fin n) ℂ` with the
completeness relation `∑_α K_α† K_α = I` is the operational definition of
a CPTP channel `Φ(ρ) = ∑_α K_α ρ K_α†`.  `StinespringDilation` builds its
isometry `V = krausToStinespring K : Matrix (Fin n × Fin d) (Fin n) ℂ`
UNCONDITIONALLY.  Reindexing the dilated index `Fin n × Fin d ≃ Fin (n*d)`
via `finProdFinEquiv` lands the isometry in the `Fin (n_A*n_B)` shape that
`traceDistance_cptp_dpi_of_isometricDilation` consumes.  The DPI then holds
unconditionally for any Kraus channel. -/

open UnifiedTheory.LayerB.StinespringDilation

variable {d : ℕ}

/-- The Kraus → Stinespring isometry, with its dilated row-index
    `Fin n × Fin d` reindexed to `Fin (n * d)` via `finProdFinEquiv`. -/
noncomputable def krausIsometry
    (K : Fin d → Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin (n * d)) (Fin n) ℂ :=
  (krausToStinespring K).submatrix
    (finProdFinEquiv : Fin n × Fin d ≃ Fin (n * d)).symm (Equiv.refl _)

/-- **The reindexed Kraus isometry is an isometry** (`V† V = I`) whenever
    the Kraus family is complete.  Reindexing the dilated index by a
    bijection leaves `V† V` invariant (`submatrix_mul_equiv`), and
    `krausToStinespring K` is an isometry by
    `StinespringDilation.krausToStinespring_isIsometry`. -/
theorem krausIsometry_isIsometry
    {K : Fin d → Matrix (Fin n) (Fin n) ℂ}
    (hK : ∑ α, (K α).conjTranspose * K α = (1 : Matrix (Fin n) (Fin n) ℂ)) :
    (krausIsometry K).conjTranspose * krausIsometry K = 1 := by
  classical
  set e := (finProdFinEquiv : Fin n × Fin d ≃ Fin (n * d)) with he
  unfold krausIsometry
  -- (V.submatrix e.symm id)† = V†.submatrix id e.symm.
  rw [conjTranspose_submatrix]
  -- (V†.submatrix id e.symm) * (V.submatrix e.symm id)
  --   = (V† * V).submatrix id id  (shared middle index e.symm).
  rw [Matrix.submatrix_mul_equiv (krausToStinespring K).conjTranspose
        (krausToStinespring K) (Equiv.refl _) e.symm (Equiv.refl _)]
  -- V† V = I (krausToStinespring is an isometry).
  have hIso : (krausToStinespring K).conjTranspose * krausToStinespring K
            = (1 : Matrix (Fin n) (Fin n) ℂ) :=
    krausToStinespring_isIsometry hK
  rw [hIso]
  simp

/-- **Full Kraus-map trace-distance DPI, UNCONDITIONAL.**

    For a complete Kraus family `K` (i.e. a CPTP channel in operational
    form), the channel realized by its Stinespring dilation —
    `Φ ρ = Tr_E (V ρ V†)` packaged as
    `partialTraceDensity_right (isometricConjugate (krausIsometry_isIsometry hK) ρ)`
    — contracts the trace distance:

        `traceDistance (Φ ρ) (Φ σ)  ≤  traceDistance ρ σ`.

    This is `traceDistance_cptp_dpi_of_isometricDilation` specialised to
    the unconditionally-built Kraus isometry.  No hypotheses beyond Kraus
    completeness; no `Prop`-threading. -/
theorem traceDistance_cptp_dpi_kraus
    {K : Fin d → Matrix (Fin n) (Fin n) ℂ}
    (hK : ∑ α, (K α).conjTranspose * K α = (1 : Matrix (Fin n) (Fin n) ℂ))
    (ρ σ : ComplexDensityMatrix n) :
    traceDistance
        (partialTraceDensity_right
          (isometricConjugate (krausIsometry_isIsometry hK) ρ))
        (partialTraceDensity_right
          (isometricConjugate (krausIsometry_isIsometry hK) σ))
      ≤ traceDistance ρ σ :=
  traceDistance_cptp_dpi_of_isometricDilation (krausIsometry_isIsometry hK) ρ σ

/-! ## 5.  Operational corollary: distinguishability is non-increasing.

The Helstrom optimal success probability `½(1 + ½·traceDistance)` cannot
rise under a CPTP channel — the single-shot data-processing statement
behind Helstrom / BB84 security. -/

/-- **No CPTP channel increases distinguishability (UNCONDITIONAL).**

    For a channel given by an isometric dilation, the (un-halved) trace
    distance — hence the Helstrom optimal success probability
    `½(1 + ½·traceDistance)` — does not increase. -/
theorem distinguishability_nonincreasing_cptp
    {V : Matrix (Fin (n_A * n_B)) (Fin n) ℂ} (hV : V.conjTranspose * V = 1)
    (ρ σ : ComplexDensityMatrix n) :
    (1 / 2 : ℝ)
        * traceDistance
            (partialTraceDensity_right (isometricConjugate hV ρ))
            (partialTraceDensity_right (isometricConjugate hV σ))
      ≤ (1 / 2 : ℝ) * traceDistance ρ σ := by
  have h := traceDistance_cptp_dpi_of_isometricDilation hV ρ σ
  linarith

/-! ## 6.  Axiom audit. -/

#print axioms cfcAbs_isometric_conj
#print axioms traceDistance_isometricConjugate
#print axioms traceDistance_cptp_dpi_of_isometricDilation
#print axioms cptp_contractive_target_of_isometricDilation
#print axioms krausIsometry_isIsometry
#print axioms traceDistance_cptp_dpi_kraus
#print axioms distinguishability_nonincreasing_cptp

end UnifiedTheory.LayerB.TraceDistanceCPTPDPI
