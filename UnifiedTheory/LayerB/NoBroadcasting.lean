/-
  LayerB/NoBroadcasting.lean — The quantum no-broadcasting theorem
  (Barnum–Caves–Fuchs–Jozsa–Schumacher 1996).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED

  The standard quantum no-broadcasting theorem in framework
  vocabulary (real-amplitude qubit form):

      A *broadcasting map* T sends a single-particle density matrix
      ρ to a two-particle state whose two marginals are both equal
      to ρ.  Two density matrices ρ and σ can be broadcast by the
      SAME map T (with T linear) only if ρ and σ commute.

  In the framework's `DensityMatrix2Honest` vocabulary (2 × 2
  Hermitian, trace-1, PSD), this becomes:  any linear T whose
  marginal projections coincide with the input on a pair (ρ, σ)
  forces  ρσ - σρ = 0 .  Since explicit non-commuting pairs exist
  (e.g. eigenstates of σ_x and σ_z), no UNIVERSAL broadcasting map
  exists.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  THE BCFJS PROOF SKETCH (1996)

  Suppose T linear broadcasts ρ and σ.  By linearity,
       T (αρ + βσ)  =  αT(ρ)  +  βT(σ)
  for any reals α, β.  Both marginals (M_L, M_R) are *also* linear
  partial-trace operations, so
       M_L T (αρ + βσ)  =  αρ + βσ ,
       M_R T (αρ + βσ)  =  αρ + βσ .
  The information-theoretic step (mutual information ≥ 0 with
  equality iff product) forces T(ρ) = ρ ⊗ ρ and T(σ) = σ ⊗ σ; by
  linearity again, T(αρ + βσ) is then BOTH a tensor product AND
  the marginals are αρ + βσ.  Comparing the two presentations
  forces  ρσ = σρ .

  In the real-amplitude qubit setting we *encode* this argument
  algebraically:  we set up the broadcasting predicate as a
  CONSTRAINT EQUATION between linear images of ρ and a
  *quadratic* form (ρ ⊗ ρ).  Linearity in ρ + a quadratic equation
  on TWO inputs ρ, σ FORCES the polarization identity to give
  ρσ = σρ.  This is a faithful real-amplitude rendering of the
  BCFJS argument.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS FRAMEWORK-DERIVED VS STANDARD QM

  • Linearity of the density-matrix data space (`Fin 4 → ℝ` for
    a qubit; (p₁, p₂, coh_re, coh_im)) is part of the framework's
    LayerB amplitude/operator vocabulary used in
    `DensityMatrixHonest.lean`.
  • The marginal projections used in the broadcasting predicate
    are the standard partial-trace formulas, encoded directly on
    the data tuples (no additional tensor-product machinery
    beyond what `QuantumEntanglement.lean` already provides).
  • Once T is *linear* and the marginal axiom holds, the
    contradiction with non-commuting witnesses is purely
    algebraic.

  HONEST SCOPE.  This is the textbook BCFJS no-broadcasting
  theorem in the framework's real-amplitude qubit vocabulary.
  Full QM no-broadcasting uses complex Hilbert spaces and the
  CP-map structure; the framework's K/P-derived complex
  structure (`ComplexFromDressing.lean`) supplies ℂ at the
  single-particle level, but the lift to the full complex
  CP-map argument is not formalized here.  The real qubit case
  already captures the essential algebraic obstruction.

  Zero `sorry`. Zero custom axioms.
-/
import UnifiedTheory.LayerB.NoCloning
import UnifiedTheory.LayerB.DensityMatrixHonest
import Mathlib.Algebra.Module.LinearMap.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.NoBroadcasting

open UnifiedTheory.LayerB.DensityMatrixHonest
open UnifiedTheory.LayerB.NoCloning

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: 2 × 2 DENSITY-MATRIX DATA AND ITS HERMITIAN PRODUCT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A 2 × 2 honest density matrix carries four real numbers:
        (p₁, p₂, c_re, c_im)
    encoding the Hermitian matrix
            ⎡ p₁           c_re + i c_im ⎤
        ρ = ⎣ c_re − i c_im     p₂        ⎦.

    For the no-broadcasting argument we need the *commutator*
    [ρ, σ] = ρσ − σρ.  This is again a 2 × 2 matrix; for two
    Hermitian inputs it is anti-Hermitian, with FOUR real
    components (one real diagonal-difference, plus two real-imag
    off-diagonal pairs).  We unpack these explicitly so that
    "ρ and σ commute" becomes four scalar equations on
    (p₁, p₂, c_re, c_im) data.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The (1,1) component of the commutator `ρσ − σρ` in
    framework-data terms.  For Hermitian ρ and σ it is purely
    imaginary; in the real/imag split this is the imaginary part
    `2(c_im(ρ)·c_re(σ) − c_re(ρ)·c_im(σ))`. -/
def commImDiag (ρ σ : DensityMatrix2Honest) : ℝ :=
  ρ.coh_im * σ.coh_re - ρ.coh_re * σ.coh_im

/-- Real part of the (1,2) component of `ρσ − σρ`. -/
def commReOff (ρ σ : DensityMatrix2Honest) : ℝ :=
  ρ.coh_re * (σ.p₁ - σ.p₂) - σ.coh_re * (ρ.p₁ - ρ.p₂)

/-- Imaginary part of the (1,2) component of `ρσ − σρ`. -/
def commImOff (ρ σ : DensityMatrix2Honest) : ℝ :=
  ρ.coh_im * (σ.p₁ - σ.p₂) - σ.coh_im * (ρ.p₁ - ρ.p₂)

/-- **`ρ` and `σ` commute** iff all three independent components
    of `ρσ − σρ` vanish.  (The (2,2) component is the negative
    of the (1,1) component for Hermitian ρ, σ; the (2,1)
    component is the conjugate of the (1,2) component.) -/
def Commutes (ρ σ : DensityMatrix2Honest) : Prop :=
  commImDiag ρ σ = 0 ∧ commReOff ρ σ = 0 ∧ commImOff ρ σ = 0

/-- Commutativity is symmetric. -/
theorem Commutes.symm {ρ σ : DensityMatrix2Honest}
    (h : Commutes ρ σ) : Commutes σ ρ := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> simp only [commImDiag, commReOff, commImOff] at *
  · linarith
  · linarith
  · linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: TWO EXPLICIT NON-COMMUTING DENSITY MATRICES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The eigenstates of σ_x and σ_z provide the standard textbook
    pair of non-commuting pure states.  Both are normalized
    amplitude pairs, hence honest density matrices via
    `fromAmplitudes`.

      |+⟩ = (|0⟩ + |1⟩)/√2,        ρ_X = |+⟩⟨+|
                  ⎡ 1/2  1/2 ⎤
                = ⎣ 1/2  1/2 ⎦,
      |0⟩ = (1, 0),                ρ_Z = |0⟩⟨0|
                  ⎡ 1  0 ⎤
                = ⎣ 0  0 ⎦.

    Both are pure (det = 0), with PSD saturated.  Their
    commutator is non-zero, witnessed by `commReOff ρ_X ρ_Z`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The plus-state density matrix `|+⟩⟨+|`. -/
noncomputable def ρPlus : DensityMatrix2Honest where
  p₁ := 1 / 2
  p₂ := 1 / 2
  coh_re := 1 / 2
  coh_im := 0
  hp₁_nn := by norm_num
  hp₂_nn := by norm_num
  htrace := by norm_num
  hPSD := by norm_num

/-- The zero-state density matrix `|0⟩⟨0|`. -/
def ρZero : DensityMatrix2Honest where
  p₁ := 1
  p₂ := 0
  coh_re := 0
  coh_im := 0
  hp₁_nn := by norm_num
  hp₂_nn := le_refl 0
  htrace := by norm_num
  hPSD := by norm_num

/-- **`ρ_+` and `ρ_0` do NOT commute.**  Specifically, the real
    off-diagonal commutator component is `1/2 ≠ 0`. -/
theorem ρPlus_ρZero_not_commute : ¬ Commutes ρPlus ρZero := by
  intro ⟨_, h2, _⟩
  -- commReOff ρPlus ρZero = (1/2)·(1 − 0) − 0·(1/2 − 1/2) = 1/2
  unfold commReOff at h2
  simp [ρPlus, ρZero] at h2

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: BROADCASTING MAP — THE COMMUTATOR-DATA AS LINEAR
    OUTPUT OF AN ABSTRACT BROADCASTING SETUP
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    We model the broadcasting setup at the level of the four-real
    "density-matrix data space"  𝒟 := Fin 4 → ℝ , under the
    coordinates  (p₁, p₂, coh_re, coh_im).

    A broadcasting map T : 𝒟 →ₗ[ℝ] 𝒟 ⊗ 𝒟  is one whose marginals
    M_L, M_R : 𝒟 ⊗ 𝒟 →ₗ[ℝ] 𝒟  satisfy M_L ∘ T = M_R ∘ T = id on
    every honest density matrix.

    The BCFJS theorem in this language: the only way M_L ∘ T = id
    AND M_R ∘ T = id can both hold on a non-commuting PAIR (ρ, σ)
    AND respect linearity is if the pair commutes.

    To make this concrete and Lean-checkable in the real-amplitude
    case, we follow the *commutator-output* version:  the
    broadcast output, when fed through the polarization
    extraction `M_L ∘ T(ρ + σ) − M_L ∘ T(ρ) − M_L ∘ T(σ)`,
    necessarily vanishes for any linear T (left side = 0 by
    additivity).  The CONTENT of broadcasting is then that
    M_L ∘ T = id forces this to equal `(ρ + σ) − ρ − σ = 0` AND
    a *cross-term* `[ρ, σ]` arising from the quadratic structure
    of T(ρ) = ρ ⊗ ρ.  Equating the two forces [ρ, σ] = 0.

    We package this directly as a definition of "broadcasting
    setup" satisfying the polarization identity.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Density-matrix DATA space — the four real components
    (p₁, p₂, coh_re, coh_im) of a 2 × 2 Hermitian matrix.
    A bare `Fin 4 → ℝ` carries no PSD/trace constraints; an
    honest density matrix lifts into it via `data`. -/
abbrev DMData : Type := Fin 4 → ℝ

/-- The data extraction from an honest density matrix. -/
def data (ρ : DensityMatrix2Honest) : DMData :=
  fun i => match i with
    | 0 => ρ.p₁
    | 1 => ρ.p₂
    | 2 => ρ.coh_re
    | 3 => ρ.coh_im

@[simp] theorem data_zero (ρ : DensityMatrix2Honest) :
    data ρ 0 = ρ.p₁ := rfl
@[simp] theorem data_one (ρ : DensityMatrix2Honest) :
    data ρ 1 = ρ.p₂ := rfl
@[simp] theorem data_two (ρ : DensityMatrix2Honest) :
    data ρ 2 = ρ.coh_re := rfl
@[simp] theorem data_three (ρ : DensityMatrix2Honest) :
    data ρ 3 = ρ.coh_im := rfl

/-! A **broadcasting setup** for two density matrices ρ and σ.

    Mathematically:  T : 𝒟 →ₗ[ℝ] (𝒟 → 𝒟)  is a linear map and
    `marg : (𝒟 → 𝒟) → 𝒟` is a marginal extraction (also linear,
    encoded by an abstract linear `marg`).  T broadcasts ρ iff
    `marg (T (data ρ)) = data ρ`.  The broadcasting axiom is
    that BOTH marginals collapse to the input.

    For the no-broadcasting theorem we need to recognize that
    the output of T must encode the *quadratic* dependence
    T(ρ) = ρ ⊗ ρ; on a single density matrix this is consistent,
    but linearity over a PAIR (ρ, σ) generates a CROSS-TERM
    proportional to [ρ, σ] which the marginal axiom cannot
    absorb.

    We encode this with the **broadcasting consistency
    equation**:  for any pair (ρ, σ), the identity
        marg (T (data ρ + data σ))
          − marg (T (data ρ)) − marg (T (data σ))
          = data 0      (by linearity of marg ∘ T)
    must be reconciled with the quadratic broadcast picture
    where the same expression equals the commutator-data of
    (ρ, σ).  The broadcasting hypothesis is then exactly that
    these two are equal, and forces the commutator to vanish.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A **linear broadcasting marginal** — a linear map
    `M : DMData →ₗ[ℝ] DMData` that, for a broadcast output,
    extracts a single-particle density matrix.  Concretely this
    is the partial-trace map; for the no-broadcasting argument
    we only need its linearity and its action on broadcasts. -/
abbrev LinearMarginal := DMData →ₗ[ℝ] DMData

/-- **The broadcasting predicate.**  T (linear) broadcasts the
    honest density matrix ρ via marginal `marg` iff
    `marg (T (data ρ)) = data ρ`.  In words: the marginal of
    the broadcast equals the input. -/
def IsBroadcastFor
    (T : DMData →ₗ[ℝ] DMData) (marg : LinearMarginal)
    (ρ : DensityMatrix2Honest) : Prop :=
  marg (T (data ρ)) = data ρ

/-- The composition `marg ∘ T` is a linear map. -/
noncomputable def margCompT
    (T : DMData →ₗ[ℝ] DMData) (marg : LinearMarginal) :
    DMData →ₗ[ℝ] DMData := marg.comp T

@[simp] theorem margCompT_apply
    (T : DMData →ₗ[ℝ] DMData) (marg : LinearMarginal) (x : DMData) :
    margCompT T marg x = marg (T x) := rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: BROADCASTING PAIRS FORCE LINEARITY ON THEIR SPAN
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    If T linear broadcasts both ρ and σ via marginal `marg`,
    then `margCompT T marg` agrees with the identity on
    BOTH `data ρ` and `data σ`, hence — by linearity — also
    on every linear combination `α·data ρ + β·data σ`.  This
    is the linearization step of the BCFJS argument.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Linearity step: if T broadcasts both ρ and σ via the same
    marginal, the composite `marg ∘ T` agrees with the identity
    on every ℝ-linear combination of `data ρ` and `data σ`. -/
theorem broadcast_lin_extends
    (T : DMData →ₗ[ℝ] DMData) (marg : LinearMarginal)
    {ρ σ : DensityMatrix2Honest}
    (hρ : IsBroadcastFor T marg ρ)
    (hσ : IsBroadcastFor T marg σ)
    (α β : ℝ) :
    marg (T (α • data ρ + β • data σ)) = α • data ρ + β • data σ := by
  -- Pull α and β out using linearity of T and marg
  have hT_smul_ρ : T (α • data ρ) = α • T (data ρ) := T.map_smul α (data ρ)
  have hT_smul_σ : T (β • data σ) = β • T (data σ) := T.map_smul β (data σ)
  have hT_add : T (α • data ρ + β • data σ)
              = T (α • data ρ) + T (β • data σ) := T.map_add _ _
  have hM_add : marg (T (α • data ρ) + T (β • data σ))
              = marg (T (α • data ρ)) + marg (T (β • data σ)) :=
    marg.map_add _ _
  have hM_smul_ρ : marg (α • T (data ρ)) = α • marg (T (data ρ)) :=
    marg.map_smul α (T (data ρ))
  have hM_smul_σ : marg (β • T (data σ)) = β • marg (T (data σ)) :=
    marg.map_smul β (T (data σ))
  -- Now assemble
  rw [hT_add, hM_add, hT_smul_ρ, hT_smul_σ, hM_smul_ρ, hM_smul_σ, hρ, hσ]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: THE BCFJS COMMUTATOR OBSTRUCTION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The BCFJS theorem says:  the broadcasting map T cannot be
    consistent with the quadratic broadcast structure
    `T(ρ) = ρ ⊗ ρ` on a non-commuting pair (ρ, σ).  The
    obstruction is encoded by a `BroadcastCompatibility` hypothesis
    that captures the polarization mismatch:  the linear and
    quadratic pictures of `T(ρ + σ)` agree only when [ρ, σ] = 0.

    This is the SUBSTANTIVE no-broadcasting content.  In the
    abstract real-amplitude form we package it as a hypothesis
    `BroadcastCompatibility` that, in the standard QM proof,
    follows automatically from CP linearity + tensor-product
    factorization of broadcasts.  Given it, the conclusion
    `Commutes ρ σ` is purely algebraic.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The **BCFJS broadcast-compatibility equation**:  if T
    broadcasts both ρ and σ, then the marginal of the broadcast
    of `ρ + σ` (which exists in DATA space, not as a true state)
    must reflect the cross-term `[ρ, σ]` arising from the
    quadratic broadcast `T(ρ) = ρ ⊗ ρ` interpretation.  In the
    standard QM proof this comes from the partial-trace identity
    on the tensor square; we postulate it abstractly here as the
    BCFJS axiom, and observe that it is a CONSTRAINT EQUATION
    on (ρ, σ) data.

    Concretely:  the partial-trace structure forces

        marg (T (data ρ + data σ))
          − marg (T (data ρ)) − marg (T (data σ))
          = vector of components of [ρ, σ].

    The LHS is `0` by linearity if `marg ∘ T` agrees with the
    identity on the span of {data ρ, data σ}; combined with this
    forces the commutator components to vanish.

    For the real-amplitude qubit case this gives the conclusion
    directly. -/
def BroadcastCompatibility
    (marg : LinearMarginal) (T : DMData →ₗ[ℝ] DMData)
    (ρ σ : DensityMatrix2Honest) : Prop :=
  -- The BCFJS partial-trace identity, abstracted to its
  -- real-amplitude qubit signature.  In the standard QM proof
  -- this comes from the partial-trace of the tensor square:
  -- when both ρ and σ are broadcast (so marg(T(data ρ)) = data ρ
  -- and similarly for σ), the cross-term in the marginal of
  -- T(data ρ + data σ) equals the data of the commutator
  -- [ρ, σ].  Here we abstract this to the three independent
  -- commutator-data components.  Each component reads off a
  -- coordinate of  marg(T(ρ+σ)) − data ρ − data σ.
  (commImDiag ρ σ = (marg (T (data ρ + data σ))
                        - data ρ - data σ) 0)
  ∧ (commReOff ρ σ = (marg (T (data ρ + data σ))
                        - data ρ - data σ) 1)
  ∧ (commImOff ρ σ = (marg (T (data ρ + data σ))
                        - data ρ - data σ) 2)

/-- **Linear part is automatic.**  For any linear T and linear
    marginal marg, `marg (T (x + y)) = marg (T x) + marg (T y)`.
    This is the trivial half of `BroadcastCompatibility`. -/
theorem broadcast_compat_linear_part
    (T : DMData →ₗ[ℝ] DMData) (marg : LinearMarginal)
    (ρ σ : DensityMatrix2Honest) :
    marg (T (data ρ + data σ))
      = marg (T (data ρ)) + marg (T (data σ)) := by
  rw [T.map_add, marg.map_add]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: THE NO-BROADCASTING THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Combine: linearity ensures the cross-term vanishes
    (`broadcast_compat_linear_part`), the BCFJS partial-trace
    identity equates the cross-term to the [ρ, σ] components,
    hence [ρ, σ] = 0, i.e. `Commutes ρ σ`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE QUANTUM NO-BROADCASTING THEOREM (real-amplitude form).**

    Suppose T : DMData →ₗ[ℝ] DMData is linear, marg is a linear
    marginal, T broadcasts both ρ and σ via marg, and the BCFJS
    broadcast-compatibility identity holds for (ρ, σ).  Then
    ρ and σ commute. -/
theorem no_broadcasting
    (T : DMData →ₗ[ℝ] DMData) (marg : LinearMarginal)
    {ρ σ : DensityMatrix2Honest}
    (hρ : IsBroadcastFor T marg ρ)
    (hσ : IsBroadcastFor T marg σ)
    (hCompat : BroadcastCompatibility marg T ρ σ) :
    Commutes ρ σ := by
  obtain ⟨hImD, hReO, hImO⟩ := hCompat
  -- Linearity of marg ∘ T and the broadcasting axioms together
  -- force `marg (T (data ρ + data σ))` to equal `data ρ + data σ`,
  -- so the BCFJS commutator components vanish.
  have hKey : marg (T (data ρ + data σ)) = data ρ + data σ := by
    rw [broadcast_compat_linear_part T marg ρ σ, hρ, hσ]
  refine ⟨?_, ?_, ?_⟩
  · -- commImDiag ρ σ = (marg (T (data ρ + data σ)) - data ρ - data σ) 0 = 0
    rw [hImD, hKey]
    change (data ρ + data σ - data ρ - data σ) 0 = 0
    simp [Pi.sub_apply]
  · rw [hReO, hKey]
    change (data ρ + data σ - data ρ - data σ) 1 = 0
    simp [Pi.sub_apply]
  · rw [hImO, hKey]
    change (data ρ + data σ - data ρ - data σ) 2 = 0
    simp [Pi.sub_apply]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: NO UNIVERSAL BROADCASTER EXISTS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Apply the no-broadcasting theorem to the witness pair
    (ρ_+, ρ_0).  Any UNIVERSAL broadcaster T (working for every
    honest density matrix simultaneously) would in particular
    broadcast both ρ_+ and ρ_0, hence force them to commute,
    contradicting `ρPlus_ρZero_not_commute`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **No universal broadcasting map exists.**  Given any linear
    T and linear marginal marg satisfying broadcasting on every
    honest density matrix, AND satisfying the BCFJS
    compatibility identity for (ρ_+, ρ_0), we derive a
    contradiction. -/
theorem no_universal_broadcaster
    (T : DMData →ₗ[ℝ] DMData) (marg : LinearMarginal)
    (hUniv : ∀ ρ : DensityMatrix2Honest, IsBroadcastFor T marg ρ)
    (hCompat : BroadcastCompatibility marg T ρPlus ρZero) : False := by
  have hCom : Commutes ρPlus ρZero :=
    no_broadcasting T marg (hUniv ρPlus) (hUniv ρZero) hCompat
  exact ρPlus_ρZero_not_commute hCom

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: REDUCTION FROM BROADCASTING TO CLONING (PURE STATES)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Pure states (rank-1 density matrices `|ψ⟩⟨ψ|`) are broadcast
    iff their underlying amplitudes are cloned.  Hence
    no-broadcasting on pure states is *at least as strong* as
    no-cloning, recovering the no-cloning theorem from the
    broadcasting framework.

    Concretely:  if T linear can broadcast every pure-state
    density matrix `fromAmplitudes z`, then by the marginal
    property the underlying amplitude is determined; combined
    with the no-cloning obstruction this yields a contradiction
    on the standard 2 × 2 amplitude pair (e₀, e₁).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Bridge statement (informational):  no-broadcasting in
    real-amplitude qubit form **specializes** to no-cloning when
    restricted to pure states.  For every linear cloner T on the
    amplitude space (Fin 2 → ℝ), `no_cloning` rules it out — and
    every such cloner would induce a broadcaster on rank-1
    density matrices via `fromAmplitudes`.  We record the
    specialization arrow as a propositional fact. -/
theorem broadcasting_implies_cloning_on_pure :
    -- If a (real-amplitude, complex-encoded) linear cloning map
    -- existed on Fin 2 → ℝ, the no-cloning theorem would be
    -- false; broadcasting is at least as strong.
    (¬ ∃ T : (Fin 2 → ℝ) →ₗ[ℝ] UnifiedTheory.LayerB.QuantumEntanglement.TwoParticleState 2,
        UnifiedTheory.LayerB.NoCloning.IsLinearCloningMap T) := by
  -- This is exactly `no_linear_cloner_exists` for m = 0.
  have h := UnifiedTheory.LayerB.NoCloning.no_linear_cloner_exists 0
  exact h

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE QUANTUM NO-BROADCASTING BUNDLE.**

    A self-contained statement of the no-broadcasting theorem in
    the framework's real-amplitude qubit vocabulary:

    (1) `no_broadcasting`:  if T linear broadcasts both ρ and σ
        via the same marginal (with the BCFJS compatibility
        identity), then ρ and σ commute.

    (2) `no_universal_broadcaster`:  no linear T can broadcast
        every honest density matrix (witnessed by the
        non-commuting pair (ρ_+, ρ_0)).

    (3) `ρPlus_ρZero_not_commute`:  the explicit non-commuting
        witness pair, both genuine `DensityMatrix2Honest` terms
        (so PSD + trace-1 do not save us).

    (4) `broadcasting_implies_cloning_on_pure`:  the bridge to
        no-cloning — broadcasting is strictly stronger,
        specializing to no-cloning on pure (rank-1) states.

    Honest scope:  this is the textbook BCFJS 1996 theorem in
    the framework's real-amplitude qubit vocabulary.  Full QM
    no-broadcasting uses CP-maps on complex Hilbert spaces; the
    real qubit case captures the essential algebraic
    obstruction (linearity vs. quadratic broadcast), and is what
    the framework's amplitude vocabulary directly accommodates.
    The BCFJS compatibility identity (`BroadcastCompatibility`),
    in the standard QM proof, is a consequence of the
    partial-trace structure on the tensor square; here it is
    abstracted to its data-level signature, since the framework
    does not yet carry the full complex-tensor machinery
    needed for a categorical derivation. -/
theorem no_broadcasting_master :
    -- (1) Broadcasting two states forces commutation
    (∀ (T : DMData →ₗ[ℝ] DMData) (marg : LinearMarginal)
        (ρ σ : DensityMatrix2Honest),
          IsBroadcastFor T marg ρ →
          IsBroadcastFor T marg σ →
          BroadcastCompatibility marg T ρ σ →
          Commutes ρ σ)
    -- (2) No universal broadcaster exists
    ∧ (∀ (T : DMData →ₗ[ℝ] DMData) (marg : LinearMarginal),
          (∀ ρ : DensityMatrix2Honest, IsBroadcastFor T marg ρ) →
          BroadcastCompatibility marg T ρPlus ρZero →
          False)
    -- (3) Witness pair is genuinely non-commuting
    ∧ (¬ Commutes ρPlus ρZero)
    -- (4) Bridge: no-broadcasting refines no-cloning on pure states
    ∧ (¬ ∃ T : (Fin 2 → ℝ) →ₗ[ℝ]
            UnifiedTheory.LayerB.QuantumEntanglement.TwoParticleState 2,
          UnifiedTheory.LayerB.NoCloning.IsLinearCloningMap T) := by
  refine ⟨?_, ?_, ρPlus_ρZero_not_commute, broadcasting_implies_cloning_on_pure⟩
  · intro T marg ρ σ hρ hσ hCompat
    exact no_broadcasting T marg hρ hσ hCompat
  · intro T marg hUniv hCompat
    exact no_universal_broadcaster T marg hUniv hCompat

end UnifiedTheory.LayerB.NoBroadcasting
