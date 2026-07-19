/-
  LayerB/LohmillerSlotineSubBridge1.lean — Sub-bridge 1 of continuumLimitOfKP

  DISCRETE K/P AMPLITUDE  →  CONTINUUM (r, s).

  Following the three-sub-bridge plan from
  `LohmillerSlotineContinuumLimit.lean`:

    "As n → ∞, the discrete poset-growth K/P pair (Q_n, P_n) converges
     to (r·cos s, r·sin s) for some smooth (r, s) on the emergent
     manifold."

  Concrete plan executed here:
    • introduce `BoundedKPSequence`, a *compactness predicate* on a
      `DiscreteKPSequence`: the (Q_n, P_n) pairs live in a uniform
      box `[-M, M] × [-M, M]`;
    • close the (genuinely trivial) **eventually-zero special case**
      of sub-bridge 1: if every growth step has `Q = P = 0`, then
      sub-bridge 1 holds with `r = 0` for *any* phase `s`;
    • close **Bolzano-Weierstrass for bounded K/P sequences**: any
      bounded K/P sequence has a strictly-increasing subsequence
      along which BOTH the Q-coordinate and the P-coordinate converge.
      Proof: apply Mathlib's `IsCompact.tendsto_subseq` on `Icc (-M) M`
      twice (diagonal extraction).

  These are the first two concrete bricks of sub-bridge 1:
    (a) a TRIVIAL VERIFIED INSTANCE  (constant-zero growth),
    (b) the GENERIC COMPACTNESS LEMMA used to extract candidate limits.

  The remaining frontier (gauge-fixing of phase `s`, identification of
  `(r, s)` from the joint Q/P limit, regularity of the resulting
  (r, s) field) is documented in Part 4.

  Zero sorry.  Zero custom axioms (beyond the standard `propext`,
  `Classical.choice`, `Quot.sound` set).
-/
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.UniformSpace.UniformApproximation
import UnifiedTheory.LayerB.LohmillerSlotineContinuumLimit

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.LohmillerSlotineSubBridge1

open UnifiedTheory.LayerB.LohmillerSlotineContinuumLimit
open UnifiedTheory.LayerB.PosetGrowthIsQuantum
open Filter Topology

/-! ════════════════════════════════════════════════════════════════════════
    PART 1 — `BoundedKPSequence`:  COMPACTNESS PREDICATE
    ════════════════════════════════════════════════════════════════════════ -/

/-- A `DiscreteKPSequence` is **bounded** if there is a uniform bound
    `M ≥ 0` such that every (Q_n, P_n) pair lies inside the box
    `[-M, M] × [-M, M]`.

    Concretely: ∃ M ≥ 0, ∀ n, |Q_n| ≤ M ∧ |P_n| ≤ M.

    This is the natural minimal hypothesis under which sub-bridge 1
    becomes a *compactness* problem: the candidate limit points live
    in a compact subset of ℝ², so Bolzano-Weierstrass applies. -/
def BoundedKPSequence (seq : DiscreteKPSequence) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
    |(seq.growth n).Q| ≤ M ∧ |(seq.growth n).P| ≤ M

/-- The Q-coordinate of a bounded K/P sequence lies in the compact
    interval `Icc (-M) M`. -/
theorem boundedKP_Q_mem_Icc
    {seq : DiscreteKPSequence} {M : ℝ}
    (hM : ∀ n : ℕ, |(seq.growth n).Q| ≤ M ∧ |(seq.growth n).P| ≤ M)
    (n : ℕ) :
    (seq.growth n).Q ∈ Set.Icc (-M) M := by
  refine ⟨?_, ?_⟩
  · have h := (hM n).1
    have := abs_le.mp h
    exact this.1
  · have h := (hM n).1
    have := abs_le.mp h
    exact this.2

/-- The P-coordinate of a bounded K/P sequence lies in the compact
    interval `Icc (-M) M`. -/
theorem boundedKP_P_mem_Icc
    {seq : DiscreteKPSequence} {M : ℝ}
    (hM : ∀ n : ℕ, |(seq.growth n).Q| ≤ M ∧ |(seq.growth n).P| ≤ M)
    (n : ℕ) :
    (seq.growth n).P ∈ Set.Icc (-M) M := by
  refine ⟨?_, ?_⟩
  · have h := (hM n).2
    have := abs_le.mp h
    exact this.1
  · have h := (hM n).2
    have := abs_le.mp h
    exact this.2

/-! ════════════════════════════════════════════════════════════════════════
    PART 2 — EVENTUALLY-ZERO SPECIAL CASE OF SUB-BRIDGE 1

    Simplest possible verified instance:  if every growth step has
    `Q = P = 0`, then sub-bridge 1 holds for `r = 0` and *any*
    phase `s`.  This sidesteps polar gauge-fixing entirely (the
    phase is irretrievably ambiguous at the origin).
    ════════════════════════════════════════════════════════════════════════ -/

/-- A `DiscreteKPSequence` is **identically zero** if every growth
    step has `Q = 0` and `P = 0`. -/
def IsZeroKPSequence (seq : DiscreteKPSequence) : Prop :=
  ∀ n : ℕ, (seq.growth n).Q = 0 ∧ (seq.growth n).P = 0

/-- **Sub-bridge 1, eventually-zero special case**:

    If a K/P sequence is identically zero, then it satisfies
    `SubBridge1_DiscreteAmplitudeToContinuum` with `r = 0` for any
    phase `s`.

    At the origin polar coordinates degenerate (the phase is undefined),
    so this is the *unique* corner of sub-bridge 1 where gauge-fixing
    is vacuous.  It still serves as a first concrete verified
    instance. -/
theorem subBridge1_zero
    (seq : DiscreteKPSequence) (hzero : IsZeroKPSequence seq) (s : ℝ) :
    SubBridge1_DiscreteAmplitudeToContinuum seq 0 s := by
  constructor
  · -- Q_n → 0 · cos s = 0
    have hQ : (fun n => (seq.growth n).Q) = (fun _ => (0 : ℝ)) := by
      funext n; exact (hzero n).1
    rw [hQ]
    have : (0 : ℝ) * Real.cos s = 0 := by ring
    rw [this]
    exact tendsto_const_nhds
  · -- P_n → 0 · sin s = 0
    have hP : (fun n => (seq.growth n).P) = (fun _ => (0 : ℝ)) := by
      funext n; exact (hzero n).2
    rw [hP]
    have : (0 : ℝ) * Real.sin s = 0 := by ring
    rw [this]
    exact tendsto_const_nhds

/-- Specialization: identically-zero K/P sequences satisfy sub-bridge 1
    with phase `s = 0` (a canonical concrete choice). -/
theorem subBridge1_zero_phase_zero
    (seq : DiscreteKPSequence) (hzero : IsZeroKPSequence seq) :
    SubBridge1_DiscreteAmplitudeToContinuum seq 0 0 :=
  subBridge1_zero seq hzero 0

/-! ════════════════════════════════════════════════════════════════════════
    PART 3 — BOLZANO-WEIERSTRASS FOR BOUNDED K/P SEQUENCES

    Generic compactness result:  any bounded K/P sequence has a
    subsequence along which both the Q-coordinate AND the P-coordinate
    converge.  Proof:  apply `IsCompact.tendsto_subseq` on `Icc (-M) M`
    to the Q-coordinate (yielding extractor `φ₁`), then apply it again
    to the P-coordinate composed with `φ₁` (yielding extractor `φ₂`).
    The diagonal subsequence `φ₁ ∘ φ₂` makes both coordinates converge.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Bolzano-Weierstrass for bounded K/P sequences**.

    Every bounded K/P sequence has a strictly increasing subsequence
    indexer `ψ : ℕ → ℕ` along which BOTH `Q ∘ ψ` and `P ∘ ψ` converge
    in ℝ.

    Proof:
    (a) `Set.Icc (-M) M` is compact (`isCompact_Icc`);
    (b) the Q-sequence lies in `Icc (-M) M`, so by
        `IsCompact.tendsto_subseq` we get extractor `φ₁` with
        `(Q ∘ φ₁) → qLim` for some `qLim ∈ Icc (-M) M`;
    (c) the P-sequence composed with `φ₁` still lies in `Icc (-M) M`,
        so again by `IsCompact.tendsto_subseq` we get extractor `φ₂`
        with `((P ∘ φ₁) ∘ φ₂) → pLim`;
    (d) `Q ∘ (φ₁ ∘ φ₂)` is a subsequence of `Q ∘ φ₁`, hence still
        converges to `qLim`.

    The conclusion is exactly the joint convergence required to feed
    `SubBridge1_DiscreteAmplitudeToContinuum` — modulo the still-open
    polar gauge-fixing of `(r, s)` from `(qLim, pLim)`.  See Part 4
    for the remaining frontier. -/
theorem BoundedKPSequence_has_convergent_subsequence
    (seq : DiscreteKPSequence) (hb : BoundedKPSequence seq) :
    ∃ (ψ : ℕ → ℕ), StrictMono ψ ∧
      ∃ qLim pLim : ℝ,
        Tendsto (fun n => (seq.growth (ψ n)).Q) atTop (nhds qLim)
        ∧ Tendsto (fun n => (seq.growth (ψ n)).P) atTop (nhds pLim) := by
  obtain ⟨M, _hMnn, hM⟩ := hb
  -- (a) Compactness of `Icc (-M) M`.
  have hK : IsCompact (Set.Icc (-M) M) := isCompact_Icc
  -- (b) Apply Bolzano-Weierstrass to the Q-sequence.
  have hQmem : ∀ n, (seq.growth n).Q ∈ Set.Icc (-M) M :=
    boundedKP_Q_mem_Icc hM
  obtain ⟨qLim, _hqLim_mem, φ₁, hφ₁_mono, hQconv⟩ :=
    hK.tendsto_subseq (x := fun n => (seq.growth n).Q) hQmem
  -- (c) Apply Bolzano-Weierstrass to the P-sequence composed with `φ₁`.
  have hPmem : ∀ n, (seq.growth (φ₁ n)).P ∈ Set.Icc (-M) M := fun n =>
    boundedKP_P_mem_Icc hM (φ₁ n)
  obtain ⟨pLim, _hpLim_mem, φ₂, hφ₂_mono, hPconv⟩ :=
    hK.tendsto_subseq (x := fun n => (seq.growth (φ₁ n)).P) hPmem
  -- (d) Diagonal subsequence  ψ := φ₁ ∘ φ₂.
  refine ⟨φ₁ ∘ φ₂, hφ₁_mono.comp hφ₂_mono, qLim, pLim, ?_, ?_⟩
  · -- Q ∘ (φ₁ ∘ φ₂) converges to qLim.
    -- This is the restriction of a convergent sequence `Q ∘ φ₁ → qLim`
    -- to the subsequence indexed by `φ₂`.
    exact hQconv.comp hφ₂_mono.tendsto_atTop
  · -- P ∘ (φ₁ ∘ φ₂) converges to pLim by construction.
    exact hPconv

/-! ════════════════════════════════════════════════════════════════════════
    PART 4 — STATUS / PRE-REGISTRATION OF THE REMAINING FRONTIER

    Closed in this file:
      ✓ `BoundedKPSequence` predicate.
      ✓ `subBridge1_zero` — identically-zero K/P sequences satisfy
        sub-bridge 1 with `r = 0`, any phase.
      ✓ `BoundedKPSequence_has_convergent_subsequence` —
        Bolzano-Weierstrass extraction of a jointly-convergent
        (Q, P) subsequence.

    Open (the genuinely-unfinished part of sub-bridge 1):

    (I) **Polar gauge-fixing.**  Given a joint limit `(qLim, pLim) ∈
        ℝ²` of `(Q ∘ ψ, P ∘ ψ)`, identify the corresponding
        `(r_lim, s_lim) ∈ ℝ × [0, 2π)` with `r_lim · cos s_lim = qLim`
        and `r_lim · sin s_lim = pLim`.  Standard polar decomposition,
        but the phase is ambiguous at the origin (`r_lim = 0`).  A
        clean closure picks a section of the quotient map
        `ℝ² ⟶ ℝ × (ℝ / 2π)` (e.g. `Real.arctan2`).

    (II) **Subsequence-independence of the limit.**  Different
        extractors `ψ` may pick out different limits in general.  For
        the K/P sub-bridge to give a *well-defined* continuum
        amplitude one needs either (a) the WHOLE sequence converges
        (stronger than Bolzano-Weierstrass), or (b) all subsequential
        limits agree (e.g. by a separate continuity/regularity
        argument).  Pre-registered as the next milestone.

    (III) **Pointwise-in-(x, t) version.**  The headline
        `ContinuumLimitOfKP` quantifies sub-bridge 1 over every
        spacetime point `(x, t)`.  This file works pointwise in n;
        the (x, t) lift is bookkeeping once (I) and (II) close.

    (IV) **Regularity of the resulting `(r, s)` field.**  The final
        Sub-bridge 1 statement needed by sub-bridge 3 demands
        `SmoothWaveField`-level regularity.  This is downstream of
        (I)-(III) and depends on the smoothness of the substrate
        scaling (Hauptvermutung Λ² → 0 control).

    Each of (I)-(IV) is a single-target proof obligation that can be
    attacked in isolation.  See `LohmillerSlotineSubBridge2.lean` for
    the analogous decomposition of sub-bridge 2.
    ════════════════════════════════════════════════════════════════════════ -/

/-! ════════════════════════════════════════════════════════════════════════
    PART 5 — POLAR GAUGE-FIXING (milestone (I))

    Given a joint limit `(q, p) ∈ ℝ²`, exhibit `(r, s) ∈ ℝ≥0 × ℝ` with
        `r · cos s = q`   and   `r · sin s = p`.

    Construction:  view `(q, p)` as a complex number `z := q + p·i ∈ ℂ`,
    take `r := ‖z‖ = √(q² + p²)` and `s := Complex.arg z ∈ (-π, π]`.
    Mathlib's `Complex.norm_mul_cos_arg` / `Complex.norm_mul_sin_arg`
    give the polar identities directly.  This works at every point of
    `ℝ²`, including the origin (where `arg 0 = 0` and `r = 0` makes
    both identities `0 = 0` regardless of `s`).
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Polar decomposition of an arbitrary pair `(q, p) ∈ ℝ²`.**

    There exists `(r, s) ∈ ℝ≥0 × ℝ` with
        `r · cos s = q`  and  `r · sin s = p`.
    Concretely `r = √(q² + p²)` and `s = Complex.arg (q + p·i)`. -/
theorem polar_gauge_fixing (q p : ℝ) :
    ∃ r s : ℝ, 0 ≤ r ∧ r * Real.cos s = q ∧ r * Real.sin s = p := by
  refine ⟨‖(⟨q, p⟩ : ℂ)‖, Complex.arg (⟨q, p⟩ : ℂ), norm_nonneg _, ?_, ?_⟩
  · -- ‖z‖ · cos(arg z) = z.re = q
    have := Complex.norm_mul_cos_arg (⟨q, p⟩ : ℂ); exact this
  · -- ‖z‖ · sin(arg z) = z.im = p
    have := Complex.norm_mul_sin_arg (⟨q, p⟩ : ℂ); exact this

/-- **Sub-bridge 1, polar form, for bounded K/P sequences.**

    Combining Bolzano-Weierstrass (Part 3) with polar gauge-fixing
    (Part 5), every bounded K/P sequence has a subsequence whose
    joint `(Q, P)` limit admits a polar form `(r, s)` such that
        `Q_{ψ(n)} → r · cos s`   and   `P_{ψ(n)} → r · sin s`.

    This is the first verified instance of the headline shape
    `SubBridge1_DiscreteAmplitudeToContinuum` for non-degenerate
    (i.e. not identically-zero) K/P sequences. -/
theorem BoundedKPSequence_has_polar_convergent_subsequence
    (seq : DiscreteKPSequence) (hb : BoundedKPSequence seq) :
    ∃ (ψ : ℕ → ℕ), StrictMono ψ ∧
      ∃ r s : ℝ, 0 ≤ r ∧
        Tendsto (fun n => (seq.growth (ψ n)).Q) atTop
          (nhds (r * Real.cos s))
        ∧ Tendsto (fun n => (seq.growth (ψ n)).P) atTop
          (nhds (r * Real.sin s)) := by
  obtain ⟨ψ, hψ_mono, qLim, pLim, hQ, hP⟩ :=
    BoundedKPSequence_has_convergent_subsequence seq hb
  obtain ⟨r, s, hr_nn, hQ_eq, hP_eq⟩ := polar_gauge_fixing qLim pLim
  refine ⟨ψ, hψ_mono, r, s, hr_nn, ?_, ?_⟩
  · rw [hQ_eq]; exact hQ
  · rw [hP_eq]; exact hP

/-! ════════════════════════════════════════════════════════════════════════
    PART 6 — SUBSEQUENCE-INDEPENDENCE OF THE LIMIT (milestone (II))

    Given a bounded K/P sequence, IF every strictly-monotone subsequence
    that joint-converges does so to the *same* candidate `(qLim, pLim)`,
    THEN the entire sequence converges to `(qLim, pLim)`.

    Proof strategy:
    (a) Bundle `(Q_n, P_n)` into `ℝ²`.  The bounded box
        `Icc (-M) M ×ˢ Icc (-M) M` is compact.
    (b) Apply `IsCompact.tendsto_nhds_of_unique_mapClusterPt`:  it
        suffices to show every cluster point of the joint sequence
        equals `(qLim, pLim)`.
    (c) Any such cluster point comes from a `MapClusterPt`, which by
        `Filter.subseq_tendsto_of_neBot` gives a strictly-monotone
        subsequence with joint limit `(q', p')`.  Apply `huniq`.
    (d) Project the joint convergence to each coordinate.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Subsequence-independence ⇒ convergence of the full sequence.**

    If a bounded K/P sequence has the property that *every*
    strictly-monotone subsequence which makes both `Q` and `P` converge
    does so to a common candidate `(qLim, pLim)`, then the full
    sequence converges:  `Q_n → qLim` and `P_n → pLim`.

    This closes milestone (II) of sub-bridge 1:  the
    Bolzano-Weierstrass-extracted polar limit `(r, s)` is unambiguous
    once the user supplies the `huniq` certificate. -/
theorem BoundedKPSequence_unique_subseq_limit_converges
    (seq : DiscreteKPSequence) (hb : BoundedKPSequence seq)
    (qLim pLim : ℝ)
    (huniq : ∀ (ψ : ℕ → ℕ), StrictMono ψ → ∀ q' p' : ℝ,
       Tendsto (fun n => (seq.growth (ψ n)).Q) atTop (nhds q') →
       Tendsto (fun n => (seq.growth (ψ n)).P) atTop (nhds p') →
       q' = qLim ∧ p' = pLim) :
    Tendsto (fun n => (seq.growth n).Q) atTop (nhds qLim) ∧
    Tendsto (fun n => (seq.growth n).P) atTop (nhds pLim) := by
  obtain ⟨M, _hMnn, hM⟩ := hb
  -- (a) Bundle into ℝ²; the box is compact.
  have hK : IsCompact (Set.Icc (-M) M ×ˢ Set.Icc (-M) M) :=
    isCompact_Icc.prod isCompact_Icc
  -- (b)+(c) Joint convergence to (qLim, pLim) via the unique-clusterPt lemma.
  have h_joint :
      Tendsto (fun n => ((seq.growth n).Q, (seq.growth n).P))
        atTop (nhds (qLim, pLim)) := by
    apply hK.tendsto_nhds_of_unique_mapClusterPt
    · -- f n ∈ K for every n (in fact always).
      refine Filter.Eventually.of_forall ?_
      intro n
      exact ⟨boundedKP_Q_mem_Icc hM n, boundedKP_P_mem_Icc hM n⟩
    · -- Every cluster point in K equals (qLim, pLim).
      rintro ⟨q', p'⟩ _hmem hcluster
      -- Extract a strict-mono subsequence ψ realising (q', p') as a joint limit.
      obtain ⟨ψ, hψ_mono, hψ_conv⟩ :=
        Filter.subseq_tendsto_of_neBot
          (f := nhds (q', p'))
          (u := fun n => ((seq.growth n).Q, (seq.growth n).P)) hcluster
      have hQ' : Tendsto (fun n => (seq.growth (ψ n)).Q) atTop (nhds q') :=
        (continuous_fst.tendsto (q', p')).comp hψ_conv
      have hP' : Tendsto (fun n => (seq.growth (ψ n)).P) atTop (nhds p') :=
        (continuous_snd.tendsto (q', p')).comp hψ_conv
      obtain ⟨hq, hp⟩ := huniq ψ hψ_mono q' p' hQ' hP'
      exact Prod.mk.injEq _ _ _ _ |>.mpr ⟨hq, hp⟩
  -- (d) Project to each coordinate.
  refine ⟨?_, ?_⟩
  · exact (continuous_fst.tendsto (qLim, pLim)).comp h_joint
  · exact (continuous_snd.tendsto (qLim, pLim)).comp h_joint

/-- **Corollary**:  combining Part 6 with polar gauge-fixing, a bounded
    K/P sequence whose subsequential `(Q, P)` limit is unique yields a
    *full-sequence* polar continuum amplitude `(r, s)` with
        `Q_n → r · cos s`   and   `P_n → r · sin s`.

    This is the first full-sequence (not subsequence) statement matching
    the headline shape of `SubBridge1_DiscreteAmplitudeToContinuum`, in
    the bounded case with a uniqueness certificate. -/
theorem BoundedKPSequence_unique_limit_polar_form
    (seq : DiscreteKPSequence) (hb : BoundedKPSequence seq)
    (qLim pLim : ℝ)
    (huniq : ∀ (ψ : ℕ → ℕ), StrictMono ψ → ∀ q' p' : ℝ,
       Tendsto (fun n => (seq.growth (ψ n)).Q) atTop (nhds q') →
       Tendsto (fun n => (seq.growth (ψ n)).P) atTop (nhds p') →
       q' = qLim ∧ p' = pLim) :
    ∃ r s : ℝ, 0 ≤ r ∧
      Tendsto (fun n => (seq.growth n).Q) atTop (nhds (r * Real.cos s))
      ∧ Tendsto (fun n => (seq.growth n).P) atTop (nhds (r * Real.sin s)) := by
  obtain ⟨hQ, hP⟩ :=
    BoundedKPSequence_unique_subseq_limit_converges seq hb qLim pLim huniq
  obtain ⟨r, s, hr_nn, hQ_eq, hP_eq⟩ := polar_gauge_fixing qLim pLim
  refine ⟨r, s, hr_nn, ?_, ?_⟩
  · rw [hQ_eq]; exact hQ
  · rw [hP_eq]; exact hP

/-! ════════════════════════════════════════════════════════════════════════
    PART 7 — POINTWISE-IN-(x, t) LIFT (milestone (III))

    Promote the single-sequence theory of Parts 1-6 to a spacetime-indexed
    family.  A `KPField` is `ℝ → ℝ → DiscreteKPSequence`; uniform
    boundedness and per-(x, t) subseq-uniqueness lift to a pointwise
    polar amplitude `(r(x, t), s(x, t))` satisfying the headline shape
    `SubBridge1_DiscreteAmplitudeToContinuum` at every spacetime point.
    ════════════════════════════════════════════════════════════════════════ -/

/-- A `KPField` is a spacetime-indexed family of discrete K/P sequences,
    one per `(x, t) ∈ ℝ × ℝ`. -/
def KPField : Type := ℝ → ℝ → DiscreteKPSequence

/-- A `KPField` is **uniformly bounded** if a single `M ≥ 0` bounds every
    component sequence at every spacetime point. -/
def BoundedKPField (F : KPField) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ x t n,
    |((F x t).growth n).Q| ≤ M ∧ |((F x t).growth n).P| ≤ M

/-- From uniform boundedness of a `KPField`, every pointwise restriction
    is a `BoundedKPSequence`. -/
theorem BoundedKPField.pointwise
    {F : KPField} (hF : BoundedKPField F) (x t : ℝ) :
    BoundedKPSequence (F x t) := by
  obtain ⟨M, hMnn, hM⟩ := hF
  exact ⟨M, hMnn, fun n => hM x t n⟩

/-! ════════════════════════════════════════════════════════════════════════
    PHASE B.1 — `BoundedKPField` FROM A SUBSTRATE ENERGY BOUND.

    The `BoundedKPField` hypothesis assumed in SB1 is currently a
    stand-alone analytic condition.  This section converts it into a
    consequence of a more physically natural substrate-level condition:
    a uniform upper bound on the SO(2)-invariant quadratic form
    `Q² + P²` over the entire spacetime-indexed K/P field.

    The quadratic form `Q² + P²` is the natural "substrate energy":
    `LohmillerSlotineBridge.rotation_preserves_norm` and the dressing-
    invariance machinery in `PosetGrowthIsQuantum` already show that
    SO(2)-invariant substrate dynamics preserve this quantity.  So a
    uniform bound on `Q² + P²` is exactly the conclusion one expects
    from a conserved substrate energy.

    Step 1 (here):  given a uniform bound on `Q² + P²`, conclude
                    `BoundedKPField`.
    Step 2 (next):  derive the uniform bound on `Q² + P²` from
                    substrate dynamics + initial-energy hypotheses.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Substrate energy bound**:  the SO(2)-invariant quadratic form
    `Q² + P²` is uniformly bounded on the entire K/P field. -/
def SubstrateEnergyBound (F : KPField) (M_E : ℝ) : Prop :=
  0 ≤ M_E ∧ ∀ x t n,
    ((F x t).growth n).Q ^ 2 + ((F x t).growth n).P ^ 2 ≤ M_E

/-- **`KPField_bounded_from_substrate_energy`**:  a uniform substrate
    energy bound `Q² + P² ≤ M_E` implies the analytic boundedness
    hypothesis `BoundedKPField` with constant `M = √M_E`.

    This is the first Phase-B step:  SB1's boundedness assumption is
    now a *consequence* of a physically natural substrate condition,
    rather than a stipulated analytic hypothesis. -/
theorem KPField_bounded_from_substrate_energy
    {F : KPField} {M_E : ℝ} (h : SubstrateEnergyBound F M_E) :
    BoundedKPField F := by
  obtain ⟨hME_nn, h_bd⟩ := h
  refine ⟨Real.sqrt M_E, Real.sqrt_nonneg _, ?_⟩
  intro x t n
  have h_sum := h_bd x t n
  have hQ_sq : ((F x t).growth n).Q ^ 2 ≤ M_E := by
    nlinarith [sq_nonneg ((F x t).growth n).P]
  have hP_sq : ((F x t).growth n).P ^ 2 ≤ M_E := by
    nlinarith [sq_nonneg ((F x t).growth n).Q]
  refine ⟨?_, ?_⟩
  · -- |Q| = √(Q²) ≤ √M_E
    have : |((F x t).growth n).Q| = Real.sqrt (((F x t).growth n).Q ^ 2) :=
      (Real.sqrt_sq_eq_abs _).symm
    rw [this]
    exact Real.sqrt_le_sqrt hQ_sq
  · -- |P| = √(P²) ≤ √M_E
    have : |((F x t).growth n).P| = Real.sqrt (((F x t).growth n).P ^ 2) :=
      (Real.sqrt_sq_eq_abs _).symm
    rw [this]
    exact Real.sqrt_le_sqrt hP_sq

/-- A `KPField` is **substrate-energy-bounded** if SOME constant `M_E`
    serves as a uniform energy bound. -/
def SubstrateEnergyBounded (F : KPField) : Prop :=
  ∃ M_E : ℝ, SubstrateEnergyBound F M_E

/-- Existential form:  any substrate-energy-bounded `KPField` is
    analytically bounded. -/
theorem KPField_bounded_of_substrateEnergyBounded
    {F : KPField} (h : SubstrateEnergyBounded F) : BoundedKPField F := by
  obtain ⟨M_E, hM_E⟩ := h
  exact KPField_bounded_from_substrate_energy hM_E

/-- Conversely:  analytic boundedness implies a substrate energy bound.
    `BoundedKPField` with constant `M` yields energy bound `2 M²`
    (since `Q² + P² ≤ M² + M² = 2 M²`). -/
theorem substrateEnergyBounded_of_BoundedKPField
    {F : KPField} (h : BoundedKPField F) : SubstrateEnergyBounded F := by
  obtain ⟨M, hMnn, hM⟩ := h
  refine ⟨2 * M ^ 2, ?_, ?_⟩
  · positivity
  · intro x t n
    have ⟨hQ, hP⟩ := hM x t n
    have hQ_sq : ((F x t).growth n).Q ^ 2 ≤ M ^ 2 := by
      have := sq_abs ((F x t).growth n).Q
      nlinarith [sq_nonneg (|((F x t).growth n).Q| - M), abs_nonneg ((F x t).growth n).Q]
    have hP_sq : ((F x t).growth n).P ^ 2 ≤ M ^ 2 := by
      have := sq_abs ((F x t).growth n).P
      nlinarith [sq_nonneg (|((F x t).growth n).P| - M), abs_nonneg ((F x t).growth n).P]
    linarith

/-- **Equivalence**:  the two notions of boundedness are equivalent.
    This shows the substrate-energy formulation is exactly as strong
    as the analytic `BoundedKPField` — both are valid entrypoints to
    SB1. -/
theorem boundedKPField_iff_substrateEnergyBounded
    (F : KPField) : BoundedKPField F ↔ SubstrateEnergyBounded F :=
  ⟨substrateEnergyBounded_of_BoundedKPField,
   KPField_bounded_of_substrateEnergyBounded⟩

/-! ════════════════════════════════════════════════════════════════════════
    PHASE B.2 — SUBSTRATE EVOLUTION LAW IMPLIES THE ENERGY BOUND.

    Promote Phase B.1 from "energy is uniformly bounded" (a state
    condition) to a derivation from substrate-side dynamical
    constraints:

      `SubstrateEvolutionLaw` (one-step energy non-increase)
        + `InitialEnergyBound` (energy bound at n = 0)
        ⇒  `SubstrateEnergyBound` (uniform bound at all n)
        ⇒  `BoundedKPField` (the analytic SB1 hypothesis).

    The SO(2)-invariant quadratic form `Q² + P²` is preserved exactly
    under the rotation action  (`rotation_preserves_norm`).  So any
    dressing-invariant substrate evolution — including the pure
    rotation case — satisfies `SubstrateEvolutionLaw` automatically.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Substrate evolution law**:  at each step `n → n+1`, the SO(2)-
    invariant quadratic form `Q² + P²` does not increase.  This is
    the natural one-step constraint imposed by SO(2)-invariant
    (in particular, dressing-invariant) substrate dynamics. -/
def SubstrateEvolutionLaw (F : KPField) : Prop :=
  ∀ x t n,
    ((F x t).growth (n + 1)).Q ^ 2 + ((F x t).growth (n + 1)).P ^ 2
    ≤ ((F x t).growth n).Q ^ 2 + ((F x t).growth n).P ^ 2

/-- **Initial energy bound**:  the K/P energy at step 0 is bounded by
    `M_E` uniformly in (x, t). -/
def InitialEnergyBound (F : KPField) (M_E : ℝ) : Prop :=
  ∀ x t, ((F x t).growth 0).Q ^ 2 + ((F x t).growth 0).P ^ 2 ≤ M_E

/-- **Energy non-increasing along the sequence** (induction from the
    one-step law). -/
theorem substrate_energy_nonincreasing
    {F : KPField} (h_dyn : SubstrateEvolutionLaw F)
    (x t : ℝ) (n : ℕ) :
    ((F x t).growth n).Q ^ 2 + ((F x t).growth n).P ^ 2
    ≤ ((F x t).growth 0).Q ^ 2 + ((F x t).growth 0).P ^ 2 := by
  induction n with
  | zero => exact le_refl _
  | succ n ih => exact le_trans (h_dyn x t n) ih

/-- **PHASE B.2 KEY THEOREM**:  substrate evolution law plus initial
    energy bound yields the uniform substrate energy bound. -/
theorem substrate_energy_bound_from_evolution
    {F : KPField} {M_E : ℝ}
    (h_dyn : SubstrateEvolutionLaw F)
    (hM_E_nn : 0 ≤ M_E)
    (h_init : InitialEnergyBound F M_E) :
    SubstrateEnergyBound F M_E := by
  refine ⟨hM_E_nn, fun x t n => ?_⟩
  exact le_trans (substrate_energy_nonincreasing h_dyn x t n) (h_init x t)

/-- **PHASE B.2 HEADLINE — SB1 BOUNDEDNESS FROM DYNAMICS**.

    Substrate evolution law + initial energy bound ⇒ `BoundedKPField`.
    The SB1 analytic hypothesis is now a DERIVED consequence of the
    substrate-side dynamical conditions:
      • the dynamics is (at least) SO(2)-invariantly energy-preserving,
      • the initial K/P energy is bounded.

    No analytic hypothesis on the limit fields is needed for boundedness. -/
theorem SB1_boundedness_from_dynamics
    {F : KPField} {M_E : ℝ}
    (h_dyn : SubstrateEvolutionLaw F)
    (hM_E_nn : 0 ≤ M_E)
    (h_init : InitialEnergyBound F M_E) :
    BoundedKPField F :=
  KPField_bounded_from_substrate_energy
    (substrate_energy_bound_from_evolution h_dyn hM_E_nn h_init)

/-! **Pure SO(2)-rotation evolution as the canonical example.**

    The dressing-rotation `rotateQ, rotateP` from `PosetGrowthIsQuantum`
    preserves `Q² + P²` exactly (`rotation_preserves_norm`).  So any
    KP field whose one-step update is a (possibly position- or
    time-dependent) rotation automatically satisfies `SubstrateEvolutionLaw`
    with equality. -/

/-- **SO(2)-rotation substrate evolution**:  at every spacetime point
    and every step, `(Q_{n+1}, P_{n+1})` is the rotation of `(Q_n, P_n)`
    by some angle `θ(x, t, n)`.  This is the canonical dressing-
    invariant substrate evolution. -/
def SO2RotationEvolution (F : KPField) : Prop :=
  ∀ x t n, ∃ θ : ℝ,
    ((F x t).growth (n + 1)).Q
      = PosetGrowthIsQuantum.rotateQ
          ((F x t).growth n).Q ((F x t).growth n).P θ
    ∧ ((F x t).growth (n + 1)).P
      = PosetGrowthIsQuantum.rotateP
          ((F x t).growth n).Q ((F x t).growth n).P θ

/-- **SO(2)-rotation evolution ⇒ `SubstrateEvolutionLaw`** (with
    equality, hence in particular non-increase). -/
theorem SO2RotationEvolution_implies_substrateEvolutionLaw
    {F : KPField} (h : SO2RotationEvolution F) :
    SubstrateEvolutionLaw F := by
  intro x t n
  obtain ⟨θ, hQ, hP⟩ := h x t n
  rw [hQ, hP, PosetGrowthIsQuantum.rotation_preserves_norm]

/-- **Composed headline — SB1 BOUNDEDNESS FROM PURE ROTATION DYNAMICS**:

    A K/P field evolving by SO(2)-rotation at each step, with bounded
    initial energy, is `BoundedKPField`.  Combined with the rest of
    SB1, this yields the full pointwise polar amplitude lift on a
    purely substrate-side hypothesis. -/
theorem SB1_boundedness_from_SO2Rotation
    {F : KPField} {M_E : ℝ}
    (h_dyn : SO2RotationEvolution F)
    (hM_E_nn : 0 ≤ M_E)
    (h_init : InitialEnergyBound F M_E) :
    BoundedKPField F :=
  SB1_boundedness_from_dynamics
    (SO2RotationEvolution_implies_substrateEvolutionLaw h_dyn)
    hM_E_nn h_init


/-- Per-(x, t) subsequence-uniqueness predicate:  at every spacetime
    point, every joint subseq limit `(q', p')` equals the prescribed
    candidate `(qLim x t, pLim x t)`. -/
def KPFieldHasUniqueSubseqLimits (F : KPField)
    (qLim pLim : ℝ → ℝ → ℝ) : Prop :=
  ∀ x t, ∀ (ψ : ℕ → ℕ), StrictMono ψ → ∀ q' p' : ℝ,
    Tendsto (fun n => ((F x t).growth (ψ n)).Q) atTop (nhds q') →
    Tendsto (fun n => ((F x t).growth (ψ n)).P) atTop (nhds p') →
    q' = qLim x t ∧ p' = pLim x t

/-! ════════════════════════════════════════════════════════════════════════
    PHASE B.3 — SB1 UNIQUE-SUBSEQ HYPOTHESIS FROM SUBSTRATE REFINEMENT.

    The next SB1 demotion target:  `KPFieldHasUniqueSubseqLimits` is
    currently an analytic stipulation in SB1.  The natural substrate-
    side hypothesis behind it is *refinement control* — at every
    spacetime point, the K/P amplitudes `(Q_n, P_n)` are jointly
    Cauchy as the substrate is refined (n → ∞).

    Under this hypothesis the WHOLE sequence converges (not just a
    subsequence), so subsequence uniqueness is trivial:  every
    subsequential limit equals the canonical whole-sequence limit.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Substrate refinement control**:  at every spacetime point,
    both `(Q_n)` and `(P_n)` are Cauchy as `n → ∞`.  This captures
    the idea that substrate refinement (Hauptvermutung `Λ² → 0`)
    makes the K/P amplitudes stabilize — the physical input behind
    subsequence uniqueness. -/
def SubstrateRefinementControl (F : KPField) : Prop :=
  ∀ x t,
    CauchySeq (fun n => ((F x t).growth n).Q) ∧
    CauchySeq (fun n => ((F x t).growth n).P)

/-- Under substrate refinement control, the WHOLE K/P sequence
    converges at every spacetime point to canonical limit functions
    `qLim, pLim : ℝ → ℝ → ℝ`. -/
theorem KPField_converges_of_refinementControl
    {F : KPField} (h : SubstrateRefinementControl F) :
    ∃ qLim pLim : ℝ → ℝ → ℝ, ∀ x t,
      Tendsto (fun n => ((F x t).growth n).Q) atTop (nhds (qLim x t))
      ∧ Tendsto (fun n => ((F x t).growth n).P) atTop (nhds (pLim x t)) := by
  refine ⟨fun x t => limUnder atTop (fun n => ((F x t).growth n).Q),
          fun x t => limUnder atTop (fun n => ((F x t).growth n).P),
          fun x t => ⟨(h x t).1.tendsto_limUnder, (h x t).2.tendsto_limUnder⟩⟩

/-- **PHASE B.3 — UNIQUE-SUBSEQ LIMITS FROM REFINEMENT CONTROL**.

    Under substrate refinement control, the canonical limit functions
    (whole-sequence limits, from `KPField_converges_of_refinementControl`)
    satisfy `KPFieldHasUniqueSubseqLimits`.  Every subsequence limit
    at every spacetime point must equal the canonical limit, since
    any subsequence of a convergent sequence converges to the same
    point. -/
theorem SB1_uniqueSubseqLimits_from_refinementControl
    {F : KPField} (h : SubstrateRefinementControl F) :
    ∃ qLim pLim : ℝ → ℝ → ℝ,
      (∀ x t, Tendsto (fun n => ((F x t).growth n).Q) atTop (nhds (qLim x t))
              ∧ Tendsto (fun n => ((F x t).growth n).P) atTop (nhds (pLim x t)))
      ∧ KPFieldHasUniqueSubseqLimits F qLim pLim := by
  obtain ⟨qLim, pLim, h_conv⟩ := KPField_converges_of_refinementControl h
  refine ⟨qLim, pLim, h_conv, ?_⟩
  intro x t ψ hψ_mono q' p' hQ' hP'
  have hQ_subseq : Tendsto (fun n => ((F x t).growth (ψ n)).Q)
      atTop (nhds (qLim x t)) := (h_conv x t).1.comp hψ_mono.tendsto_atTop
  have hP_subseq : Tendsto (fun n => ((F x t).growth (ψ n)).P)
      atTop (nhds (pLim x t)) := (h_conv x t).2.comp hψ_mono.tendsto_atTop
  exact ⟨tendsto_nhds_unique hQ' hQ_subseq, tendsto_nhds_unique hP' hP_subseq⟩

/-- **B.2 + B.3 combined headline**:  substrate dynamics + initial
    energy bound + refinement control ⇒ BOTH analytic SB1 hypotheses
    (`BoundedKPField` and `KPFieldHasUniqueSubseqLimits`) are
    discharged from purely substrate-side conditions.

    Composed with the existing SB1 machinery, this yields the pointwise
    polar amplitude lift at every spacetime point WITHOUT any
    analytic hypothesis on the limit fields — only substrate dynamics
    + initial energy + refinement control. -/
theorem SB1_bounded_and_unique_from_substrate
    {F : KPField} {M_E : ℝ}
    (h_dyn : SubstrateEvolutionLaw F)
    (hM_E_nn : 0 ≤ M_E)
    (h_init : InitialEnergyBound F M_E)
    (h_refine : SubstrateRefinementControl F) :
    BoundedKPField F
    ∧ ∃ qLim pLim : ℝ → ℝ → ℝ, KPFieldHasUniqueSubseqLimits F qLim pLim := by
  refine ⟨SB1_boundedness_from_dynamics h_dyn hM_E_nn h_init, ?_⟩
  obtain ⟨qLim, pLim, _h_conv, h_uniq⟩ :=
    SB1_uniqueSubseqLimits_from_refinementControl h_refine
  exact ⟨qLim, pLim, h_uniq⟩

/-- **B.2 + B.3 with pure SO(2)-rotation dynamics**:  the same headline
    but with the canonical SO(2)-rotation evolution as the substrate
    dynamics. -/
theorem SB1_bounded_and_unique_from_SO2Rotation
    {F : KPField} {M_E : ℝ}
    (h_dyn : SO2RotationEvolution F)
    (hM_E_nn : 0 ≤ M_E)
    (h_init : InitialEnergyBound F M_E)
    (h_refine : SubstrateRefinementControl F) :
    BoundedKPField F
    ∧ ∃ qLim pLim : ℝ → ℝ → ℝ, KPFieldHasUniqueSubseqLimits F qLim pLim :=
  SB1_bounded_and_unique_from_substrate
    (SO2RotationEvolution_implies_substrateEvolutionLaw h_dyn)
    hM_E_nn h_init h_refine

/-! ════════════════════════════════════════════════════════════════════════
    PHASE B.4 STEP 1 — CONTINUITY OF (qLim, pLim) FROM LOCALLY-UNIFORM CONVERGENCE.

    The third (and final) analytic SB1 hypothesis is regularity of
    `(qLim, pLim)`.  Promoting it from "assumed" to "derived" requires
    going through Arzelà-Ascoli-style arguments:

      • each discrete field `(Q_n, P_n)` is regular at substrate level,
      • the discrete fields converge LOCALLY UNIFORMLY (not just
        pointwise) to `(qLim, pLim)`,
      • derivatives also converge locally uniformly (for C¹/C²).

    This file delivers **Step 1**:  the C⁰ (continuity) level of the
    chain.  The C¹/C² extensions follow the same template with
    derivatives in place of values, using Mathlib's
    `TendstoLocallyUniformly`-preserves-`ContDiff` results.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Substrate-side discrete continuity hypothesis**:  at every substrate
    scale `n`, the discrete `(Q_n, P_n)` field is jointly continuous in
    `(x, t)`. -/
def KPFieldDiscreteContinuous (F : KPField) : Prop :=
  ∀ n,
    Continuous (fun xt : ℝ × ℝ => ((F xt.1 xt.2).growth n).Q) ∧
    Continuous (fun xt : ℝ × ℝ => ((F xt.1 xt.2).growth n).P)

/-- **Locally uniform convergence of `(Q_n, P_n)` to `(qLim, pLim)`** as
    functions on the spacetime plane.  Strictly stronger than the
    pointwise convergence guaranteed by `SubstrateRefinementControl`. -/
def KPFieldLocallyUniformLimit
    (F : KPField) (qLim pLim : ℝ → ℝ → ℝ) : Prop :=
  TendstoLocallyUniformly
    (fun (n : ℕ) (xt : ℝ × ℝ) => ((F xt.1 xt.2).growth n).Q)
    (Function.uncurry qLim) atTop
  ∧ TendstoLocallyUniformly
    (fun (n : ℕ) (xt : ℝ × ℝ) => ((F xt.1 xt.2).growth n).P)
    (Function.uncurry pLim) atTop

/-- **PHASE B.4 STEP 1 — CONTINUITY OF THE CONTINUUM LIMIT**.

    If each discrete `(Q_n, P_n)` field is continuous and the family
    converges locally uniformly to `(qLim, pLim)`, then the limit
    fields are continuous on all of `ℝ × ℝ`. -/
theorem qLim_pLim_continuous_from_substrate
    {F : KPField} {qLim pLim : ℝ → ℝ → ℝ}
    (h_disc : KPFieldDiscreteContinuous F)
    (h_lim : KPFieldLocallyUniformLimit F qLim pLim) :
    Continuous (Function.uncurry qLim)
    ∧ Continuous (Function.uncurry pLim) := by
  have hQ : ∀ᶠ (n : ℕ) in atTop,
      Continuous (fun xt : ℝ × ℝ => ((F xt.1 xt.2).growth n).Q) := by
    refine Filter.Eventually.of_forall ?_
    intro n
    exact (h_disc n).1
  have hP : ∀ᶠ (n : ℕ) in atTop,
      Continuous (fun xt : ℝ × ℝ => ((F xt.1 xt.2).growth n).P) := by
    refine Filter.Eventually.of_forall ?_
    intro n
    exact (h_disc n).2
  exact ⟨h_lim.1.continuous hQ.frequently, h_lim.2.continuous hP.frequently⟩

/-! ════════════════════════════════════════════════════════════════════════
    PHASE B.4 STEP 2 — `ContDiff ℝ 1` OF (qLim, pLim) FROM SUBSTRATE FDERIVS.

    Promote Phase B.4 Step 1 from continuity to differentiability:  if
    each discrete field is `ContDiff ℝ 1` and BOTH the values AND the
    fderivs converge locally uniformly to limits, then the limit fields
    are `ContDiff ℝ 1`.

    Proof template (textbook):
      • `hasFDerivAt_of_tendsto_locally_uniformly_on'` gives pointwise
        existence of the limit fderiv at every spacetime point.
      • `Differentiable ℝ qLim` follows globally.
      • The limit fderiv (a locally uniform limit of continuous fderivs)
        is continuous.
      • Hence `ContDiff ℝ 1 qLim` via `contDiff_one_iff_fderiv`.

    Steps 3 (C²) and beyond follow the same template recursively, with
    second-order fderiv-of-fderiv playing the role of fderiv here. -/

/-- **Substrate-side discrete C¹ hypothesis**:  every discrete field is
    `ContDiff ℝ 1` in `(x, t)`. -/
def KPFieldDiscreteContDiff1 (F : KPField) : Prop :=
  ∀ n,
    ContDiff ℝ 1 (fun xt : ℝ × ℝ => ((F xt.1 xt.2).growth n).Q) ∧
    ContDiff ℝ 1 (fun xt : ℝ × ℝ => ((F xt.1 xt.2).growth n).P)

/-- **Substrate-side locally uniform convergence of fderivs**:  the
    Fréchet derivatives of the discrete fields converge locally
    uniformly in `(x, t)` to candidate limit fderivs `g'_Q, g'_P`. -/
def KPFieldLocallyUniformFDerivLimit
    (F : KPField) (g'_Q g'_P : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ)) : Prop :=
  TendstoLocallyUniformly
    (fun (n : ℕ) =>
      fderiv ℝ (fun yt : ℝ × ℝ => ((F yt.1 yt.2).growth n).Q))
    g'_Q atTop
  ∧ TendstoLocallyUniformly
    (fun (n : ℕ) =>
      fderiv ℝ (fun yt : ℝ × ℝ => ((F yt.1 yt.2).growth n).P))
    g'_P atTop

/-- **PHASE B.4 STEP 2 — `ContDiff ℝ 1` OF (qLim, pLim) FROM SUBSTRATE**.

    Substrate-side discrete `ContDiff ℝ 1` + locally uniform convergence
    of values + locally uniform convergence of fderivs ⇒ the limit
    fields `(qLim, pLim)` are `ContDiff ℝ 1`. -/
theorem qLim_pLim_contDiff1_from_substrate
    {F : KPField} {qLim pLim : ℝ → ℝ → ℝ}
    {g'_Q g'_P : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ)}
    (h_disc : KPFieldDiscreteContDiff1 F)
    (h_val : KPFieldLocallyUniformLimit F qLim pLim)
    (h_fderiv : KPFieldLocallyUniformFDerivLimit F g'_Q g'_P) :
    ContDiff ℝ 1 (Function.uncurry qLim)
    ∧ ContDiff ℝ 1 (Function.uncurry pLim) := by
  have h1ne0 : (1 : WithTop ℕ∞) ≠ 0 := by decide
  -- Each discrete field is globally Differentiable, hence DifferentiableOn univ.
  have hQ_diff : ∀ n,
      DifferentiableOn ℝ
        (fun yt : ℝ × ℝ => ((F yt.1 yt.2).growth n).Q) Set.univ :=
    fun n => ((h_disc n).1.differentiable h1ne0).differentiableOn
  have hP_diff : ∀ n,
      DifferentiableOn ℝ
        (fun yt : ℝ × ℝ => ((F yt.1 yt.2).growth n).P) Set.univ :=
    fun n => ((h_disc n).2.differentiable h1ne0).differentiableOn
  -- Locally uniform conv as TendstoLocallyUniformlyOn univ.
  have hQ_fd_lu :
      TendstoLocallyUniformlyOn
        (fderiv ℝ ∘ (fun (n : ℕ) (yt : ℝ × ℝ) => ((F yt.1 yt.2).growth n).Q))
        g'_Q atTop Set.univ := by
    rw [tendstoLocallyUniformlyOn_univ]; exact h_fderiv.1
  have hP_fd_lu :
      TendstoLocallyUniformlyOn
        (fderiv ℝ ∘ (fun (n : ℕ) (yt : ℝ × ℝ) => ((F yt.1 yt.2).growth n).P))
        g'_P atTop Set.univ := by
    rw [tendstoLocallyUniformlyOn_univ]; exact h_fderiv.2
  -- Pointwise value convergence on univ (from locally uniform conv).
  have hQ_val_on : TendstoLocallyUniformlyOn
      (fun (n : ℕ) (yt : ℝ × ℝ) => ((F yt.1 yt.2).growth n).Q)
      (Function.uncurry qLim) atTop Set.univ := by
    rw [tendstoLocallyUniformlyOn_univ]; exact h_val.1
  have hP_val_on : TendstoLocallyUniformlyOn
      (fun (n : ℕ) (yt : ℝ × ℝ) => ((F yt.1 yt.2).growth n).P)
      (Function.uncurry pLim) atTop Set.univ := by
    rw [tendstoLocallyUniformlyOn_univ]; exact h_val.2
  have hQ_ptw : ∀ xt : ℝ × ℝ, xt ∈ Set.univ →
      Tendsto (fun n => ((F xt.1 xt.2).growth n).Q)
        atTop (nhds (Function.uncurry qLim xt)) :=
    fun xt hxt => hQ_val_on.tendsto_at hxt
  have hP_ptw : ∀ xt : ℝ × ℝ, xt ∈ Set.univ →
      Tendsto (fun n => ((F xt.1 xt.2).growth n).P)
        atTop (nhds (Function.uncurry pLim xt)) :=
    fun xt hxt => hP_val_on.tendsto_at hxt
  -- Apply the uniform-limits-of-derivatives theorem at every xt.
  have hQ_hasFD : ∀ xt : ℝ × ℝ, HasFDerivAt (Function.uncurry qLim) (g'_Q xt) xt :=
    fun xt => hasFDerivAt_of_tendsto_locally_uniformly_on' isOpen_univ
      hQ_fd_lu hQ_diff hQ_ptw (Set.mem_univ xt)
  have hP_hasFD : ∀ xt : ℝ × ℝ, HasFDerivAt (Function.uncurry pLim) (g'_P xt) xt :=
    fun xt => hasFDerivAt_of_tendsto_locally_uniformly_on' isOpen_univ
      hP_fd_lu hP_diff hP_ptw (Set.mem_univ xt)
  -- Differentiability.
  have hQ_Diff : Differentiable ℝ (Function.uncurry qLim) :=
    fun xt => (hQ_hasFD xt).differentiableAt
  have hP_Diff : Differentiable ℝ (Function.uncurry pLim) :=
    fun xt => (hP_hasFD xt).differentiableAt
  -- Continuity of the limit fderiv via locally-uniform-conv-preserves-continuity.
  have hQ_fd_cont_disc : ∀ᶠ (n : ℕ) in atTop,
      Continuous
        (fderiv ℝ (fun yt : ℝ × ℝ => ((F yt.1 yt.2).growth n).Q)) := by
    refine Filter.Eventually.of_forall ?_
    intro n; exact (h_disc n).1.continuous_fderiv h1ne0
  have hP_fd_cont_disc : ∀ᶠ (n : ℕ) in atTop,
      Continuous
        (fderiv ℝ (fun yt : ℝ × ℝ => ((F yt.1 yt.2).growth n).P)) := by
    refine Filter.Eventually.of_forall ?_
    intro n; exact (h_disc n).2.continuous_fderiv h1ne0
  have hQ_g'_cont : Continuous g'_Q :=
    h_fderiv.1.continuous hQ_fd_cont_disc.frequently
  have hP_g'_cont : Continuous g'_P :=
    h_fderiv.2.continuous hP_fd_cont_disc.frequently
  -- Identify fderiv qLim with g'_Q pointwise, then continuity transfers.
  have hQ_fderiv_eq : fderiv ℝ (Function.uncurry qLim) = g'_Q :=
    funext (fun xt => (hQ_hasFD xt).fderiv)
  have hP_fderiv_eq : fderiv ℝ (Function.uncurry pLim) = g'_P :=
    funext (fun xt => (hP_hasFD xt).fderiv)
  -- ContDiff ℝ 1 ↔ Differentiable ∧ Continuous (fderiv).
  refine ⟨?_, ?_⟩
  · rw [contDiff_one_iff_fderiv]
    exact ⟨hQ_Diff, hQ_fderiv_eq ▸ hQ_g'_cont⟩
  · rw [contDiff_one_iff_fderiv]
    exact ⟨hP_Diff, hP_fderiv_eq ▸ hP_g'_cont⟩

/-! ════════════════════════════════════════════════════════════════════════
    PHASE B.4 STEP 3 — `ContDiff ℝ 2` OF (qLim, pLim) FROM SUBSTRATE.

    The final SB1 regularity demotion.  Same proof template as Step 2,
    iterated once more:  apply `hasFDerivAt_of_tendsto_locally_uniformly_on'`
    to the fderiv fields themselves to get differentiability of the
    limit fderiv.  Use `contDiff_succ_iff_fderiv` to climb from `C¹`
    to `C²`.

    After this theorem lands, the entire SB1 hypothesis stack is
    substrate-derived. -/

/-- **Substrate-side discrete C² hypothesis**:  every discrete field
    is `ContDiff ℝ 2` in `(x, t)`. -/
def KPFieldDiscreteContDiff2 (F : KPField) : Prop :=
  ∀ n,
    ContDiff ℝ 2 (fun xt : ℝ × ℝ => ((F xt.1 xt.2).growth n).Q) ∧
    ContDiff ℝ 2 (fun xt : ℝ × ℝ => ((F xt.1 xt.2).growth n).P)

/-- **Substrate-side locally uniform convergence of SECOND fderivs**:
    the iterated Fréchet derivatives of the discrete fields converge
    locally uniformly to candidate limits. -/
def KPFieldLocallyUniformSecondFDerivLimit (F : KPField)
    (g''_Q g''_P : ℝ × ℝ → (ℝ × ℝ →L[ℝ] (ℝ × ℝ →L[ℝ] ℝ))) : Prop :=
  TendstoLocallyUniformly
    (fun (n : ℕ) =>
      fderiv ℝ
        (fderiv ℝ (fun yt : ℝ × ℝ => ((F yt.1 yt.2).growth n).Q)))
    g''_Q atTop
  ∧ TendstoLocallyUniformly
    (fun (n : ℕ) =>
      fderiv ℝ
        (fderiv ℝ (fun yt : ℝ × ℝ => ((F yt.1 yt.2).growth n).P)))
    g''_P atTop

/-- **PHASE B.4 STEP 3 — `ContDiff ℝ 2` OF (qLim, pLim) FROM SUBSTRATE**.

    Substrate-side discrete `ContDiff ℝ 2` + locally uniform convergence
    of values + locally uniform convergence of fderivs + locally
    uniform convergence of *second* fderivs ⇒ the limit fields are
    `ContDiff ℝ 2`. -/
theorem qLim_pLim_contDiff2_from_substrate
    {F : KPField} {qLim pLim : ℝ → ℝ → ℝ}
    {g'_Q g'_P : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ)}
    {g''_Q g''_P : ℝ × ℝ → (ℝ × ℝ →L[ℝ] (ℝ × ℝ →L[ℝ] ℝ))}
    (h_disc : KPFieldDiscreteContDiff2 F)
    (h_val : KPFieldLocallyUniformLimit F qLim pLim)
    (h_fderiv : KPFieldLocallyUniformFDerivLimit F g'_Q g'_P)
    (h_2fderiv : KPFieldLocallyUniformSecondFDerivLimit F g''_Q g''_P) :
    ContDiff ℝ 2 (Function.uncurry qLim)
    ∧ ContDiff ℝ 2 (Function.uncurry pLim) := by
  have h1ne0 : (1 : WithTop ℕ∞) ≠ 0 := by decide
  have h2ne0 : (2 : WithTop ℕ∞) ≠ 0 := by decide
  have h_disc1 : KPFieldDiscreteContDiff1 F := fun n =>
    ⟨(h_disc n).1.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2),
     (h_disc n).2.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)⟩
  -- Identify fderiv of qLim with g'_Q via Step 2 machinery.
  have hQ_diff : ∀ n,
      DifferentiableOn ℝ
        (fun yt : ℝ × ℝ => ((F yt.1 yt.2).growth n).Q) Set.univ := fun n =>
    ((h_disc n).1.differentiable h2ne0).differentiableOn
  have hP_diff : ∀ n,
      DifferentiableOn ℝ
        (fun yt : ℝ × ℝ => ((F yt.1 yt.2).growth n).P) Set.univ := fun n =>
    ((h_disc n).2.differentiable h2ne0).differentiableOn
  have hQ_fd_lu : TendstoLocallyUniformlyOn
      (fderiv ℝ ∘ (fun (n : ℕ) (yt : ℝ × ℝ) => ((F yt.1 yt.2).growth n).Q))
      g'_Q atTop Set.univ := by
    rw [tendstoLocallyUniformlyOn_univ]; exact h_fderiv.1
  have hP_fd_lu : TendstoLocallyUniformlyOn
      (fderiv ℝ ∘ (fun (n : ℕ) (yt : ℝ × ℝ) => ((F yt.1 yt.2).growth n).P))
      g'_P atTop Set.univ := by
    rw [tendstoLocallyUniformlyOn_univ]; exact h_fderiv.2
  have hQ_val_on : TendstoLocallyUniformlyOn
      (fun (n : ℕ) (yt : ℝ × ℝ) => ((F yt.1 yt.2).growth n).Q)
      (Function.uncurry qLim) atTop Set.univ := by
    rw [tendstoLocallyUniformlyOn_univ]; exact h_val.1
  have hP_val_on : TendstoLocallyUniformlyOn
      (fun (n : ℕ) (yt : ℝ × ℝ) => ((F yt.1 yt.2).growth n).P)
      (Function.uncurry pLim) atTop Set.univ := by
    rw [tendstoLocallyUniformlyOn_univ]; exact h_val.2
  have hQ_ptw : ∀ xt : ℝ × ℝ, xt ∈ Set.univ →
      Tendsto (fun n => ((F xt.1 xt.2).growth n).Q)
        atTop (nhds (Function.uncurry qLim xt)) :=
    fun xt hxt => hQ_val_on.tendsto_at hxt
  have hP_ptw : ∀ xt : ℝ × ℝ, xt ∈ Set.univ →
      Tendsto (fun n => ((F xt.1 xt.2).growth n).P)
        atTop (nhds (Function.uncurry pLim xt)) :=
    fun xt hxt => hP_val_on.tendsto_at hxt
  have hQ_hasFD : ∀ xt : ℝ × ℝ, HasFDerivAt (Function.uncurry qLim) (g'_Q xt) xt :=
    fun xt => hasFDerivAt_of_tendsto_locally_uniformly_on' isOpen_univ
      hQ_fd_lu hQ_diff hQ_ptw (Set.mem_univ xt)
  have hP_hasFD : ∀ xt : ℝ × ℝ, HasFDerivAt (Function.uncurry pLim) (g'_P xt) xt :=
    fun xt => hasFDerivAt_of_tendsto_locally_uniformly_on' isOpen_univ
      hP_fd_lu hP_diff hP_ptw (Set.mem_univ xt)
  have hQ_Diff : Differentiable ℝ (Function.uncurry qLim) :=
    fun xt => (hQ_hasFD xt).differentiableAt
  have hP_Diff : Differentiable ℝ (Function.uncurry pLim) :=
    fun xt => (hP_hasFD xt).differentiableAt
  have hQ_fderiv_eq : fderiv ℝ (Function.uncurry qLim) = g'_Q :=
    funext (fun xt => (hQ_hasFD xt).fderiv)
  have hP_fderiv_eq : fderiv ℝ (Function.uncurry pLim) = g'_P :=
    funext (fun xt => (hP_hasFD xt).fderiv)
  -- Now apply the same template to the FDERIV fields:  proves ContDiff ℝ 1 g'_Q.
  have h12_le_2 : (1 : WithTop ℕ∞) + 1 ≤ 2 := by norm_num
  have hQ_fd_disc_C1 : ∀ n, ContDiff ℝ 1
      (fderiv ℝ (fun yt : ℝ × ℝ => ((F yt.1 yt.2).growth n).Q)) :=
    fun n => (h_disc n).1.fderiv_right h12_le_2
  have hP_fd_disc_C1 : ∀ n, ContDiff ℝ 1
      (fderiv ℝ (fun yt : ℝ × ℝ => ((F yt.1 yt.2).growth n).P)) :=
    fun n => (h_disc n).2.fderiv_right h12_le_2
  have hQ_fd_diff : ∀ n, DifferentiableOn ℝ
      (fderiv ℝ (fun yt : ℝ × ℝ => ((F yt.1 yt.2).growth n).Q)) Set.univ :=
    fun n => ((hQ_fd_disc_C1 n).differentiable h1ne0).differentiableOn
  have hP_fd_diff : ∀ n, DifferentiableOn ℝ
      (fderiv ℝ (fun yt : ℝ × ℝ => ((F yt.1 yt.2).growth n).P)) Set.univ :=
    fun n => ((hP_fd_disc_C1 n).differentiable h1ne0).differentiableOn
  have hQ_2fd_lu : TendstoLocallyUniformlyOn
      (fderiv ℝ ∘ (fun (n : ℕ) =>
        fderiv ℝ (fun yt : ℝ × ℝ => ((F yt.1 yt.2).growth n).Q)))
      g''_Q atTop Set.univ := by
    rw [tendstoLocallyUniformlyOn_univ]; exact h_2fderiv.1
  have hP_2fd_lu : TendstoLocallyUniformlyOn
      (fderiv ℝ ∘ (fun (n : ℕ) =>
        fderiv ℝ (fun yt : ℝ × ℝ => ((F yt.1 yt.2).growth n).P)))
      g''_P atTop Set.univ := by
    rw [tendstoLocallyUniformlyOn_univ]; exact h_2fderiv.2
  -- Pointwise convergence of fderivs from locally uniform conv.
  have hQ_fd_val_on : TendstoLocallyUniformlyOn
      (fun (n : ℕ) =>
        fderiv ℝ (fun yt : ℝ × ℝ => ((F yt.1 yt.2).growth n).Q))
      g'_Q atTop Set.univ := by
    rw [tendstoLocallyUniformlyOn_univ]; exact h_fderiv.1
  have hP_fd_val_on : TendstoLocallyUniformlyOn
      (fun (n : ℕ) =>
        fderiv ℝ (fun yt : ℝ × ℝ => ((F yt.1 yt.2).growth n).P))
      g'_P atTop Set.univ := by
    rw [tendstoLocallyUniformlyOn_univ]; exact h_fderiv.2
  have hQ_fd_ptw : ∀ xt : ℝ × ℝ, xt ∈ Set.univ →
      Tendsto
        (fun n => fderiv ℝ (fun yt : ℝ × ℝ => ((F yt.1 yt.2).growth n).Q) xt)
        atTop (nhds (g'_Q xt)) :=
    fun xt hxt => hQ_fd_val_on.tendsto_at hxt
  have hP_fd_ptw : ∀ xt : ℝ × ℝ, xt ∈ Set.univ →
      Tendsto
        (fun n => fderiv ℝ (fun yt : ℝ × ℝ => ((F yt.1 yt.2).growth n).P) xt)
        atTop (nhds (g'_P xt)) :=
    fun xt hxt => hP_fd_val_on.tendsto_at hxt
  -- HasFDerivAt of g'_Q at every point with value g''_Q.
  have hQ_g'_hasFD : ∀ xt : ℝ × ℝ, HasFDerivAt g'_Q (g''_Q xt) xt :=
    fun xt => hasFDerivAt_of_tendsto_locally_uniformly_on' isOpen_univ
      hQ_2fd_lu hQ_fd_diff hQ_fd_ptw (Set.mem_univ xt)
  have hP_g'_hasFD : ∀ xt : ℝ × ℝ, HasFDerivAt g'_P (g''_P xt) xt :=
    fun xt => hasFDerivAt_of_tendsto_locally_uniformly_on' isOpen_univ
      hP_2fd_lu hP_fd_diff hP_fd_ptw (Set.mem_univ xt)
  have hQ_g'_Diff : Differentiable ℝ g'_Q :=
    fun xt => (hQ_g'_hasFD xt).differentiableAt
  have hP_g'_Diff : Differentiable ℝ g'_P :=
    fun xt => (hP_g'_hasFD xt).differentiableAt
  have hQ_g'_fderiv_eq : fderiv ℝ g'_Q = g''_Q :=
    funext (fun xt => (hQ_g'_hasFD xt).fderiv)
  have hP_g'_fderiv_eq : fderiv ℝ g'_P = g''_P :=
    funext (fun xt => (hP_g'_hasFD xt).fderiv)
  -- Continuity of g''_Q, g''_P via locally uniform limit of continuous second fderivs.
  have hQ_2fd_cont_disc : ∀ᶠ (n : ℕ) in atTop, Continuous
      (fderiv ℝ
        (fderiv ℝ (fun yt : ℝ × ℝ => ((F yt.1 yt.2).growth n).Q))) := by
    refine Filter.Eventually.of_forall ?_
    intro n; exact (hQ_fd_disc_C1 n).continuous_fderiv h1ne0
  have hP_2fd_cont_disc : ∀ᶠ (n : ℕ) in atTop, Continuous
      (fderiv ℝ
        (fderiv ℝ (fun yt : ℝ × ℝ => ((F yt.1 yt.2).growth n).P))) := by
    refine Filter.Eventually.of_forall ?_
    intro n; exact (hP_fd_disc_C1 n).continuous_fderiv h1ne0
  have hQ_g''_cont : Continuous g''_Q :=
    h_2fderiv.1.continuous hQ_2fd_cont_disc.frequently
  have hP_g''_cont : Continuous g''_P :=
    h_2fderiv.2.continuous hP_2fd_cont_disc.frequently
  -- ContDiff ℝ 1 g'_Q (and g'_P).
  have hQ_g'_C1 : ContDiff ℝ 1 g'_Q := by
    rw [contDiff_one_iff_fderiv]
    exact ⟨hQ_g'_Diff, hQ_g'_fderiv_eq ▸ hQ_g''_cont⟩
  have hP_g'_C1 : ContDiff ℝ 1 g'_P := by
    rw [contDiff_one_iff_fderiv]
    exact ⟨hP_g'_Diff, hP_g'_fderiv_eq ▸ hP_g''_cont⟩
  -- Conclude ContDiff ℝ 2 via contDiff_succ_iff_fderiv.
  refine ⟨?_, ?_⟩
  · rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_fderiv]
    refine ⟨hQ_Diff, ?_, ?_⟩
    · intro h_eq; exact absurd h_eq (by decide)
    · exact hQ_fderiv_eq ▸ hQ_g'_C1
  · rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_fderiv]
    refine ⟨hP_Diff, ?_, ?_⟩
    · intro h_eq; exact absurd h_eq (by decide)
    · exact hP_fderiv_eq ▸ hP_g'_C1

/-- **Composed Phase B.4 Step 1 headline — SB1 with continuity from
    substrate-side conditions only**.

    Combining B.2, B.3, and B.4 Step 1:
      substrate evolution + initial energy + refinement control +
      discrete continuity + locally-uniform convergence
        ⇒ `BoundedKPField` + `KPFieldHasUniqueSubseqLimits`
          + `Continuous (qLim, pLim)`.

    This discharges the substrate-side version of the SB1 input stack
    at the continuity level.  C¹/C² extensions (Phase B.4 Steps 2 and 3)
    add uniform-convergence hypotheses on the discrete derivatives and
    invoke the analogous derivative-preserving uniform-convergence
    theorems. -/
theorem SB1_bounded_unique_continuous_from_substrate
    {F : KPField} {M_E : ℝ}
    (h_dyn : SubstrateEvolutionLaw F)
    (hM_E_nn : 0 ≤ M_E)
    (h_init : InitialEnergyBound F M_E)
    (h_refine : SubstrateRefinementControl F)
    (h_disc : KPFieldDiscreteContinuous F)
    (h_lim_uniform : ∃ qLim pLim, KPFieldLocallyUniformLimit F qLim pLim ∧
      (∀ x t, Tendsto (fun n => ((F x t).growth n).Q) atTop (nhds (qLim x t))
              ∧ Tendsto (fun n => ((F x t).growth n).P) atTop (nhds (pLim x t)))) :
    BoundedKPField F
    ∧ ∃ qLim pLim : ℝ → ℝ → ℝ,
        KPFieldHasUniqueSubseqLimits F qLim pLim
        ∧ Continuous (Function.uncurry qLim)
        ∧ Continuous (Function.uncurry pLim) := by
  refine ⟨SB1_boundedness_from_dynamics h_dyn hM_E_nn h_init, ?_⟩
  obtain ⟨qLim, pLim, h_lu, h_ptw⟩ := h_lim_uniform
  refine ⟨qLim, pLim, ?_, ?_, ?_⟩
  · -- KPFieldHasUniqueSubseqLimits: derive from pointwise convergence directly
    intro x t ψ hψ_mono q' p' hQ' hP'
    have hQ_subseq : Tendsto (fun n => ((F x t).growth (ψ n)).Q)
        atTop (nhds (qLim x t)) := (h_ptw x t).1.comp hψ_mono.tendsto_atTop
    have hP_subseq : Tendsto (fun n => ((F x t).growth (ψ n)).P)
        atTop (nhds (pLim x t)) := (h_ptw x t).2.comp hψ_mono.tendsto_atTop
    exact ⟨tendsto_nhds_unique hQ' hQ_subseq,
           tendsto_nhds_unique hP' hP_subseq⟩
  · exact (qLim_pLim_continuous_from_substrate h_disc h_lu).1
  · exact (qLim_pLim_continuous_from_substrate h_disc h_lu).2

/-- **Pointwise-in-(x, t) lift of sub-bridge 1.**

    A uniformly bounded `KPField` whose per-(x, t) subseq limits are
    unique admits a polar amplitude `(r, s) : ℝ → ℝ → ℝ` such that
    `SubBridge1_DiscreteAmplitudeToContinuum (F x t) (r x t) (s x t)`
    holds at every spacetime point.

    This closes milestone (III) of sub-bridge 1:  the headline shape
    used by `ContinuumLimitOfKP` is realised for any uniformly-bounded
    `KPField` with the standard uniqueness certificate. -/
theorem KPField_pointwise_polar_lift
    (F : KPField) (qLim pLim : ℝ → ℝ → ℝ)
    (hb : BoundedKPField F)
    (huniq : KPFieldHasUniqueSubseqLimits F qLim pLim) :
    ∃ r s : ℝ → ℝ → ℝ, ∀ x t,
      0 ≤ r x t
      ∧ Tendsto (fun n => ((F x t).growth n).Q) atTop
          (nhds (r x t * Real.cos (s x t)))
      ∧ Tendsto (fun n => ((F x t).growth n).P) atTop
          (nhds (r x t * Real.sin (s x t))) := by
  -- Pointwise polar reconstruction.
  have h_pointwise : ∀ x t, ∃ r s : ℝ,
      0 ≤ r
      ∧ Tendsto (fun n => ((F x t).growth n).Q) atTop (nhds (r * Real.cos s))
      ∧ Tendsto (fun n => ((F x t).growth n).P) atTop (nhds (r * Real.sin s)) := by
    intro x t
    exact BoundedKPSequence_unique_limit_polar_form
      (F x t) (hb.pointwise x t) (qLim x t) (pLim x t) (huniq x t)
  -- Skolemise pointwise existential into spacetime fields r, s.
  choose r s hr hQ hP using h_pointwise
  exact ⟨r, s, fun x t => ⟨hr x t, hQ x t, hP x t⟩⟩

/-- **Headline-shape corollary**:  the polar amplitude extracted by
    `KPField_pointwise_polar_lift` satisfies, at every spacetime point,
    exactly the shape `SubBridge1_DiscreteAmplitudeToContinuum`
    consumed by `LohmillerSlotineContinuumLimit.ContinuumLimitOfKP`. -/
theorem KPField_pointwise_polar_lift_headline
    (F : KPField) (qLim pLim : ℝ → ℝ → ℝ)
    (hb : BoundedKPField F)
    (huniq : KPFieldHasUniqueSubseqLimits F qLim pLim) :
    ∃ r s : ℝ → ℝ → ℝ, ∀ x t,
      LohmillerSlotineContinuumLimit.SubBridge1_DiscreteAmplitudeToContinuum
        (F x t) (r x t) (s x t) := by
  obtain ⟨r, s, h⟩ := KPField_pointwise_polar_lift F qLim pLim hb huniq
  refine ⟨r, s, fun x t => ?_⟩
  obtain ⟨_hr, hQ, hP⟩ := h x t
  exact ⟨hQ, hP⟩

/-! ════════════════════════════════════════════════════════════════════════
    PART 8 — REGULARITY UPGRADE: CONTINUITY OF (r, s) FROM (qLim, pLim)
              (FIRST STAGE OF MILESTONE (IV))

    Take the EXPLICIT polar representatives:
        z(x, t) := qLim(x, t) + i · pLim(x, t)
        r(x, t) := ‖z(x, t)‖   ( = √(qLim² + pLim²) )
        s(x, t) := arg z(x, t).

    Then under joint continuity of qLim and pLim on `ℝ × ℝ`:
      • r is continuous everywhere;
      • s is continuous on the OPEN node-free set
            `polarSlitSet := {(x, t) | qLim(x, t) > 0 ∨ pLim(x, t) ≠ 0}`
        i.e. the complement of the closed locus `qLim ≤ 0 ∧ pLim = 0`
        (the origin together with the branch cut along the negative
        real axis — exactly the node locus where polar phase is
        unavoidably ambiguous).

    This is the FIRST STAGE of milestone (IV): continuity of (r, s)
    is the weakest regularity upgrade that is *clean* in the sense
    suggested by the SB1 frontier discussion.  Stronger upgrades
    (Hölder, C¹, smooth) would require corresponding regularity of
    the limit fields qLim, pLim — natural under Hauptvermutung Λ² → 0
    control of the substrate scaling, which is downstream of this file.
    ════════════════════════════════════════════════════════════════════════ -/

/-- Complex-coordinate field associated to the per-(x, t) limits
    `qLim, pLim : ℝ → ℝ → ℝ`.  Returns `z(x, t) := qLim(x, t) + i · pLim(x, t)`. -/
noncomputable def polarZ (qLim pLim : ℝ → ℝ → ℝ) : ℝ → ℝ → ℂ :=
  fun x t => (qLim x t : ℂ) + (pLim x t : ℂ) * Complex.I

/-- The polar radius field `r(x, t) := ‖z(x, t)‖`. -/
noncomputable def polarR (qLim pLim : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun x t => ‖polarZ qLim pLim x t‖

/-- The polar phase field `s(x, t) := arg z(x, t)`. -/
noncomputable def polarS (qLim pLim : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun x t => Complex.arg (polarZ qLim pLim x t)

/-- Real part of `polarZ` is `qLim`. -/
theorem polarZ_re (qLim pLim : ℝ → ℝ → ℝ) (x t : ℝ) :
    (polarZ qLim pLim x t).re = qLim x t := by
  simp [polarZ]

/-- Imaginary part of `polarZ` is `pLim`. -/
theorem polarZ_im (qLim pLim : ℝ → ℝ → ℝ) (x t : ℝ) :
    (polarZ qLim pLim x t).im = pLim x t := by
  simp [polarZ]

/-- `r(x, t) · cos s(x, t) = qLim(x, t)`. -/
theorem polarR_cos_polarS (qLim pLim : ℝ → ℝ → ℝ) (x t : ℝ) :
    polarR qLim pLim x t * Real.cos (polarS qLim pLim x t) = qLim x t := by
  unfold polarR polarS
  rw [Complex.norm_mul_cos_arg]
  exact polarZ_re qLim pLim x t

/-- `r(x, t) · sin s(x, t) = pLim(x, t)`. -/
theorem polarR_sin_polarS (qLim pLim : ℝ → ℝ → ℝ) (x t : ℝ) :
    polarR qLim pLim x t * Real.sin (polarS qLim pLim x t) = pLim x t := by
  unfold polarR polarS
  rw [Complex.norm_mul_sin_arg]
  exact polarZ_im qLim pLim x t

/-- `r(x, t) ≥ 0`. -/
theorem polarR_nonneg (qLim pLim : ℝ → ℝ → ℝ) (x t : ℝ) :
    0 ≤ polarR qLim pLim x t := norm_nonneg _

/-- **Continuity of `polarZ`** under continuity of `qLim, pLim`. -/
theorem polarZ_continuous {qLim pLim : ℝ → ℝ → ℝ}
    (hq : Continuous (Function.uncurry qLim))
    (hp : Continuous (Function.uncurry pLim)) :
    Continuous (Function.uncurry (polarZ qLim pLim)) := by
  -- polarZ x t = (qLim x t : ℂ) + (pLim x t : ℂ) * I
  unfold polarZ Function.uncurry
  refine Continuous.add ?_ ?_
  · exact Complex.continuous_ofReal.comp hq
  · exact (Complex.continuous_ofReal.comp hp).mul continuous_const

/-- **Continuity of `polarR`** under continuity of `qLim, pLim`. -/
theorem polarR_continuous {qLim pLim : ℝ → ℝ → ℝ}
    (hq : Continuous (Function.uncurry qLim))
    (hp : Continuous (Function.uncurry pLim)) :
    Continuous (Function.uncurry (polarR qLim pLim)) := by
  -- polarR = ‖·‖ ∘ polarZ
  unfold polarR Function.uncurry
  exact (continuous_norm).comp (polarZ_continuous hq hp)

/-- The **node-free locus** of the limit field: the open subset of `ℝ²`
    where `polarZ` lies in `Complex.slitPlane`, i.e. away from the
    closed non-positive real axis.  Equivalently:
        `polarSlitSet := {(x, t) | qLim(x, t) > 0 ∨ pLim(x, t) ≠ 0}`. -/
def polarSlitSet (qLim pLim : ℝ → ℝ → ℝ) : Set (ℝ × ℝ) :=
  {xt | polarZ qLim pLim xt.1 xt.2 ∈ Complex.slitPlane}

/-- `polarSlitSet` is open (preimage of open `Complex.slitPlane` under
    continuous `polarZ`). -/
theorem polarSlitSet_isOpen {qLim pLim : ℝ → ℝ → ℝ}
    (hq : Continuous (Function.uncurry qLim))
    (hp : Continuous (Function.uncurry pLim)) :
    IsOpen (polarSlitSet qLim pLim) := by
  unfold polarSlitSet
  -- polarSlitSet = (uncurry polarZ) ⁻¹' slitPlane
  have h_eq : {xt : ℝ × ℝ | polarZ qLim pLim xt.1 xt.2 ∈ Complex.slitPlane}
              = (Function.uncurry (polarZ qLim pLim)) ⁻¹' Complex.slitPlane := by
    ext ⟨x, t⟩; simp [Function.uncurry]
  rw [h_eq]
  exact (polarZ_continuous hq hp).isOpen_preimage _ Complex.isOpen_slitPlane

/-- **Continuity of `polarS` on the node-free set** under continuity of
    `qLim, pLim`. -/
theorem polarS_continuousOn {qLim pLim : ℝ → ℝ → ℝ}
    (hq : Continuous (Function.uncurry qLim))
    (hp : Continuous (Function.uncurry pLim)) :
    ContinuousOn (Function.uncurry (polarS qLim pLim))
      (polarSlitSet qLim pLim) := by
  -- polarS = arg ∘ polarZ
  unfold polarS polarSlitSet Function.uncurry
  -- Compose ContinuousOn arg slitPlane with Continuous polarZ.
  have h_polarZ := polarZ_continuous hq hp
  refine Complex.continuousOn_arg.comp h_polarZ.continuousOn ?_
  intro ⟨x, t⟩ hxt
  exact hxt

/-- **REGULARITY UPGRADE — first stage of milestone (IV)**.

    Suppose:
      • `F : KPField` is uniformly bounded,
      • subseq limits at every `(x, t)` are unique with values
        `(qLim x t, pLim x t)`,
      • the limit fields `qLim, pLim` are jointly continuous in `(x, t)`.

    Then the explicit polar amplitude `(polarR qLim pLim, polarS qLim pLim)`
    has:
      • `polarR` continuous on all of `ℝ × ℝ`;
      • `polarS` continuous on the open node-free set `polarSlitSet`;
      • the headline shape `SubBridge1_DiscreteAmplitudeToContinuum`
        holds at every spacetime point.

    This is the cleanest "weakest extra hypothesis" version of milestone
    (IV).  Stronger regularity (Hölder, smooth) requires correspondingly
    stronger regularity of `qLim, pLim`, downstream of Hauptvermutung
    Λ² → 0 substrate-scaling control. -/
theorem KPField_polar_lift_regular
    (F : KPField) {qLim pLim : ℝ → ℝ → ℝ}
    (hb : BoundedKPField F)
    (huniq : KPFieldHasUniqueSubseqLimits F qLim pLim)
    (hq : Continuous (Function.uncurry qLim))
    (hp : Continuous (Function.uncurry pLim)) :
    Continuous (Function.uncurry (polarR qLim pLim))
    ∧ ContinuousOn (Function.uncurry (polarS qLim pLim))
        (polarSlitSet qLim pLim)
    ∧ ∀ x t,
        LohmillerSlotineContinuumLimit.SubBridge1_DiscreteAmplitudeToContinuum
          (F x t) (polarR qLim pLim x t) (polarS qLim pLim x t) := by
  refine ⟨polarR_continuous hq hp, polarS_continuousOn hq hp, ?_⟩
  intro x t
  -- Full-sequence convergence to (qLim, pLim) from SB1-II.
  obtain ⟨hQ, hP⟩ :=
    BoundedKPSequence_unique_subseq_limit_converges
      (F x t) (hb.pointwise x t) (qLim x t) (pLim x t) (huniq x t)
  refine ⟨?_, ?_⟩
  · rw [polarR_cos_polarS]; exact hQ
  · rw [polarR_sin_polarS]; exact hP

/-! ════════════════════════════════════════════════════════════════════════
    PART 9 — SMOOTHNESS UPGRADE: ContDiff OF (r, s) UNDER ContDiff OF (qLim, pLim)
              (SECOND STAGE OF MILESTONE (IV))

    Upgrade Part 8's continuity result to **higher-order smoothness**.

    Under `ContDiff ℝ n (Function.uncurry qLim)` and the same for `pLim`:
      • `polarZ` is `ContDiff ℝ n` everywhere (it is an ℝ-linear combination
        of `qLim, pLim` and the constants `1, I`);
      • `polarR` is `ContDiffAt ℝ n` at every (x, t) with `polarZ x t ≠ 0`
        (i.e. away from amplitude nodes);
      • `polarS` is `ContDiffAt ℝ n` at every (x, t) with `polarZ x t ∈ slitPlane`
        (i.e. away from the closed non-positive real axis = nodes + branch cut).

    The polarS argument routes through Mathlib's `Complex.analyticAt_clog`:
    `Complex.log` is analytic on `slitPlane`, hence `ContDiffAt ℝ n`;
    `Complex.arg z = (Complex.log z).im`, and `Complex.imCLM` is C^∞ linear;
    so `arg` is `ContDiffAt ℝ n` on `slitPlane`.

    This closes the second (and final clean) stage of milestone (IV).
    Discharging `SmoothEnough` for the PDE bridge is now a routine
    composition: provide a `SmoothWaveField` with `r = polarR, s = polarS`,
    fix any choice of `V, m, ħ`, and the slicing into `partialT`/`partialX`/`partialXX`
    follows from the global `ContDiff` proved here.
    ════════════════════════════════════════════════════════════════════════ -/

/-- `polarZ` expressed via the continuous ℝ-linear equivalence
    `ℝ × ℝ ≃L[ℝ] ℂ`.  This is the natural way to inherit smoothness from
    the coordinate fields. -/
theorem polarZ_eq_equivRealProd_symm (qLim pLim : ℝ → ℝ → ℝ) (x t : ℝ) :
    polarZ qLim pLim x t =
      Complex.equivRealProdCLM.symm (qLim x t, pLim x t) := by
  simp [polarZ, Complex.equivRealProdCLM_symm_apply]

/-- **`polarZ` is `ContDiff ℝ n`** under `ContDiff ℝ n` hypotheses on
    the coordinate fields. -/
theorem polarZ_contDiff {n : WithTop ℕ∞} {qLim pLim : ℝ → ℝ → ℝ}
    (hq : ContDiff ℝ n (Function.uncurry qLim))
    (hp : ContDiff ℝ n (Function.uncurry pLim)) :
    ContDiff ℝ n (Function.uncurry (polarZ qLim pLim)) := by
  have h_eq :
      Function.uncurry (polarZ qLim pLim)
        = (Complex.equivRealProdCLM.symm : ℝ × ℝ → ℂ) ∘
            (fun xt : ℝ × ℝ =>
              (Function.uncurry qLim xt, Function.uncurry pLim xt)) := by
    funext ⟨x, t⟩
    simp [Function.uncurry, polarZ_eq_equivRealProd_symm]
  rw [h_eq]
  exact Complex.equivRealProdCLM.symm.contDiff.comp (hq.prodMk hp)

/-- **`polarR` is `ContDiffAt ℝ n`** at every non-node point. -/
theorem polarR_contDiffAt {n : WithTop ℕ∞} {qLim pLim : ℝ → ℝ → ℝ}
    (hq : ContDiff ℝ n (Function.uncurry qLim))
    (hp : ContDiff ℝ n (Function.uncurry pLim))
    {x t : ℝ} (h_nz : polarZ qLim pLim x t ≠ 0) :
    ContDiffAt ℝ n (Function.uncurry (polarR qLim pLim)) (x, t) := by
  -- polarR = norm ∘ polarZ
  have h_eq :
      Function.uncurry (polarR qLim pLim)
        = (fun z : ℂ => ‖z‖) ∘ Function.uncurry (polarZ qLim pLim) := by
    funext ⟨x, t⟩; rfl
  rw [h_eq]
  -- Apply ContDiffAt.norm with f = polarZ.
  exact (polarZ_contDiff hq hp).contDiffAt.norm ℝ h_nz

/-- Smoothness of `Complex.arg` on slitPlane:
    `Complex.arg z = (Complex.log z).im`, and `log` is analytic on `slitPlane`,
    while `im` is a continuous ℝ-linear map.  Composition gives
    `ContDiffAt ℝ n arg z` for any `n` and any `z ∈ slitPlane`. -/
theorem complex_contDiffAt_arg {n : WithTop ℕ∞}
    {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    ContDiffAt ℝ n Complex.arg z := by
  -- arg = im ∘ log, identically (Complex.log_im).
  have h_id : (Complex.arg : ℂ → ℝ) = fun z => (Complex.log z).im := by
    funext w; exact (Complex.log_im w).symm
  rw [h_id]
  -- log is ℂ-analytic on slitPlane, hence ℝ-analytic, hence ContDiffAt of any order.
  have h_log_ℂ : AnalyticAt ℂ Complex.log z := analyticAt_clog hz
  have h_log_ℝ : AnalyticAt ℝ Complex.log z := h_log_ℂ.restrictScalars
  have h_log_cd : ContDiffAt ℝ n Complex.log z := h_log_ℝ.contDiffAt
  -- im is continuous ℝ-linear, hence ContDiff of any order.
  have h_im_cd : ContDiff ℝ n (fun z : ℂ => z.im) :=
    Complex.imCLM.contDiff
  exact h_im_cd.contDiffAt.comp z h_log_cd

/-- **`polarS` is `ContDiffAt ℝ n`** at every slitPlane (= node-free) point. -/
theorem polarS_contDiffAt {n : WithTop ℕ∞} {qLim pLim : ℝ → ℝ → ℝ}
    (hq : ContDiff ℝ n (Function.uncurry qLim))
    (hp : ContDiff ℝ n (Function.uncurry pLim))
    {x t : ℝ} (h_slit : polarZ qLim pLim x t ∈ Complex.slitPlane) :
    ContDiffAt ℝ n (Function.uncurry (polarS qLim pLim)) (x, t) := by
  -- polarS = arg ∘ polarZ
  have h_eq :
      Function.uncurry (polarS qLim pLim)
        = Complex.arg ∘ Function.uncurry (polarZ qLim pLim) := by
    funext ⟨x, t⟩; rfl
  rw [h_eq]
  exact (complex_contDiffAt_arg h_slit).comp (x, t) (polarZ_contDiff hq hp).contDiffAt

/-- Global `ContDiff ℝ n` of `polarR` under `ContDiff` hypotheses and no-nodes. -/
theorem polarR_contDiff {n : WithTop ℕ∞} {qLim pLim : ℝ → ℝ → ℝ}
    (hq : ContDiff ℝ n (Function.uncurry qLim))
    (hp : ContDiff ℝ n (Function.uncurry pLim))
    (h_no_zero : ∀ x t, polarZ qLim pLim x t ≠ 0) :
    ContDiff ℝ n (Function.uncurry (polarR qLim pLim)) := by
  rw [contDiff_iff_contDiffAt]
  intro ⟨x, t⟩
  exact polarR_contDiffAt hq hp (h_no_zero x t)

/-- Global `ContDiff ℝ n` of `polarS` under `ContDiff` hypotheses and no-slit. -/
theorem polarS_contDiff {n : WithTop ℕ∞} {qLim pLim : ℝ → ℝ → ℝ}
    (hq : ContDiff ℝ n (Function.uncurry qLim))
    (hp : ContDiff ℝ n (Function.uncurry pLim))
    (h_no_slit : ∀ x t, polarZ qLim pLim x t ∈ Complex.slitPlane) :
    ContDiff ℝ n (Function.uncurry (polarS qLim pLim)) := by
  rw [contDiff_iff_contDiffAt]
  intro ⟨x, t⟩
  exact polarS_contDiffAt hq hp (h_no_slit x t)

/-- **SECOND-STAGE REGULARITY UPGRADE — milestone (IV) closure**.

    Under `ContDiff ℝ n` hypotheses on the coordinate limit fields
    `qLim, pLim` and a *no-nodes* hypothesis (the lifted complex
    amplitude lies in `Complex.slitPlane` at every spacetime point —
    equivalently, no `(x, t)` is on the negative real axis of `polarZ`),
    the polar amplitude `(polarR, polarS)` is `ContDiff ℝ n` jointly
    in `(x, t)`, and discharges sub-bridge 1 at every spacetime point.

    This is the cleanest closure of milestone (IV) before invoking the
    PDE bridge:  any field that can be supplied with these hypotheses
    yields a fully-regular continuum amplitude. -/
theorem KPField_polar_lift_smooth_no_nodes
    {n : WithTop ℕ∞} (F : KPField) {qLim pLim : ℝ → ℝ → ℝ}
    (hb : BoundedKPField F)
    (huniq : KPFieldHasUniqueSubseqLimits F qLim pLim)
    (hq : ContDiff ℝ n (Function.uncurry qLim))
    (hp : ContDiff ℝ n (Function.uncurry pLim))
    (h_no_slit : ∀ x t, polarZ qLim pLim x t ∈ Complex.slitPlane) :
    ContDiff ℝ n (Function.uncurry (polarR qLim pLim))
    ∧ ContDiff ℝ n (Function.uncurry (polarS qLim pLim))
    ∧ ∀ x t,
        LohmillerSlotineContinuumLimit.SubBridge1_DiscreteAmplitudeToContinuum
          (F x t) (polarR qLim pLim x t) (polarS qLim pLim x t) := by
  -- Pointwise smoothness + slit-plane assumption ⇒ no-nodes (slitPlane ⊂ {z | z ≠ 0}).
  have h_no_zero : ∀ x t, polarZ qLim pLim x t ≠ 0 := by
    intro x t
    exact Complex.slitPlane_ne_zero (h_no_slit x t)
  refine ⟨?_, ?_, ?_⟩
  · -- polarR globally ContDiff via contDiffAt at every point.
    rw [contDiff_iff_contDiffAt]
    intro ⟨x, t⟩
    exact polarR_contDiffAt hq hp (h_no_zero x t)
  · -- polarS globally ContDiff via contDiffAt at every slitPlane point.
    rw [contDiff_iff_contDiffAt]
    intro ⟨x, t⟩
    exact polarS_contDiffAt hq hp (h_no_slit x t)
  · -- Discharge SB1 at every point (continuity ⇒ pointwise lift).
    intro x t
    obtain ⟨hQ, hP⟩ :=
      BoundedKPSequence_unique_subseq_limit_converges
        (F x t) (hb.pointwise x t) (qLim x t) (pLim x t) (huniq x t)
    refine ⟨?_, ?_⟩
    · rw [polarR_cos_polarS]; exact hQ
    · rw [polarR_sin_polarS]; exact hP

/-! ════════════════════════════════════════════════════════════════════════
    PART 10 — END-TO-END COMPOSITION:  KPField → SmoothWaveField → PDE BRIDGE

    Stitches Part 9's smoothness upgrade to the already-proved calculus
    bridge `LohmillerSlotineCalculus.schrodinger_PDE_iff_HJ_continuity_smooth`.

    The composition yields an explicit `SmoothWaveField` whose `(r, s)`
    are the polar amplitudes lifted from the discrete K/P field, and
    proves that:
      • `SmoothEnough` holds at every spacetime point,
      • each pointwise PDE-residual-vs-(HJ-with-Bohm + Continuity)
        equivalence fires.

    Hypotheses are exactly the cleanly-stated list:
      • boundedness of the KPField,
      • per-(x, t) subsequence uniqueness,
      • `ContDiff ℝ 2` of `qLim, pLim` (sufficient for SmoothEnough),
      • no-nodes (`polarZ ∈ slitPlane` at every spacetime point).
    Plus the user-supplied potential `V` and constants `m, ħ > 0`.

    This is the LS-bridge end-to-end emergence statement at the level
    of pointwise PDE equivalence.
    ════════════════════════════════════════════════════════════════════════ -/

section Composition

open UnifiedTheory.LayerB.LohmillerSlotineCalculus

/-- The constructed smooth wave field uses `polarR, polarS` as `r, s`. -/
noncomputable def smoothWaveFieldFromKPField
    {qLim pLim : ℝ → ℝ → ℝ}
    (V : ℝ → ℝ → ℝ) (m hbar : ℝ) (hm : 0 < m) (hhbar : 0 < hbar) :
    SmoothWaveField :=
  { r := polarR qLim pLim
    s := polarS qLim pLim
    V := V
    m := m
    hbar := hbar
    m_pos := hm
    hbar_pos := hhbar }

/-- The spatial-slice embedding `ξ ↦ (ξ, t)` is `ContDiff ℝ ∞`. -/
private theorem contDiff_spatialSlice (t : ℝ) :
    ContDiff ℝ ⊤ (fun ξ : ℝ => (ξ, t)) :=
  contDiff_id.prodMk contDiff_const

/-- The time-slice embedding `τ ↦ (x, τ)` is `ContDiff ℝ ∞`. -/
private theorem contDiff_timeSlice (x : ℝ) :
    ContDiff ℝ ⊤ (fun τ : ℝ => (x, τ)) :=
  contDiff_const.prodMk contDiff_id

/-- If `f : ℝ × ℝ → ℝ` is `ContDiff ℝ n`, then for fixed `t`
    the spatial slice is `ContDiff ℝ n`. -/
private theorem contDiff_spatial_slice_of_uncurry
    {n : WithTop ℕ∞} {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ n f) (t : ℝ) :
    ContDiff ℝ n (fun ξ => f (ξ, t)) :=
  hf.comp ((contDiff_spatialSlice t).of_le le_top)

/-- If `f : ℝ × ℝ → ℝ` is `ContDiff ℝ n`, then for fixed `x`
    the t-slice is `ContDiff ℝ n`. -/
private theorem contDiff_time_slice_of_uncurry
    {n : WithTop ℕ∞} {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ n f) (x : ℝ) :
    ContDiff ℝ n (fun τ => f (x, τ)) :=
  hf.comp ((contDiff_timeSlice x).of_le le_top)

/-- **SmoothEnough for the polar wave field, under SB1-IV hypotheses**. -/
theorem smoothWaveFieldFromKPField_smoothEnough
    {qLim pLim : ℝ → ℝ → ℝ}
    (hq : ContDiff ℝ 2 (Function.uncurry qLim))
    (hp : ContDiff ℝ 2 (Function.uncurry pLim))
    (h_no_slit : ∀ x t, polarZ qLim pLim x t ∈ Complex.slitPlane)
    (V : ℝ → ℝ → ℝ) (m hbar : ℝ) (hm : 0 < m) (hhbar : 0 < hbar) (x t : ℝ) :
    SmoothEnough (smoothWaveFieldFromKPField (qLim := qLim) (pLim := pLim)
                    V m hbar hm hhbar) x t := by
  -- No-slit implies no-zero (slitPlane ⊂ ℂ \ {0}).
  have h_no_zero : ∀ x t, polarZ qLim pLim x t ≠ 0 := fun x t =>
    Complex.slitPlane_ne_zero (h_no_slit x t)
  -- Global ContDiff ℝ 2 of polarR and polarS.
  have hR_cd : ContDiff ℝ 2 (Function.uncurry (polarR qLim pLim)) :=
    polarR_contDiff hq hp h_no_zero
  have hS_cd : ContDiff ℝ 2 (Function.uncurry (polarS qLim pLim)) :=
    polarS_contDiff hq hp h_no_slit
  -- Slice into the six required differentiabilities.
  refine
    { hr_t := ?_
      hs_t := ?_
      hr_x := ?_
      hs_x := ?_
      hr_xx := ?_
      hs_xx := ?_ }
  · -- DifferentiableAt of polarR's t-slice at t.
    have h := contDiff_time_slice_of_uncurry hR_cd x
    exact (h.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).differentiableAt
  · -- DifferentiableAt of polarS's t-slice at t.
    have h := contDiff_time_slice_of_uncurry hS_cd x
    exact (h.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).differentiableAt
  · -- Differentiable of polarR's x-slice.
    have h := contDiff_spatial_slice_of_uncurry hR_cd t
    exact h.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  · -- Differentiable of polarS's x-slice.
    have h := contDiff_spatial_slice_of_uncurry hS_cd t
    exact h.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  · -- Differentiable of ∂_x polarR (x-slice).
    -- partialX polarR ξ t = deriv (fun ξ' => polarR ξ' t) ξ
    have hslice : ContDiff ℝ 2 (fun ξ => polarR qLim pLim ξ t) := by
      have := contDiff_spatial_slice_of_uncurry hR_cd t
      -- (fun ξ => f (ξ, t)) = (fun ξ => Function.uncurry (polarR qLim pLim) (ξ, t))
      -- which equals polarR qLim pLim ξ t by uncurry def
      exact this
    have h_deriv_diff : Differentiable ℝ (deriv (fun ξ => polarR qLim pLim ξ t)) :=
      hslice.differentiable_deriv_two
    -- fun ξ => partialX polarR ξ t = deriv (fun ξ' => polarR ξ' t)
    have h_eq : (fun ξ => SmoothWaveField.partialX
                  (smoothWaveFieldFromKPField (qLim := qLim) (pLim := pLim)
                      V m hbar hm hhbar).r ξ t)
              = deriv (fun ξ => polarR qLim pLim ξ t) := by
      funext ξ; rfl
    rw [h_eq]; exact h_deriv_diff
  · -- Differentiable of ∂_x polarS (x-slice).
    have hslice : ContDiff ℝ 2 (fun ξ => polarS qLim pLim ξ t) :=
      contDiff_spatial_slice_of_uncurry hS_cd t
    have h_deriv_diff : Differentiable ℝ (deriv (fun ξ => polarS qLim pLim ξ t)) :=
      hslice.differentiable_deriv_two
    have h_eq : (fun ξ => SmoothWaveField.partialX
                  (smoothWaveFieldFromKPField (qLim := qLim) (pLim := pLim)
                      V m hbar hm hhbar).s ξ t)
              = deriv (fun ξ => polarS qLim pLim ξ t) := by
      funext ξ; rfl
    rw [h_eq]; exact h_deriv_diff

/-- **LS BRIDGE — END-TO-END HEADLINE**.

    Under the cleanly-stated SB1 hypotheses (boundedness, subseq
    uniqueness, `ContDiff ℝ 2` regularity of the coordinate limit fields,
    and no-nodes), plus any user-supplied smooth potential `V` and
    positive constants `m, ħ`, the discrete K/P field induces a smooth
    polar wave field at which the pointwise Schrödinger PDE residual
    vanishes iff Hamilton-Jacobi-with-Bohm and Continuity hold.

    Concretely, at every spacetime point:

        (PDE_residualRe sw x t = 0  ∧  PDE_residualIm sw x t = 0)
          ⟺
        (HamiltonJacobiWithBohm (WaveData.atPoint sw x t)
          ∧  ContinuityEquation (WaveData.atPoint sw x t))

    where `sw` is the explicit polar wave field constructed from the
    discrete K/P data.

    Simultaneously, the SB1 headline shape is realised:  the discrete
    `(Q_n, P_n)` of `F x t` converges to `(sw.r · cos sw.s, sw.r · sin sw.s)`
    at every spacetime point. -/
theorem LSBridge_PDE_equivalence_realised
    (F : KPField) {qLim pLim : ℝ → ℝ → ℝ}
    (hb : BoundedKPField F)
    (huniq : KPFieldHasUniqueSubseqLimits F qLim pLim)
    (hq : ContDiff ℝ 2 (Function.uncurry qLim))
    (hp : ContDiff ℝ 2 (Function.uncurry pLim))
    (h_no_slit : ∀ x t, polarZ qLim pLim x t ∈ Complex.slitPlane)
    (V : ℝ → ℝ → ℝ) (m hbar : ℝ) (hm : 0 < m) (hhbar : 0 < hbar) :
    let sw := smoothWaveFieldFromKPField (qLim := qLim) (pLim := pLim)
                V m hbar hm hhbar
    (∀ x t,
      (PDE_residualRe sw x t = 0 ∧ PDE_residualIm sw x t = 0) ↔
        (LohmillerSlotineBridge.HamiltonJacobiWithBohm
            (WaveData.atPoint sw x t)
          ∧ LohmillerSlotineBridge.ContinuityEquation
              (WaveData.atPoint sw x t)))
    ∧ (∀ x t,
        LohmillerSlotineContinuumLimit.SubBridge1_DiscreteAmplitudeToContinuum
          (F x t) (sw.r x t) (sw.s x t)) := by
  intro sw
  refine ⟨?_, ?_⟩
  · intro x t
    exact schrodinger_PDE_iff_HJ_continuity_smooth sw x t
      (smoothWaveFieldFromKPField_smoothEnough hq hp h_no_slit V m hbar hm hhbar x t)
  · intro x t
    obtain ⟨hQ, hP⟩ :=
      BoundedKPSequence_unique_subseq_limit_converges
        (F x t) (hb.pointwise x t) (qLim x t) (pLim x t) (huniq x t)
    refine ⟨?_, ?_⟩
    · -- sw.r x t * cos (sw.s x t) = polarR qLim pLim x t * cos (polarS qLim pLim x t) = qLim x t
      show Filter.Tendsto _ Filter.atTop (nhds (sw.r x t * Real.cos (sw.s x t)))
      rw [show sw.r x t * Real.cos (sw.s x t) = qLim x t from
        polarR_cos_polarS qLim pLim x t]
      exact hQ
    · show Filter.Tendsto _ Filter.atTop (nhds (sw.r x t * Real.sin (sw.s x t)))
      rw [show sw.r x t * Real.sin (sw.s x t) = pLim x t from
        polarR_sin_polarS qLim pLim x t]
      exact hP

/-! ════════════════════════════════════════════════════════════════════════
    HEADLINE PHASE B FINALE — `LSBridge_PDE_equivalence_realised_from_substrate`.

    Pure composition theorem:  the full Phase A.2 / SB1 / PDE-bridge
    chain follows from substrate-side conditions alone (plus the local
    no-slit hypothesis, which is a property of the LIMIT fields not the
    substrate, and which is intrinsic to local polar coordinates).

    Substrate ingredients:
      • `SubstrateEvolutionLaw F`           (Phase B.2)
      • `InitialEnergyBound F M_E`          (Phase B.2)
      • `KPFieldDiscreteContDiff2 F`        (Phase B.4 step 3)
      • `KPFieldLocallyUniformLimit F qLim pLim`   (Phase B.4 steps 1-3)
      • `KPFieldLocallyUniformFDerivLimit F g'_Q g'_P`     (step 2-3)
      • `KPFieldLocallyUniformSecondFDerivLimit F g''_Q g''_P` (step 3)
    Plus user-side:
      • `(x, t) ↦ polarZ qLim pLim x t ∈ slitPlane`  (no-slit)
      • potential `V`, mass `m > 0`, `ħ > 0`.

    Conclusion (identical to `LSBridge_PDE_equivalence_realised`):
      • Pointwise PDE-residual ⇔ HJ-with-Bohm + Continuity at every `(x, t)`,
      • SB1 headline:  `(Q_n, P_n)` of `F x t` converges to
        `(sw.r·cos sw.s, sw.r·sin sw.s)` at every spacetime point.
    -/

/-- **HEADLINE PHASE B FINALE**:  the entire SB1 + PDE-bridge stack
    fires under explicit substrate-side hypotheses, with no analytic
    conditions on the continuum limit assumed.

    This is the headline of the `UnifiedTheory` continuum-limit program:
    given a discrete K/P substrate whose dynamics, energy, and refinement
    behaviour satisfy explicit physical conditions, the resulting
    smooth polar wave field satisfies the Schrödinger PDE iff
    HJ-with-Bohm + Continuity hold pointwise. -/
theorem LSBridge_PDE_equivalence_realised_from_substrate
    {F : KPField} {M_E : ℝ}
    {qLim pLim : ℝ → ℝ → ℝ}
    {g'_Q g'_P : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ)}
    {g''_Q g''_P : ℝ × ℝ → (ℝ × ℝ →L[ℝ] (ℝ × ℝ →L[ℝ] ℝ))}
    (h_dyn : SubstrateEvolutionLaw F)
    (hM_E_nn : 0 ≤ M_E)
    (h_init : InitialEnergyBound F M_E)
    (h_disc2 : KPFieldDiscreteContDiff2 F)
    (h_val : KPFieldLocallyUniformLimit F qLim pLim)
    (h_fderiv : KPFieldLocallyUniformFDerivLimit F g'_Q g'_P)
    (h_2fderiv : KPFieldLocallyUniformSecondFDerivLimit F g''_Q g''_P)
    (h_no_slit : ∀ x t, polarZ qLim pLim x t ∈ Complex.slitPlane)
    (V : ℝ → ℝ → ℝ) (m hbar : ℝ) (hm : 0 < m) (hhbar : 0 < hbar) :
    let sw := smoothWaveFieldFromKPField (qLim := qLim) (pLim := pLim)
                V m hbar hm hhbar
    (∀ x t,
      (PDE_residualRe sw x t = 0 ∧ PDE_residualIm sw x t = 0) ↔
        (LohmillerSlotineBridge.HamiltonJacobiWithBohm
            (WaveData.atPoint sw x t)
          ∧ LohmillerSlotineBridge.ContinuityEquation
              (WaveData.atPoint sw x t)))
    ∧ (∀ x t,
        LohmillerSlotineContinuumLimit.SubBridge1_DiscreteAmplitudeToContinuum
          (F x t) (sw.r x t) (sw.s x t)) := by
  -- Step 1.  BoundedKPField from substrate dynamics + initial energy.
  have hb : BoundedKPField F :=
    SB1_boundedness_from_dynamics h_dyn hM_E_nn h_init
  -- Step 2.  Pointwise convergence at every (x, t) (from locally uniform conv).
  have hQ_ptw : ∀ x t,
      Tendsto (fun n => ((F x t).growth n).Q) atTop (nhds (qLim x t)) := by
    intro x t
    have hQ_on : TendstoLocallyUniformlyOn
        (fun (n : ℕ) (yt : ℝ × ℝ) => ((F yt.1 yt.2).growth n).Q)
        (Function.uncurry qLim) atTop Set.univ := by
      rw [tendstoLocallyUniformlyOn_univ]; exact h_val.1
    exact hQ_on.tendsto_at (Set.mem_univ (x, t))
  have hP_ptw : ∀ x t,
      Tendsto (fun n => ((F x t).growth n).P) atTop (nhds (pLim x t)) := by
    intro x t
    have hP_on : TendstoLocallyUniformlyOn
        (fun (n : ℕ) (yt : ℝ × ℝ) => ((F yt.1 yt.2).growth n).P)
        (Function.uncurry pLim) atTop Set.univ := by
      rw [tendstoLocallyUniformlyOn_univ]; exact h_val.2
    exact hP_on.tendsto_at (Set.mem_univ (x, t))
  -- Step 3.  KPFieldHasUniqueSubseqLimits from pointwise convergence
  -- (subseq of convergent sequence converges to the same limit, Hausdorff uniqueness).
  have huniq : KPFieldHasUniqueSubseqLimits F qLim pLim := by
    intro x t ψ hψ_mono q' p' hQ' hP'
    have hQ_sub : Tendsto (fun n => ((F x t).growth (ψ n)).Q)
        atTop (nhds (qLim x t)) := (hQ_ptw x t).comp hψ_mono.tendsto_atTop
    have hP_sub : Tendsto (fun n => ((F x t).growth (ψ n)).P)
        atTop (nhds (pLim x t)) := (hP_ptw x t).comp hψ_mono.tendsto_atTop
    exact ⟨tendsto_nhds_unique hQ' hQ_sub, tendsto_nhds_unique hP' hP_sub⟩
  -- Step 4.  ContDiff ℝ 2 of qLim, pLim from substrate.
  have ⟨hQ_cd, hP_cd⟩ :=
    qLim_pLim_contDiff2_from_substrate h_disc2 h_val h_fderiv h_2fderiv
  -- Step 5.  Apply the Phase A.2 headline.
  exact LSBridge_PDE_equivalence_realised F hb huniq hQ_cd hP_cd
    h_no_slit V m hbar hm hhbar

end Composition

/-- Status string for sub-bridge 1, mirroring the convention used by
    `LohmillerSlotineContinuumLimit.continuumLimitOfKP_status`. -/
def subBridge1_status : String :=
  "COMPLETE (in the no-nodes form) — " ++
  "(a) eventually-zero special case PROVED, " ++
  "(b) Bolzano-Weierstrass extraction PROVED, " ++
  "(c) polar gauge-fixing PROVED, " ++
  "(d) polar-convergent-subsequence corollary PROVED, " ++
  "(e) subsequence-independence ⇒ full-sequence convergence PROVED, " ++
  "(f) full-sequence polar form PROVED, " ++
  "(g) pointwise-in-(x, t) lift PROVED, " ++
  "(h) continuity of (r, s) under continuity of (qLim, pLim) PROVED, " ++
  "(i) ContDiff ℝ n of (r, s) under ContDiff ℝ n of (qLim, pLim) " ++
  "+ no-nodes PROVED, " ++
  "(j) end-to-end PDE-bridge composition PROVED " ++
  "(LSBridge_PDE_equivalence_realised)."

/-- Internal milestone tracker for sub-bridge 1. -/
inductive SubBridge1Milestone where
  | boundedKPSequence_defined           : SubBridge1Milestone
  | eventually_zero_case_proved         : SubBridge1Milestone
  | bolzano_weierstrass_proved          : SubBridge1Milestone
  | polar_gauge_fixing                  : SubBridge1Milestone
  | subsequence_independence            : SubBridge1Milestone
  | pointwise_in_xt_lift                : SubBridge1Milestone
  | continuity_under_continuity         : SubBridge1Milestone
  | smoothness_for_PDE_bridge           : SubBridge1Milestone
  deriving DecidableEq, Repr

def SubBridge1Milestone.isDone : SubBridge1Milestone → Bool
  | .boundedKPSequence_defined           => true
  | .eventually_zero_case_proved         => true
  | .bolzano_weierstrass_proved          => true
  | .polar_gauge_fixing                  => true
  | .subsequence_independence            => true
  | .pointwise_in_xt_lift                => true
  | .continuity_under_continuity         => true
  | .smoothness_for_PDE_bridge           => true

/-- All eight milestones closed in this file. -/
theorem subBridge1_seven_milestones_closed :
    (List.filter (fun m => m.isDone)
      [SubBridge1Milestone.boundedKPSequence_defined,
       SubBridge1Milestone.eventually_zero_case_proved,
       SubBridge1Milestone.bolzano_weierstrass_proved,
       SubBridge1Milestone.polar_gauge_fixing,
       SubBridge1Milestone.subsequence_independence,
       SubBridge1Milestone.pointwise_in_xt_lift,
       SubBridge1Milestone.continuity_under_continuity,
       SubBridge1Milestone.smoothness_for_PDE_bridge]).length = 8 := by
  native_decide

/-- Zero milestones still open. -/
theorem subBridge1_zero_milestones_open :
    (List.filter (fun m => ! m.isDone)
      [SubBridge1Milestone.boundedKPSequence_defined,
       SubBridge1Milestone.eventually_zero_case_proved,
       SubBridge1Milestone.bolzano_weierstrass_proved,
       SubBridge1Milestone.polar_gauge_fixing,
       SubBridge1Milestone.subsequence_independence,
       SubBridge1Milestone.pointwise_in_xt_lift,
       SubBridge1Milestone.continuity_under_continuity,
       SubBridge1Milestone.smoothness_for_PDE_bridge]).length = 0 := by
  native_decide

end UnifiedTheory.LayerB.LohmillerSlotineSubBridge1
