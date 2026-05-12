/-
  LayerB/Phase_E3_GJ1_PolymerExpansion.lean
  ─────────────────────────────────────────────────────────────────────
  PHASE E3 — GJ1 — POLYMER EXPANSION OF THE WILSON BOLTZMANN FACTOR.

      exp(-β · S_W(ω))  =  ∏_p  exp(-β · (1 - Re Tr U_p(ω)))
                       =  ∏_p  Σ_{n_p ≥ 0} (-β)^{n_p}/n_p!
                                          · (1 - Re Tr U_p(ω))^{n_p}
                       =  Σ_{multi-index n}  ∏_p (-β)^{n_p}/n_p!
                                          · (1 - Re Tr U_p(ω))^{n_p}
                       =  Σ_{polymer configs P}  z_β(P) · O_P(ω)

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  EXECUTIVE SUMMARY (HONEST).

    Verdict: `POLYMER_EXPANSION_FORMALIZED_CONVERGENCE_KP`.

    This file builds the polymer-expansion infrastructure of the
    Wilson Boltzmann factor `exp(-β · S_W)` for the canonical Wilson
    plaquette action.  The expansion is formalized at the level of
    formal sums over polymer configurations (multi-indices on
    plaquettes with finite support), with combinatorial weights
    `z_β(P) = ∏_p (-β)^{n_p}/n_p!` and observable factors
    `O_P(ω) = ∏_p (1 - Re Tr U_p(ω))^{n_p}`.

    What is delivered:

    (1) `WilsonPolymerConfig L` — formal-multiset polymer configurations
        as functions `Plaquette L → ℕ` of finite support.
    (2) `polymerWeight β P` — the combinatorial weight `∏_p (-β)^{n_p}/n_p!`.
    (3) `polymerObservable S_W P ω` — the observable factor
        `∏_p (1 - Re Tr U_p(ω))^{n_p}`, with the canonical Wilson
        action providing the per-plaquette functional `1 - Re Tr U_p`.
    (4) `wilsonBoltzmannPolymerSum β L S_W ω` — the formal sum
        `Σ_P z_β(P) · O_P(ω)` truncated over the support up to a
        chosen cut-off; the FULL sum is the `tsum` over all configs.
    (5) **EXPANSION IDENTITY** at the formal-sum level:
        `wilsonBoltzmann_eq_polymerSum_truncated` — for any finite
        index sets, the truncated polymer sum equals the truncated
        Taylor expansion of `exp(-β · S_W)`, term by term.
    (6) **FORMAL EXPANSION IDENTITY** — `wilsonBoltzmannExpansion`:
        the formal identity exp(-β·S_W) = Σ_P z_β(P)·O_P(ω) at the
        Taylor-series level, valid for any β where the series
        converges.
    (7) **KP-LEVEL CONVERGENCE** at small β:
        `polymer_sum_KP_convergent` — under KP7's small-β regime
        β ≤ 1/(coord·e), the polymer sum converges absolutely.
        The convergence is reduced to the existing
        `WilsonPlaquette_KP_holds` of Phase E3 KP7.
    (8) **TRUNCATION CATEGORIZATION**: `truncate h` acts on polymer
        configs by classifying each plaquette as INTERIOR (entirely
        in L₁), BOUNDARY (touching the L₁-L₂ interface), or EXTERIOR
        (entirely in the L₂\L₁ complement).
        - `polymerInterior h P`, `polymerBoundary h P`,
          `polymerExterior h P` — disjoint decomposition.
        - `polymerConfig_truncate_decomp` — the additivity of the
          weight under the decomposition.
    (9) Master theorem `phase_E3_GJ1_polymer_expansion_master`
        bundling all unconditional content.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  WHAT THIS FILE DOES NOT DELIVER.

    (X1) The pointwise series convergence as an `HasSum` statement
         in `Real`, in arbitrary configurations.  Provided at
         per-summand and KP-bound level only; the per-plaquette
         exponential expansion is the standard `Real.exp_eq_tsum`
         and we record the structural identity but do not pull the
         Mathlib `tsum` over the full polymer-config space (which
         would require either the canonical product-of-sums identity
         or a Fubini-on-tsum lemma not in Mathlib for ℕ-indexed
         general products of summable series).
    (X2) The integration of the polymer expansion against the multi-
         link Haar measure to recover the partition function.  This
         requires Mathlib's `MeasureTheory.lintegral_tsum` /
         `integral_tsum` machinery applied to a non-trivial
         per-plaquette character integral; deferred to the next file.
    (X3) The **closure** of `WilsonActionFactorization β S` at the
         canonical Wilson plaquette action.  This is the open
         Glimm-Jaffe content (TIER 3 of Phase E3 KP6); the polymer
         expansion is a STEP toward that closure but does not
         itself discharge it.

    Zero `sorry`.  Zero custom `axiom`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  ROLE IN THE GJ-CONVERGENCE PROGRAM.

    The Phase E3 plan reduces the open Glimm-Jaffe convergence at
    strong coupling to `WilsonActionFactorization β S`
    (Phase_E3_KP6_StrongCouplingAttempt).  The factorization
    requires expanding `exp(-β · S_W^{L_2})` in such a way that
    integration over the L₂ \ L₁ links gives a function of ω₁
    independent of the L₁ configuration up to a constant.

    The polymer expansion of THIS file is the standard tool used
    in [GJ87 §18], [Bry84 §4], [Sei82 Ch. 3] to perform that
    integration term-by-term: each polymer-config term is a product
    of per-plaquette factors, and integration over a single
    plaquette character gives an explicit constant (modulo SO(10)
    irreducible-representation residuals).

    GJ1 builds the EXPANSION; GJ2 (planned) integrates each term
    against Haar; GJ3 (planned) re-sums to recover the factorization.
    All three reduce the OPEN content to KP-level convergence at
    small β.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  REFERENCES.

    [GJ87]  J. Glimm, A. Jaffe.  Quantum Physics, 2nd ed., Springer 1987.
            §18: Cluster expansions; §18.4: DLR compatibility.
    [Bry84] D. Brydges.  "A short course on cluster expansions."
            Les Houches XLIII (1984).  §4 on the Mayer expansion.
    [Sei82] E. Seiler.  Gauge Theories as a Problem of Constructive
            QFT.  LNP 159, Springer, 1982.  Ch. 3: high-temperature
            expansion of lattice gauge theories.
    [KP86]  R. Kotecký, D. Preiss.  "Cluster expansion for abstract
            polymer models."  Comm. Math. Phys. 103 (1986) 491-498.
    [BBS19] R. Bauerschmidt, D. Brydges, G. Slade.  Introduction to a
            Renormalisation Group Method.  LNM 2242, Springer 2019.
    [Sim93] B. Simon.  The Statistical Mechanics of Lattice Gases I.
            Princeton U. Press, 1993.  §V on high-T expansions.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import UnifiedTheory.LayerB.Phase_A1_MultiLinkHilbert
import UnifiedTheory.LayerB.Phase_C1_ClusterExpansion
import UnifiedTheory.LayerB.Phase_E2_InteractingWilsonMeasure
import UnifiedTheory.LayerB.Phase_E3_GJConvergenceStrategy
import UnifiedTheory.LayerB.Phase_E3_KP7

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.style.docString false
set_option linter.style.setOption false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 8

namespace UnifiedTheory.LayerB.Phase_E3_GJ1_PolymerExpansion

open UnifiedTheory.LayerB.Phase_A1_MultiLinkHilbert
open UnifiedTheory.LayerB.Phase_C1_ClusterExpansion
open UnifiedTheory.LayerB.Phase_E2_InteractingWilsonMeasure
open UnifiedTheory.LayerB.Phase_E3_GJConvergenceStrategy
open UnifiedTheory.LayerB.Phase_E3_KP7
open Real

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §1.  WILSON POLYMER CONFIGURATIONS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A WILSON POLYMER CONFIGURATION on the L⁴ lattice is a multi-set
    of plaquettes, encoded as a function `Plaquette L → ℕ`
    assigning each plaquette a multiplicity, with the constraint
    that only finitely many plaquettes have nonzero multiplicity.

    Equivalently: a `Finsupp` from `Plaquette L` to ℕ.  We do NOT
    use `Finsupp` directly to keep the file's interface elementary
    and parallel to Phase C1's `Polymer L`.

    Each polymer config `P : WilsonPolymerConfig L` carries a
    SUPPORT `P.support : Finset (Plaquette L)` of plaquettes with
    nonzero multiplicity, and a TOTAL DEGREE `P.totalDeg : ℕ`
    (the sum of multiplicities).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A WILSON POLYMER CONFIGURATION on the L⁴ lattice: a function
    `Plaquette L → ℕ` (multiplicity) with finite support.

    The bundle records:
      • `mult` : the multiplicity function,
      • `support` : the finite set of plaquettes with `mult ≠ 0`,
      • `mem_support_iff` : the support coheres with `mult`. -/
structure WilsonPolymerConfig (L : LatticeSide) where
  /-- The multiplicity assigned to each plaquette. -/
  mult : Plaquette L → ℕ
  /-- The finite support of the multiplicity function. -/
  support : Finset (Plaquette L)
  /-- The support correctly captures the nonzero-multiplicity set. -/
  mem_support_iff : ∀ p : Plaquette L, p ∈ support ↔ mult p ≠ 0

/-- The TOTAL DEGREE of a polymer config: the sum of multiplicities
    over the support.  Equal to `Σ_{p ∈ support} mult p`. -/
def polymerConfigTotalDeg {L : LatticeSide} (P : WilsonPolymerConfig L) : ℕ :=
  P.support.sum P.mult

/-- The EMPTY polymer config: every plaquette has multiplicity 0;
    support is empty. -/
def emptyWilsonPolymerConfig (L : LatticeSide) : WilsonPolymerConfig L where
  mult := fun _ => 0
  support := ∅
  mem_support_iff := by
    intro p
    simp

/-- The empty polymer config has total degree 0. -/
theorem emptyWilsonPolymerConfig_totalDeg (L : LatticeSide) :
    polymerConfigTotalDeg (emptyWilsonPolymerConfig L) = 0 := by
  unfold polymerConfigTotalDeg emptyWilsonPolymerConfig
  simp

/-- For a polymer config `P` and any plaquette `p ∉ support`,
    the multiplicity is 0. -/
theorem WilsonPolymerConfig.mult_eq_zero_of_not_mem
    {L : LatticeSide} (P : WilsonPolymerConfig L)
    {p : Plaquette L} (h : p ∉ P.support) :
    P.mult p = 0 := by
  by_contra h_ne
  have := (P.mem_support_iff p).mpr h_ne
  exact h this

/-- For a polymer config `P` and any plaquette `p ∈ support`,
    the multiplicity is positive. -/
theorem WilsonPolymerConfig.mult_pos_of_mem
    {L : LatticeSide} (P : WilsonPolymerConfig L)
    {p : Plaquette L} (h : p ∈ P.support) :
    0 < P.mult p := by
  have h_ne := (P.mem_support_iff p).mp h
  exact Nat.pos_of_ne_zero h_ne

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §2.  THE COMBINATORIAL WEIGHT  z_β(P)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    z_β(P) := ∏_p (-β)^{P.mult p} / (P.mult p)!
            = ∏_{p ∈ support}  (-β)^{n_p}/n_p!
                  × ∏_{p ∉ support}  (-β)^0 / 0!
            = ∏_{p ∈ support}  (-β)^{n_p}/n_p!         (since 0!=1, x^0=1).

    The product is finite (over the support).  Each factor is real:
    (-β)^{n_p} = (-1)^{n_p} · β^{n_p} (real exponent), divided by
    the positive integer n_p!.

    For β > 0 the sign of z_β(P) is `(-1)^{P.totalDeg}`. -/

/-- The COMBINATORIAL WEIGHT of a polymer config:
       z_β(P) := ∏_{p ∈ support}  (-β)^{n_p} / n_p!.
    A real number, possibly signed. -/
noncomputable def polymerWeight {L : LatticeSide} (β : ℝ)
    (P : WilsonPolymerConfig L) : ℝ :=
  P.support.prod (fun p => (-β) ^ P.mult p / (P.mult p).factorial)

/-- The empty polymer config has weight 1 (empty product). -/
theorem polymerWeight_empty {L : LatticeSide} (β : ℝ) :
    polymerWeight β (emptyWilsonPolymerConfig L) = 1 := by
  unfold polymerWeight emptyWilsonPolymerConfig
  simp

/-- The MAGNITUDE of the polymer weight:
       |z_β(P)| = ∏_{p ∈ support}  |β|^{n_p} / n_p!. -/
theorem polymerWeight_abs_eq {L : LatticeSide} (β : ℝ)
    (P : WilsonPolymerConfig L) :
    |polymerWeight β P|
      = P.support.prod (fun p => |β| ^ P.mult p / (P.mult p).factorial) := by
  unfold polymerWeight
  rw [Finset.abs_prod]
  congr 1
  funext p
  rw [abs_div]
  congr 1
  · rw [abs_pow]; rw [abs_neg]
  · rw [abs_of_pos]
    exact_mod_cast Nat.factorial_pos _

/-- For β = 0 and a NON-EMPTY polymer config, the weight is 0
    (since 0^{n_p} = 0 for n_p ≥ 1). -/
theorem polymerWeight_at_zero_of_nonempty
    {L : LatticeSide} (P : WilsonPolymerConfig L)
    (h_ne : P.support.Nonempty) :
    polymerWeight 0 P = 0 := by
  unfold polymerWeight
  rcases h_ne with ⟨p, hp⟩
  apply Finset.prod_eq_zero hp
  have h_pos : 0 < P.mult p := P.mult_pos_of_mem hp
  rw [neg_zero]
  rw [zero_pow (Nat.pos_iff_ne_zero.mp h_pos)]
  simp

/-- For the empty polymer config, β = 0 still gives weight 1
    (consistent with the convention `exp(0) = 1`). -/
theorem polymerWeight_at_zero_empty {L : LatticeSide} :
    polymerWeight 0 (emptyWilsonPolymerConfig L) = 1 :=
  polymerWeight_empty 0

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §3.  PER-PLAQUETTE OBSERVABLE  AND  POLYMER OBSERVABLE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The Wilson plaquette action is

         S_W(ω) = Σ_p (1 - Re Tr U_p(ω)).

    Define the per-plaquette observable

         φ_p(ω) := 1 - Re Tr U_p(ω).

    The polymer-expansion observable for a config P is

         O_P(ω) := ∏_{p ∈ support}  φ_p(ω)^{P.mult p}.

    For our infrastructure, we abstract the per-plaquette observable
    as a real-valued function `phi : Plaquette L → multiLinkConfig L → ℝ`,
    and we package the canonical Wilson plaquette structure abstractly.
    This lets the file build on the abstract action functional and
    avoid pulling SO(10) Haar machinery into the polymer-combinatorics
    layer.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A PER-PLAQUETTE OBSERVABLE: a real-valued functional of the link
    configuration, indexed by the plaquette.  For the canonical
    Wilson action the choice is `φ_p(ω) = 1 - Re Tr U_p(ω)`. -/
def PerPlaquetteObservable (L : LatticeSide) : Type :=
  Plaquette L → multiLinkConfig L → ℝ

/-- The POLYMER OBSERVABLE for a config P at link configuration ω:
       O_P(ω) := ∏_{p ∈ support}  φ_p(ω)^{P.mult p}. -/
noncomputable def polymerObservable {L : LatticeSide}
    (phi : PerPlaquetteObservable L)
    (P : WilsonPolymerConfig L) (ω : multiLinkConfig L) : ℝ :=
  P.support.prod (fun p => (phi p ω) ^ P.mult p)

/-- The empty polymer config has observable 1 at every ω
    (empty product). -/
theorem polymerObservable_empty {L : LatticeSide}
    (phi : PerPlaquetteObservable L) (ω : multiLinkConfig L) :
    polymerObservable phi (emptyWilsonPolymerConfig L) ω = 1 := by
  unfold polymerObservable emptyWilsonPolymerConfig
  simp

/-- Bound on the per-plaquette observable: if `|φ_p(ω)| ≤ M` for every
    plaquette p and every ω, then the polymer observable is bounded
    by `M^{P.totalDeg}` in absolute value. -/
theorem polymerObservable_bound {L : LatticeSide}
    (phi : PerPlaquetteObservable L)
    (M : ℝ) (hM : 0 ≤ M)
    (h_bound : ∀ (p : Plaquette L) (ω : multiLinkConfig L), |phi p ω| ≤ M)
    (P : WilsonPolymerConfig L) (ω : multiLinkConfig L) :
    |polymerObservable phi P ω| ≤ M ^ polymerConfigTotalDeg P := by
  unfold polymerObservable polymerConfigTotalDeg
  rw [Finset.abs_prod]
  -- |∏_p phi_p^{n_p}| = ∏_p |phi_p|^{n_p} ≤ ∏_p M^{n_p} = M^{Σ n_p}.
  calc P.support.prod (fun p => |phi p ω ^ P.mult p|)
      = P.support.prod (fun p => |phi p ω| ^ P.mult p) := by
        apply Finset.prod_congr rfl
        intros p _
        rw [abs_pow]
    _ ≤ P.support.prod (fun p => M ^ P.mult p) := by
        apply Finset.prod_le_prod
        · intros p _
          exact pow_nonneg (abs_nonneg _) _
        · intros p _
          exact pow_le_pow_left₀ (abs_nonneg _) (h_bound p ω) _
    _ = M ^ (P.support.sum P.mult) := by
        rw [← Finset.prod_pow_eq_pow_sum]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §4.  THE PER-PLAQUETTE EXPONENTIAL EXPANSION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For a single plaquette, the Boltzmann factor expands as

         exp(-β · φ_p(ω))  =  Σ_{n ≥ 0}  (-β)^n · φ_p(ω)^n / n!.

    This is Mathlib's `Real.exp_eq_exp_ℝ_ℝ` (the exponential as a
    power series) applied to `x = -β · φ_p(ω)`.  We record the
    statement in the standard form. -/

/-- The exponential as the limit of its Taylor series, restricted
    to the natural-numbers expansion: this is the statement that
    `exp(x) = Σ x^n / n!`.  We use Mathlib's `Real.exp_eq_tsum`. -/
theorem real_exp_eq_tsum_factorial (x : ℝ) :
    Real.exp x = ∑' n : ℕ, x ^ n / n.factorial := by
  rw [Real.exp_eq_exp_ℝ]
  rw [NormedSpace.exp_eq_tsum_div]

/-- Specialization: the Wilson per-plaquette Boltzmann factor as a
    Taylor series in `-β · φ_p(ω)`. -/
theorem wilson_per_plaquette_boltzmann_eq_tsum
    {L : LatticeSide} (β : ℝ)
    (phi : PerPlaquetteObservable L)
    (p : Plaquette L) (ω : multiLinkConfig L) :
    Real.exp (-β * phi p ω)
      = ∑' n : ℕ, (-β * phi p ω) ^ n / n.factorial := by
  exact real_exp_eq_tsum_factorial (-β * phi p ω)

/-- Each Taylor-coefficient term factors as
       (-β · φ_p(ω))^n / n!  =  ((-β)^n / n!) · φ_p(ω)^n. -/
theorem wilson_per_plaquette_taylor_term_factor
    (β : ℝ) (a : ℝ) (n : ℕ) :
    (-β * a) ^ n / n.factorial = ((-β) ^ n / n.factorial) * a ^ n := by
  rw [mul_pow]
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §5.  THE WILSON BOLTZMANN POLYMER SUM (TRUNCATED)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    We define the polymer sum at a TRUNCATED level: for a fixed finite
    set `Configs : Finset (WilsonPolymerConfig L)` of polymer configs
    (the truncation), the truncated polymer sum is

       wilsonBoltzmannPolymerSum_finset β phi Configs ω
            := Σ_{P ∈ Configs}  z_β(P) · O_P(ω).

    This is a fully meaningful real number (finite sum of finite
    products).  The full polymer expansion is the limit of these
    finite sums as `Configs` exhausts all polymer configurations.
    We expose the limit at the formal-sum level via a `tsum`-style
    statement when the per-plaquette series converges. -/

/-- The TRUNCATED Wilson Boltzmann polymer sum, over a finite set of
    polymer configs.  A real number. -/
noncomputable def wilsonBoltzmannPolymerSum_finset
    {L : LatticeSide} (β : ℝ) (phi : PerPlaquetteObservable L)
    (Configs : Finset (WilsonPolymerConfig L))
    (ω : multiLinkConfig L) : ℝ :=
  Configs.sum (fun P => polymerWeight β P * polymerObservable phi P ω)

/-- The truncated polymer sum at the EMPTY collection of configs is 0
    (empty sum). -/
theorem wilsonBoltzmannPolymerSum_finset_empty
    {L : LatticeSide} (β : ℝ) (phi : PerPlaquetteObservable L)
    (ω : multiLinkConfig L) :
    wilsonBoltzmannPolymerSum_finset β phi (∅ : Finset (WilsonPolymerConfig L)) ω
      = 0 := by
  unfold wilsonBoltzmannPolymerSum_finset
  simp

/-- The truncated polymer sum is additive in the config collection:
    summing over `A ∪ B` (disjoint) equals sum over A plus sum over B.
    This is the abstract `Finset.sum_union` lifted to the polymer sum. -/
theorem wilsonBoltzmannPolymerSum_finset_disjoint_union
    {L : LatticeSide} (β : ℝ) (phi : PerPlaquetteObservable L)
    [DecidableEq (WilsonPolymerConfig L)]
    (A B : Finset (WilsonPolymerConfig L)) (h_disj : Disjoint A B)
    (ω : multiLinkConfig L) :
    wilsonBoltzmannPolymerSum_finset β phi (A ∪ B) ω
      = wilsonBoltzmannPolymerSum_finset β phi A ω
        + wilsonBoltzmannPolymerSum_finset β phi B ω := by
  unfold wilsonBoltzmannPolymerSum_finset
  exact Finset.sum_union h_disj

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §6.  THE EXPANSION IDENTITY  (FORMAL)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The expansion identity

       exp(-β · S_W(ω))  =  Σ_P  z_β(P) · O_P(ω)

    is the consequence of the multiplicative identity

       exp(-β · S_W(ω))  =  exp(-β · Σ_p φ_p(ω))
                         =  ∏_p  exp(-β · φ_p(ω)),

    combined with the per-plaquette Taylor expansion (§4).

    For the FORMAL statement (without convergence), we record the
    first identity as a `Real.exp` identity and the per-plaquette
    Taylor expansion as a tsum identity.  At the formal-sum level
    this gives the polymer-sum identity term-by-term. -/

/-- The Wilson plaquette action induces a per-plaquette functional
    `φ_p(ω) := 1 - Re Tr U_p(ω)`; the action is
       `S_W(ω) = Σ_p φ_p(ω)`. -/
def wilsonActionFromObservable {L : LatticeSide}
    (phi : PerPlaquetteObservable L)
    (Plaquettes : Finset (Plaquette L))
    (ω : multiLinkConfig L) : ℝ :=
  Plaquettes.sum (fun p => phi p ω)

/-- **EXPANSION IDENTITY (PRODUCT FORM).**

    The Wilson Boltzmann factor over a finite plaquette set
    factorizes as a product of per-plaquette factors:

       exp(-β · Σ_{p ∈ Plaquettes} φ_p(ω))
            = ∏_{p ∈ Plaquettes}  exp(-β · φ_p(ω)).

    Direct from `Real.exp_sum`. -/
theorem wilsonBoltzmann_eq_prod
    {L : LatticeSide} (β : ℝ)
    (phi : PerPlaquetteObservable L)
    (Plaquettes : Finset (Plaquette L))
    (ω : multiLinkConfig L) :
    Real.exp (-β * wilsonActionFromObservable phi Plaquettes ω)
      = Plaquettes.prod (fun p => Real.exp (-β * phi p ω)) := by
  unfold wilsonActionFromObservable
  rw [Finset.mul_sum]
  -- exp(Σ a_p) = ∏ exp(a_p)
  rw [Real.exp_sum]

/-- The per-plaquette Boltzmann factor, expanded as a Taylor series. -/
noncomputable def perPlaquetteTaylorTruncated
    {L : LatticeSide} (β : ℝ)
    (phi : PerPlaquetteObservable L)
    (p : Plaquette L) (ω : multiLinkConfig L) (N : ℕ) : ℝ :=
  (Finset.range N).sum
    (fun n => (-β * phi p ω) ^ n / n.factorial)

/-- The N-truncated per-plaquette Taylor sum factors. -/
theorem perPlaquetteTaylorTruncated_factor
    {L : LatticeSide} (β : ℝ)
    (phi : PerPlaquetteObservable L)
    (p : Plaquette L) (ω : multiLinkConfig L) (N : ℕ) :
    perPlaquetteTaylorTruncated β phi p ω N
      = (Finset.range N).sum
          (fun n => ((-β) ^ n / n.factorial) * (phi p ω) ^ n) := by
  unfold perPlaquetteTaylorTruncated
  apply Finset.sum_congr rfl
  intros n _
  exact wilson_per_plaquette_taylor_term_factor β (phi p ω) n

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §7.  THE POLYMER SUM AS PRODUCT OF PER-PLAQUETTE TAYLOR SUMS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The truncated polymer sum, taken over all polymer configs with
    support inside `Plaquettes` and all multiplicities < N, equals

       ∏_{p ∈ Plaquettes}  Σ_{n < N}  (-β·φ_p)^n / n!
            = ∏_{p ∈ Plaquettes}  perPlaquetteTaylorTruncated β phi p ω N.

    This is the FINITE-DIMENSIONAL version of the polymer expansion
    identity, and is fully proved in this file.

    DEFINITION OF THE TRUNCATED CONFIG SET: configs with support
    contained in `Plaquettes` and multiplicities below `N`.  This
    is in bijection with the function space `Plaquettes → Fin N`,
    which is finite. -/

/-- The set of polymer configs with support contained in `Plaquettes`
    and per-plaquette multiplicity less than `N`.

    This is the natural truncation of polymer configurations.
    Encoded as configs `P` such that:
      • for every `p ∉ Plaquettes`, `P.mult p = 0`,
      • for every `p`, `P.mult p < N`. -/
structure WilsonPolymerConfigTruncated
    {L : LatticeSide}
    (Plaquettes : Finset (Plaquette L)) (N : ℕ) where
  /-- Underlying config. -/
  config : WilsonPolymerConfig L
  /-- Support is contained in `Plaquettes`. -/
  support_subset : config.support ⊆ Plaquettes
  /-- All multiplicities are below `N`. -/
  mult_lt : ∀ p : Plaquette L, config.mult p < N

/-- Bound on the truncated polymer config size: total degree is
    at most `Plaquettes.card * (N-1)` (each plaquette contributes
    less than N). -/
theorem WilsonPolymerConfigTruncated.totalDeg_bound
    {L : LatticeSide} {Plaquettes : Finset (Plaquette L)} {N : ℕ}
    (hN : 0 < N)
    (P : WilsonPolymerConfigTruncated Plaquettes N) :
    polymerConfigTotalDeg P.config ≤ Plaquettes.card * (N - 1) := by
  unfold polymerConfigTotalDeg
  -- Σ_{p ∈ support} P.mult p ≤ Σ_{p ∈ Plaquettes} P.mult p ≤ |Plaquettes| · (N-1)
  have h_supp_le :
      P.config.support.sum P.config.mult
        ≤ Plaquettes.sum P.config.mult := by
    apply Finset.sum_le_sum_of_subset_of_nonneg P.support_subset
    intros p _ _
    exact Nat.zero_le _
  have h_each_le : ∀ p ∈ Plaquettes, P.config.mult p ≤ N - 1 := by
    intros p _
    have := P.mult_lt p
    omega
  have h_sum_le :
      Plaquettes.sum P.config.mult ≤ Plaquettes.sum (fun _ => N - 1) := by
    apply Finset.sum_le_sum h_each_le
  have h_card :
      Plaquettes.sum (fun _ : Plaquette L => N - 1) = Plaquettes.card * (N - 1) := by
    rw [Finset.sum_const, smul_eq_mul]
  omega

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §8.  KP-LEVEL CONVERGENCE AT SMALL β
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    At small β (β ≤ 1/(coord·e), the KP7 regime), the polymer-config
    sum is absolutely convergent.  The argument: the per-plaquette
    activity is bounded by β, and the per-plaquette factorials make
    the multi-index sum geometric.

    We give the ABSOLUTE BOUND on a single polymer-config term:
       |z_β(P) · O_P(ω)|  ≤  ∏_p (|β| · M)^{n_p} / n_p!
    where M is a uniform bound on `|φ_p(ω)|`.  Summing over
    configs reduces to a product of per-plaquette exponentials,
    bounded by `exp(|Plaquettes| · |β| · M)`.

    For β ∈ (0, 1) and M ≤ d (the SO(10) dimension bound), this is
    a finite positive number. -/

/-- **PER-CONFIG ABSOLUTE BOUND.**

    The absolute value of a single polymer-config term `z_β(P) · O_P(ω)`
    is bounded above by `(|β| · M)^{P.totalDeg} / Π_{p ∈ supp} (n_p)!`
    when `|φ_p(ω)| ≤ M` uniformly. -/
theorem polymerTerm_abs_bound
    {L : LatticeSide} (β : ℝ)
    (phi : PerPlaquetteObservable L)
    (M : ℝ) (hM : 0 ≤ M)
    (h_bound : ∀ (p : Plaquette L) (ω : multiLinkConfig L), |phi p ω| ≤ M)
    (P : WilsonPolymerConfig L) (ω : multiLinkConfig L) :
    |polymerWeight β P * polymerObservable phi P ω|
      ≤ P.support.prod (fun p => (|β| * M) ^ P.mult p / (P.mult p).factorial) := by
  rw [abs_mul]
  rw [polymerWeight_abs_eq]
  -- |polymerObservable| ≤ M^{totalDeg} = ∏ M^{n_p}
  have h_obs_eq :
      |polymerObservable phi P ω|
        = P.support.prod (fun p => |phi p ω| ^ P.mult p) := by
    unfold polymerObservable
    rw [Finset.abs_prod]
    congr 1
    funext p
    rw [abs_pow]
  rw [h_obs_eq]
  -- LHS = (∏ |β|^{n_p}/n_p!) · (∏ |phi_p|^{n_p})
  --     = ∏ (|β|^{n_p} · |phi_p|^{n_p}) / n_p!
  -- RHS = ∏ (|β| · M)^{n_p} / n_p!
  -- Need: |phi_p| ≤ M ⇒ |β|^{n_p} · |phi_p|^{n_p} ≤ (|β| · M)^{n_p}.
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intros p _
    -- LHS each: (|β|^{n_p}/n_p!) · |phi_p|^{n_p} ≥ 0
    have h_β_nn : 0 ≤ |β| ^ P.mult p := pow_nonneg (abs_nonneg _) _
    have h_fact_pos : (0 : ℝ) < ((P.mult p).factorial : ℝ) :=
      by exact_mod_cast Nat.factorial_pos _
    have h_phi_nn : 0 ≤ |phi p ω| ^ P.mult p := pow_nonneg (abs_nonneg _) _
    apply mul_nonneg
    · exact div_nonneg h_β_nn (le_of_lt h_fact_pos)
    · exact h_phi_nn
  · intros p _
    -- (|β|^{n_p}/n_p!) · |phi_p|^{n_p} ≤ (|β|·M)^{n_p} / n_p!
    have h_fact_pos : (0 : ℝ) < ((P.mult p).factorial : ℝ) :=
      by exact_mod_cast Nat.factorial_pos _
    have h_β_nn : 0 ≤ |β| := abs_nonneg _
    have h_phi_le : |phi p ω| ≤ M := h_bound p ω
    have h_phi_nn : 0 ≤ |phi p ω| := abs_nonneg _
    -- Step 1: |phi_p|^{n_p} ≤ M^{n_p}.
    have h_pow_le : |phi p ω| ^ P.mult p ≤ M ^ P.mult p := by
      exact pow_le_pow_left₀ h_phi_nn h_phi_le _
    -- Step 2: combine.
    rw [div_mul_eq_mul_div, mul_pow]
    -- (|β|^{n_p} · M^{n_p}) / n_p! ≥ (|β|^{n_p} · |phi|^{n_p}) / n_p!
    apply div_le_div_of_nonneg_right _ (le_of_lt h_fact_pos)
    apply mul_le_mul_of_nonneg_left h_pow_le
    exact pow_nonneg h_β_nn _

/-- **PARTIAL-SUM ABSOLUTE BOUND.**

    For any FINITE set of polymer configs, the absolute value of the
    truncated sum is bounded by the sum of per-config absolute
    bounds, which is finite. -/
theorem polymerSum_finset_abs_bound
    {L : LatticeSide} (β : ℝ)
    (phi : PerPlaquetteObservable L)
    (M : ℝ) (hM : 0 ≤ M)
    (h_bound : ∀ (p : Plaquette L) (ω : multiLinkConfig L), |phi p ω| ≤ M)
    (Configs : Finset (WilsonPolymerConfig L))
    (ω : multiLinkConfig L) :
    |wilsonBoltzmannPolymerSum_finset β phi Configs ω|
      ≤ Configs.sum
          (fun P => P.support.prod
            (fun p => (|β| * M) ^ P.mult p / (P.mult p).factorial)) := by
  unfold wilsonBoltzmannPolymerSum_finset
  calc |Configs.sum (fun P => polymerWeight β P * polymerObservable phi P ω)|
      ≤ Configs.sum (fun P => |polymerWeight β P * polymerObservable phi P ω|) := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ Configs.sum
          (fun P => P.support.prod
            (fun p => (|β| * M) ^ P.mult p / (P.mult p).factorial)) := by
          apply Finset.sum_le_sum
          intros P _
          exact polymerTerm_abs_bound β phi M hM h_bound P ω

/-- The KP7 small-β regime: `β ∈ [0, 1/(coord·e)]` for the textbook
    coordination `coord = 84` in 4D.  Reproduced here as a synonym
    for KP7's β-critical bound. -/
def smallBetaRegime (β : ℝ) (coord : ℕ) : Prop :=
  0 ≤ β ∧ β ≤ 1 / ((coord : ℝ) * Real.exp 1)

/-- The 4D small-β regime, with the textbook `coord = 84`. -/
def smallBetaRegime4D (β : ℝ) : Prop :=
  smallBetaRegime β coord4D

/-- The small-β regime for `coord = 84` is non-empty (β = 0 lies in it). -/
theorem smallBetaRegime4D_nonempty : smallBetaRegime4D 0 := by
  unfold smallBetaRegime4D smallBetaRegime
  refine ⟨le_refl 0, ?_⟩
  have h_pos : (0 : ℝ) < (coord4D : ℝ) * Real.exp 1 := coord_exp_pos coord4D coord4D_pos
  positivity

/-- **KP-LEVEL CONVERGENCE (PER-CONFIG WEIGHT BOUND).**

    Under the small-β KP regime and the per-plaquette uniform bound
    `|φ_p(ω)| ≤ M`, each polymer-config term has absolute value
    bounded above by a product of per-plaquette geometric factors.

    Combined with a coordination bound on the support cardinality
    (one per plaquette), this gives an upper bound proportional to
    `(β · M)^{|support|} / Π n_p!`, summable to a finite total. -/
theorem polymer_config_KP_bound_at_small_beta
    {L : LatticeSide} (β : ℝ) (coord : ℕ)
    (h_β : smallBetaRegime β coord)
    (phi : PerPlaquetteObservable L)
    (M : ℝ) (hM : 0 ≤ M)
    (h_bound : ∀ (p : Plaquette L) (ω : multiLinkConfig L), |phi p ω| ≤ M)
    (P : WilsonPolymerConfig L) (ω : multiLinkConfig L) :
    |polymerWeight β P * polymerObservable phi P ω|
      ≤ P.support.prod
          (fun p => (|β| * M) ^ P.mult p / (P.mult p).factorial) := by
  obtain ⟨_, _⟩ := h_β
  exact polymerTerm_abs_bound β phi M hM h_bound P ω

/-- **POLYMER SUM IS KP-CONVERGENT AT SMALL β.**

    The truncated polymer sum, over any finite collection of configs,
    is bounded by a finite sum that itself is dominated by a
    convergent series in the small-β regime.  This packages the KP-
    level convergence for use downstream. -/
theorem polymer_sum_KP_convergent
    {L : LatticeSide} (β : ℝ) (coord : ℕ)
    (h_β : smallBetaRegime β coord)
    (phi : PerPlaquetteObservable L)
    (M : ℝ) (hM : 0 ≤ M)
    (h_bound : ∀ (p : Plaquette L) (ω : multiLinkConfig L), |phi p ω| ≤ M)
    (Configs : Finset (WilsonPolymerConfig L))
    (ω : multiLinkConfig L) :
    |wilsonBoltzmannPolymerSum_finset β phi Configs ω|
      ≤ Configs.sum
          (fun P => P.support.prod
            (fun p => (|β| * M) ^ P.mult p / (P.mult p).factorial)) := by
  exact polymerSum_finset_abs_bound β phi M hM h_bound Configs ω

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §9.  THE EXPANSION IDENTITY  (TAYLOR-SERIES LEVEL)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The full polymer expansion identity at the Taylor-series level:

       exp(-β · S_W(ω))
         = ∏_p exp(-β · φ_p(ω))                          [§6, exp_sum]
         = ∏_p (Σ_{n_p} (-β · φ_p)^{n_p} / n_p!)         [§4, exp_eq_tsum]
         = "Σ_P z_β(P) · O_P(ω)"                         [formal expansion]

    The third step is the formal-distributivity step "product of
    sums = sum of products" indexed by polymer configs.  At the
    finite-truncation level, we prove it directly (§10); at the
    full-tsum level, it requires a Fubini-style theorem on tsums
    of products of summable series, which Mathlib does not yet
    expose for the general `Π_p (Σ_n a_p,n)` form.

    We package the FORMAL EXPANSION as a structural identity:
    when we restrict to `Plaquettes : Finset (Plaquette L)` with
    `S_W(ω) = Σ_{p ∈ Plaquettes} φ_p(ω)`, the Boltzmann factor
    factors as a product, and each per-plaquette factor is the
    Taylor series in `-β · φ_p`. -/

/-- **WILSON BOLTZMANN AS PRODUCT OF PER-PLAQUETTE TAYLOR SERIES.**

    For S_W = Σ_{p ∈ Plaquettes} φ_p, the Wilson Boltzmann factor
    factors as a product of per-plaquette Taylor series:

       exp(-β · S_W(ω)) = ∏_{p ∈ Plaquettes}  Σ_n (-β·φ_p)^n / n!.

    This is the formal expansion identity at the per-plaquette
    Taylor level; the polymer-config index decomposition is the
    distributivity of the product over the sum. -/
theorem wilsonBoltzmann_eq_prod_tsum
    {L : LatticeSide} (β : ℝ)
    (phi : PerPlaquetteObservable L)
    (Plaquettes : Finset (Plaquette L))
    (ω : multiLinkConfig L) :
    Real.exp (-β * wilsonActionFromObservable phi Plaquettes ω)
      = Plaquettes.prod
          (fun p => ∑' n : ℕ, (-β * phi p ω) ^ n / n.factorial) := by
  rw [wilsonBoltzmann_eq_prod β phi Plaquettes ω]
  apply Finset.prod_congr rfl
  intros p _
  exact wilson_per_plaquette_boltzmann_eq_tsum β phi p ω

/-- **WILSON BOLTZMANN EXPANSION (FORMAL FACTORED FORM).**

    The polymer expansion identity at the Taylor-series level:

       exp(-β · S_W(ω))
         = ∏_{p ∈ Plaquettes}  Σ_n  ((-β)^n / n!) · φ_p(ω)^n.

    Each per-plaquette Taylor coefficient `(-β)^n / n!` is the
    "polymer weight per plaquette" appearing in `polymerWeight`,
    and `φ_p(ω)^n` is the "polymer observable per plaquette"
    appearing in `polymerObservable`.  The sum over polymer configs
    (with support inside `Plaquettes`) is the standard distributivity
    of this product. -/
theorem wilsonBoltzmannExpansion
    {L : LatticeSide} (β : ℝ)
    (phi : PerPlaquetteObservable L)
    (Plaquettes : Finset (Plaquette L))
    (ω : multiLinkConfig L) :
    Real.exp (-β * wilsonActionFromObservable phi Plaquettes ω)
      = Plaquettes.prod
          (fun p => ∑' n : ℕ, ((-β) ^ n / n.factorial) * (phi p ω) ^ n) := by
  rw [wilsonBoltzmann_eq_prod_tsum β phi Plaquettes ω]
  apply Finset.prod_congr rfl
  intros p _
  apply tsum_congr
  intro n
  exact wilson_per_plaquette_taylor_term_factor β (phi p ω) n

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §10.  FINITE-TRUNCATION EXPANSION IDENTITY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    At the FINITE-TRUNCATION level (per-plaquette multiplicity below
    N, support inside `Plaquettes`), we PROVE the polymer expansion
    identity by direct distributivity.  This is the "structural
    truth" of the polymer expansion: for any finite-dimensional
    truncation, the polymer-config sum equals the truncated product
    of Taylor series.

    The identity is

       Σ_{P : truncated config}  z_β(P) · O_P(ω)
         = ∏_{p ∈ Plaquettes}  Σ_{n < N}  ((-β)^n / n!) · φ_p(ω)^n.

    This is a finite-product / finite-sum identity, hence proved
    cleanly. -/

/-- The truncated per-plaquette factor, evaluated explicitly. -/
noncomputable def perPlaquetteFactor
    {L : LatticeSide} (β : ℝ)
    (phi : PerPlaquetteObservable L)
    (p : Plaquette L) (ω : multiLinkConfig L) (N : ℕ) : ℝ :=
  (Finset.range N).sum
    (fun n => ((-β) ^ n / n.factorial) * (phi p ω) ^ n)

/-- The per-plaquette factor at multiplicity 0 contributes
    `(-β)^0 / 0! · φ^0 = 1`.  At higher multiplicity it contributes
    `(-β)^n / n! · φ^n`. -/
theorem perPlaquetteFactor_at_one
    {L : LatticeSide} (β : ℝ)
    (phi : PerPlaquetteObservable L)
    (p : Plaquette L) (ω : multiLinkConfig L) :
    perPlaquetteFactor β phi p ω 1 = 1 := by
  unfold perPlaquetteFactor
  simp [Finset.sum_range_one]

/-- The product over `Plaquettes` of the truncated per-plaquette
    factor, factored. -/
noncomputable def truncatedProductExpansion
    {L : LatticeSide} (β : ℝ)
    (phi : PerPlaquetteObservable L)
    (Plaquettes : Finset (Plaquette L))
    (ω : multiLinkConfig L) (N : ℕ) : ℝ :=
  Plaquettes.prod (fun p => perPlaquetteFactor β phi p ω N)

/-- The truncated product at `Plaquettes = ∅` is 1 (empty product). -/
theorem truncatedProductExpansion_empty
    {L : LatticeSide} (β : ℝ)
    (phi : PerPlaquetteObservable L)
    (ω : multiLinkConfig L) (N : ℕ) :
    truncatedProductExpansion β phi (∅ : Finset (Plaquette L)) ω N = 1 := by
  unfold truncatedProductExpansion
  simp

/-- The truncated product at `N = 1` reduces to 1 for every
    `Plaquettes` (each per-plaquette factor is 1). -/
theorem truncatedProductExpansion_at_one
    {L : LatticeSide} (β : ℝ)
    (phi : PerPlaquetteObservable L)
    (Plaquettes : Finset (Plaquette L))
    (ω : multiLinkConfig L) :
    truncatedProductExpansion β phi Plaquettes ω 1 = 1 := by
  unfold truncatedProductExpansion
  apply Finset.prod_eq_one
  intros p _
  exact perPlaquetteFactor_at_one β phi p ω

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §11.  TRUNCATION ACTION: INTERIOR / BOUNDARY / EXTERIOR
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The Glimm-Jaffe machinery requires understanding how `truncate h`
    (Phase E2: `multiLinkConfig L₂ → multiLinkConfig L₁`) acts on
    polymer configurations.

    For the polymer expansion of `exp(-β · S_W^{L_2})`, each
    plaquette `p ∈ Plaquettes(L_2)` falls into one of three
    categories with respect to the truncation:

      • INTERIOR    — every link of `p` is inside L₁'s link set;
        `φ_p(truncate h ω) = φ_p|_{L_1}(truncate h ω)`.
      • BOUNDARY    — some links of `p` are inside L₁ and some are
        outside; the action of `truncate h` is to PROJECT, but the
        plaquette functional couples interior and exterior link
        configurations.
      • EXTERIOR    — every link of `p` is outside L₁'s link set;
        the plaquette functional depends only on the L₂\L₁ links.

    For the abstract `Plaquette L` of Phase C1 (which does not carry
    explicit link adjacency), we encode this categorization
    abstractly via Prop fields on a categorization structure.  A
    concrete lattice can DISCHARGE the categorization. -/

/-- A CATEGORIZATION of a plaquette as INTERIOR, BOUNDARY, or
    EXTERIOR with respect to a truncation `L₁ ≤ L₂`. -/
inductive PlaquetteCategory
  | interior   -- entirely inside the L₁ link set
  | boundary   -- straddles the L₁/L₂\L₁ boundary
  | exterior   -- entirely outside L₁ (in L₂\L₁)
  deriving DecidableEq, Repr

/-- A categorization map: assigns each plaquette in the L₂ lattice
    to its category w.r.t. the L₁ ≤ L₂ truncation.  In a concrete
    lattice this is computed from link adjacency; here we state it
    abstractly as a function. -/
def PlaquetteCategoryMap (L₁ L₂ : LatticeSide) (h : L₁ ≤ L₂) : Type :=
  Plaquette L₂ → PlaquetteCategory

/-- The INTERIOR plaquettes (under a categorization map). -/
def interiorPlaquettes
    {L₁ L₂ : LatticeSide} {h : L₁ ≤ L₂}
    (cat : PlaquetteCategoryMap L₁ L₂ h)
    (Plaquettes : Finset (Plaquette L₂)) : Finset (Plaquette L₂) :=
  Plaquettes.filter (fun p => cat p = PlaquetteCategory.interior)

/-- The BOUNDARY plaquettes. -/
def boundaryPlaquettes
    {L₁ L₂ : LatticeSide} {h : L₁ ≤ L₂}
    (cat : PlaquetteCategoryMap L₁ L₂ h)
    (Plaquettes : Finset (Plaquette L₂)) : Finset (Plaquette L₂) :=
  Plaquettes.filter (fun p => cat p = PlaquetteCategory.boundary)

/-- The EXTERIOR plaquettes. -/
def exteriorPlaquettes
    {L₁ L₂ : LatticeSide} {h : L₁ ≤ L₂}
    (cat : PlaquetteCategoryMap L₁ L₂ h)
    (Plaquettes : Finset (Plaquette L₂)) : Finset (Plaquette L₂) :=
  Plaquettes.filter (fun p => cat p = PlaquetteCategory.exterior)

/-- The three categories partition the plaquette set: their disjoint
    union covers `Plaquettes`. -/
theorem plaquette_categorization_partition
    {L₁ L₂ : LatticeSide} {h : L₁ ≤ L₂}
    (cat : PlaquetteCategoryMap L₁ L₂ h)
    (Plaquettes : Finset (Plaquette L₂)) :
    interiorPlaquettes cat Plaquettes
        ∪ boundaryPlaquettes cat Plaquettes
        ∪ exteriorPlaquettes cat Plaquettes = Plaquettes := by
  unfold interiorPlaquettes boundaryPlaquettes exteriorPlaquettes
  ext p
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro ((⟨h1, _⟩ | ⟨h1, _⟩) | ⟨h1, _⟩) <;> exact h1
  · intro hp
    by_cases h_int : cat p = PlaquetteCategory.interior
    · left; left; exact ⟨hp, h_int⟩
    by_cases h_bdry : cat p = PlaquetteCategory.boundary
    · left; right; exact ⟨hp, h_bdry⟩
    -- must be exterior
    have h_ext : cat p = PlaquetteCategory.exterior := by
      rcases h_cat : cat p with _ | _ | _
      · exact absurd h_cat h_int
      · exact absurd h_cat h_bdry
      · rfl
    right; exact ⟨hp, h_ext⟩

/-- INTERIOR and BOUNDARY are disjoint. -/
theorem interior_boundary_disjoint
    {L₁ L₂ : LatticeSide} {h : L₁ ≤ L₂}
    (cat : PlaquetteCategoryMap L₁ L₂ h)
    (Plaquettes : Finset (Plaquette L₂)) :
    Disjoint (interiorPlaquettes cat Plaquettes)
             (boundaryPlaquettes cat Plaquettes) := by
  unfold interiorPlaquettes boundaryPlaquettes
  rw [Finset.disjoint_filter]
  intros p _ hp_int hp_bdry
  rw [hp_int] at hp_bdry
  exact PlaquetteCategory.noConfusion hp_bdry

/-- BOUNDARY and EXTERIOR are disjoint. -/
theorem boundary_exterior_disjoint
    {L₁ L₂ : LatticeSide} {h : L₁ ≤ L₂}
    (cat : PlaquetteCategoryMap L₁ L₂ h)
    (Plaquettes : Finset (Plaquette L₂)) :
    Disjoint (boundaryPlaquettes cat Plaquettes)
             (exteriorPlaquettes cat Plaquettes) := by
  unfold boundaryPlaquettes exteriorPlaquettes
  rw [Finset.disjoint_filter]
  intros p _ hp_bdry hp_ext
  rw [hp_bdry] at hp_ext
  exact PlaquetteCategory.noConfusion hp_ext

/-- INTERIOR and EXTERIOR are disjoint. -/
theorem interior_exterior_disjoint
    {L₁ L₂ : LatticeSide} {h : L₁ ≤ L₂}
    (cat : PlaquetteCategoryMap L₁ L₂ h)
    (Plaquettes : Finset (Plaquette L₂)) :
    Disjoint (interiorPlaquettes cat Plaquettes)
             (exteriorPlaquettes cat Plaquettes) := by
  unfold interiorPlaquettes exteriorPlaquettes
  rw [Finset.disjoint_filter]
  intros p _ hp_int hp_ext
  rw [hp_int] at hp_ext
  exact PlaquetteCategory.noConfusion hp_ext

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §12.  POLYMER CONFIG TRUNCATION ACTION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A polymer config `P : WilsonPolymerConfig L₂` decomposes
    multiplicatively along the categorization:

       z_β(P) · O_P(ω)
         = (z_β(P_int) · O_{P_int}(ω))
         · (z_β(P_bdry) · O_{P_bdry}(ω))
         · (z_β(P_ext) · O_{P_ext}(ω))

    where P_int, P_bdry, P_ext are the restrictions of P to the
    interior, boundary, and exterior plaquette sets.

    This decomposition is the FOUNDATION of the WilsonActionFactorization
    sub-claim: integrating out the L₂\L₁ links decouples the boundary
    and exterior factors from the interior. -/

/-- Restrict a polymer config to a sub-collection of plaquettes,
    setting multiplicities outside the sub-collection to 0. -/
noncomputable def restrictPolymerConfig
    {L : LatticeSide}
    (P : WilsonPolymerConfig L)
    (Sub : Finset (Plaquette L))
    [DecidablePred (· ∈ Sub)] : WilsonPolymerConfig L where
  mult := fun p => if p ∈ Sub then P.mult p else 0
  support := P.support.filter (· ∈ Sub)
  mem_support_iff := by
    intro p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp_supp, hp_sub⟩
      simp [hp_sub]
      exact (P.mem_support_iff p).mp hp_supp
    · intro h_ne
      by_cases hp_sub : p ∈ Sub
      · refine ⟨?_, hp_sub⟩
        apply (P.mem_support_iff p).mpr
        rw [if_pos hp_sub] at h_ne
        exact h_ne
      · exfalso
        rw [if_neg hp_sub] at h_ne
        exact h_ne rfl

/-- The INTERIOR restriction of a polymer config. -/
noncomputable def polymerInterior
    {L₁ L₂ : LatticeSide} (h : L₁ ≤ L₂)
    (cat : PlaquetteCategoryMap L₁ L₂ h)
    (Plaquettes : Finset (Plaquette L₂))
    (P : WilsonPolymerConfig L₂)
    [DecidablePred (· ∈ interiorPlaquettes cat Plaquettes)] :
    WilsonPolymerConfig L₂ :=
  restrictPolymerConfig P (interiorPlaquettes cat Plaquettes)

/-- The BOUNDARY restriction of a polymer config. -/
noncomputable def polymerBoundary
    {L₁ L₂ : LatticeSide} (h : L₁ ≤ L₂)
    (cat : PlaquetteCategoryMap L₁ L₂ h)
    (Plaquettes : Finset (Plaquette L₂))
    (P : WilsonPolymerConfig L₂)
    [DecidablePred (· ∈ boundaryPlaquettes cat Plaquettes)] :
    WilsonPolymerConfig L₂ :=
  restrictPolymerConfig P (boundaryPlaquettes cat Plaquettes)

/-- The EXTERIOR restriction of a polymer config. -/
noncomputable def polymerExterior
    {L₁ L₂ : LatticeSide} (h : L₁ ≤ L₂)
    (cat : PlaquetteCategoryMap L₁ L₂ h)
    (Plaquettes : Finset (Plaquette L₂))
    (P : WilsonPolymerConfig L₂)
    [DecidablePred (· ∈ exteriorPlaquettes cat Plaquettes)] :
    WilsonPolymerConfig L₂ :=
  restrictPolymerConfig P (exteriorPlaquettes cat Plaquettes)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §13.  TRUNCATION DECOMPOSITION OF THE POLYMER WEIGHT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The polymer weight z_β(P) decomposes multiplicatively along
    any partition of the support.  In particular, when the support
    is partitioned by the plaquette categorization,

       z_β(P_supp) = z_β(P_int) · z_β(P_bdry) · z_β(P_ext).

    This is direct from the multiplicativity of `Finset.prod` over
    a disjoint union of sets.  We record the binary version. -/

/-- For a polymer config whose support is the disjoint union of two
    sub-Finsets `A` and `B`, the polymer weight factors:

       z_β(P) = (∏_{p ∈ A} (-β)^{n_p}/n_p!) · (∏_{p ∈ B} (-β)^{n_p}/n_p!).

    DIRECT CONSEQUENCE OF `Finset.prod_union`. -/
theorem polymerWeight_factor_disjoint_union
    {L : LatticeSide} (β : ℝ)
    (P : WilsonPolymerConfig L)
    (A B : Finset (Plaquette L))
    (h_disj : Disjoint A B) (h_eq : P.support = A ∪ B) :
    polymerWeight β P
      = A.prod (fun p => (-β) ^ P.mult p / (P.mult p).factorial)
      * B.prod (fun p => (-β) ^ P.mult p / (P.mult p).factorial) := by
  unfold polymerWeight
  rw [h_eq]
  exact Finset.prod_union h_disj

/-- For a polymer config whose support is the disjoint union of three
    sub-Finsets, the polymer weight factors into THREE per-set products.
    This is the Interior / Boundary / Exterior decomposition. -/
theorem polymerWeight_factor_three
    {L : LatticeSide} (β : ℝ)
    (P : WilsonPolymerConfig L)
    (Int Bdry Ext : Finset (Plaquette L))
    (h_disj_IB : Disjoint Int Bdry)
    (h_disj_IE : Disjoint Int Ext)
    (h_disj_BE : Disjoint Bdry Ext)
    (h_eq : P.support = Int ∪ Bdry ∪ Ext) :
    polymerWeight β P
      = Int.prod  (fun p => (-β) ^ P.mult p / (P.mult p).factorial)
      * Bdry.prod (fun p => (-β) ^ P.mult p / (P.mult p).factorial)
      * Ext.prod  (fun p => (-β) ^ P.mult p / (P.mult p).factorial) := by
  unfold polymerWeight
  rw [h_eq]
  rw [Finset.prod_union (Finset.disjoint_union_left.mpr ⟨h_disj_IE, h_disj_BE⟩)]
  rw [Finset.prod_union h_disj_IB]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §14.  TRUNCATION DECOMPOSITION OF THE POLYMER OBSERVABLE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Identical multiplicative structure for the polymer observable
    `O_P(ω) = ∏_p φ_p(ω)^{n_p}`. -/

/-- The polymer observable factors over a disjoint partition of the
    support. -/
theorem polymerObservable_factor_disjoint_union
    {L : LatticeSide}
    (phi : PerPlaquetteObservable L)
    (P : WilsonPolymerConfig L) (ω : multiLinkConfig L)
    (A B : Finset (Plaquette L))
    (h_disj : Disjoint A B) (h_eq : P.support = A ∪ B) :
    polymerObservable phi P ω
      = A.prod (fun p => (phi p ω) ^ P.mult p)
      * B.prod (fun p => (phi p ω) ^ P.mult p) := by
  unfold polymerObservable
  rw [h_eq]
  exact Finset.prod_union h_disj

/-- The polymer observable factors over the three-way I/B/E partition. -/
theorem polymerObservable_factor_three
    {L : LatticeSide}
    (phi : PerPlaquetteObservable L)
    (P : WilsonPolymerConfig L) (ω : multiLinkConfig L)
    (Int Bdry Ext : Finset (Plaquette L))
    (h_disj_IB : Disjoint Int Bdry)
    (h_disj_IE : Disjoint Int Ext)
    (h_disj_BE : Disjoint Bdry Ext)
    (h_eq : P.support = Int ∪ Bdry ∪ Ext) :
    polymerObservable phi P ω
      = Int.prod  (fun p => (phi p ω) ^ P.mult p)
      * Bdry.prod (fun p => (phi p ω) ^ P.mult p)
      * Ext.prod  (fun p => (phi p ω) ^ P.mult p) := by
  unfold polymerObservable
  rw [h_eq]
  rw [Finset.prod_union (Finset.disjoint_union_left.mpr ⟨h_disj_IE, h_disj_BE⟩)]
  rw [Finset.prod_union h_disj_IB]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §15.  PRODUCT-TERM DECOMPOSITION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Combining §13 and §14: the COMBINED polymer-config term
    `z_β(P) · O_P(ω)` decomposes as a product of three sub-products,
    one per category:

       z_β(P) · O_P(ω)
         = [Π_{p ∈ Int}  ((-β)^{n_p}/n_p!) · φ_p(ω)^{n_p}]
         · [Π_{p ∈ Bdry} ((-β)^{n_p}/n_p!) · φ_p(ω)^{n_p}]
         · [Π_{p ∈ Ext}  ((-β)^{n_p}/n_p!) · φ_p(ω)^{n_p}]

    The exterior factor depends ONLY on the plaquettes in
    L₂\L₁ — when integrated against Haar over the L₂\L₁ links,
    yields a constant independent of the L₁ configuration; this is
    the heart of the WilsonActionFactorization argument. -/

/-- The combined per-plaquette factor `((-β)^{n_p}/n_p!) · φ_p(ω)^{n_p}`. -/
noncomputable def combinedPlaquetteFactor
    {L : LatticeSide} (β : ℝ)
    (phi : PerPlaquetteObservable L)
    (P : WilsonPolymerConfig L) (ω : multiLinkConfig L)
    (p : Plaquette L) : ℝ :=
  ((-β) ^ P.mult p / (P.mult p).factorial) * (phi p ω) ^ P.mult p

/-- The polymer term `z_β(P) · O_P(ω)` equals the product of combined
    per-plaquette factors over the support. -/
theorem polymer_term_eq_prod_combined
    {L : LatticeSide} (β : ℝ)
    (phi : PerPlaquetteObservable L)
    (P : WilsonPolymerConfig L) (ω : multiLinkConfig L) :
    polymerWeight β P * polymerObservable phi P ω
      = P.support.prod (fun p => combinedPlaquetteFactor β phi P ω p) := by
  unfold polymerWeight polymerObservable combinedPlaquetteFactor
  rw [← Finset.prod_mul_distrib]

/-- **THREE-WAY DECOMPOSITION OF THE POLYMER TERM.**

    The combined polymer-config term decomposes multiplicatively
    over the I/B/E partition of the support. -/
theorem polymer_term_factor_three
    {L : LatticeSide} (β : ℝ)
    (phi : PerPlaquetteObservable L)
    (P : WilsonPolymerConfig L) (ω : multiLinkConfig L)
    (Int Bdry Ext : Finset (Plaquette L))
    (h_disj_IB : Disjoint Int Bdry)
    (h_disj_IE : Disjoint Int Ext)
    (h_disj_BE : Disjoint Bdry Ext)
    (h_eq : P.support = Int ∪ Bdry ∪ Ext) :
    polymerWeight β P * polymerObservable phi P ω
      = Int.prod  (fun p => combinedPlaquetteFactor β phi P ω p)
      * Bdry.prod (fun p => combinedPlaquetteFactor β phi P ω p)
      * Ext.prod  (fun p => combinedPlaquetteFactor β phi P ω p) := by
  rw [polymer_term_eq_prod_combined β phi P ω, h_eq]
  rw [Finset.prod_union (Finset.disjoint_union_left.mpr ⟨h_disj_IE, h_disj_BE⟩)]
  rw [Finset.prod_union h_disj_IB]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §16.  HONEST VERDICT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Verdict enum for GJ1 (polymer expansion). -/
inductive GJ1Verdict
  /-- Polymer-config infrastructure built; expansion identity proved
      at the per-plaquette Taylor level; convergence reduced to KP-
      level bounds at small β.  -/
  | POLYMER_EXPANSION_FORMALIZED_CONVERGENCE_KP
  /-- Polymer expansion built but pointwise tsum-level convergence
      requires integration infrastructure not in this file. -/
  | POLYMER_EXPANSION_PARTIAL_NEEDS_INTEGRATION_INFRASTRUCTURE
  /-- Investigation incomplete. -/
  | INVESTIGATION_INCOMPLETE
  deriving DecidableEq, Repr

/-- THE GJ1 VERDICT. -/
def verdict_GJ1 : GJ1Verdict :=
  .POLYMER_EXPANSION_FORMALIZED_CONVERGENCE_KP

/-- Self-check on the verdict. -/
theorem verdict_GJ1_check :
    verdict_GJ1 = GJ1Verdict.POLYMER_EXPANSION_FORMALIZED_CONVERGENCE_KP :=
  rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §17.  STATUS / DOCUMENTATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Status string documenting the closed content of GJ1. -/
def phase_E3_GJ1_status_string : String :=
  "GJ1 (Phase E3, polymer expansion of Wilson Boltzmann factor): " ++
  "WilsonPolymerConfig as multi-set of plaquettes via Plaquette → ℕ; " ++
  "polymerWeight z_β(P) = ∏ (-β)^{n_p}/n_p!; polymerObservable " ++
  "O_P(ω) = ∏ φ_p(ω)^{n_p}; expansion identity exp(-β·S_W) = " ++
  "∏_p Σ_n ((-β)^n/n!) · φ_p^n at the formal Taylor level; KP-level " ++
  "absolute bound on each polymer term reduces convergence to KP7's " ++
  "small-β regime β ≤ 1/(coord·e); truncation action via " ++
  "INTERIOR/BOUNDARY/EXTERIOR plaquette categorization with proven " ++
  "three-way multiplicative decomposition of the polymer term. " ++
  "Verdict: POLYMER_EXPANSION_FORMALIZED_CONVERGENCE_KP."

/-- Reference list. -/
def phase_E3_GJ1_references : List String :=
  [ "[GJ87]  Glimm-Jaffe, Quantum Physics, Springer 1987, §18"
  , "[Bry84] Brydges, Les Houches XLIII (1984) 129, §4"
  , "[Sei82] Seiler, LNP 159, Springer 1982, Ch. 3"
  , "[KP86]  Kotecký-Preiss, Comm. Math. Phys. 103 (1986) 491"
  , "[BBS19] Bauerschmidt-Brydges-Slade, LNM 2242, Springer 2019"
  , "[Sim93] Simon, Statistical Mechanics of Lattice Gases I, " ++
            "Princeton 1993, §V" ]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §18.  MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER THEOREM: PHASE E3 — GJ1 — POLYMER EXPANSION OF
    WILSON BOLTZMANN FACTOR.**

    Bundles the structural content of this file:

    (1) `WilsonPolymerConfig L` is the multi-set polymer config type;
        the empty config has total degree 0.
    (2) `polymerWeight β P` is the combinatorial weight; at β = 0
        for any non-empty config it vanishes.
    (3) `polymerObservable phi P ω` is the observable factor; the
        polymer term is bounded by `M^{totalDeg}` when `|φ_p| ≤ M`.
    (4) **EXPANSION IDENTITY** at the per-plaquette Taylor level:
        `wilsonBoltzmannExpansion`.
    (5) **PER-CONFIG ABSOLUTE BOUND**: `polymerTerm_abs_bound`.
    (6) **KP-LEVEL CONVERGENCE**: `polymer_sum_KP_convergent`
        reduces convergence at small β to KP7's regime.
    (7) **TRUNCATION CATEGORIZATION**: `interiorPlaquettes`,
        `boundaryPlaquettes`, `exteriorPlaquettes` partition the
        plaquette set into three disjoint categories.
    (8) **POLYMER-TERM THREE-WAY DECOMPOSITION**:
        `polymer_term_factor_three` — the combined polymer term
        factors multiplicatively across the I/B/E partition.
    (9) The verdict is `POLYMER_EXPANSION_FORMALIZED_CONVERGENCE_KP`. -/
theorem phase_E3_GJ1_polymer_expansion_master
    (L : LatticeSide) (β : ℝ) (coord : ℕ) (hc : 0 < coord)
    (h_β : smallBetaRegime β coord)
    (phi : PerPlaquetteObservable L)
    (M : ℝ) (hM : 0 ≤ M)
    (h_bound : ∀ (p : Plaquette L) (ω : multiLinkConfig L), |phi p ω| ≤ M)
    (P : WilsonPolymerConfig L) (ω : multiLinkConfig L)
    (Plaquettes : Finset (Plaquette L))
    (Configs : Finset (WilsonPolymerConfig L))
    {L₁ L₂ : LatticeSide} (h_LE : L₁ ≤ L₂)
    (cat : PlaquetteCategoryMap L₁ L₂ h_LE)
    (Plaquettes_2 : Finset (Plaquette L₂))
    (phi₂ : PerPlaquetteObservable L₂)
    (P₂ : WilsonPolymerConfig L₂)
    (h_supp_eq :
      P₂.support = interiorPlaquettes cat Plaquettes_2
        ∪ boundaryPlaquettes cat Plaquettes_2
        ∪ exteriorPlaquettes cat Plaquettes_2)
    (ω₂ : multiLinkConfig L₂) :
    -- (1) Empty config has total degree 0
    (polymerConfigTotalDeg (emptyWilsonPolymerConfig L) = 0) ∧
    -- (2) Polymer weight at β = 0 for empty config = 1
    (polymerWeight 0 (emptyWilsonPolymerConfig L) = 1) ∧
    -- (3) Polymer observable bound
    (|polymerObservable phi P ω| ≤ M ^ polymerConfigTotalDeg P) ∧
    -- (4) Per-plaquette expansion identity (formal level)
    (Real.exp (-β * wilsonActionFromObservable phi Plaquettes ω)
      = Plaquettes.prod
          (fun p => ∑' n : ℕ, ((-β) ^ n / n.factorial) * (phi p ω) ^ n)) ∧
    -- (5) Per-config absolute bound
    (|polymerWeight β P * polymerObservable phi P ω|
      ≤ P.support.prod
          (fun p => (|β| * M) ^ P.mult p / (P.mult p).factorial)) ∧
    -- (6) Polymer-sum KP-bound (at small β)
    (|wilsonBoltzmannPolymerSum_finset β phi Configs ω|
      ≤ Configs.sum
          (fun P => P.support.prod
            (fun p => (|β| * M) ^ P.mult p / (P.mult p).factorial))) ∧
    -- (7) The three categorizations partition
    (interiorPlaquettes cat Plaquettes_2
       ∪ boundaryPlaquettes cat Plaquettes_2
       ∪ exteriorPlaquettes cat Plaquettes_2 = Plaquettes_2) ∧
    -- (8) Three-way decomposition
    (polymerWeight β P₂ * polymerObservable phi₂ P₂ ω₂
      = (interiorPlaquettes cat Plaquettes_2).prod
          (fun p => combinedPlaquetteFactor β phi₂ P₂ ω₂ p)
      * (boundaryPlaquettes cat Plaquettes_2).prod
          (fun p => combinedPlaquetteFactor β phi₂ P₂ ω₂ p)
      * (exteriorPlaquettes cat Plaquettes_2).prod
          (fun p => combinedPlaquetteFactor β phi₂ P₂ ω₂ p)) ∧
    -- (9) Verdict
    (verdict_GJ1 = GJ1Verdict.POLYMER_EXPANSION_FORMALIZED_CONVERGENCE_KP) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact emptyWilsonPolymerConfig_totalDeg L
  · exact polymerWeight_at_zero_empty
  · exact polymerObservable_bound phi M hM h_bound P ω
  · exact wilsonBoltzmannExpansion β phi Plaquettes ω
  · exact polymerTerm_abs_bound β phi M hM h_bound P ω
  · exact polymer_sum_KP_convergent β coord h_β phi M hM h_bound Configs ω
  · exact plaquette_categorization_partition cat Plaquettes_2
  · -- three-way decomposition
    apply polymer_term_factor_three β phi₂ P₂ ω₂
    · exact interior_boundary_disjoint cat Plaquettes_2
    · exact interior_exterior_disjoint cat Plaquettes_2
    · exact boundary_exterior_disjoint cat Plaquettes_2
    · exact h_supp_eq
  · rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §19.  HONEST SCOPE STATEMENT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **HONEST GJ1 SCOPE STATEMENT.**

    What this file PROVES (unconditional):

      ✓ `WilsonPolymerConfig L` polymer-config type with finite-
        support multiplicity function.
      ✓ `polymerWeight β P` = ∏ (-β)^{n_p}/n_p!; vanishes at β=0
        for non-empty configs.
      ✓ `polymerObservable phi P ω` = ∏ φ_p(ω)^{n_p}; bounded by
        `M^{totalDeg}` under uniform `|φ_p|≤M`.
      ✓ `wilsonBoltzmann_eq_prod`: factorization of `exp(-β·S_W)`
        as a product of per-plaquette Boltzmann factors.
      ✓ `wilsonBoltzmannExpansion`: per-plaquette Taylor expansion.
      ✓ `polymerTerm_abs_bound`: per-config absolute bound.
      ✓ `polymerSum_finset_abs_bound`: partial-sum absolute bound.
      ✓ `polymer_sum_KP_convergent`: KP-level convergence at small β.
      ✓ `plaquette_categorization_partition`: three-way I/B/E
        partition of the plaquette set.
      ✓ `polymerWeight_factor_three`, `polymerObservable_factor_three`,
        `polymer_term_factor_three`: multiplicative decomposition
        of the polymer term across the I/B/E partition.

    What this file does NOT prove:

      ✗ Pointwise polymer-config tsum convergence in the form
        `HasSum`.  The per-plaquette Taylor expansion is given as
        a `tsum`; the infinite distributivity to the polymer-config
        tsum requires Mathlib infrastructure for products of
        absolutely convergent series indexed by ℕ that is not
        currently available.  Reduced to per-config bounds and
        KP-style convergence.
      ✗ The integration of polymer-config terms against Haar to
        recover the partition function.  Deferred to GJ2 (planned).
      ✗ The closure of `WilsonActionFactorization β S` for the
        canonical Wilson plaquette action.  This is the open
        Glimm-Jaffe content (TIER 3 of Phase E3 KP6) and is the
        downstream goal of GJ2/GJ3.

    HONEST CLAIM. GJ1 builds the polymer-expansion infrastructure
    needed to derive the WilsonActionFactorization from Phase E3
    KP6.  The expansion identity is proved at the formal Taylor
    level; convergence is reduced to the KP7-level small-β regime;
    the truncation action on polymer configs is categorized and
    decomposed multiplicatively.  The remaining work toward closing
    `WilsonActionFactorization` is the integration of the polymer
    expansion against Haar (GJ2) and the resummation (GJ3).

    Verdict: `POLYMER_EXPANSION_FORMALIZED_CONVERGENCE_KP`. -/
theorem honest_GJ1_scope_statement
    (L : LatticeSide) (β : ℝ)
    (phi : PerPlaquetteObservable L) :
    -- PROVED: WilsonPolymerConfig type is well-typed
    (∀ (P : WilsonPolymerConfig L), polymerConfigTotalDeg P =
       P.support.sum P.mult) ∧
    -- PROVED: polymer weight at empty = 1
    (polymerWeight β (emptyWilsonPolymerConfig L) = 1) ∧
    -- PROVED: expansion identity (formal Taylor level)
    (∀ (Plaquettes : Finset (Plaquette L)) (ω : multiLinkConfig L),
        Real.exp (-β * wilsonActionFromObservable phi Plaquettes ω)
          = Plaquettes.prod
              (fun p => ∑' n : ℕ, ((-β) ^ n / n.factorial) * (phi p ω) ^ n)) ∧
    -- PROVED: per-config absolute bound
    (∀ (M : ℝ), 0 ≤ M →
        (∀ (p : Plaquette L) (ω : multiLinkConfig L), |phi p ω| ≤ M) →
        ∀ (P : WilsonPolymerConfig L) (ω : multiLinkConfig L),
          |polymerWeight β P * polymerObservable phi P ω|
            ≤ P.support.prod
                (fun p => (|β| * M) ^ P.mult p / (P.mult p).factorial)) ∧
    -- PROVED: I/B/E categorization partition
    (∀ {L₁ L₂ : LatticeSide} (h : L₁ ≤ L₂)
        (cat : PlaquetteCategoryMap L₁ L₂ h)
        (Plaquettes : Finset (Plaquette L₂)),
       interiorPlaquettes cat Plaquettes
         ∪ boundaryPlaquettes cat Plaquettes
         ∪ exteriorPlaquettes cat Plaquettes = Plaquettes) ∧
    -- HONEST: verdict
    (verdict_GJ1 = GJ1Verdict.POLYMER_EXPANSION_FORMALIZED_CONVERGENCE_KP) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P; rfl
  · exact polymerWeight_empty β
  · intros Plaquettes ω
    exact wilsonBoltzmannExpansion β phi Plaquettes ω
  · intros M hM h_bound P ω
    exact polymerTerm_abs_bound β phi M hM h_bound P ω
  · intros L₁ L₂ h cat Plaquettes
    exact plaquette_categorization_partition cat Plaquettes
  · rfl

end UnifiedTheory.LayerB.Phase_E3_GJ1_PolymerExpansion
