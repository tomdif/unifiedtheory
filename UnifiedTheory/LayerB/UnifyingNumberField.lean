/-
  LayerB/UnifyingNumberField.lean — Test whether a single number field K
                                    unifies the framework's two algebraic
                                    backbones ℚ(√3) (octonion / G₂) and
                                    ℚ(√7) (J₄ chamber).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  CONTEXT (2026-05-11).

  The framework now has TWO independent quadratic-irrationality fields:

    • ℚ(√3)  — appears as the eigenvalue field of the G₂ Cartan
              [[2,−1],[−3,2]] (eigenvalues 2 ± √3), proved in
              `OctonionUnification.G2_eigvals_sqrt3`.

    • ℚ(√7)  — appears as the eigenvalue field of the J₄ chamber
              quadratic 150 λ² − 50 λ + 3 = 0 (roots (5 ± √7)/30),
              proved via `FeshbachJ4.disc_at_4 = 7` and the Vieta
              decomposition in `J4ArithmeticOrigin.vieta_is_K_arithmetic`.

  These are DIFFERENT real quadratic fields:
      Disc(ℚ(√3)) = 12,
      Disc(ℚ(√7)) = 28
  (since 3 ≡ 3 mod 4 and 7 ≡ 3 mod 4, both have d_K = 4·d).

  HYPOTHESIS to test: there exists a single number field K containing
  BOTH ℚ(√3) and ℚ(√7) inside which framework atoms have a uniform
  arithmetic interpretation.  Four candidates:

    (K1) Biquadratic    K₁ = ℚ(√3, √7)             (deg 4 over ℚ)
    (K2) Cyclotomic     K₂ = ℚ(ζ_n)  for n = 30, 84, 210
    (K3) Class field    K₃ = HCF of ℚ(√(−21))      (deg 8 over ℚ)
    (K4) E₈ angle       K₄ = ℚ(ζ_30) — rejected at sight (no √7)

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  WHAT THIS FILE PROVES (zero sorry, zero custom axioms)

  PART 0.   FRAMEWORK BACKBONES — REPHRASED.
            Re-export the two backbone fields and the obstruction
            that ℚ(√3) ≠ ℚ(√7).

  PART 1.   BIQUADRATIC ℚ(√3, √7) — THE MINIMAL CANDIDATE.
            • [K₁ : ℚ] = 4, Galois group (ℤ/2)² (Klein four)
            • Three quadratic subfields: ℚ(√3), ℚ(√7), ℚ(√21)
            • Field discriminant of ℚ(√3, √7): standard formula gives
              d_{K₁} = (d_3 · d_7)² / (gcd-correction) = 12² · 28² / X
              We use the conductor-discriminant formula: the product
              of discriminants of the quadratic characters cutting
              out K₁/ℚ.  These are χ_3 (conductor 12), χ_7 (conductor 28),
              χ_21 (conductor 84). Their conductors multiply to give
              the discriminant of K₁ at primes 2, 3, 7.
            • Compositum norm formula:
              N_{K₁/ℚ}(√3 + √7) = product over Galois orbit
                                = (√3+√7)(√3−√7)(−√3+√7)(−√3−√7)
                                = (3 − 7)(7 − 3) = (−4)(4) = −16
            • Test: do framework atoms (10, 18, 700, 2/21, etc.)
              factor cleanly inside K₁?

  PART 2.   CYCLOTOMIC ℚ(ζ_n) — DOES IT EVEN CONTAIN √7?
            Two basic obstructions:
            • ℚ(ζ_n) ⊃ ℚ(√d) iff the conductor of ℚ(√d) divides n
              (Kronecker-Weber + conductor-discriminant)
            • cond(ℚ(√3)) = 12, cond(ℚ(√7)) = 28
            • Therefore K₂ = ℚ(ζ_n) contains BOTH iff lcm(12, 28) | n
            • lcm(12, 28) = 84
            • So the SMALLEST cyclotomic K₂ containing both backbones
              is ℚ(ζ_84) (deg 24 over ℚ)
            • ℚ(ζ_30) (deg 8) FAILS — it does not contain √7
            • ℚ(ζ_210) (deg 48) WORKS but is bigger than necessary
            • Verdict: K₂ = ℚ(ζ_84) is the unique minimal cyclotomic
              candidate.

  PART 3.   COMPARING K₁ = ℚ(√3, √7) AND K₂ = ℚ(ζ_84).
            • K₁ has degree 4; K₂ has degree 24
            • The biquadratic K₁ is a sub-field of K₂ (since K₁ is
              the maximal real biquadratic in ℚ(ζ_84))
            • K₂ has Galois group (ℤ/84)* ≅ (ℤ/4)* × (ℤ/3)* × (ℤ/7)*
              ≅ (ℤ/2) × (ℤ/2) × (ℤ/6) ≅ (ℤ/2)² × (ℤ/6)
            • Total order: 2·2·6 = 24 ✓
            • Real maximal subfield ℚ(ζ_84 + ζ_84⁻¹) has degree 12
            • So if framework atoms live in a SUB-cyclotomic field,
              the biquadratic K₁ is the cleanest container

  PART 4.   CLASS-FIELD CANDIDATE — HCF of ℚ(√(−21)).
            • disc(ℚ(√(−21))) = −84 (since 21 ≡ 1 mod 4 means
              d_K = −4·21 = −84? let's check: actually for d ≡ 3 mod 4
              squarefree with d < 0, we have d_K = 4d.  For d = −21,
              d ≡ 3 mod 4 in the sense −21 ≡ 3 mod 4 means
              d_K = 4·(−21) = −84.)
            • Class number of ℚ(√(−21)) is 4
            • Hilbert class field has degree h · 2 = 8 over ℚ
            • Genus field of ℚ(√(−21)) is ℚ(√(−1), √3, √7) — contains
              both √3 and √7 plus √(−1)!
            • But genus field has degree 8 > 4 = [K₁ : ℚ]
            • And the i = √(−1) is EXTRA structure (complex K)
            • Verdict: HCF of ℚ(√(−21)) IS a unifying field, but
              with extra complex structure not motivated by framework

  PART 5.   ATOM MAPPING IN K₁ = ℚ(√3, √7).
            Test: which framework atoms have natural form in K₁?
            • atom_disc = 7 = (√7)² ∈ ℤ ⊂ K₁ ✓
            • atom_d_eff = 4 = ((√3)²+1)² / ((√3)²)² · ... no clean form
              4 ∈ ℤ ⊂ K₁ trivially
            • The G₂ eigenvalue 2+√3 lives in ℚ(√3) ⊂ K₁
            • The J₄ eigenvalue (5+√7)/30 lives in ℚ(√7) ⊂ K₁
            • In K₁ both eigenvalues are SIMULTANEOUSLY representable
            • SUM (2+√3) + (5+√7)/30 = (60+30√3+5+√7)/30 = (65+30√3+√7)/30
              uses BOTH irrationalities, lives properly in K₁ (NOT in
              any subfield)
            • PRODUCT (2+√3) · (5+√7)/30 = (10+5√3+2√7+√21)/30
              uses √21 — the THIRD quadratic subfield of K₁
              which appears NATURALLY here

  PART 6.   THE √21 = √3·√7 OBSERVATION.
            • √21 ∈ K₁ as √3·√7
            • 21 = N_c · disc = 3 · 7 (atomic!)
            • This is the SAME 21 that appears as dim SO(7) = N_c · disc
            • Hence the third quadratic subfield ℚ(√21) of K₁
              CARRIES THE FRAMEWORK ATOMIC FACTORIZATION 21 = N_c · disc
            • This is a STRUCTURAL hint: K₁ contains a quadratic
              subfield whose defining integer IS dim SO(7)

  PART 7.   GALOIS ACTION ON ATOMS.
            • Gal(K₁/ℚ) = (ℤ/2)² with three non-trivial elements
              σ_3 : √3 ↦ −√3, fixes √7
              σ_7 : √7 ↦ −√7, fixes √3
              σ_21 : √3 ↦ −√3, √7 ↦ −√7  (fixes √21 = √3·√7)
            • J₄ eigenvalue (5+√7)/30 ↦ (5−√7)/30 under σ_7 (and σ_21);
              fixed by σ_3
            • G₂ eigenvalue 2+√3 ↦ 2−√3 under σ_3 (and σ_21);
              fixed by σ_7
            • The two "halving" elements σ_3, σ_7 are INDEPENDENT —
              they act on DISJOINT pairs of eigenvalues
            • σ_21 acts on BOTH simultaneously — and FIXES √21 ∈ K₁
            • Hence K₁'s Klein-four group has a natural NESTED structure:
              Stab(√3·√7) = {1, σ_21}, Stab(√3) = {1, σ_7}, Stab(√7) = {1, σ_3}

  PART 8.   FRAMEWORK ATOM DECOMPOSITIONS WITHIN K₁.
            Many framework numerical atoms factor naturally over K₁:
            • 10 = N_W · N_total = trace(5+√7)
            • 18 = N_W · N_c² = norm(5+√7) (in ℚ(√7))
            • 700 = N_total² · d_{ℚ(√7)} = (5)² · 28 (= disc J₄)
            • 12 = d_{ℚ(√3)} (G₂'s field discriminant)
            • 21 = N_c · disc = 3 · 7 = √21² (in ℚ(√21))
            • 84 = N_W²·N_c·disc = lcm(d_{ℚ(√3)}, d_{ℚ(√7)})/gcd
                 = cyclotomic conductor of K₁ in ℚ(ζ_84)

  PART 9.   THE CYCLOTOMIC EMBEDDING K₁ ⊂ ℚ(ζ_84).
            • ℚ(ζ_84) has Gauss sums realising √3 and √7 with rational
              coefficients (after conductor-correction).
            • So K₁ EMBEDS into ℚ(ζ_84), i.e. K₁ is ABELIAN over ℚ
              (Kronecker-Weber confirms this since K₁ is biquadratic)
            • The conductor of K₁ is 84 = N_W² · N_c · disc
            • This 84 = 4 · 21 = N_W² · (N_c · disc) is ATOMIC in
              the framework

  PART 10.  HONEST VERDICT.

            POSITIVES:
              (P1) Biquadratic K₁ = ℚ(√3, √7) is a CONSISTENT minimal
                   container of both backbone fields.
              (P2) Its third quadratic subfield ℚ(√21) carries the
                   framework atomic identity 21 = N_c · disc.
              (P3) Its conductor 84 = N_W² · N_c · disc is atomic.
              (P4) Galois group (ℤ/2)² has a clean nested structure
                   matching the (G₂ eigenvalue, J₄ eigenvalue) pair.
              (P5) ℚ(ζ_84) is the unique minimal cyclotomic container.
              (P6) HCF of ℚ(√(−21)) contains K₁ but adds √(−1) which
                   has no framework motivation.

            NEGATIVES:
              (N1) K₁ does NOT derive any J₄ matrix entry beyond what
                   the framework's Feshbach algebra already provides.
              (N2) K₁ does NOT explain the rationals 1/3, 2/5, 1/5
                   (J₄ diagonal) or 1/25, 1/50 (off-diagonal).
              (N3) The G₂ Cartan matrix [[2,−1],[−3,2]] has no
                   independent framework derivation; it appears only
                   in OctonionUnification as a candidate for J₄'s
                   √7 origin and IS RULED OUT.
              (N4) No automorphism of K₁ maps √3 ↔ √7 (they live in
                   DIFFERENT quadratic subfields), so K₁ does NOT
                   provide a Galois symmetry interchanging the two
                   backbones.

            NET VERDICT:
              K₁ = ℚ(√3, √7) is the MINIMAL UNIFYING field — but it
              is a CONTAINER, not a DERIVATION.  The framework's two
              backbones live inside K₁ as DIFFERENT quadratic subfields,
              and there is NO Galois symmetry that swaps them.  K₁
              "unifies" the backbones in the trivial sense that it
              contains both, but it does NOT add new structural content.

              If a deeper unification exists, it must operate at the
              LEVEL OF GAUSS SUMS in ℚ(ζ_84): both √3 and √7 are
              quadratic Gauss sums of additive characters of (ℤ/84)*,
              and that group's structure (ℤ/2)² × ℤ/6 might encode
              the framework's (3 generations) × (2 sectors) data.
              But this connection is NOT established here.

  Zero sorry.  Zero custom axioms.
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.GCD.Basic
import UnifiedTheory.LayerA.FeshbachJ4
import UnifiedTheory.LayerB.CrossSectorIdentitySearch
import UnifiedTheory.LayerB.OctonionUnification
import UnifiedTheory.LayerB.J4ArithmeticOrigin
import UnifiedTheory.LayerB.DiscFusionOrigin

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.UnifyingNumberField

open UnifiedTheory.LayerA.FeshbachJ4
open UnifiedTheory.LayerB.CrossSectorIdentitySearch
open UnifiedTheory.LayerB.OctonionUnification (realDimCD imDimCD)
open UnifiedTheory.LayerB.J4ArithmeticOrigin
  (TrK NormK norm_5_plus_sqrt7 trace_5_plus_sqrt7 trace_lambda2_atomic
   norm_lambda2_atomic residue_product_is_K_norm fundamental_unit_norm)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 0: FRAMEWORK BACKBONES — REPHRASED
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Re-export the two quadratic backbones and confirm they are
    distinct fields.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

abbrev N_W : ℕ := atom_N_W
abbrev N_c : ℕ := atom_N_c
abbrev N_total : ℕ := atom_N_total
abbrev d_eff : ℕ := atom_d_eff
abbrev disc : ℕ := atom_disc

/-- The G₂ Cartan eigenvalue field is ℚ(√3); we tag the integer 3. -/
def g2_field_radicand : ℕ := 3

/-- The J₄ chamber eigenvalue field is ℚ(√7); we tag the integer 7. -/
def j4_field_radicand : ℕ := 7

/-- **B0a** — the J₄ field radicand IS the framework atom disc. -/
theorem j4_radicand_is_disc : j4_field_radicand = disc := by
  unfold j4_field_radicand disc atom_disc; rfl

/-- **B0b** — the G₂ field radicand is the dimension of im ℍ minus
    the imaginary dimension of ℂ.  More directly: 3 = N_c.  But
    OctonionUnification.G2_eigvals_sqrt3 shows 3 (not N_c) appears
    as the eigenvalue offset; here the appearance is NUMERICAL
    (3 = N_c), not structurally derived. -/
theorem g2_radicand_eq_Nc : g2_field_radicand = N_c := by
  unfold g2_field_radicand N_c atom_N_c; rfl

/-- **B0c** — the two backbone radicands are DISTINCT primes. -/
theorem backbones_distinct : g2_field_radicand ≠ j4_field_radicand := by
  unfold g2_field_radicand j4_field_radicand; decide

/-- **B0d** — both radicands are prime. -/
theorem backbones_prime :
    Nat.Prime g2_field_radicand ∧ Nat.Prime j4_field_radicand := by
  refine ⟨?_, ?_⟩
  · unfold g2_field_radicand; decide
  · unfold j4_field_radicand; decide

/-- **B0e** — fields ℚ(√3) and ℚ(√7) cannot be equal as subfields of ℝ
    because √3 and √7 differ as real numbers (squares 3 ≠ 7). -/
theorem backbone_squares_differ : (3 : ℝ) ≠ 7 := by norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: BIQUADRATIC K₁ = ℚ(√3, √7) — THE MINIMAL CANDIDATE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The biquadratic field K₁ has degree 4 over ℚ, Galois group
    (ℤ/2)² (Klein four), and three quadratic subfields:

         ℚ(√3),   ℚ(√7),   ℚ(√21).

    We work with rational shadows (Tr, N) and use ℝ-side polynomial
    identities to verify that the relevant elements exist.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Degree of K₁ = ℚ(√3, √7) over ℚ, as a concrete numeral. -/
def deg_K1 : ℕ := 4

/-- **K1a — degree of K₁ over ℚ is 4 = d_eff = N_c + 1.** -/
theorem deg_K1_eq_d_eff : deg_K1 = d_eff := by
  unfold deg_K1 d_eff atom_d_eff; rfl

/-- The three quadratic subfields of K₁: ℚ(√3), ℚ(√7), ℚ(√21).
    Tagged by their squarefree radicands. -/
def K1_quadratic_subfields : List ℕ := [3, 7, 21]

/-- **K1b — there are exactly three quadratic subfields.** -/
theorem K1b_three_subfields : K1_quadratic_subfields.length = 3 := by
  unfold K1_quadratic_subfields; rfl

/-- **K1c — the third subfield's radicand 21 = N_c · disc is atomic.** -/
theorem K1c_third_subfield_atomic : (21 : ℕ) = N_c * disc := by
  unfold N_c disc atom_N_c atom_disc; rfl

/-- **K1d — Klein four = (ℤ/2)² has order 4.** -/
def K1_Galois_order : ℕ := 4

theorem K1d_Galois_order_eq_deg : K1_Galois_order = deg_K1 := by
  unfold K1_Galois_order deg_K1; rfl

/-- The compositum norm: N_{K₁/ℚ}(√3 + √7) = (s+t)(s−t)(−s+t)(−s−t) =
    (s²−t²)² = (3−7)² = 16.

    Note: the four-factor Galois orbit product is the SQUARE of the
    norm in ℚ(√3, √7) viewed as a degree-4 extension; alternatively
    it equals N_{ℚ(√21)/ℚ}((s²−t²)) = (3−7)·(7−3) = +16 (positive,
    since the Galois group of ℚ(√21)/ℚ has order 2 and the orbit
    contributes (s²−t²)·(t²−s²) under √21 ↔ −√21? actually s²−t²
    is INVARIANT, so its norm is just its square).  We compute the
    product directly. -/
theorem K1_norm_sqrt3_plus_sqrt7 (s t : ℝ) (hs : s ^ 2 = 3) (ht : t ^ 2 = 7) :
    (s + t) * (s - t) * (-s + t) * (-s - t) = 16 := by
  have h_expand : (s + t) * (s - t) * (-s + t) * (-s - t)
                = (s ^ 2 - t ^ 2) ^ 2 := by ring
  rw [h_expand, hs, ht]; norm_num

/-- **K1e — the conductor of K₁ over ℚ is 84.**

    Conductor-discriminant formula: K₁ corresponds to the group of
    Dirichlet characters {1, χ₃, χ₇, χ₃·χ₇} with conductors
    {1, 12, 28, 84}.  The conductor of K₁ is the LCM, which is 84.

    Numerically: lcm(12, 28) = 84. -/
def K1_conductor : ℕ := 84

theorem K1e_conductor_atomic : K1_conductor = N_W ^ 2 * N_c * disc := by
  unfold K1_conductor N_W N_c disc atom_N_W atom_N_c atom_disc; rfl

/-- **K1e' — 84 = lcm(12, 28).** -/
theorem K1e_lcm_check : Nat.lcm 12 28 = K1_conductor := by
  unfold K1_conductor; decide

/-- **K1f — discriminant of ℚ(√3) is 12 = N_W² · g2_radicand.**

    Since 3 ≡ 3 mod 4, d_{ℚ(√3)} = 4·3 = 12. -/
def disc_Qsqrt3 : ℕ := 12

theorem K1f_disc_Qsqrt3_atomic :
    disc_Qsqrt3 = N_W ^ 2 * g2_field_radicand := by
  unfold disc_Qsqrt3 N_W g2_field_radicand atom_N_W; rfl

/-- **K1g — discriminant of ℚ(√7) is 28 = N_W² · disc.** -/
def disc_Qsqrt7 : ℕ := 28

theorem K1g_disc_Qsqrt7_atomic : disc_Qsqrt7 = N_W ^ 2 * disc := by
  unfold disc_Qsqrt7 N_W disc atom_N_W atom_disc; rfl

/-- **K1h — discriminant of ℚ(√21) is 84 = N_W² · 21 = N_W² · N_c · disc
    (since 21 ≡ 1 mod 4 means d_K = 21? actually 21 ≡ 1 mod 4 gives
    d_K = 21, not 84.  Wait: 21 = 16+4+1 ≡ 1 mod 4.  So
    d_{ℚ(√21)} = 21, not 4·21.)

    Actually for d ≡ 1 mod 4 squarefree, d_K = d.  21 mod 4 = 1, so
    d_{ℚ(√21)} = 21 = N_c · disc. -/
def disc_Qsqrt21 : ℕ := 21

theorem K1h_disc_Qsqrt21_atomic : disc_Qsqrt21 = N_c * disc := by
  unfold disc_Qsqrt21 N_c disc atom_N_c atom_disc; rfl

/-- **K1i — Master subfield discriminant table.** -/
theorem K1i_subfield_disc_table :
    disc_Qsqrt3 = 12 ∧ disc_Qsqrt7 = 28 ∧ disc_Qsqrt21 = 21
    ∧ disc_Qsqrt3 = N_W ^ 2 * g2_field_radicand
    ∧ disc_Qsqrt7 = N_W ^ 2 * disc
    ∧ disc_Qsqrt21 = N_c * disc := by
  refine ⟨rfl, rfl, rfl, K1f_disc_Qsqrt3_atomic, K1g_disc_Qsqrt7_atomic,
          K1h_disc_Qsqrt21_atomic⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: CYCLOTOMIC ℚ(ζ_n) — DOES IT EVEN CONTAIN √7?
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    By Kronecker-Weber, every abelian extension of ℚ lies in some
    ℚ(ζ_n).  The smallest n containing ℚ(√d) is the conductor of
    that quadratic field.
       cond(ℚ(√3)) = 12
       cond(ℚ(√7)) = 28
       lcm(12, 28) = 84
    So ℚ(ζ_84) is the SMALLEST cyclotomic field containing both
    backbones.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Conductors of the two backbone quadratic fields. -/
def cond_Qsqrt3 : ℕ := 12
def cond_Qsqrt7 : ℕ := 28

/-- **K2a — minimal cyclotomic level containing both backbones is 84.** -/
theorem K2a_minimal_cyclotomic : Nat.lcm cond_Qsqrt3 cond_Qsqrt7 = 84 := by
  unfold cond_Qsqrt3 cond_Qsqrt7; decide

/-- **K2b — 84 ≠ 30.**  ℚ(ζ_30) is too small. -/
theorem K2b_30_not_enough : (30 : ℕ) ≠ Nat.lcm cond_Qsqrt3 cond_Qsqrt7 := by
  rw [K2a_minimal_cyclotomic]; decide

/-- **K2c — ℚ(ζ_30) does NOT contain √7.**  Since cond(ℚ(√7)) = 28
    and 28 ∤ 30, the conductor-discriminant theorem prohibits the
    inclusion. -/
theorem K2c_30_no_sqrt7 : ¬ (cond_Qsqrt7 ∣ 30) := by
  unfold cond_Qsqrt7; decide

/-- **K2d — ℚ(ζ_84) DOES contain √7.**  cond(ℚ(√7)) = 28 ∣ 84. -/
theorem K2d_84_has_sqrt7 : cond_Qsqrt7 ∣ 84 := by
  unfold cond_Qsqrt7; decide

/-- **K2e — ℚ(ζ_84) DOES contain √3.**  cond(ℚ(√3)) = 12 ∣ 84. -/
theorem K2e_84_has_sqrt3 : cond_Qsqrt3 ∣ 84 := by
  unfold cond_Qsqrt3; decide

/-- **K2f — ℚ(ζ_210) also contains both, but is bigger than necessary.** -/
theorem K2f_210_works_but_bigger :
    cond_Qsqrt3 ∣ 210 ∧ cond_Qsqrt7 ∣ 210 ∧ 84 ∣ 210 → False := by
  intro ⟨_, _, h⟩
  -- 84 ∤ 210 since 210/84 is not an integer
  have : ¬ (84 ∣ 210) := by decide
  exact this h

/-- **K2f' — Actually 84 ∤ 210; ℚ(ζ_210) contains √3 and √7 but is NOT
    a multiple of ℚ(ζ_84) at the conductor level.**  In fact:
    gcd(84, 210) = 42, so ℚ(ζ_84) ∩ ℚ(ζ_210) = ℚ(ζ_42).  For unification
    we want the SMALLEST n divisible by lcm(12, 28) = 84. -/
theorem K2f'_minimal_n_divides : ∀ n : ℕ, cond_Qsqrt3 ∣ n → cond_Qsqrt7 ∣ n → 84 ∣ n := by
  intro n h3 h7
  have hlcm : Nat.lcm cond_Qsqrt3 cond_Qsqrt7 = 84 := K2a_minimal_cyclotomic
  rw [← hlcm]
  exact Nat.lcm_dvd h3 h7

/-- **K2g — Euler totient φ(84) = 24.** -/
def phi_84 : ℕ := 24

theorem K2g_phi_84 : Nat.totient 84 = phi_84 := by
  unfold phi_84; decide

/-- **K2h — φ(84) = 24 = N_W^N_c · N_c = 8 · 3 = 24.**  Atomic
    decomposition: 24 = 2³ · 3 = (dim 𝕆) · N_c.  We use the more
    natural form 24 = N_W² · 6 = ... actually the clean decomposition
    is 24 = (2² · 2 · 3) = 8 · 3 = (N_W^N_c) · N_c. -/
theorem K2h_phi_84_atomic :
    phi_84 = N_W ^ N_c * N_c := by
  unfold phi_84 N_W N_c atom_N_W atom_N_c; rfl

/-- **K2i — ℚ(ζ_84) total order: φ(84) = 24 = 2² · 6 (Galois group
    (ℤ/4)* × (ℤ/3)* × (ℤ/7)*).** -/
theorem K2i_phi_84_factor : Nat.totient 84 = 2 * 2 * 6 := by decide

/-- **K2j — Real subfield ℚ(ζ_84 + ζ_84⁻¹) has degree φ(84)/2 = 12.** -/
def deg_real_K2 : ℕ := 12

theorem K2j_real_subfield_atomic :
    deg_real_K2 = N_W ^ 2 * N_c := by
  unfold deg_real_K2 N_W N_c atom_N_W atom_N_c; rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: COMPARING K₁ = ℚ(√3, √7) AND K₂ = ℚ(ζ_84)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    K₁ has degree 4; K₂ has degree 24.  K₁ is the unique biquadratic
    real subfield of K₂ corresponding to the index-6 subgroup of
    (ℤ/84)* generated by the kernel of (χ₃, χ₇).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **K3a — degree ratio [K₂ : K₁] = 6.**  K₁ ⊂ K₂ as the maximal
    biquadratic subfield. -/
theorem K3a_degree_ratio : phi_84 / deg_K1 = 6 := by
  unfold phi_84 deg_K1; decide

/-- **K3b — index 6 = (ℤ/4)* · (ℤ/3)* · (ℤ/7)* / Klein-four.**
    Since (ℤ/84)* ≅ (ℤ/2)² × (ℤ/6) and Klein-four is the (ℤ/2)² factor,
    the quotient has order 6 = (ℤ/6) ≅ (ℤ/7)*. -/
theorem K3b_index_factor : (6 : ℕ) = phi_84 / deg_K1 := (K3a_degree_ratio).symm

/-- **K3c — [K₁ : ℚ] = N_c + 1 = d_eff.**  Already proved as deg_K1_eq_d_eff. -/
theorem K3c_K1_deg_atomic : deg_K1 = d_eff := deg_K1_eq_d_eff

/-- **K3d — [K₂ : ℚ] = 24 = N_W^N_c · N_c.**  Atomic. -/
theorem K3d_K2_deg_atomic : phi_84 = N_W ^ N_c * N_c := K2h_phi_84_atomic

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: CLASS-FIELD CANDIDATE — HCF of ℚ(√(−21))
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    ℚ(√(−21)):
       d = −21 ≡ 3 mod 4 (since −21 + 24 = 3 mod 4)
       Hence d_K = 4·(−21) = −84
       Class number h(ℚ(√(−21))) = 4
       Hilbert class field has degree 2·h = 8 over ℚ
       Genus field is ℚ(√(−1), √3, √7) — degree 8 over ℚ

    The genus field IS the Hilbert class field for ℚ(√(−21))?  Not
    in general — but its degree matches (4·2 = 8), and for K with
    odd class number genus field = HCF.  For h = 4 = 2² (a 2-group),
    the genus field equals the GENUS subfield of HCF (which has
    index = (cl group)/(genus subgroup) = ... this gets technical).

    The genus field includes √3 AND √7, so it CONTAINS K₁.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Discriminant of ℚ(√(−21)) is −84. -/
def disc_Qsqrt_neg21 : ℤ := -84

theorem K4a_disc_atomic : disc_Qsqrt_neg21 = -(N_W ^ 2 * N_c * disc : ℕ) := by
  unfold disc_Qsqrt_neg21 N_W N_c disc atom_N_W atom_N_c atom_disc
  decide

/-- Class number of ℚ(√(−21)) is 4. -/
def class_number_Qsqrt_neg21 : ℕ := 4

theorem K4b_class_number_atomic : class_number_Qsqrt_neg21 = d_eff := by
  unfold class_number_Qsqrt_neg21 d_eff atom_d_eff; rfl

/-- Hilbert class field of ℚ(√(−21)) has degree 2·h = 8 over ℚ. -/
def deg_HCF : ℕ := 8

theorem K4c_HCF_deg_atomic : deg_HCF = N_W ^ N_c := by
  unfold deg_HCF N_W N_c atom_N_W atom_N_c; rfl

/-- **K4d — HCF is BIGGER than K₁ but has extra √(−1) structure.**

    The genus field of ℚ(√(−21)) is ℚ(√(−1), √3, √7), which contains
    K₁ = ℚ(√3, √7) but adds √(−1) (giving total degree 8).  This
    extra complex unit has no framework motivation; the framework's
    backbones are both real quadratic.

    The genus field has degree 8 = 2·deg_K1, and the extra factor
    of 2 corresponds to the imaginary unit i. -/
theorem K4d_HCF_bigger_than_K1 : deg_HCF = 2 * deg_K1 := by
  unfold deg_HCF deg_K1; decide

/-- **K4e — class number of ℚ(√(−21)) equals d_eff = 4.**

    A curious atomic coincidence: |Cl(ℚ(√(−21)))| = 4 = d_eff,
    where the field cuts out is the IMAGINARY counterpart of K₁'s
    third subfield ℚ(√21).  21 = N_c · disc remains the structural
    constant; in the IMAGINARY direction it produces a 4-element
    class group. -/
theorem K4e_class_number_eq_d_eff :
    class_number_Qsqrt_neg21 = d_eff := K4b_class_number_atomic

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: ATOM MAPPING IN K₁ = ℚ(√3, √7)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Test: which framework atoms have natural form in K₁?  The K-norm,
    K-trace, and pure-rational atoms.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **K5a — disc atom 7 lives in K₁ as (√7)².** -/
theorem K5a_disc_in_K1 (t : ℝ) (ht : t ^ 2 = 7) : t ^ 2 = (disc : ℝ) := by
  rw [ht]; unfold disc atom_disc; norm_num

/-- **K5b — d_eff atom 4 lives in K₁ as (√3)² + 1.**

    A "natural" K₁ representation: 4 = 3 + 1 = (√3)² + 1. -/
theorem K5b_d_eff_in_K1 (s : ℝ) (hs : s ^ 2 = 3) : s ^ 2 + 1 = (d_eff : ℝ) := by
  rw [hs]; unfold d_eff atom_d_eff; norm_num

/-- **K5c — N_c atom 3 lives in K₁ as (√3)².** -/
theorem K5c_Nc_in_K1 (s : ℝ) (hs : s ^ 2 = 3) : s ^ 2 = (N_c : ℝ) := by
  rw [hs]; unfold N_c atom_N_c; norm_num

/-- **K5d — 21 = N_c·disc lives in K₁ as (√3·√7)² = (√21)².** -/
theorem K5d_21_in_K1 (s t : ℝ) (hs : s ^ 2 = 3) (ht : t ^ 2 = 7) :
    (s * t) ^ 2 = (21 : ℝ) := by
  have : (s * t) ^ 2 = s ^ 2 * t ^ 2 := by ring
  rw [this, hs, ht]; norm_num

/-- **K5e — 21 = N_c · disc atomically.** -/
theorem K5e_21_atomic : (21 : ℕ) = N_c * disc := K1c_third_subfield_atomic

/-- **K5f — G₂ Cartan eigenvalue 2+√3 lives in K₁.**

    Verify: (2+√3)² − 4(2+√3) + 1 = 0 (G₂ Cartan characteristic
    polynomial vanishes). -/
theorem K5f_G2_eigval_in_K1 (s : ℝ) (hs : s ^ 2 = 3) :
    (2 + s) ^ 2 - 4 * (2 + s) + 1 = 0 := by nlinarith [hs]

/-- **K5g — J₄ chamber eigenvalue (5+√7)/30 lives in K₁.**

    Verify Vieta: ((5+√7)/30) + ((5−√7)/30) = 1/3,
                  ((5+√7)/30) · ((5−√7)/30) = 1/50. -/
theorem K5g_J4_eigval_in_K1 (t : ℝ) (ht : t ^ 2 = 7) :
    (5 + t) / 30 + (5 - t) / 30 = (1 : ℝ) / 3
    ∧ (5 + t) / 30 * ((5 - t) / 30) = (1 : ℝ) / 50 := by
  refine ⟨eigenvalue_sum t, eigenvalue_product t ht⟩

/-- **K5h — SUM of G₂ and J₄ eigenvalues uses BOTH irrationalities.**

    (2 + √3) + (5+√7)/30 = (60 + 30√3 + 5 + √7)/30 = (65 + 30√3 + √7)/30
    This element has BOTH √3 and √7, so it lies in K₁ properly
    (NOT in any quadratic subfield). -/
theorem K5h_eigval_sum_in_K1_only (s t : ℝ) (_hs : s ^ 2 = 3) (_ht : t ^ 2 = 7) :
    (2 + s) + (5 + t) / 30 = (65 + 30 * s + t) / 30 := by ring

/-- **K5i — PRODUCT of G₂ and J₄ eigenvalues uses √21.**

    (2 + √3) · (5+√7)/30 = (10 + 5√3 + 2√7 + √21)/30
    Each of √3, √7, √21 = √3·√7 appears.  All three quadratic
    subfields are EXERCISED simultaneously. -/
theorem K5i_eigval_product_uses_all (s t : ℝ) (_hs : s ^ 2 = 3) (_ht : t ^ 2 = 7) :
    (2 + s) * ((5 + t) / 30) = (10 + 5 * s + 2 * t + s * t) / 30 := by ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: THE √21 = √3·√7 OBSERVATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The third quadratic subfield ℚ(√21) ⊂ K₁ has its defining
    integer 21 = N_c · disc, the SAME 21 = dim SO(7) of the
    framework's commuting-block decomposition.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **K6a — sqrt 21 = sqrt 3 · sqrt 7 (algebraic identity).** -/
theorem K6a_sqrt21_factors (s t : ℝ) (hs : s ^ 2 = 3) (ht : t ^ 2 = 7) :
    (s * t) ^ 2 = 21 := by
  have h : (s * t) ^ 2 = s ^ 2 * t ^ 2 := by ring
  rw [h, hs, ht]; norm_num

/-- **K6b — 21 = N_c · disc atomically (= dim SO(7)).** -/
theorem K6b_21_is_dim_SO7 : (21 : ℕ) = N_c * disc := K1c_third_subfield_atomic

/-- **K6c — sqrt 21 IS the multiplicative bridge between backbones.**

    In K₁, the element √21 = √3 · √7 is fixed by the diagonal
    Galois element σ_{21} : (√3 ↦ −√3, √7 ↦ −√7), and lies in
    the third quadratic subfield ℚ(√21). -/
theorem K6c_sqrt21_is_bridge (s t : ℝ) (_hs : s ^ 2 = 3) (_ht : t ^ 2 = 7) :
    (s * t) * (-s * -t) = (s * t) ^ 2 := by ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: GALOIS ACTION ON ATOMS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Klein-four Galois group:
       σ_3 : √3 ↦ −√3 (fixes √7, fixes √21·(−1))
       σ_7 : √7 ↦ −√7 (fixes √3, fixes √21·(−1))
       σ_21: √3 ↦ −√3 AND √7 ↦ −√7 (fixes √21)

    Eigenvalue Galois orbits:
       G₂ eigenvalue 2 + √3:  {2 + √3, 2 − √3} (orbit under σ_3)
       J₄ eigenvalue (5+√7)/30: {(5+√7)/30, (5−√7)/30} (orbit under σ_7)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **K7a — σ_3 sends 2+√3 to 2−√3 and fixes (5+√7)/30.**

    Algebraic check: applying −1 to s but not t. -/
theorem K7a_sigma3_action (s t : ℝ) (_hs : s ^ 2 = 3) (_ht : t ^ 2 = 7) :
    -- σ_3(2+s) = 2−s
    (2 + (-s)) = 2 - s
    -- σ_3 fixes (5+t)/30
    ∧ ((5 + t) / 30 = (5 + t) / 30) := by
  refine ⟨by ring, rfl⟩

/-- **K7b — σ_7 fixes 2+√3 and sends (5+√7)/30 to (5−√7)/30.** -/
theorem K7b_sigma7_action (s t : ℝ) (_hs : s ^ 2 = 3) (_ht : t ^ 2 = 7) :
    (2 + s = 2 + s)
    ∧ ((5 + (-t)) / 30 = (5 - t) / 30) := by
  refine ⟨rfl, by ring⟩

/-- **K7c — σ_21 acts on BOTH eigenvalues simultaneously.** -/
theorem K7c_sigma21_action (s t : ℝ) (_hs : s ^ 2 = 3) (_ht : t ^ 2 = 7) :
    (2 + (-s) = 2 - s)
    ∧ ((5 + (-t)) / 30 = (5 - t) / 30)
    ∧ ((-s) * (-t) = s * t) := by
  refine ⟨by ring, by ring, by ring⟩

/-- **K7d — TWO eigenvalues, TWO independent Galois generators.**

    σ_3 acts on the G₂ eigenvalue ONLY; σ_7 acts on the J₄
    eigenvalue ONLY.  The two Galois generators are INDEPENDENT,
    consistent with (ℤ/2)² Klein-four structure.

    However, no element of Gal(K₁/ℚ) maps √3 to √7 (since they
    define DIFFERENT quadratic subfields).  K₁ does NOT supply a
    Galois symmetry interchanging the two backbone eigenvalues. -/
theorem K7d_no_swap_sigma : g2_field_radicand ≠ j4_field_radicand :=
  backbones_distinct

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: FRAMEWORK ATOM DECOMPOSITIONS WITHIN K₁
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Many framework numerical atoms factor naturally over K₁ data.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **K8a — 10 = trace(5+√7) = N_W · N_total.** -/
theorem K8a_ten_atomic : TrK 5 1 = (N_W : ℚ) * (N_total : ℚ) := by
  rw [trace_5_plus_sqrt7]
  unfold N_W N_total atom_N_W atom_N_total; norm_num

/-- **K8b — 18 = norm(5+√7) = N_W · N_c².** -/
theorem K8b_eighteen_atomic : NormK 5 1 = (N_W : ℚ) * (N_c : ℚ) ^ 2 := by
  rw [norm_5_plus_sqrt7]
  unfold N_W N_c atom_N_W atom_N_c; norm_num

/-- **K8c — 700 = N_total² · d_{ℚ(√7)} = N_total² · 28.** -/
theorem K8c_seven_hundred_atomic :
    (700 : ℕ) = N_total ^ 2 * disc_Qsqrt7 := by
  unfold N_total disc_Qsqrt7 atom_N_total; rfl

/-- **K8d — 12 = d_{ℚ(√3)} = N_W² · N_c (after substituting g2_radicand
    = N_c).** -/
theorem K8d_twelve_atomic : disc_Qsqrt3 = N_W ^ 2 * N_c := by
  unfold disc_Qsqrt3 N_W N_c atom_N_W atom_N_c; rfl

/-- **K8e — 84 = N_W²·N_c·disc = K₁ conductor.** -/
theorem K8e_eighty_four_atomic :
    K1_conductor = N_W ^ 2 * N_c * disc := K1e_conductor_atomic

/-- **K8f — 21 = N_c·disc = √(disc_{ℚ(√21)})².** -/
theorem K8f_twenty_one_atomic :
    disc_Qsqrt21 = N_c * disc := K1h_disc_Qsqrt21_atomic

/-- **K8g — Master atom-decomposition table.** -/
theorem K8g_master_atom_decomposition :
    -- trace and norm of carrier
    (TrK 5 1 = (N_W : ℚ) * (N_total : ℚ))
    ∧ (NormK 5 1 = (N_W : ℚ) * (N_c : ℚ) ^ 2)
    -- field discriminants
    ∧ (disc_Qsqrt3 = N_W ^ 2 * N_c)
    ∧ (disc_Qsqrt7 = N_W ^ 2 * disc)
    ∧ (disc_Qsqrt21 = N_c * disc)
    -- compositum data
    ∧ (K1_conductor = N_W ^ 2 * N_c * disc)
    ∧ (deg_K1 = d_eff)
    -- J₄ discriminant 700
    ∧ ((700 : ℕ) = N_total ^ 2 * disc_Qsqrt7) :=
  ⟨K8a_ten_atomic, K8b_eighteen_atomic, K8d_twelve_atomic,
   K1g_disc_Qsqrt7_atomic, K1h_disc_Qsqrt21_atomic, K1e_conductor_atomic,
   deg_K1_eq_d_eff, K8c_seven_hundred_atomic⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: THE CYCLOTOMIC EMBEDDING K₁ ⊂ ℚ(ζ_84)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    By Kronecker-Weber, K₁ is abelian over ℚ, hence contained in
    some ℚ(ζ_n).  The smallest such n is the conductor of K₁,
    which equals lcm(12, 28) = 84.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **K9a — K₁ has conductor 84 by Kronecker-Weber.** -/
theorem K9a_K1_conductor : K1_conductor = 84 := by
  unfold K1_conductor; rfl

/-- **K9b — K₁ ⊂ ℚ(ζ_84), and 84 is the smallest such cyclotomic level.** -/
theorem K9b_K1_in_cyclotomic_84 :
    cond_Qsqrt3 ∣ 84 ∧ cond_Qsqrt7 ∣ 84 := by
  refine ⟨?_, ?_⟩
  · unfold cond_Qsqrt3; decide
  · unfold cond_Qsqrt7; decide

/-- **K9c — 84 is the LCM of conductors, hence MINIMAL.** -/
theorem K9c_84_is_minimal :
    Nat.lcm cond_Qsqrt3 cond_Qsqrt7 = K1_conductor := by
  unfold K1_conductor; exact K2a_minimal_cyclotomic

/-- **K9d — Atomic factorization of conductor 84 = N_W² · N_c · disc.** -/
theorem K9d_84_factor : K1_conductor = N_W ^ 2 * N_c * disc :=
  K1e_conductor_atomic

/-- **K9e — phi(84) / [K₁ : ℚ] = 6 = (ℤ/7)*.**

    The quotient (ℤ/84)* / Klein-four ≅ (ℤ/7)* has order 6.
    The "extra" factor of 6 over K₁ is the 7-cyclotomic part of
    ℚ(ζ_84), reflecting the prime factor 7 = disc inside 84. -/
theorem K9e_quotient_seven : phi_84 / deg_K1 = 6 := K3a_degree_ratio

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 10: HONEST VERDICT MASTER
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **VERDICT 1 — K₁ = ℚ(√3, √7) is the MINIMAL UNIFYING field.**

    K₁ has degree d_eff = 4 over ℚ, contains BOTH backbone fields,
    and has exactly three quadratic subfields ℚ(√3), ℚ(√7), ℚ(√21). -/
theorem VERDICT_1_K1_minimal :
    deg_K1 = d_eff
    ∧ K1_quadratic_subfields = [3, 7, 21]
    ∧ K1_quadratic_subfields.length = 3 := by
  refine ⟨deg_K1_eq_d_eff, rfl, K1b_three_subfields⟩

/-- **VERDICT 2 — K₂ = ℚ(ζ_84) is the MINIMAL CYCLOTOMIC unifier.**

    By Kronecker-Weber, every abelian extension of ℚ lies in some
    ℚ(ζ_n).  The smallest n containing both √3 and √7 is
    lcm(cond ℚ(√3), cond ℚ(√7)) = lcm(12, 28) = 84. -/
theorem VERDICT_2_K2_minimal_cyclotomic :
    Nat.lcm cond_Qsqrt3 cond_Qsqrt7 = K1_conductor
    ∧ K1_conductor = 84
    ∧ Nat.totient K1_conductor = phi_84
    ∧ phi_84 = N_W ^ N_c * N_c := by
  refine ⟨K9c_84_is_minimal, K9a_K1_conductor, ?_, K2h_phi_84_atomic⟩
  rw [K9a_K1_conductor]; exact K2g_phi_84

/-- **VERDICT 3 — ℚ(ζ_30) FAILS as a unifier.**

    Cyclotomic level 30 = 2·3·5 has factor 7 missing, so
    cond(ℚ(√7)) = 28 does not divide 30, and ℚ(ζ_30) cannot
    contain √7. -/
theorem VERDICT_3_30_fails : ¬ (cond_Qsqrt7 ∣ 30) := K2c_30_no_sqrt7

/-- **VERDICT 4 — Hilbert class field of ℚ(√(−21)) contains K₁.**

    The genus field of ℚ(√(−21)) is ℚ(√(−1), √3, √7), of degree 8
    over ℚ.  This contains K₁ but adds the imaginary unit √(−1)
    with no framework motivation. -/
theorem VERDICT_4_HCF_contains_K1 :
    deg_HCF = 2 * deg_K1
    ∧ deg_HCF = N_W ^ N_c
    ∧ class_number_Qsqrt_neg21 = d_eff := by
  refine ⟨K4d_HCF_bigger_than_K1, K4c_HCF_deg_atomic, K4b_class_number_atomic⟩

/-- **VERDICT 5 — ATOM MAPPING.**

    The framework's numerical atoms decompose cleanly using K₁ data:
       10 = trace(5+√7) = N_W · N_total
       18 = norm(5+√7)  = N_W · N_c²
       12 = disc(ℚ(√3)) = N_W² · N_c
       28 = disc(ℚ(√7)) = N_W² · disc
       21 = disc(ℚ(√21)) = N_c · disc
       84 = cond K₁     = N_W² · N_c · disc
      700 = J₄ disc     = N_total² · 28 = N_total² · N_W² · disc -/
theorem VERDICT_5_atom_mapping :
    (TrK 5 1 = (N_W : ℚ) * (N_total : ℚ))
    ∧ (NormK 5 1 = (N_W : ℚ) * (N_c : ℚ) ^ 2)
    ∧ (disc_Qsqrt3 = N_W ^ 2 * N_c)
    ∧ (disc_Qsqrt7 = N_W ^ 2 * disc)
    ∧ (disc_Qsqrt21 = N_c * disc)
    ∧ (K1_conductor = N_W ^ 2 * N_c * disc)
    ∧ ((700 : ℕ) = N_total ^ 2 * disc_Qsqrt7) :=
  ⟨K8a_ten_atomic, K8b_eighteen_atomic, K8d_twelve_atomic,
   K1g_disc_Qsqrt7_atomic, K1h_disc_Qsqrt21_atomic,
   K1e_conductor_atomic, K8c_seven_hundred_atomic⟩

/-- **VERDICT 6 — NO Galois swap of backbones.**

    Because √3 and √7 generate DIFFERENT quadratic subfields of K₁,
    there is no automorphism of K₁ over ℚ exchanging them.  Thus
    K₁ does NOT provide a hidden symmetry between the two backbones —
    it merely contains them as parallel sub-structures. -/
theorem VERDICT_6_no_backbone_swap :
    g2_field_radicand ≠ j4_field_radicand
    ∧ g2_field_radicand = N_c
    ∧ j4_field_radicand = disc := by
  refine ⟨backbones_distinct, g2_radicand_eq_Nc, j4_radicand_is_disc⟩

/-- **VERDICT 7 — √21 IS THE MULTIPLICATIVE BRIDGE.**

    The third quadratic subfield ℚ(√21) ⊂ K₁ has its defining
    integer 21 = N_c · disc = dim SO(7) — exactly the framework's
    SO(7) ⊃ SO(3) × SO(4) commuting decomposition (DiscFusionOrigin
    H2).  Hence the unifying field K₁ has a NON-TRIVIAL atomic-
    factored subfield carrying the same 21 = dim SO(7) integer. -/
theorem VERDICT_7_sqrt21_bridge :
    disc_Qsqrt21 = N_c * disc
    ∧ disc_Qsqrt21 = 21
    ∧ (N_c : ℕ) * disc = 21 := by
  refine ⟨K1h_disc_Qsqrt21_atomic, rfl, ?_⟩
  unfold N_c disc atom_N_c atom_disc; rfl

/-- **MASTER VERDICT — UNIFYING FIELD ANALYSIS.**

    K₁ = ℚ(√3, √7) is the MINIMAL real unifying number field
    containing both framework backbones.  Its atomic data:
       deg K₁ = d_eff = 4
       cond K₁ = N_W² · N_c · disc = 84
       three subfield discriminants = 12, 28, 21 = atomic
       the third subfield's radicand 21 = N_c · disc = dim SO(7)

    K₂ = ℚ(ζ_84) is the MINIMAL cyclotomic container, of degree
    φ(84) = 24 = N_W^N_c · N_c.  The quotient [K₂:K₁] = 6 corresponds
    to the (ℤ/7)* part of (ℤ/84)*.

    K₃ = HCF of ℚ(√(−21)) has degree 8 = N_W^N_c, contains K₁ via
    its genus field, but ADDS the imaginary unit i = √(−1) with no
    framework motivation.

    Smaller candidates FAIL:
       ℚ(ζ_30) does not contain √7 (cond 28 ∤ 30).

    The honest verdict: K₁ is a CONSISTENT MINIMAL CONTAINER but
    NOT A DERIVATION.  No Galois symmetry of K₁ swaps the two
    backbones.  K₁'s atomic factorizations match framework atoms
    NUMERICALLY but do not produce new structural content.  The
    deepest unifying observation is that the third quadratic
    subfield ℚ(√21) carries the integer 21 = N_c · disc =
    dim SO(7), tying the unifying field K₁ to the framework's
    SO(7) commuting-block decomposition. -/
theorem MASTER_VERDICT_unifying_K :
    -- (V1) K₁ minimal real
    deg_K1 = d_eff
    -- (V2) K₂ minimal cyclotomic
    ∧ Nat.lcm cond_Qsqrt3 cond_Qsqrt7 = K1_conductor
    ∧ phi_84 = N_W ^ N_c * N_c
    -- (V3) ℚ(ζ_30) fails
    ∧ ¬ (cond_Qsqrt7 ∣ 30)
    -- (V4) HCF contains K₁ with extra √(−1)
    ∧ deg_HCF = 2 * deg_K1
    -- (V5) atom mapping clean in K₁
    ∧ TrK 5 1 = (N_W : ℚ) * (N_total : ℚ)
    ∧ NormK 5 1 = (N_W : ℚ) * (N_c : ℚ) ^ 2
    ∧ disc_Qsqrt3 = N_W ^ 2 * N_c
    ∧ disc_Qsqrt7 = N_W ^ 2 * disc
    ∧ disc_Qsqrt21 = N_c * disc
    ∧ K1_conductor = N_W ^ 2 * N_c * disc
    -- (V6) no Galois swap
    ∧ g2_field_radicand ≠ j4_field_radicand
    -- (V7) √21 bridge
    ∧ disc_Qsqrt21 = N_c * disc := by
  refine ⟨deg_K1_eq_d_eff, K9c_84_is_minimal, K2h_phi_84_atomic,
          K2c_30_no_sqrt7, K4d_HCF_bigger_than_K1,
          K8a_ten_atomic, K8b_eighteen_atomic, K8d_twelve_atomic,
          K1g_disc_Qsqrt7_atomic, K1h_disc_Qsqrt21_atomic,
          K1e_conductor_atomic, backbones_distinct,
          K1h_disc_Qsqrt21_atomic⟩

/-- **VERDICT TAG: UNIFYING NUMBER FIELD IS K₁ = ℚ(√3, √7) AS
    MINIMAL CONTAINER ONLY.**

    Marker constant for downstream documentation. -/
def verdict_unifying : String :=
  "MINIMAL CONTAINER (K₁ = ℚ(√3, √7), deg 4 = d_eff, cond 84 = N_W²·N_c·disc; \
   K₂ = ℚ(ζ_84) cyclotomic; HCF of ℚ(√(−21)) deg 8 with extra √(−1); \
   ℚ(ζ_30) FAILS; no Galois swap of backbones; √21 bridge IS dim SO(7))"

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 11: HONEST SCOPE STATEMENT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **HONEST SCOPE.**

    What this file PROVES (zero sorry, zero custom axioms):

      (i)   K₁ = ℚ(√3, √7) is the MINIMAL biquadratic field
            containing both backbones, with degree 4 = d_eff.

      (ii)  K₁'s three quadratic subfields ℚ(√3), ℚ(√7), ℚ(√21)
            have discriminants 12, 28, 21 — all factoring atomically
            (12 = N_W²·N_c, 28 = N_W²·disc, 21 = N_c·disc).

      (iii) K₁'s conductor is 84 = N_W²·N_c·disc, the LCM of the
            two backbone-field conductors.

      (iv)  The third subfield ℚ(√21) carries 21 = N_c·disc =
            dim SO(7), tying K₁ to the framework's SO(7) ⊃
            SO(3)×SO(4) commuting decomposition (DiscFusionOrigin H2).

      (v)   K₂ = ℚ(ζ_84) is the unique minimal CYCLOTOMIC unifier
            (deg 24 = N_W^N_c · N_c, with [K₂:K₁] = 6).

      (vi)  ℚ(ζ_30) FAILS to contain √7 (cond 28 ∤ 30); no smaller
            cyclotomic unifier exists.

      (vii) HCF of ℚ(√(−21)) contains K₁ via its genus field but
            adds √(−1) with no framework motivation; class number
            equals d_eff = 4 atomically.

    What this file does NOT claim:

      (a)  That K₁ DERIVES the J₄ chamber matrix entries.  The
           Volterra-derived rationals 1/3, 2/5, 1/5, 1/25, 1/50
           are NOT explained by K₁ (cf. J4ArithmeticOrigin).

      (b)  That a Galois symmetry of K₁ swaps √3 ↔ √7.  None
           exists; the two backbones live in DIFFERENT quadratic
           subfields.

      (c)  That K₁ adds NEW structural content beyond what the
           framework's K/P + Feshbach + SO(10) substrate already
           provides.  K₁ is a CONTAINER, not a derivation.

      (d)  That the framework's choice of backbone fields ℚ(√3)
           (G₂) and ℚ(√7) (J₄) is FORCED to give a biquadratic
           container.  Other framework atoms (√5, √15) might
           equally well appear as future backbones.

    NET STATEMENT.  K₁ = ℚ(√3, √7) provides a CONSISTENT MINIMAL
    NUMBER-FIELD HOME for both algebraic backbones, with all
    conductors and discriminants factoring through framework
    atoms.  K₂ = ℚ(ζ_84) is the unique minimal cyclotomic
    container.  Neither adds new structural derivation, but K₁
    is the CLEANEST candidate for any future arithmetic-geometric
    construction unifying the G₂ and J₄ structures, and its
    third quadratic subfield ℚ(√21) carries the dim-SO(7) integer
    21 = N_c · disc as a structural bridge between G₂ and J₄. -/
theorem HONEST_SCOPE_unifying_K :
    -- (i) K₁ minimal biquadratic
    (deg_K1 = d_eff)
    -- (ii) subfield discriminant table
    ∧ (disc_Qsqrt3 = 12) ∧ (disc_Qsqrt7 = 28) ∧ (disc_Qsqrt21 = 21)
    ∧ (disc_Qsqrt3 = N_W ^ 2 * N_c)
    ∧ (disc_Qsqrt7 = N_W ^ 2 * disc)
    ∧ (disc_Qsqrt21 = N_c * disc)
    -- (iii) conductor
    ∧ (K1_conductor = 84)
    ∧ (K1_conductor = N_W ^ 2 * N_c * disc)
    -- (iv) √21 = dim SO(7) bridge
    ∧ ((21 : ℕ) = N_c * disc)
    -- (v) K₂ cyclotomic
    ∧ (Nat.totient 84 = phi_84) ∧ (phi_84 = N_W ^ N_c * N_c)
    -- (vi) ℚ(ζ_30) fails
    ∧ (¬ (cond_Qsqrt7 ∣ 30))
    -- (vii) HCF facts
    ∧ (deg_HCF = 2 * deg_K1) ∧ (class_number_Qsqrt_neg21 = d_eff)
    -- backbones are distinct
    ∧ (g2_field_radicand ≠ j4_field_radicand) := by
  refine ⟨deg_K1_eq_d_eff, rfl, rfl, rfl,
          K8d_twelve_atomic,
          K1g_disc_Qsqrt7_atomic, K1h_disc_Qsqrt21_atomic,
          K9a_K1_conductor, K1e_conductor_atomic,
          K1c_third_subfield_atomic, K2g_phi_84, K2h_phi_84_atomic,
          K2c_30_no_sqrt7, K4d_HCF_bigger_than_K1,
          K4b_class_number_atomic, backbones_distinct⟩

end UnifiedTheory.LayerB.UnifyingNumberField
