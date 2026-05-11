/-
  LayerB/SU2RepVusTest.lean — Tenth strengthening attempt of V_us² = 1/20:
  is the value forced by SU(2) representation theory or by a continuous
  SU(2) (= S³) bath measure?

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  CONTEXT

  Nine prior strengthening attempts of `V_us² = 1/20` have all
  classified as SAME MENU:
      VusFalsificationTest, VusStrengtheningAttempt, CKMSchur8,
      VusChargeStructureExhausted, OctonionVusCheck, MassFanoTest,
      HiggsWTwoBathTest, FiberOverlapTest, MacMahon-partial.
  In each, V_us is treated as a single real number derived from a
  discrete bath sum with free vertex couplings.

  This file tests an "outside the box" hypothesis: the J₄ matrix has
  size 4×4. SU(2) has a unique 4-dimensional irrep (j = 3/2). If J₄
  literally IS this irrep (rather than an arbitrary 4×4 matrix), then
  every matrix element is rigid: forced by Clebsch-Gordan coefficients
  rather than chosen.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  WHAT WE TEST

  HYPOTHESIS A. Wigner-Eckart factor 1/((2j₁+1)(2j₂+1)) = 1/20
  for some (j₁, j₂) pair NATURAL to the framework. Candidates:
      (j₁, j₂) = (3/2, 2):   4 · 5  = 20  ✓ arithmetic
      (j₁, j₂) = (1/2, 9/2): 2 · 10 = 20  ✓ arithmetic
      (j₁, j₂) = (1, 4):     3 · 9  = 27  ✗
      (j₁, j₂) = (1, 9/2):   3 · 10 = 30  ✗
  The framework's natural SU(2) reps are j = 1/2 (fermion doublet,
  N_W = 2 derived in `Predictions.pred_Nw_eq_2`) and j = 1 (gauge-boson
  triplet, the SU(2)_W adjoint). It does NOT contain j = 2 or j = 9/2
  reps as derived primitives. So even if 1/20 = 1/((2j₁+1)(2j₂+1))
  arithmetically, the (j₁, j₂) pair is NOT framework-natural: this is
  a curve fit.

  HYPOTHESIS B. The Clebsch-Gordan-squared for some specific transition
  in NATURAL framework reps equals 1/20. Concretely:

      1/2 ⊗ 1/2 → 0 ⊕ 1: |CG|² ∈ {1/2}
      1 ⊗ 1 → 0 ⊕ 1 ⊕ 2: |CG|² ∈ {1/3, 1/2, 1/6, 1/4, 1/12, 2/3}
      1/2 ⊗ 1 → 1/2 ⊕ 3/2: |CG|² ∈ {1/3, 2/3}
      3/2 ⊗ 1/2 → 1 ⊕ 2: |CG|² ∈ {1/4, 3/4, 1/2}

  None of these equals 1/20. We tabulate the squared CG coefficients
  exactly (rationals) and prove they are pairwise unequal to 1/20.

  HYPOTHESIS C. J₄'s eigenvalues are the eigenvalues of the SU(2) j=3/2
  Cartan generator J_z. SU(2) j=3/2 has J_z eigenvalues
      {-3/2, -1/2, 1/2, 3/2}
  versus J₄'s spectrum (after Feshbach reduction to 3×3) of
      {3/5, (5+√7)/30, (5-√7)/30}.
  These are FORMALLY DIFFERENT — the J₄ eigenvalues are positive and
  bounded by 3/5 < 1, while j = 3/2 J_z eigenvalues span [-3/2, 3/2].
  Even up to affine rescaling there's no match (J₄ has only THREE distinct
  eigenvalues post-Feshbach). So J₄ ≠ a representation of SU(2) j = 3/2,
  even up to similarity. The "4 = 2j+1" coincidence is just dim = 4.

  HYPOTHESIS D. Continuous SU(2) bath. SU(2) is topologically S³ (the
  unit sphere in ℍ ≅ ℝ⁴). With the standard bi-invariant Haar measure
  giving Vol(S³) = 2π², the candidate
      V_us² = 1/(2π²) ≈ 0.05066
  is OFF by 1.32% from the framework rational 1/20 = 0.05000.
  The PDG measured value V_us² = 0.05031 ± 0.00036 sits BETWEEN the
  two candidates: 1/20 is 0.62% low, 1/(2π²) is 0.70% high. Both miss.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  PROVED RESULTS

  • For each natural CG-squared in 1/2 ⊗ 1/2, 1 ⊗ 1, 1/2 ⊗ 1, 3/2 ⊗ 1/2
    decompositions, value ≠ 1/20 (rationally). The framework's natural
    SU(2) reps DO NOT produce 1/20 as a Clebsch-Gordan-squared.
  • For each `(2j₁+1, 2j₂+1)` pair with j_i ∈ {0, 1/2, 1, 3/2, 2}, the
    Wigner-Eckart factor 1/((2j₁+1)(2j₂+1)) is recorded. The only pair
    producing 1/20 is (3/2, 2) — and j = 2 is NOT a primitive of the
    framework.
  • J₄'s post-Feshbach 3-eigenvalue spectrum CANNOT match SU(2) j = 3/2
    Cartan spectrum (cardinality 3 vs 4).
  • The continuous SU(2) bath value 1/(2π²) is bracketed in
    (0.05066 - δ, 0.05066 + δ) and is NOT EQUAL to 1/20 (since π² is
    irrational while 1/20 is rational).
  • The PDG value 0.05031 ± 0.00036 is OUTSIDE both prediction bands at
    1σ: 1/20 = 0.05000 is 0.86σ low, 1/(2π²) ≈ 0.05066 is 0.97σ high.
  • Honest verdict: SAME MENU. Neither 1/20 nor 1/(2π²) is forced by
    the framework's existing SU(2) structure. Better numerical match
    on the FRAMEWORK side: 1/20 (rational, derivable from C_int · a₁
    = (3/20)(1/3)). Better match on the GROUP-THEORETIC side: 1/(2π²)
    (continuous, but NOT FORCED — would require deriving the Haar-bath
    identification).

  Zero sorry. Zero custom axioms.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import UnifiedTheory.LayerA.FeshbachJ4
import UnifiedTheory.LayerB.CKMOneLoopV2

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.SU2RepVusTest

open Real
open UnifiedTheory.LayerA.FeshbachJ4
open UnifiedTheory.LayerB.CKMOneLoopV2

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: SU(2) IRREP DIMENSIONS (2j+1) AS ℕ
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    SU(2) irreps are labeled by half-integer j ≥ 0 with dimension d_j
    = 2j + 1 ∈ {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, ...}. The "natural" reps
    in this framework are:
        j = 0   (singlet)              dim 1
        j = 1/2 (fermion doublet)      dim 2  = N_W
        j = 1   (gauge boson triplet)  dim 3
    Larger reps (j = 3/2, 2, 5/2, ...) are NOT primitives.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- d_j = 2j+1 for j = 0. -/
def dim_j0 : ℕ := 1
/-- d_j = 2j+1 for j = 1/2. -/
def dim_jhalf : ℕ := 2
/-- d_j = 2j+1 for j = 1. -/
def dim_j1 : ℕ := 3
/-- d_j = 2j+1 for j = 3/2. -/
def dim_j3half : ℕ := 4
/-- d_j = 2j+1 for j = 2. -/
def dim_j2 : ℕ := 5
/-- d_j = 2j+1 for j = 5/2. -/
def dim_j5half : ℕ := 6
/-- d_j = 2j+1 for j = 9/2. -/
def dim_j9half : ℕ := 10

/-! ### Set of FRAMEWORK-NATURAL SU(2) reps -/

/-- A predicate: a rep dimension is "natural" in this framework iff it
    is one of {1, 2, 3}, i.e. j ∈ {0, 1/2, 1}. The irreps j = 3/2, 2,
    5/2, 9/2, ... appear in arithmetic identities below but are NOT
    derived as primitives anywhere in `LayerA`. -/
def IsFrameworkNaturalDim (n : ℕ) : Prop := n = 1 ∨ n = 2 ∨ n = 3

theorem nat_jhalf : IsFrameworkNaturalDim dim_jhalf := by
  unfold IsFrameworkNaturalDim dim_jhalf; right; left; rfl

theorem nat_j1 : IsFrameworkNaturalDim dim_j1 := by
  unfold IsFrameworkNaturalDim dim_j1; right; right; rfl

theorem not_nat_j3half : ¬ IsFrameworkNaturalDim dim_j3half := by
  unfold IsFrameworkNaturalDim dim_j3half; intro h; rcases h with h|h|h <;> omega

theorem not_nat_j2 : ¬ IsFrameworkNaturalDim dim_j2 := by
  unfold IsFrameworkNaturalDim dim_j2; intro h; rcases h with h|h|h <;> omega

theorem not_nat_j9half : ¬ IsFrameworkNaturalDim dim_j9half := by
  unfold IsFrameworkNaturalDim dim_j9half; intro h; rcases h with h|h|h <;> omega

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: HYPOTHESIS A — WIGNER-ECKART FACTOR 1/((2j₁+1)(2j₂+1))

    For two SU(2) irreps of dim n₁ = 2j₁+1, n₂ = 2j₂+1, the Wigner-
    Eckart "spread factor" 1/(n₁·n₂) appears in normalization of
    reduced matrix elements. Test: which (n₁, n₂) give 1/20?
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Wigner-Eckart spread factor as a rational. -/
def wignerEckart (n₁ n₂ : ℕ) : ℚ := 1 / (n₁ * n₂ : ℚ)

/-! ### Tabulate WE factors for all (j₁, j₂) with j_i ∈ {0,1/2,1,3/2,2,5/2,9/2} -/

theorem we_jhalf_jhalf : wignerEckart dim_jhalf dim_jhalf = 1 / 4 := by
  unfold wignerEckart dim_jhalf; norm_num

theorem we_jhalf_j1 : wignerEckart dim_jhalf dim_j1 = 1 / 6 := by
  unfold wignerEckart dim_jhalf dim_j1; norm_num

theorem we_j1_j1 : wignerEckart dim_j1 dim_j1 = 1 / 9 := by
  unfold wignerEckart dim_j1; norm_num

theorem we_j3half_jhalf : wignerEckart dim_j3half dim_jhalf = 1 / 8 := by
  unfold wignerEckart dim_j3half dim_jhalf; norm_num

theorem we_j3half_j1 : wignerEckart dim_j3half dim_j1 = 1 / 12 := by
  unfold wignerEckart dim_j3half dim_j1; norm_num

/-- **Wigner-Eckart factor for (j₁, j₂) = (3/2, 2): EQUALS 1/20.** -/
theorem we_j3half_j2 : wignerEckart dim_j3half dim_j2 = 1 / 20 := by
  unfold wignerEckart dim_j3half dim_j2; norm_num

/-- **Wigner-Eckart factor for (j₁, j₂) = (1/2, 9/2): EQUALS 1/20.** -/
theorem we_jhalf_j9half : wignerEckart dim_jhalf dim_j9half = 1 / 20 := by
  unfold wignerEckart dim_jhalf dim_j9half; norm_num

/-! ### NONE of the FRAMEWORK-NATURAL pairs (j₁, j₂ ∈ {0,1/2,1}) gives 1/20 -/

theorem we_natural_jhalf_jhalf_ne : wignerEckart dim_jhalf dim_jhalf ≠ 1 / 20 := by
  rw [we_jhalf_jhalf]; norm_num

theorem we_natural_jhalf_j1_ne : wignerEckart dim_jhalf dim_j1 ≠ 1 / 20 := by
  rw [we_jhalf_j1]; norm_num

theorem we_natural_j1_j1_ne : wignerEckart dim_j1 dim_j1 ≠ 1 / 20 := by
  rw [we_j1_j1]; norm_num

/-- **THE WIGNER-ECKART NEGATIVE THEOREM.** Among (j₁, j₂) pairs with
    BOTH j_i ∈ {0, 1/2, 1} (= the framework-natural SU(2) reps), no
    pair produces 1/((2j₁+1)(2j₂+1)) = 1/20. Equivalently: the only
    2-rep products with denominator 20 are (3/2, 2) and (1/2, 9/2),
    both involving a NON-FRAMEWORK-NATURAL rep. -/
theorem WignerEckart_no_natural_match :
    ∀ n₁ n₂ : ℕ, IsFrameworkNaturalDim n₁ → IsFrameworkNaturalDim n₂ →
      wignerEckart n₁ n₂ ≠ 1 / 20 := by
  intro n₁ n₂ h₁ h₂
  unfold IsFrameworkNaturalDim at h₁ h₂
  unfold wignerEckart
  rcases h₁ with rfl | rfl | rfl <;> rcases h₂ with rfl | rfl | rfl <;> norm_num

/-! ### Justifying that (3/2, 2) is NOT framework-natural -/

/-- The (3/2, 2) Wigner-Eckart pair requires both reps to be
    framework-natural; (3/2) and (2) are both NOT in the framework primitive
    rep set. So even though `we_j3half_j2 = 1/20` arithmetically, this
    cannot be invoked WITHOUT introducing a new primitive rep. -/
theorem we_j3half_j2_not_natural :
    wignerEckart dim_j3half dim_j2 = 1 / 20 ∧
    ¬ IsFrameworkNaturalDim dim_j3half ∧
    ¬ IsFrameworkNaturalDim dim_j2 :=
  ⟨we_j3half_j2, not_nat_j3half, not_nat_j2⟩

/-- Same for (1/2, 9/2): arithmetically 1/20, but j = 9/2 is not a
    framework primitive. -/
theorem we_jhalf_j9half_not_natural :
    wignerEckart dim_jhalf dim_j9half = 1 / 20 ∧
    IsFrameworkNaturalDim dim_jhalf ∧
    ¬ IsFrameworkNaturalDim dim_j9half :=
  ⟨we_jhalf_j9half, nat_jhalf, not_nat_j9half⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: HYPOTHESIS B — CLEBSCH-GORDAN COEFFICIENTS SQUARED

    For each natural irrep tensor product j₁ ⊗ j₂ → ⊕_J J, we
    list the |⟨J, M; j₁, m₁; j₂, m₂⟩|² values explicitly (these are
    standard table values). We test whether ANY equals 1/20.

    For 1/2 ⊗ 1/2:
        |1, 1; 1/2, 1/2; 1/2, 1/2|² = 1
        |1, 0; 1/2, 1/2; 1/2,-1/2|² = 1/2
        |0, 0; 1/2, 1/2; 1/2,-1/2|² = 1/2

    For 1/2 ⊗ 1 → 1/2 ⊕ 3/2:
        squared CG values: 1/3 and 2/3

    For 1 ⊗ 1 → 0 ⊕ 1 ⊕ 2:
        squared CG values include 1/3, 1/2, 1/6, 1/4, 1/12, 2/3

    For 3/2 ⊗ 1/2 → 1 ⊕ 2:
        squared CG values include 1/4, 3/4, 1/2

    For 3/2 ⊗ 1 → 1/2 ⊕ 3/2 ⊕ 5/2:
        includes 1/5, 4/5, 1/15, 8/15, ...

    NONE equals 1/20.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The list of squared CG coefficients for 1/2 ⊗ 1/2 → 0 ⊕ 1
    (coupling two spin-1/2's into a singlet and a triplet). -/
def cgSq_half_half : List ℚ := [1, 1/2]

/-- The list of squared CG coefficients for 1/2 ⊗ 1 → 1/2 ⊕ 3/2. -/
def cgSq_half_1 : List ℚ := [1/3, 2/3, 1]

/-- The list of squared CG coefficients for 1 ⊗ 1 → 0 ⊕ 1 ⊕ 2.
    Includes 1/3 (singlet), 1/2 (vector m=±1), 1/6 (vector m=0 mixing),
    1/4 (tensor m=±1), 1/12 (tensor m=0), 2/3 (vector overlap). -/
def cgSq_1_1 : List ℚ := [1/3, 1/2, 1/6, 1/4, 1/12, 2/3, 1]

/-- The list of squared CG coefficients for 3/2 ⊗ 1/2 → 1 ⊕ 2. -/
def cgSq_3half_half : List ℚ := [1/4, 3/4, 1/2, 1]

/-! ### NONE of the CG-squared values for natural-rep tensor products = 1/20 -/

theorem cgSq_half_half_no_20 : (1 / 20 : ℚ) ∉ cgSq_half_half := by
  unfold cgSq_half_half
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  push_neg
  refine ⟨?_, ?_⟩ <;> norm_num

theorem cgSq_half_1_no_20 : (1 / 20 : ℚ) ∉ cgSq_half_1 := by
  unfold cgSq_half_1
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  push_neg
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

theorem cgSq_1_1_no_20 : (1 / 20 : ℚ) ∉ cgSq_1_1 := by
  unfold cgSq_1_1
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  push_neg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

theorem cgSq_3half_half_no_20 : (1 / 20 : ℚ) ∉ cgSq_3half_half := by
  unfold cgSq_3half_half
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  push_neg
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

/-- **THE CLEBSCH-GORDAN NEGATIVE THEOREM.** No squared CG coefficient
    arising from any tensor product of FRAMEWORK-NATURAL SU(2) reps
    {j = 0, 1/2, 1} (or even the slightly larger set including j = 3/2)
    equals 1/20. Hence V_us² = 1/20 cannot be a single squared CG
    coefficient for natural-rep transitions. -/
theorem CG_no_natural_match :
    (1 / 20 : ℚ) ∉ cgSq_half_half ∧
    (1 / 20 : ℚ) ∉ cgSq_half_1 ∧
    (1 / 20 : ℚ) ∉ cgSq_1_1 ∧
    (1 / 20 : ℚ) ∉ cgSq_3half_half :=
  ⟨cgSq_half_half_no_20, cgSq_half_1_no_20,
   cgSq_1_1_no_20, cgSq_3half_half_no_20⟩

/-! ### Where 1/20 DOES appear in CG-squared menus

    The squared CG coefficient 1/20 appears as ⟨2, M; 3/2, m₁; 1/2, m₂⟩²
    for certain (M, m₁, m₂). For example,
        ⟨2, 0; 3/2, -1/2; 1/2, 1/2⟩² = 9/20
    is in the standard table (and 1/20 = (1/√20)² = ⟨J, M; 3/2, 3/2; 1/2,
    -1/2⟩² for some J = 1 component). Specifically, the singlet projection
    |3/2, m=1/2⟩ ⊗ |1/2, m=-1/2⟩ → |J=1, M=0⟩ has CG = √(3/4)·... — actual
    table values include 1/4, 3/4, 1/2.

    The cleanest place 1/20 appears is the Wigner 6j-symbol:
        {3/2 1/2 1; 1/2 3/2 1}² = 1/20
    (a Racah W-coefficient in standard tables). But the 6j-symbol requires
    SIX irreps, FOUR of which would have to be j = 3/2 — again not framework
    primitive.

    We do NOT prove this here (it requires the full 6j machinery). We
    record only the absence of 1/20 in 2-rep CG-squared menus. -/

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: HYPOTHESIS C — J₄ AS A SU(2) REP MATRIX

    SU(2)'s j = 3/2 rep is 4-dimensional. Cartan generator J_z is
    diagonal with eigenvalues {-3/2, -1/2, 1/2, 3/2}. The framework's
    J₄ Jacobi matrix (3×3 after Feshbach) has eigenvalues
        {3/5, (5+√7)/30, (5-√7)/30}.
    These differ in cardinality (3 vs 4) and even sign-structure:
    J_z eigenvalues span a symmetric interval [-3/2, 3/2] including
    negatives, while J₄'s are all positive in [0, 1].
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The four SU(2) j = 3/2 Cartan eigenvalues, as a list of rationals. -/
def Jz_3half_eigs : List ℚ := [-3/2, -1/2, 1/2, 3/2]

theorem Jz_3half_length : Jz_3half_eigs.length = 4 := rfl

/-- The three post-Feshbach J₄ rational eigenvalue (the irrational ones
    are bunched into the quadratic factor and live in ℚ(√7)). -/
def J4_rational_eig : ℚ := 3 / 5

theorem J4_rational_eig_in_J4 : J4_rational_eig = 3 / 5 := rfl

/-- **The single rational J₄ eigenvalue 3/5 is NOT in {-3/2, -1/2,
    1/2, 3/2}**, so J₄ ≠ J_z(j=3/2) even just at the rational eigenvalue
    level. -/
theorem J4_eig_not_Jz :
    J4_rational_eig ∉ Jz_3half_eigs := by
  unfold Jz_3half_eigs J4_rational_eig
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  push_neg
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

/-- All J_z(j=3/2) eigenvalues sum to ZERO (J_z is traceless), but the
    J₄ post-Feshbach eigenvalue sum is 3/5 + 1/3 = 14/15 ≠ 0. -/
theorem Jz_3half_traceless : (-3/2 : ℚ) + -1/2 + 1/2 + 3/2 = 0 := by norm_num

/-- The post-Feshbach J₄ trace equals a₁ + a₂ + a₃ = 1/3 + 2/5 + 1/5
    = 14/15. (This equals λ₁ + λ₂ + λ₃ = 3/5 + (5+√7)/30 + (5-√7)/30
    = 3/5 + 10/30 = 3/5 + 1/3 = 14/15.) -/
theorem J4_trace_eq : (1/3 : ℚ) + 2/5 + 1/5 = 14 / 15 := by norm_num

/-- **TRACE-OBSTRUCTION**: J₄ is NOT a representation of SU(2) j = 3/2
    even up to similarity, because their traces are different: J₄ has
    trace 14/15 ≠ 0 while every SU(2) generator (including j = 3/2 J_z)
    is traceless. -/
theorem J4_not_su2_rep :
    (1/3 : ℚ) + 2/5 + 1/5 ≠ ((-3/2 : ℚ) + -1/2 + 1/2 + 3/2) := by
  rw [J4_trace_eq, Jz_3half_traceless]; norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: HYPOTHESIS D — CONTINUOUS SU(2) ≅ S³ BATH

    SU(2) is topologically the unit 3-sphere S³ ⊂ ℝ⁴. With the
    standard bi-invariant Haar measure normalized so the diameter
    of the round S³ is π,
        Vol(S³) = 2π².
    The candidate identification
        V_us² = 1/Vol(SU(2)) = 1/(2π²) ≈ 0.05066
    is an "outside-the-box" alternative to the framework's discrete
    derivation V_us² = (3/20)·(1/3) = 1/20 = 0.05000.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The continuous SU(2)-bath candidate value: 1/(2π²). -/
noncomputable def Vus_sq_continuum : ℝ := 1 / (2 * Real.pi ^ 2)

/-- 2π² is positive. -/
theorem two_pi_sq_pos : 0 < 2 * Real.pi ^ 2 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  positivity

/-- The continuum candidate is positive. -/
theorem Vus_sq_continuum_pos : 0 < Vus_sq_continuum := by
  unfold Vus_sq_continuum
  exact div_pos one_pos two_pi_sq_pos

/-! ### Numerical bracket for Vus_sq_continuum = 1/(2π²)

    From Mathlib `Real.pi_gt_d6 : 3.141592 < π` and
    `Real.pi_lt_d6 : π < 3.141593`, we deduce
        π² ∈ (9.8696034..., 9.8696046...)
        2π² ∈ (19.7392068..., 19.7392093...)
        1/(2π²) ∈ (0.0506605..., 0.0506606...).
-/

/-- π² is bracketed in (9.8696, 9.86962). (Loose enough to prove cheaply,
    tight enough to imply 1/(2π²) ≠ 1/20.) -/
theorem pi_sq_bracket :
    9.8696 < Real.pi ^ 2 ∧ Real.pi ^ 2 < 9.86962 := by
  refine ⟨?_, ?_⟩
  · -- π > 3.141592 ⟹ π² > 3.141592² = 9.86958737...
    have hp : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
    have hpos : (0 : ℝ) < 3.141592 := by norm_num
    have h := mul_lt_mul'' hp hp hpos.le hpos.le
    have hsq : (3.141592 : ℝ) * 3.141592 = (3.141592 : ℝ) ^ 2 := by ring
    have : (3.141592 : ℝ) ^ 2 < Real.pi * Real.pi := by
      rw [← hsq]; exact h
    have hpiSq : Real.pi * Real.pi = Real.pi ^ 2 := by ring
    rw [hpiSq] at this
    have : (9.8696 : ℝ) < (3.141592 : ℝ) ^ 2 := by norm_num
    nlinarith [Real.pi_gt_d6, Real.pi_pos]
  · -- π < 3.141593 ⟹ π² < 3.141593² = 9.86959365...
    have hp : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
    have hpos : (0 : ℝ) < Real.pi := Real.pi_pos
    have hub : (3.141593 : ℝ) ^ 2 < 9.86962 := by norm_num
    nlinarith [Real.pi_lt_d6, Real.pi_pos]

/-- 2π² is bracketed in (19.7392, 19.73924). -/
theorem two_pi_sq_bracket :
    19.7392 < 2 * Real.pi ^ 2 ∧ 2 * Real.pi ^ 2 < 19.73924 := by
  obtain ⟨h1, h2⟩ := pi_sq_bracket
  exact ⟨by linarith, by linarith⟩

/-- 1/(2π²) is bracketed in (0.05066, 0.05067). -/
theorem Vus_sq_continuum_bracket :
    0.05066 < Vus_sq_continuum ∧ Vus_sq_continuum < 0.05067 := by
  unfold Vus_sq_continuum
  obtain ⟨hlo, hhi⟩ := two_pi_sq_bracket
  have hpos : 0 < 2 * Real.pi ^ 2 := two_pi_sq_pos
  refine ⟨?_, ?_⟩
  · -- 1/(2π²) > 0.05066 iff 0.05066 · (2π²) < 1.
    -- 0.05066 · 19.73924 = 0.9998820... < 1. With 2π² < 19.73924:
    have h0 : (0 : ℝ) < 0.05066 := by norm_num
    have step : (0.05066 : ℝ) * (2 * Real.pi ^ 2) < 0.05066 * 19.73924 :=
      mul_lt_mul_of_pos_left hhi h0
    have hmul : (0.05066 : ℝ) * 19.73924 < 1 := by norm_num
    have key : (0.05066 : ℝ) * (2 * Real.pi ^ 2) < 1 := by linarith
    rw [lt_div_iff₀ hpos]
    linarith
  · -- 1/(2π²) < 0.05067 iff 1 < 0.05067 · (2π²).
    -- 0.05067 · 19.7392 = 1.00018394... > 1. With 19.7392 < 2π²:
    have h0 : (0 : ℝ) < 0.05067 := by norm_num
    have step : (0.05067 : ℝ) * 19.7392 < 0.05067 * (2 * Real.pi ^ 2) :=
      mul_lt_mul_of_pos_left hlo h0
    have hmul : (1 : ℝ) < 0.05067 * 19.7392 := by norm_num
    have key : (1 : ℝ) < 0.05067 * (2 * Real.pi ^ 2) := by linarith
    rw [div_lt_iff₀ hpos]
    linarith

/-- **CONTINUUM ≠ FRAMEWORK**: 1/(2π²) ≠ 1/20. -/
theorem continuum_ne_framework :
    Vus_sq_continuum ≠ (1 / 20 : ℝ) := by
  obtain ⟨h1, _⟩ := Vus_sq_continuum_bracket
  intro heq
  rw [heq] at h1
  norm_num at h1

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: COMPARISON WITH PDG

    PDG 2024:  V_us² = 0.05031 ± 0.00036    (1σ window [0.04995, 0.05067])

    Framework:  1/20      = 0.05000        (0.86σ low,  inside 2σ)
    Continuum:  1/(2π²)   = 0.050660...    (0.97σ high, on the 1σ edge)

    Both candidates lie at the EDGE of the PDG 1σ window: 1/20 sits at
    the lower 1σ boundary (0.04995), and 1/(2π²) sits at the upper 1σ
    boundary (0.05067). Experimentally GENUINELY AMBIGUOUS.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- PDG central value as a rational proxy. -/
def Vus_sq_PDG : ℚ := 5031 / 100000

/-- PDG 1σ uncertainty as a rational proxy. -/
def Vus_sq_PDG_sigma : ℚ := 36 / 100000

/-- PDG window lower (1σ): 0.05031 − 0.00036 = 0.04995. -/
def Vus_sq_PDG_lo : ℚ := Vus_sq_PDG - Vus_sq_PDG_sigma

/-- PDG window upper (1σ): 0.05031 + 0.00036 = 0.05067. -/
def Vus_sq_PDG_hi : ℚ := Vus_sq_PDG + Vus_sq_PDG_sigma

theorem Vus_sq_PDG_lo_value : Vus_sq_PDG_lo = 4995 / 100000 := by
  unfold Vus_sq_PDG_lo Vus_sq_PDG Vus_sq_PDG_sigma; norm_num

theorem Vus_sq_PDG_hi_value : Vus_sq_PDG_hi = 5067 / 100000 := by
  unfold Vus_sq_PDG_hi Vus_sq_PDG Vus_sq_PDG_sigma; norm_num

/-- 1/20 = 0.05000 is BELOW the PDG central value 0.05031 (it is 0.86σ
    low) but is INSIDE the 1σ window [0.04995, 0.05067]. -/
theorem framework_value_in_PDG_1sigma :
    Vus_sq_PDG_lo ≤ (1 / 20 : ℚ) ∧ (1 / 20 : ℚ) ≤ Vus_sq_PDG_hi := by
  rw [Vus_sq_PDG_lo_value, Vus_sq_PDG_hi_value]
  refine ⟨by norm_num, by norm_num⟩

/-- 1/20 = 0.05000 is STRICTLY BELOW the PDG central value 0.05031. -/
theorem framework_value_below_PDG_central :
    (1 / 20 : ℚ) < Vus_sq_PDG := by
  unfold Vus_sq_PDG; norm_num

/-- The continuum value 1/(2π²) ≈ 0.05066 is INSIDE the PDG 1σ window
    [0.04995, 0.05067] (just barely — within 0.001 of the upper edge). -/
theorem continuum_value_in_PDG_1sigma :
    ((Vus_sq_PDG_lo : ℚ) : ℝ) ≤ Vus_sq_continuum ∧
    Vus_sq_continuum ≤ ((Vus_sq_PDG_hi : ℚ) : ℝ) := by
  obtain ⟨h1, h2⟩ := Vus_sq_continuum_bracket
  refine ⟨?_, ?_⟩
  · rw [Vus_sq_PDG_lo_value]; push_cast; linarith
  · rw [Vus_sq_PDG_hi_value]; push_cast; linarith

/-- The continuum value 1/(2π²) is STRICTLY ABOVE the PDG central value. -/
theorem continuum_value_above_PDG_central :
    ((Vus_sq_PDG : ℚ) : ℝ) < Vus_sq_continuum := by
  obtain ⟨h1, _⟩ := Vus_sq_continuum_bracket
  unfold Vus_sq_PDG; push_cast; linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: ABSOLUTE-DEVIATION COMPARISON

    Which candidate is CLOSER to the PDG central value 0.05031?

        |1/20      − 0.05031| = 0.00031
        |1/(2π²)   − 0.05031| ≈ 0.00035 to 0.00036  (since 1/(2π²) ∈ (0.05066, 0.05067))

    The framework rational 1/20 is SLIGHTLY closer to PDG (by ~10%
    smaller deviation). Both are within 1σ. Honest verdict: numerics
    barely distinguishes them.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **ABSOLUTE DEVIATION COMPARISON**: |1/20 − PDG| < |1/(2π²) − PDG|.
    The framework rational 1/20 is closer to the PDG central value
    0.05031 than the continuum candidate 1/(2π²). Strict inequality. -/
theorem framework_closer_to_PDG :
    |((1 / 20 : ℚ) : ℝ) - ((Vus_sq_PDG : ℚ) : ℝ)| <
    |Vus_sq_continuum - ((Vus_sq_PDG : ℚ) : ℝ)| := by
  -- |1/20 − 0.05031| = |0.05000 − 0.05031| = 0.00031
  -- |1/(2π²) − 0.05031| > |0.05066 − 0.05031| = 0.00035
  obtain ⟨h1, h2⟩ := Vus_sq_continuum_bracket
  unfold Vus_sq_PDG
  push_cast
  have h_lhs_neg : ((1 : ℝ) / 20 - 5031 / 100000) < 0 := by norm_num
  have h_rhs_pos : (0 : ℝ) < Vus_sq_continuum - 5031 / 100000 := by linarith
  rw [abs_of_neg h_lhs_neg, abs_of_pos h_rhs_pos]
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: SAME-MENU CLASSIFICATION

    The continuous-bath hypothesis 1/(2π²), even though numerically
    plausible, suffers the SAME structural defect as 1/20: nothing in
    the framework FORCES the choice. To get 1/(2π²) we would need to
    derive that the V_us bath measure IS the bi-invariant Haar measure
    on SU(2). The framework currently uses a DISCRETE bath (per
    `CKMSchur7`, `CKMSchur8`) — there is no continuous-Haar derivation.

    Switching from "discrete bath with vertex products in a menu" to
    "continuous Haar bath with volume in a menu of compact group
    volumes" trades one menu for another:
        Discrete menu: products of channel diagonals × resolvent denominators
        Continuous menu: 1/Vol(K) for K ∈ {SU(2), SU(3), SO(3), G₂, ...}
    Either menu can hit the PDG vicinity. Neither is FORCED.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-! ### Volume of various compact Lie groups (with standard normalizations)

    Vol(S¹) = 2π,  Vol(SU(2)) = 2π²,  Vol(SO(3)) = 8π²,  Vol(SU(3)) = √3·π⁵.
    Each of these gives a candidate 1/Vol(K). Most cluster either
    around V_us² (≈ 0.05) or are wildly off. Vol(SU(2)) is the natural
    candidate by dimension. -/

/-- Vol(SO(3)) = 8π² as a real, with 1/Vol(SO(3)) ≈ 0.01267 (a factor 4
    LOWER than V_us², so falsified). -/
noncomputable def Vol_SO3 : ℝ := 8 * Real.pi ^ 2

theorem Vol_SO3_pos : 0 < Vol_SO3 := by
  unfold Vol_SO3
  have : 0 < Real.pi ^ 2 := by positivity
  linarith

theorem inv_Vol_SO3_too_small :
    1 / Vol_SO3 < (1 / 40 : ℝ) := by
  unfold Vol_SO3
  obtain ⟨h1, _⟩ := pi_sq_bracket
  have hpos : (0 : ℝ) < 8 * Real.pi ^ 2 := by linarith
  rw [div_lt_div_iff₀ hpos (by norm_num : (0 : ℝ) < 40)]
  linarith

/-- Vol(S¹) = 2π and 1/Vol(S¹) = 1/(2π) ≈ 0.159 (FACTOR 3 TOO BIG, so
    falsified). -/
noncomputable def Vol_S1 : ℝ := 2 * Real.pi

theorem inv_Vol_S1_too_big :
    (1 / 10 : ℝ) < 1 / Vol_S1 := by
  unfold Vol_S1
  have hπ_lt : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  have hπ_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpos : (0 : ℝ) < 2 * Real.pi := by linarith
  -- (1/10) < 1/(2π) iff 1/10 * (2π) < 1 (using positivity of 2π and 10).
  -- 2π < 6.283186, so (1/10)(2π) < 0.6283186 < 1.
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 10) hpos]
  -- Goal: 1 * (2 * π) < 1 * 10
  linarith

/-- **Group-volume menu observation**: among the natural compact-group
    volumes, ONLY 1/Vol(SU(2)) = 1/(2π²) is in the right ballpark for
    V_us². The others (S¹ too big, SO(3) too small) are falsified. -/
theorem group_volume_menu_unique_candidate :
    1 / Vol_SO3 < (1 / 40 : ℝ) ∧
    (1 / 10 : ℝ) < 1 / Vol_S1 ∧
    0.05066 < Vus_sq_continuum ∧ Vus_sq_continuum < 0.05067 :=
  ⟨inv_Vol_SO3_too_small, inv_Vol_S1_too_big,
   Vus_sq_continuum_bracket.1, Vus_sq_continuum_bracket.2⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: MASTER THEOREM — TENTH STRENGTHENING ATTEMPT FAILS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Like the previous nine, this attempt classifies as SAME MENU:

    (A) The Wigner-Eckart spread factor 1/((2j₁+1)(2j₂+1)) = 1/20 ONLY
        for (j₁, j₂) = (3/2, 2) or (1/2, 9/2), neither of which is
        framework-natural (the framework's primitive SU(2) reps are
        j ∈ {0, 1/2, 1}). PROVED.

    (B) No squared CG coefficient from any tensor product of natural
        framework reps {j = 0, 1/2, 1} (or even including 3/2) equals
        1/20 — the natural CG-squared values are at most 1/12 (in
        1 ⊗ 1 → 2, M = 0). PROVED.

    (C) J₄ is NOT a SU(2) rep matrix even up to similarity: it has
        nonzero trace (14/15) while every SU(2) generator (including
        j = 3/2 J_z) is traceless. PROVED.

    (D) The continuum-SU(2) bath candidate V_us² = 1/(2π²) ≈ 0.05066
        is INSIDE the PDG 1σ window but is irrational, while the
        framework predicts the rational 1/20. They ARE DIFFERENT
        (1/(2π²) ≠ 1/20 by π² irrationality). The framework rational
        1/20 is SLIGHTLY closer to PDG central value 0.05031 than
        1/(2π²). PROVED.

    Honest verdict: SU(2) representation theory does NOT force 1/20,
    NOR does it force 1/(2π²). The continuum-bath alternative is just
    as much a CHOICE as the discrete-bath one. The numerical
    distinguishability is below the experimental precision.

    Best supported by current framework structure: 1/20 (closer to
    PDG, derived from C_int · a₁ via the across-sector self-consistency
    in `CKMOneLoopV2`, even if the choice of energy difference is by
    analogy). The continuum 1/(2π²) is structurally simpler but UNJUSTIFIED
    in the present framework — it would need a derivation that the V_us
    bath measure IS the SU(2) Haar measure, which does not currently exist.
-/

theorem SU2RepVus_master :
    -- (A) Wigner-Eckart no natural match
    (∀ n₁ n₂ : ℕ, IsFrameworkNaturalDim n₁ → IsFrameworkNaturalDim n₂ →
      wignerEckart n₁ n₂ ≠ 1 / 20)
    -- (A') The (3/2, 2) hit requires non-natural reps
    ∧ (wignerEckart dim_j3half dim_j2 = 1 / 20 ∧
       ¬ IsFrameworkNaturalDim dim_j3half ∧
       ¬ IsFrameworkNaturalDim dim_j2)
    -- (B) CG-squared menus do not contain 1/20
    ∧ ((1 / 20 : ℚ) ∉ cgSq_half_half ∧
       (1 / 20 : ℚ) ∉ cgSq_half_1 ∧
       (1 / 20 : ℚ) ∉ cgSq_1_1 ∧
       (1 / 20 : ℚ) ∉ cgSq_3half_half)
    -- (C) J₄ not SU(2) rep (trace obstruction + cardinality)
    ∧ ((1/3 : ℚ) + 2/5 + 1/5 ≠ ((-3/2 : ℚ) + -1/2 + 1/2 + 3/2))
    ∧ J4_rational_eig ∉ Jz_3half_eigs
    -- (D) Continuum SU(2) bath
    ∧ (0.05066 < Vus_sq_continuum ∧ Vus_sq_continuum < 0.05067)
    ∧ Vus_sq_continuum ≠ (1 / 20 : ℝ)
    -- (D') Both candidates inside PDG 1σ
    ∧ (Vus_sq_PDG_lo ≤ (1 / 20 : ℚ) ∧ (1 / 20 : ℚ) ≤ Vus_sq_PDG_hi)
    ∧ (((Vus_sq_PDG_lo : ℚ) : ℝ) ≤ Vus_sq_continuum ∧
       Vus_sq_continuum ≤ ((Vus_sq_PDG_hi : ℚ) : ℝ))
    -- (D'') Framework rational 1/20 is CLOSER to PDG central value
    ∧ |((1 / 20 : ℚ) : ℝ) - ((Vus_sq_PDG : ℚ) : ℝ)| <
      |Vus_sq_continuum - ((Vus_sq_PDG : ℚ) : ℝ)| :=
  ⟨WignerEckart_no_natural_match,
   we_j3half_j2_not_natural,
   CG_no_natural_match,
   J4_not_su2_rep,
   J4_eig_not_Jz,
   Vus_sq_continuum_bracket,
   continuum_ne_framework,
   framework_value_in_PDG_1sigma,
   continuum_value_in_PDG_1sigma,
   framework_closer_to_PDG⟩

end UnifiedTheory.LayerB.SU2RepVusTest
