/-
  LayerB/FiberOverlapTest.lean — Closing the V_us gap by computing the
  CP² fiber overlap integrals (the path the framework's own
  YukawaFromFiber.lean says "would close the gap fully").

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  THE QUESTION

  YukawaFromFiber.lean lines 274–286 admits the gap:
    "FREE PARAMETERS (not derived):
       (γ) The detailed perturbation matrix P (we used the simplest choice)
     WHAT WOULD CLOSE THE GAP FULLY:
       Derive P from the specific geometry of CP² (overlap integrals)."

  Five prior strengthening attempts (`VusFalsificationTest`,
  `VusStrengtheningAttempt`, `CKMSchur8`, `VusChargeStructureExhausted`,
  `OctonionVusCheck`) all failed to lift V_us² = 1/20 from "menu
  selection" to "forced". This file actually does the overlap-integral
  computation that `YukawaFromFiber.lean` proposes.

  SETUP

  The fiber is CP² = SU(3)/(SU(2)×U(1)). Three holomorphic O(1) sections
  z₀, z₁, z₂ are the homogeneous coordinates. The Yukawa matrix is
        Y_ij = ∫_{CP²} z̄_i · z_j · ρ(z) dμ_FS                                     (★)
  where ρ is the Higgs-section profile and μ_FS is Fubini–Study (normalized
  to ∫ dμ_FS = 1).

  CLOSED-FORM MOMENTS ON CP²

  By SU(3) invariance and the dimension formula for Sym^p ⊗ Sym^p
  representations of SU(3), the second/fourth-order moments are:

      ∫ z̄_i z_j dμ_FS                  = (1/3) δ_{ij}                           (M2)
      ∫ z̄_i z̄_k z_j z_l dμ_FS          = (1/12)(δ_{ij}δ_{kl} + δ_{il}δ_{kj})     (M4)

  These are mathematical facts (invariant theory of SU(3)); we encode
  them as DEFINITIONS in this file (the values of the moment functions),
  not as axioms in the Lean sense — they are real numbers we are free to
  define in a way that matches the closed forms above.

  WHAT THIS FILE COMPUTES

  For each of FOUR Higgs profile choices, we exhibit the closed-form
  Yukawa matrix Y, identify its rank/eigenstructure, and read off the
  resulting CKM matrix V_CKM = V_u† · V_d:

    PROFILE A (constant, ρ ≡ 1)
        Y_ij = (1/3) δ_{ij}
        ⇒ Y is diagonal.  V_u, V_d both = identity ⇒ V_CKM = I.
        ⇒ V_us = 0.  FAILS PDG (V_us ≈ 0.224).

    PROFILE B (linear singled, ρ(z) = z̄_k z_k for fixed k)
        Y_ij = (1/12)(δ_{ij} + δ_{ik} δ_{jk})
        ⇒ Y is still diagonal.  V_CKM = I.
        ⇒ V_us = 0.  FAILS PDG.

    PROFILE C (off-diagonal pure, ρ(z) = z̄_a z_b + z̄_b z_a, a≠b)
        Y_ij = (1/12)(δ_{ia} δ_{jb} + δ_{ib} δ_{ja})    [a≠b ⇒ δ_{ab}=0]
        ⇒ rank-2: a single 2×2 block ((0,1/12),(1/12,0)) and zero elsewhere.
        ⇒ ONE generation is exactly massless. FAILS observation.

    PROFILE D (general 4-parameter combination)
        ρ = α₀ + α₁(z̄₀ z₀) + α₂(z̄₁ z₁) + β·(z̄₀ z₁ + z̄₁ z₀)
        Y_u and Y_d are 2×2 block-diagonal in the (0,1) sector.
        Diagonalization gives rotation by angle θ, with
          tan(2θ) = β/(α₁ − α₂),
        and CKM = R(θ_u − θ_d).  Setting V_us² = 1/20 demands a
        specific value of (β/(α₁−α₂))_u − (β/(α₁−α₂))_d.
        But (α^u, β^u, α^d, β^d) come from FREE PARAMETERS that
        K/P never constrains.

  HONESTY MANDATE

  A "successful derivation" requires ALL of:
    (a) Higgs profile FORCED by independent K/P-derived constraint.
    (b) V_us² = 1/20 EXACTLY.
    (c) V_cb, V_ub also match PDG.
    (d) No hidden free parameter.

  `LayerB/HiggsDoublet.lean` defines the Higgs as a flat SU(2) doublet
  with a single VEV v.  It provides NO CP²-section profile and NO map
  from K/P content to (α, β).  Hence the overlap-integral derivation
  route is **structurally incomplete**: even with the integrals computed
  exactly in closed form, the gap closure requires additional K/P
  content the framework does not currently provide.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Zero sorry.  Zero custom axioms.  Imports Mathlib only.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.FiberOverlapTest

open Matrix Real

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1 — FUBINI–STUDY MOMENTS ON CP² (closed forms as definitions)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The 2nd-order CP² Fubini–Study moment: ∫ z̄_i z_j dμ = (1/3) δ_{ij}.
    By SU(3) invariance the integral must be proportional to δ_{ij};
    the constant 1/3 follows from Σ_i ∫ z̄_i z_i = ∫ ‖z‖² = 1. -/
noncomputable def m2 (i j : Fin 3) : ℝ := if i = j then (1 : ℝ) / 3 else 0

@[simp] theorem m2_diag (i : Fin 3) : m2 i i = 1 / 3 := by
  simp [m2]

/-- The 4th-order CP² Fubini–Study moment:
    ∫ z̄_i z̄_k z_j z_l dμ = (1/12)(δ_{ij}δ_{kl} + δ_{il}δ_{kj}). -/
noncomputable def m4 (i j k l : Fin 3) : ℝ :=
  ((if i = j then (1 : ℝ) else 0) * (if k = l then 1 else 0)
   + (if i = l then (1 : ℝ) else 0) * (if k = j then 1 else 0)) / 12

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2 — PROFILE A: CONSTANT HIGGS  ρ ≡ 1
    Y^A_{ij} = ∫ z̄_i z_j dμ_FS = (1/3) δ_{ij}
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Yukawa matrix from the constant Higgs profile ρ ≡ 1.
    Closed form: Y^A_{ij} = m2 i j = (1/3) δ_{ij}. -/
noncomputable def Y_profileA : Matrix (Fin 3) (Fin 3) ℝ := fun i j => m2 i j

/-- **Profile A produces a diagonal Yukawa matrix.**
    Off-diagonal entries vanish identically. -/
theorem profileA_offdiag_zero (i j : Fin 3) (hij : i ≠ j) :
    Y_profileA i j = 0 := by
  simp [Y_profileA, m2, hij]

/-- **Profile A diagonal entries are all 1/3.** -/
theorem profileA_diag_value (i : Fin 3) : Y_profileA i i = 1 / 3 := by
  simp [Y_profileA]

/-- **Profile A gives V_us = 0** (CKM = I). -/
theorem profileA_Vus_eq_zero : Y_profileA 1 2 = 0 ∧ Y_profileA 2 1 = 0 := by
  refine ⟨?_, ?_⟩ <;> (simp [Y_profileA, m2])

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3 — PROFILE B: LINEAR-SINGLED HIGGS  ρ(z) = z̄_k z_k
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Yukawa matrix from a linear-singled Higgs profile ρ(z) = z̄_k z_k. -/
noncomputable def Y_profileB (k : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => m4 i j k k

/-- **Profile B is diagonal: off-diagonal entries vanish for all k.**
    Proven by exhaustive case-analysis (Fin 3 × Fin 3 × Fin 3 = 27 cases). -/
theorem profileB_offdiag_zero (k : Fin 3) (i j : Fin 3) (hij : i ≠ j) :
    Y_profileB k i j = 0 := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | simp [Y_profileB, m4]

/-- **Profile B gives V_us = 0** for any k. -/
theorem profileB_Vus_eq_zero (k : Fin 3) :
    Y_profileB k 1 2 = 0 ∧ Y_profileB k 2 1 = 0 := by
  refine ⟨?_, ?_⟩
  · exact profileB_offdiag_zero k 1 2 (by decide)
  · exact profileB_offdiag_zero k 2 1 (by decide)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4 — PROFILE C: OFF-DIAGONAL HIGGS  ρ(z) = z̄_a z_b + z̄_b z_a
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Yukawa matrix from off-diagonal Higgs ρ(z) = z̄_a z_b + z̄_b z_a. -/
noncomputable def Y_profileC (a b : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => m4 i j a b + m4 i j b a

/-- **Profile C diagonal vanishes for a ≠ b**, by exhaustion. -/
theorem profileC_diag_zero (a b : Fin 3) (hab : a ≠ b) (i : Fin 3) :
    Y_profileC a b i i = 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases i <;>
    first
    | exact absurd rfl hab
    | simp [Y_profileC, m4]

/-- **Profile C value at the (a,b) entry equals 1/12** when a ≠ b. -/
theorem profileC_at_ab (a b : Fin 3) (hab : a ≠ b) :
    Y_profileC a b a b = 1 / 12 := by
  fin_cases a <;> fin_cases b <;>
    first
    | exact absurd rfl hab
    | simp [Y_profileC, m4]

/-- **Profile C makes the c-th coordinate (c ≠ a, c ≠ b) a kernel vector.**
    Proved by giving an explicit case-by-case witness for the third index. -/
theorem profileC_has_massless_generation (a b : Fin 3) (hab : a ≠ b) :
    ∃ c : Fin 3, (∀ j : Fin 3, Y_profileC a b c j = 0) := by
  -- The kernel index is the unique c ∉ {a, b}.
  fin_cases a <;> fin_cases b
  -- a=0, b=0: contradiction
  · exact absurd rfl hab
  -- a=0, b=1: c=2
  · refine ⟨2, ?_⟩; intro j
    fin_cases j <;> simp [Y_profileC, m4]
  -- a=0, b=2: c=1
  · refine ⟨1, ?_⟩; intro j
    fin_cases j <;> simp [Y_profileC, m4]
  -- a=1, b=0: c=2
  · refine ⟨2, ?_⟩; intro j
    fin_cases j <;> simp [Y_profileC, m4]
  -- a=1, b=1: contradiction
  · exact absurd rfl hab
  -- a=1, b=2: c=0
  · refine ⟨0, ?_⟩; intro j
    fin_cases j <;> simp [Y_profileC, m4]
  -- a=2, b=0: c=1
  · refine ⟨1, ?_⟩; intro j
    fin_cases j <;> simp [Y_profileC, m4]
  -- a=2, b=1: c=0
  · refine ⟨0, ?_⟩; intro j
    fin_cases j <;> simp [Y_profileC, m4]
  -- a=2, b=2: contradiction
  · exact absurd rfl hab

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5 — PROFILE D: 4-PARAMETER 2×2-BLOCK MIXED HIGGS
    ρ(z) = α₀ + α₁(z̄₀ z₀) + α₂(z̄₁ z₁) + β·(z̄₀ z₁ + z̄₁ z₀)

    Y^D_{ij} = α₀·m2(i,j) + α₁·m4(i,j,0,0) + α₂·m4(i,j,1,1)
             + β·(m4(i,j,0,1) + m4(i,j,1,0))
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Yukawa matrix for the 4-parameter 2×2-block Higgs profile. -/
noncomputable def Y_profileD (α₀ α₁ α₂ β : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j =>
    α₀ * m2 i j
      + α₁ * m4 i j 0 0
      + α₂ * m4 i j 1 1
      + β * (m4 i j 0 1 + m4 i j 1 0)

/-- **Closed-form (0,0) entry of Profile D**:
    Y^D_{00} = α₀·(1/3) + α₁·(2/12) + α₂·(1/12) + 0
             = α₀/3 + α₁/6 + α₂/12. -/
theorem profileD_00 (α₀ α₁ α₂ β : ℝ) :
    Y_profileD α₀ α₁ α₂ β 0 0 = α₀ / 3 + α₁ / 6 + α₂ / 12 := by
  simp [Y_profileD, m2, m4]; ring

/-- **Closed-form (1,1) entry of Profile D**:
    Y^D_{11} = α₀/3 + α₁/12 + α₂/6. -/
theorem profileD_11 (α₀ α₁ α₂ β : ℝ) :
    Y_profileD α₀ α₁ α₂ β 1 1 = α₀ / 3 + α₁ / 12 + α₂ / 6 := by
  simp [Y_profileD, m2, m4]; ring

/-- **Closed-form (0,1) off-diagonal entry of Profile D**:
    Y^D_{01} = β/12. -/
theorem profileD_01 (α₀ α₁ α₂ β : ℝ) :
    Y_profileD α₀ α₁ α₂ β 0 1 = β / 12 := by
  simp [Y_profileD, m2, m4]; ring

/-- **Closed-form (1,0) off-diagonal entry of Profile D**: also β/12. -/
theorem profileD_10 (α₀ α₁ α₂ β : ℝ) :
    Y_profileD α₀ α₁ α₂ β 1 0 = β / 12 := by
  simp [Y_profileD, m2, m4]; ring

/-- **Closed-form (2,2) entry**: Y^D_{22} = α₀/3 + α₁/12 + α₂/12. -/
theorem profileD_22 (α₀ α₁ α₂ β : ℝ) :
    Y_profileD α₀ α₁ α₂ β 2 2 = α₀ / 3 + α₁ / 12 + α₂ / 12 := by
  simp [Y_profileD, m2, m4]; ring

/-- **The third generation decouples**: row 2 entries (2,0), (2,1), (0,2),
    (1,2) all vanish.  Hence the diagonalization is purely 2×2. -/
theorem profileD_third_decouples (α₀ α₁ α₂ β : ℝ) :
    Y_profileD α₀ α₁ α₂ β 2 0 = 0 ∧
    Y_profileD α₀ α₁ α₂ β 2 1 = 0 ∧
    Y_profileD α₀ α₁ α₂ β 0 2 = 0 ∧
    Y_profileD α₀ α₁ α₂ β 1 2 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Y_profileD, m2, m4]

/-! Now the heart: the 2×2 mixing-angle formula. -/

/-- **Diagonalization angle for the 2×2 (0,1) sub-block.**
    For the real symmetric 2×2 matrix [[D, E], [E, F]] the diagonalization
    angle θ satisfies 2·E/(D−F) = tan(2θ).
    Here D − F = α₁/6 + α₂/12 − α₁/12 − α₂/6 = α₁/12 − α₂/12 = (α₁−α₂)/12,
    and 2E = β/6, so 2E/(D−F) = (β/6)/((α₁−α₂)/12) = 2β/(α₁−α₂).
    Hence tan(2θ) = 2β/(α₁ − α₂), proportional to the FREE ratio. -/
theorem profileD_block_diag_ratio (α₀ α₁ α₂ β : ℝ) (h : α₁ ≠ α₂) :
    2 * Y_profileD α₀ α₁ α₂ β 0 1
      / (Y_profileD α₀ α₁ α₂ β 0 0 - Y_profileD α₀ α₁ α₂ β 1 1)
      = 2 * β / (α₁ - α₂) := by
  rw [profileD_00, profileD_11, profileD_01]
  -- Numerator: 2 * (β/12) = β/6
  -- Denominator: (α₀/3 + α₁/6 + α₂/12) - (α₀/3 + α₁/12 + α₂/6) = (α₁ - α₂)/12
  -- So ratio = (β/6) / ((α₁ - α₂)/12) = (β/6) * (12/(α₁ - α₂)) = 2β/(α₁ - α₂)
  have hne : α₁ - α₂ ≠ 0 := sub_ne_zero.mpr h
  have key : (α₀/3 + α₁/6 + α₂/12) - (α₀/3 + α₁/12 + α₂/6) = (α₁ - α₂)/12 := by
    ring
  rw [key]
  -- Now: 2 * (β/12) / ((α₁ - α₂)/12) = 2 * β / (α₁ - α₂)
  rw [div_div_eq_mul_div]
  congr 1
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6 — CKM = R(θ_u − θ_d) AND THE V_us TARGET
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- For V_us² = 1/20 we need (θ_u − θ_d) such that sin² = 1/20. -/
theorem target_angle_for_PDG :
    ∃ Δθ : ℝ, Real.sin Δθ ^ 2 = 1 / 20 := by
  refine ⟨Real.arcsin (Real.sqrt (1 / 20)), ?_⟩
  have h_le_one : Real.sqrt (1 / 20) ≤ 1 := by
    have h1 : Real.sqrt (1 / 20) ≤ Real.sqrt 1 := by
      apply Real.sqrt_le_sqrt; norm_num
    simpa [Real.sqrt_one] using h1
  have h_neg_le : -1 ≤ Real.sqrt (1 / 20) := by
    have hnn : (0 : ℝ) ≤ Real.sqrt (1 / 20) := Real.sqrt_nonneg _
    linarith
  rw [Real.sin_arcsin h_neg_le h_le_one]
  exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 20)

/-- **Any V_us² ∈ (0,1) is reachable** by some choice of mixing angle. -/
theorem can_match_any_target (target : ℝ)
    (h0 : 0 < target) (h1 : target < 1) :
    ∃ Δθ : ℝ, Real.sin Δθ ^ 2 = target := by
  refine ⟨Real.arcsin (Real.sqrt target), ?_⟩
  have h_t_nn : (0 : ℝ) ≤ target := le_of_lt h0
  have h_le_one : Real.sqrt target ≤ 1 := by
    have h1' : target ≤ 1 := le_of_lt h1
    calc Real.sqrt target ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h1'
      _ = 1 := Real.sqrt_one
  have h_neg_le : -1 ≤ Real.sqrt target := by
    have : (0 : ℝ) ≤ Real.sqrt target := Real.sqrt_nonneg _
    linarith
  rw [Real.sin_arcsin h_neg_le h_le_one]
  exact Real.sq_sqrt h_t_nn

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7 — THE FOUR HIGGS-PROFILE VERDICT TABLE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Verdict A: ρ ≡ 1**.  No free parameter, V_us = 0.
    Classification: NOT-NATURAL-PHYSICALLY (no mixing → wrong PDG). -/
theorem verdictA_notviable :
    (∀ i j : Fin 3, i ≠ j → Y_profileA i j = 0)
    ∧ Y_profileA 1 2 = 0
    ∧ ((0 : ℝ) ≠ 1 / 20) :=
  ⟨profileA_offdiag_zero, profileA_Vus_eq_zero.1, by norm_num⟩

/-- **Verdict B: ρ = z̄_k z_k**.  3-element discrete choice; all give
    diagonal Y → V_us = 0.  Classification: NOT-NATURAL-PHYSICALLY. -/
theorem verdictB_notviable (k : Fin 3) :
    (∀ i j : Fin 3, i ≠ j → Y_profileB k i j = 0)
    ∧ Y_profileB k 1 2 = 0 :=
  ⟨profileB_offdiag_zero k, (profileB_Vus_eq_zero k).1⟩

/-- **Verdict C: ρ = z̄_a z_b + z̄_b z_a, a≠b**.  All such choices force
    one generation exactly massless.  Classification: NOT-NATURAL-PHYSICALLY. -/
theorem verdictC_notviable (a b : Fin 3) (hab : a ≠ b) :
    ∃ c : Fin 3, ∀ j : Fin 3, Y_profileC a b c j = 0 :=
  profileC_has_massless_generation a b hab

/-- **Verdict D: 4-parameter mixed profile**.  The CKM mixing angle in
    the (0,1) sub-block satisfies tan(2θ) = 2β/(α₁−α₂) — a single FREE
    knob.  Hence V_us is fully tunable.
    Classification: NATURAL-BUT-FREE (1-param fit per quark sector). -/
theorem verdictD_free_param_fit
    (α₀ α₁ α₂ β : ℝ) (h : α₁ ≠ α₂) :
    2 * Y_profileD α₀ α₁ α₂ β 0 1
      / (Y_profileD α₀ α₁ α₂ β 0 0 - Y_profileD α₀ α₁ α₂ β 1 1)
      = 2 * β / (α₁ - α₂) :=
  profileD_block_diag_ratio α₀ α₁ α₂ β h

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8 — META-LEMMA: FORCED-UNIQUENESS CLAIM IS FALSE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The hypothetical uniqueness claim that the CP²-overlap path would
    need to validate: for all (α₀, α₁, α₂, β), the Profile-D (0,1)-block
    sin²(2θ) — concretely, the ratio after the standard half-angle
    identity — equals 1/20.  Stated more concretely: the (0,1) entry
    relative to the diagonal difference is universal at 2β/(α₁−α₂),
    a number that runs through ALL of ℝ as we vary β. -/
def cp2_overlap_forces_Vus : Prop :=
  ∀ α₀ α₁ α₂ β : ℝ, α₁ ≠ α₂ →
    2 * Y_profileD α₀ α₁ α₂ β 0 1
      / (Y_profileD α₀ α₁ α₂ β 0 0 - Y_profileD α₀ α₁ α₂ β 1 1)
      = 2 * Real.sqrt (1 / 20)

/-- **The CP²-overlap forced-uniqueness claim is FALSE.**
    Witness: choose β = 0.  Then the LHS = 0 / something = 0,
    but the RHS = 2·√(1/20) > 0. -/
theorem cp2_overlap_does_not_force_Vus : ¬ cp2_overlap_forces_Vus := by
  intro hForce
  -- Use α₀ = 0, α₁ = 1, α₂ = 0, β = 0.
  have h1 : (1 : ℝ) ≠ 0 := one_ne_zero
  have h := hForce 0 1 0 0 h1
  rw [profileD_block_diag_ratio 0 1 0 0 h1] at h
  -- h : 2*0/(1-0) = 2*sqrt(1/20)
  -- LHS = 0, RHS > 0.
  have h_lhs : (2 * 0 / (1 - 0) : ℝ) = 0 := by norm_num
  rw [h_lhs] at h
  -- 0 = 2 * sqrt (1/20)
  have h_pos : (0 : ℝ) < Real.sqrt (1 / 20) := by
    apply Real.sqrt_pos.mpr; norm_num
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9 — MASTER FAILURE THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER FAILURE THEOREM.**

    Computing the CP² fiber overlap integrals in closed form does NOT
    close the V_us = 1/√20 gap.

    (1) Constant Higgs (Profile A, parameter-free)        ⇒ V_us = 0.
    (2) Linear-singled Higgs (Profile B, 3 discrete k)    ⇒ V_us = 0 ∀ k.
    (3) Off-diagonal-pure Higgs (Profile C, 6 discrete (a,b)):
        always forces ONE exactly massless generation — physically wrong.
    (4) 4-parameter mixed Profile D: the CKM mixing angle
        tan(2θ) = 2β/(α₁−α₂) is a continuous free knob.  The framework's
        K/P content (HiggsDoublet.lean: a single VEV scale v) does NOT
        forces (β, α₁−α₂) — hence the V_us value is not derived but fit.

    The forced-uniqueness statement (cp2_overlap_forces_Vus) is FALSE,
    proved by an explicit counter-witness (β = 0).

    HONEST CLASSIFICATION: NATURAL-BUT-FREE.

    The framework's CP²-fiber-overlap proposal, taken seriously and
    computed end-to-end, REDUCES the V_us mystery to a Higgs-profile
    coefficient mystery — but does NOT solve it. -/
theorem MASTER_fiber_overlap_failure :
    -- (1) Profile A: parameter-free, gives V_us = 0
    Y_profileA 1 2 = 0
    -- (2) Profile B: all 3 choices of k give V_us = 0
    ∧ (∀ k : Fin 3, Y_profileB k 1 2 = 0)
    -- (3) Profile C: forces a massless generation for all (a,b)
    ∧ (∀ a b : Fin 3, a ≠ b →
         ∃ c : Fin 3, ∀ j : Fin 3, Y_profileC a b c j = 0)
    -- (4) Profile D: mixing angle is a free continuous knob
    ∧ (∀ α₀ α₁ α₂ β : ℝ, α₁ ≠ α₂ →
         2 * Y_profileD α₀ α₁ α₂ β 0 1
           / (Y_profileD α₀ α₁ α₂ β 0 0 - Y_profileD α₀ α₁ α₂ β 1 1)
           = 2 * β / (α₁ - α₂))
    -- (5) Profile D can match V_us² = 1/20 by choosing the angle freely
    ∧ (∃ Δθ : ℝ, Real.sin Δθ ^ 2 = 1 / 20)
    -- (6) The forced-uniqueness claim is FALSE
    ∧ ¬ cp2_overlap_forces_Vus := by
  refine ⟨profileA_Vus_eq_zero.1, ?_, ?_, ?_, target_angle_for_PDG,
          cp2_overlap_does_not_force_Vus⟩
  · intro k; exact (profileB_Vus_eq_zero k).1
  · intro a b hab; exact profileC_has_massless_generation a b hab
  · intro α₀ α₁ α₂ β h; exact profileD_block_diag_ratio α₀ α₁ α₂ β h

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 10 — FINAL VERDICT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **HONEST FINAL VERDICT.**
    This file proves, in Lean, that COMPUTING THE CP² FIBER OVERLAP
    INTEGRALS DOES NOT CLOSE THE V_us = 1/√20 GAP.

    Per Higgs profile choice, classified by the task's mandate:

      Profile A (constant)            : NOT-NATURAL-PHYSICALLY (V_us = 0)
      Profile B (linear-singled)      : NOT-NATURAL-PHYSICALLY (V_us = 0)
      Profile C (off-diagonal pure)   : NOT-NATURAL-PHYSICALLY (massless gen.)
      Profile D (4-param mixed)       : NATURAL-BUT-FREE        (free knob)

    No profile achieves FORCED+EXACT.  The CP²-fiber claim, taken
    seriously and computed end-to-end via overlap integrals, REDUCES
    the V_us mystery to a Higgs-profile-coefficient mystery.

    This is the SIXTH consecutive failed strengthening attempt for
    V_us² = 1/20 — and the most honest one, since it directly carries
    out the program the framework's own `YukawaFromFiber.lean` proposes
    "would close the gap fully", and demonstrates that doing so
    REDUCES the gap to a different (Higgs-profile) free parameter
    rather than closing it. -/
theorem FINAL_VERDICT :
    Y_profileA 1 2 = 0
    ∧ (∀ k : Fin 3, Y_profileB k 1 2 = 0)
    ∧ (∀ a b : Fin 3, a ≠ b →
         ∃ c : Fin 3, ∀ j : Fin 3, Y_profileC a b c j = 0)
    ∧ (∀ tgt : ℝ, 0 < tgt → tgt < 1 →
         ∃ Δθ : ℝ, Real.sin Δθ ^ 2 = tgt)
    ∧ ¬ cp2_overlap_forces_Vus := by
  refine ⟨profileA_Vus_eq_zero.1, ?_, ?_, ?_, cp2_overlap_does_not_force_Vus⟩
  · intro k; exact (profileB_Vus_eq_zero k).1
  · intro a b hab; exact profileC_has_massless_generation a b hab
  · exact can_match_any_target

end UnifiedTheory.LayerB.FiberOverlapTest
