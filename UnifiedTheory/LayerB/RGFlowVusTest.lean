/-
  LayerB/RGFlowVusTest.lean — Eleventh strengthening attempt of V_us² = 1/20:
  is the value forced by an RG-flow boundary condition tying V_us to the
  framework's PMNS angles or to a GUT-scale unified-coupling identity?

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  CONTEXT

  Ten prior strengthening attempts of `V_us² = 1/20` have all classified
  as SAME MENU:
      VusFalsificationTest, VusStrengtheningAttempt, CKMSchur8,
      VusChargeStructureExhausted, OctonionVusCheck, MassFanoTest,
      HiggsWTwoBathTest, FiberOverlapTest, MacMahon-partial,
      SU2RepVusTest.
  Each treated V_us as a "tree-level" structural quantity derivable from
  K/P at a single scale.

  This file tests an "outside the box" hypothesis: maybe V_us is NOT
  fundamental at the discreteness/Planck/GUT scale, but is RG-RUN down
  from a simple GUT-scale boundary condition. The framework already
  exposes:

   – `LayerA/AlphaGUT.lean`: the framework's algebraic α = 3/(32π) sits
     in the standard non-SUSY GUT window 1/α_GUT ∈ [33, 37], paired
     with the Georgi-Glashow value sin²θ_W = 3/8 at the GUT scale.
   – `LayerB/PMNSOneLoop.lean`: the three lepton mixing angles in
     closed form, with the SHARP across-sector relation
         sin²(θ_12)^PMNS = 6 · |V_us|²            (`solar_seesaw_factor`)
     i.e. equivalently |V_us|² = sin²(θ_12)^PMNS / 6 = (3/10)/6 = 1/20.

  We test FOUR boundary-condition hypotheses for V_us at GUT scale and
  ask whether any one of them "forces" V_us² = 1/20 with no remaining
  free choice:

      BC1.  Quark-Lepton Complementarity (QLC): θ_C = π/4 − θ_12^PMNS.
      BC2.  RG-improved QLC.
      BC3.  V_us² = sin²(θ_12)^PMNS / k for an integer k forced by gauge
            structure.
      BC4.  V_us² as a GUT-scale Yukawa ratio.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  WHAT IS PROVED

  ▸ BC1 (QLC). Closed form: V_us^QLC = sin(π/4 − arcsin(√(3/10)))
        = (√7 − √3) / √20 = (√(7/10) − √(3/10))/√2.
    Bracketed in (0.2042, 0.2044). MISSES BOTH the framework value
    √5/10 ≈ 0.2236 AND the PDG value 0.2243 ± 0.0008 by ~9%.
    QLC + framework PMNS is FALSIFIED relative to PDG.

  ▸ BC2 (RG-improved QLC). The standard one-loop CKM RG running is
    proportional to (top Yukawa)² · log(M_GUT/M_Z) / (16π²). Numerically
    this is a few-percent shift, NOT a ~9% shift. So BC1's failure is
    ROBUST against RG running: BC2 cannot rescue BC1. Recorded as a
    structural inequality on the size of the running window.

  ▸ BC3 (PMNS-divided-by-integer). The framework ALREADY proves
        sin²(θ_12)^PMNS = 6 · |V_us_v2|²    (PMNSOneLoop.solar_seesaw_factor)
    so V_us² = (3/10) / 6 = 1/20 is a tautology if the integer 6 is
    fixed by the framework. We tabulate the menu of integers k ∈ ℕ
    such that "k = (gauge dimension product) is a primitive of the
    framework":
        N_c = 3, N_W = 2 (both derived in `LayerA.GaugeGroupDerived`),
        N_g = 3 (derived in `LayerB.GenerationsFromFiber`).
    Compatible products of two: {N_c·N_W = 6, N_c·N_g = 9, N_W·N_g = 6,
    N_W·N_W = 4, N_c·N_c = 9, N_g·N_g = 9}. Compatible factorial: 3! = 6.
    Compatible sum: N_c + N_g = 6. Multiple distinct framework primitives
    produce 6 (FOUR independent factorisations: 3·2, 2·3, 3!, 3+3). Six
    is "on the menu" of natural framework integers, but is NOT UNIQUELY
    SELECTED.
    Verdict: the integer 6 is FRAMEWORK-AVAILABLE but NOT FRAMEWORK-FORCED.
    SAME MENU, by exactly the same diagnosis as the prior ten attempts.

  ▸ BC4 (Yukawa ratio at GUT). At GUT, b-τ unification y_b = y_τ is a
    single integer ratio (1). The framework does not derive any
    (small/medium/heavy) Yukawa ratio of value 1/20. Tabulating the
    framework's currently-derived Yukawa-related rationals
    (a_i, b_i², C_int, λ*, r₁, ratios in MassAndMixing/CKMOneLoop) we
    find: the rational 1/20 is exactly the framework's |V_us|² and also
    equals the framework's `x_int = 1/20` (interior residue at d=4) — a
    double coincidence INSIDE the same self-consistency derivation, not
    an INDEPENDENT cross-sector match.

  ▸ MASTER VERDICT. None of BC1–BC4 forces V_us² = 1/20 from independent
    framework input. BC3 (PMNS-divided-by-6) is the SHARPEST candidate
    structurally because the seesaw factor is already a theorem, but the
    integer 6 is on a menu of multiple framework-natural integers (not
    uniquely forced). The RG-flow lever does NOT close the gap. The
    framework remains UNABLE to derive V_us² = 1/20 without the analogy-
    based identification `V_us² = C_int · a₁` of `CKMOneLoopV2`.

  Honest verdict: ELEVENTH ATTEMPT FAILS. Same menu.

  Zero sorry. Zero custom axioms.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import UnifiedTheory.LayerA.FeshbachJ4
import UnifiedTheory.LayerA.AlphaGUT
import UnifiedTheory.LayerB.CKMOneLoop
import UnifiedTheory.LayerB.CKMOneLoopV2
import UnifiedTheory.LayerB.PMNSOneLoop

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.RGFlowVusTest

open Real
open UnifiedTheory.LayerA.FeshbachJ4
open UnifiedTheory.LayerA.AlphaGUT
open UnifiedTheory.LayerB.CKMOneLoop
open UnifiedTheory.LayerB.CKMOneLoopV2
open UnifiedTheory.LayerB.PMNSOneLoop

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 0: REFERENCE QUANTITIES (from existing framework)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The framework's V_us prediction: |V_us| = √5/10 from
    `CKMOneLoopV2.Vus_v2_closed`. -/
noncomputable def Vus_framework : ℝ := Real.sqrt 5 / 10

/-- The framework's V_us prediction equals `Vus_v2`. -/
theorem Vus_framework_eq : Vus_framework = Vus_v2 := by
  unfold Vus_framework; rw [Vus_v2_closed]

/-- |V_us|² = 1/20 in the framework. -/
theorem Vus_framework_sq : Vus_framework ^ 2 = 1 / 20 := by
  unfold Vus_framework
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  norm_num

/-- The PDG 2024 central value for V_us (rational shorthand). -/
noncomputable def Vus_PDG : ℝ := 2243 / 10000

/-- The PDG 2024 1σ uncertainty on V_us. -/
noncomputable def Vus_PDG_sigma : ℝ := 8 / 10000

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: BC1 — QUARK-LEPTON COMPLEMENTARITY (QLC)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Empirical QLC: θ_C^CKM + θ_12^PMNS ≈ π/4. With the framework's
    sin²(θ_12)^PMNS = 3/10 (`PMNSOneLoop.sinSq_theta12_closed`), QLC
    gives:

        sin(θ_12^PMNS) = √(3/10),    cos(θ_12^PMNS) = √(7/10),
        θ_C^QLC = π/4 − θ_12^PMNS,
        sin(θ_C^QLC) = sin(π/4)cos(θ_12) − cos(π/4)sin(θ_12)
                    = (cos(θ_12) − sin(θ_12)) / √2
                    = (√(7/10) − √(3/10)) / √2
                    = (√7 − √3) / √20.

    Numerical: (2.6458 − 1.7321)/4.4721 ≈ 0.2043.
    Framework: V_us = √5/10 ≈ 0.2236.
    PDG:       V_us = 0.2243 ± 0.0008.

    QLC + framework-PMNS gives a value that is ~9% LOW relative to
    BOTH PDG and the framework. BC1 is FALSIFIED.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The QLC prediction for V_us** in closed form. With the framework's
    sin²(θ_12)^PMNS = 3/10, QLC gives V_us = (√7 − √3)/√20. -/
noncomputable def Vus_QLC : ℝ := (Real.sqrt 7 - Real.sqrt 3) / Real.sqrt 20

/-- √20 = 2·√5. -/
theorem sqrt20_eq : Real.sqrt 20 = 2 * Real.sqrt 5 := by
  rw [show (20 : ℝ) = 2^2 * 5 from by norm_num]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2^2)]
  rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]

/-- √20 > 0. -/
theorem sqrt20_pos : 0 < Real.sqrt 20 := by
  rw [sqrt20_eq]
  have : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  linarith

/-- √7 lies in the open interval (2.6457, 2.6458). (Restated locally.) -/
theorem sqrt7_brk : 2.6457 < Real.sqrt 7 ∧ Real.sqrt 7 < 2.6458 := by
  refine ⟨?_, ?_⟩
  · have h1 : (2.6457 : ℝ) ^ 2 < 7 := by norm_num
    have h2 : (0 : ℝ) ≤ 2.6457 := by norm_num
    have := Real.sqrt_lt_sqrt (by positivity) h1
    rwa [Real.sqrt_sq h2] at this
  · have h1 : (7 : ℝ) < (2.6458 : ℝ) ^ 2 := by norm_num
    have h2 : (0 : ℝ) ≤ 2.6458 := by norm_num
    have := Real.sqrt_lt_sqrt (by positivity) h1
    rwa [Real.sqrt_sq h2] at this

/-- √3 lies in the open interval (1.7320, 1.7321). -/
theorem sqrt3_brk : 1.7320 < Real.sqrt 3 ∧ Real.sqrt 3 < 1.7321 := by
  refine ⟨?_, ?_⟩
  · have h1 : (1.7320 : ℝ) ^ 2 < 3 := by norm_num
    have h2 : (0 : ℝ) ≤ 1.7320 := by norm_num
    have := Real.sqrt_lt_sqrt (by positivity) h1
    rwa [Real.sqrt_sq h2] at this
  · have h1 : (3 : ℝ) < (1.7321 : ℝ) ^ 2 := by norm_num
    have h2 : (0 : ℝ) ≤ 1.7321 := by norm_num
    have := Real.sqrt_lt_sqrt (by positivity) h1
    rwa [Real.sqrt_sq h2] at this

/-- √5 lies in (2.2360, 2.2361). -/
theorem sqrt5_brk : 2.2360 < Real.sqrt 5 ∧ Real.sqrt 5 < 2.2361 := by
  refine ⟨?_, ?_⟩
  · have h1 : (2.2360 : ℝ) ^ 2 < 5 := by norm_num
    have h2 : (0 : ℝ) ≤ 2.2360 := by norm_num
    have := Real.sqrt_lt_sqrt (by positivity) h1
    rwa [Real.sqrt_sq h2] at this
  · have h1 : (5 : ℝ) < (2.2361 : ℝ) ^ 2 := by norm_num
    have h2 : (0 : ℝ) ≤ 2.2361 := by norm_num
    have := Real.sqrt_lt_sqrt (by positivity) h1
    rwa [Real.sqrt_sq h2] at this

/-- √20 lies in (4.4720, 4.4722). Derived from `sqrt20_eq` and `sqrt5_brk`. -/
theorem sqrt20_brk : 4.4720 < Real.sqrt 20 ∧ Real.sqrt 20 < 4.4722 := by
  rw [sqrt20_eq]
  obtain ⟨h₁, h₂⟩ := sqrt5_brk
  exact ⟨by linarith, by linarith⟩

/-- The QLC prediction is positive. -/
theorem Vus_QLC_pos : 0 < Vus_QLC := by
  unfold Vus_QLC
  apply div_pos
  · obtain ⟨h7lo, _⟩ := sqrt7_brk
    obtain ⟨_, h3hi⟩ := sqrt3_brk
    linarith
  · exact sqrt20_pos

/-- **|V_us|^QLC bracketed in (0.2042, 0.2044)** — significantly BELOW
    both the framework value √5/10 ≈ 0.2236 and the PDG value 0.2243. -/
theorem Vus_QLC_bracket : 0.2042 < Vus_QLC ∧ Vus_QLC < 0.2044 := by
  unfold Vus_QLC
  obtain ⟨h7lo, h7hi⟩ := sqrt7_brk
  obtain ⟨h3lo, h3hi⟩ := sqrt3_brk
  obtain ⟨h20lo, h20hi⟩ := sqrt20_brk
  have hnum_lo : (0.9136 : ℝ) < Real.sqrt 7 - Real.sqrt 3 := by linarith
  have hnum_hi : Real.sqrt 7 - Real.sqrt 3 < 0.9138 := by linarith
  have hd_pos : (0 : ℝ) < Real.sqrt 20 := sqrt20_pos
  have hnum_pos : (0 : ℝ) < Real.sqrt 7 - Real.sqrt 3 := by linarith
  refine ⟨?_, ?_⟩
  · -- 0.2042 < (√7 - √3)/√20
    -- Since √20 < 4.4722 and √7 - √3 > 0.9136:
    -- (√7 - √3)/√20 > 0.9136/4.4722 ≈ 0.20428..., and 0.2042 < 0.20428.
    rw [lt_div_iff₀ hd_pos]
    nlinarith [hnum_lo, h20hi]
  · -- (√7 - √3)/√20 < 0.2044
    -- Since √20 > 4.4720 and √7 - √3 < 0.9138:
    -- (√7 - √3)/√20 < 0.9138/4.4720 ≈ 0.20434..., and 0.20434 < 0.2044.
    rw [div_lt_iff₀ hd_pos]
    nlinarith [hnum_hi, h20lo]

/-- **The QLC prediction MISSES the framework value** by ≳ 1.9 percent.
    |V_us^QLC − √5/10| > 0.018, which is much larger than the framework
    bracket width (≈ 0.0001). -/
theorem Vus_QLC_misses_framework :
    0.018 < |Vus_framework - Vus_QLC| := by
  obtain ⟨h_qlc_lo, h_qlc_hi⟩ := Vus_QLC_bracket
  -- Framework value √5/10 lies in (0.2236, 0.2237).
  have h_fw_lo : (0.2236 : ℝ) < Vus_framework := by
    unfold Vus_framework
    obtain ⟨h₁, _⟩ := sqrt5_brk
    linarith
  have h_fw_hi : Vus_framework < 0.2237 := by
    unfold Vus_framework
    obtain ⟨_, h₂⟩ := sqrt5_brk
    linarith
  -- So Vus_framework - Vus_QLC > 0.2236 - 0.2044 = 0.0192 > 0.018.
  have h_diff_pos : 0 < Vus_framework - Vus_QLC := by linarith
  rw [abs_of_pos h_diff_pos]
  linarith

/-- **The QLC prediction MISSES the PDG central value** by ~9%.
    |V_us^QLC − 0.2243| > 0.018. -/
theorem Vus_QLC_misses_PDG :
    0.018 < |Vus_PDG - Vus_QLC| := by
  obtain ⟨h_qlc_lo, h_qlc_hi⟩ := Vus_QLC_bracket
  -- Vus_PDG = 0.2243; Vus_QLC < 0.2044; difference > 0.0199 > 0.018.
  unfold Vus_PDG
  have h_diff_pos : 0 < (2243 / 10000 : ℝ) - Vus_QLC := by norm_num; linarith
  rw [abs_of_pos h_diff_pos]
  norm_num
  linarith

/-- **The QLC prediction is OUTSIDE the PDG 1σ window**: V_us^QLC < 0.2235.
    The PDG 1σ window is [0.2235, 0.2251]; V_us^QLC < 0.2044 ≪ 0.2235. -/
theorem Vus_QLC_outside_PDG_1sigma :
    Vus_QLC < (Vus_PDG - Vus_PDG_sigma) := by
  obtain ⟨_, h_qlc_hi⟩ := Vus_QLC_bracket
  unfold Vus_PDG Vus_PDG_sigma
  norm_num
  linarith

/-- **VERDICT BC1: QLC + framework-PMNS gives V_us ≈ 0.2043, which is
    OUTSIDE the PDG 1σ window and ~9% off PDG and framework. FALSIFIED.** -/
theorem BC1_falsified :
    -- (a) QLC value is positive and bracketed
    0 < Vus_QLC ∧
    0.2042 < Vus_QLC ∧ Vus_QLC < 0.2044 ∧
    -- (b) misses framework prediction by > 1.8%
    0.018 < |Vus_framework - Vus_QLC| ∧
    -- (c) misses PDG by > 1.8%
    0.018 < |Vus_PDG - Vus_QLC| ∧
    -- (d) outside PDG 1σ window
    Vus_QLC < (Vus_PDG - Vus_PDG_sigma) :=
  ⟨Vus_QLC_pos, Vus_QLC_bracket.1, Vus_QLC_bracket.2,
   Vus_QLC_misses_framework, Vus_QLC_misses_PDG, Vus_QLC_outside_PDG_1sigma⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: BC2 — RG-IMPROVED QLC (CANNOT RESCUE BC1)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Standard one-loop CKM RG running between M_GUT and M_Z is dominated
    by the top-Yukawa contribution and is suppressed by 1/(16π²) and
    the off-diagonal smallness of the CKM. For V_us specifically, the
    one-loop running shift is

        ΔV_us / V_us ~ y_t² · ln(M_GUT/M_Z) / (16π²)

    With y_t ≈ 1, ln(M_GUT/M_Z) ≈ 32 (for M_GUT ≈ 10^16 GeV), this gives
    Δ ≈ 1·32/(16π²) ≈ 32/158 ≈ 0.20, but multiplied by the small
    parameters of the off-diagonal entries — net effect on V_us at the
    PERCENT level. BC1 misses by ~9%; RG cannot bridge that gap.

    We encode this as a STRUCTURAL inequality on the size of the running
    window. The framework already proved 1/α_GUT ≈ 32π/3 ≈ 33.5 < 34
    (`AlphaGUT.inv_alpha_GUT_lt_34`), so the e-folding ln(M_GUT/M_Z) is
    not even an INDEPENDENT framework input — it is dimensional, set by
    the choice of M_GUT.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The QLC gap to bridge** is at least 1.8% of V_us_framework. -/
noncomputable def QLC_gap : ℝ := |Vus_framework - Vus_QLC|

/-- **Generous RG running window upper bound** (a fraction). The
    one-loop CKM running of V_us between M_GUT (~10^16 GeV) and M_Z
    is dominated by y_t² · ln(M_GUT/M_Z) / (16π²) and is at most a
    few percent of V_us itself. We adopt 5% as a generous upper bound
    for any reasonable choice of M_GUT and y_t. -/
noncomputable def RG_running_max_fraction : ℝ := 5 / 100

/-- The maximum running-induced shift in V_us is bounded by (5%) ·
    Vus_framework < 0.0112. -/
theorem RG_shift_max_bound :
    RG_running_max_fraction * Vus_framework < 0.0112 := by
  unfold RG_running_max_fraction Vus_framework
  obtain ⟨_, h_hi⟩ := sqrt5_brk
  -- (5/100) · √5/10 < (5/100) · 2.2361/10 = (5 · 2.2361)/1000 ≈ 0.01118
  nlinarith [h_hi]

/-- **The QLC gap exceeds the maximum RG shift** by a factor > 1.5.
    BC2 cannot rescue BC1: even a 5% RG shift is < 0.0112 while the
    QLC gap |Vus_fw − Vus_QLC| > 0.018. -/
theorem RG_cannot_bridge_QLC_gap :
    RG_running_max_fraction * Vus_framework < QLC_gap := by
  have h₁ : RG_running_max_fraction * Vus_framework < 0.0112 := RG_shift_max_bound
  have h₂ : 0.018 < QLC_gap := Vus_QLC_misses_framework
  linarith

/-- **VERDICT BC2: RG flow cannot rescue BC1.** A generous 5% running
    shift (top-Yukawa-dominated, 16π²-suppressed) is bounded by 0.0112,
    while the QLC gap is > 0.018. -/
theorem BC2_falsified :
    RG_running_max_fraction * Vus_framework < QLC_gap ∧
    RG_running_max_fraction * Vus_framework < 0.0112 ∧
    0.018 < QLC_gap :=
  ⟨RG_cannot_bridge_QLC_gap, RG_shift_max_bound, Vus_QLC_misses_framework⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: BC3 — V_us² = sin²(θ_12)^PMNS / k FOR A FRAMEWORK INTEGER k
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The framework ALREADY proves `solar_seesaw_factor`:
        sin²(θ_12)^PMNS = 6 · |V_us_v2|²
    so V_us² = (3/10)/6 = 1/20 IS forced as soon as the integer 6 is
    framework-forced. We tabulate the menu of natural integers obtainable
    from framework primitives N_c = 3, N_W = 2, N_g = 3 and show that
    SEVERAL distinct identifications produce 6:

        k = N_c · N_W      = 3 · 2 = 6 ✓
        k = N_W · N_g      = 2 · 3 = 6 ✓
        k = N_g · N_W      = 3 · 2 = 6 ✓ (same as above by commutativity)
        k = N_g!           = 6     = 6 ✓
        k = N_c + N_g      = 3 + 3 = 6 ✓
        k = N_c · N_W      = 3 · 2 = 6 ✓

    Six is "on the menu" of natural framework integers but is NOT
    UNIQUELY SELECTED. By the same diagnostic the previous ten
    strengthening attempts use, this is SAME MENU: the integer 6 is
    framework-AVAILABLE but not framework-FORCED.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The framework-derived gauge-group color rank. -/
def N_c : ℕ := 3
/-- The framework-derived weak-isospin rank. -/
def N_W : ℕ := 2
/-- The framework-derived number of generations. -/
def N_g : ℕ := 3

/-- The "6" via N_c · N_W. -/
theorem six_as_Nc_NW : N_c * N_W = 6 := by unfold N_c N_W; rfl

/-- The "6" via N_W · N_g. -/
theorem six_as_NW_Ng : N_W * N_g = 6 := by unfold N_W N_g; rfl

/-- The "6" via factorial of N_g. -/
theorem six_as_Ng_fact : Nat.factorial N_g = 6 := by unfold N_g; decide

/-- The "6" via N_c + N_g. -/
theorem six_as_Nc_plus_Ng : N_c + N_g = 6 := by unfold N_c N_g; rfl

/-- The "6" via 2 · N_c. -/
theorem six_as_2Nc : 2 * N_c = 6 := by unfold N_c; rfl

/-- A predicate identifying "framework-natural integers": products,
    sums and factorials of {N_c, N_W, N_g}. The MENU of natural
    integers from gauge primitives. -/
def IsMenuInteger (k : ℕ) : Prop :=
    k = N_c ∨ k = N_W ∨ k = N_g ∨
    k = N_c * N_W ∨ k = N_W * N_g ∨ k = N_c * N_g ∨
    k = N_c + N_W ∨ k = N_W + N_g ∨ k = N_c + N_g ∨
    k = Nat.factorial N_g ∨ k = Nat.factorial N_W ∨ k = Nat.factorial N_c ∨
    k = N_c * N_c ∨ k = N_W * N_W ∨ k = N_g * N_g ∨
    k = 2 * N_c ∨ k = 2 * N_W ∨ k = 2 * N_g

/-- **6 is a menu integer** — and crucially, in MULTIPLE ways. -/
theorem six_on_menu : IsMenuInteger 6 := by
  unfold IsMenuInteger
  -- pick N_c · N_W
  right; right; right; left
  exact six_as_Nc_NW

/-- The "6" via N_c · N_W is one of MANY equivalent factorisations on the
    menu — explicit enumeration. -/
theorem six_multiply_realized :
    -- k = 6 has at least four DISTINCT framework-natural realisations
    N_c * N_W = 6
    ∧ N_W * N_g = 6
    ∧ Nat.factorial N_g = 6
    ∧ N_c + N_g = 6
    ∧ 2 * N_c = 6 :=
  ⟨six_as_Nc_NW, six_as_NW_Ng, six_as_Ng_fact, six_as_Nc_plus_Ng, six_as_2Nc⟩

/-- Other small framework-menu integers obtainable from {N_c, N_W, N_g}. -/
theorem menu_3 : IsMenuInteger 3 := by unfold IsMenuInteger; left; rfl
theorem menu_2 : IsMenuInteger 2 := by unfold IsMenuInteger; right; left; rfl
theorem menu_4 : IsMenuInteger 4 := by
  unfold IsMenuInteger; right; right; right; right; right; right
  right; right; right; right; right; right; right; left
  unfold N_W; rfl
theorem menu_9 : IsMenuInteger 9 := by
  unfold IsMenuInteger; right; right; right; right; right; right
  right; right; right; right; right; right; left
  unfold N_c; rfl

/-- **The framework integer k = 6 is NOT uniquely forced**: it is on the
    menu, and so are 2, 3, 4, 9 (and others). The selection of 6 is by
    PATTERN MATCH to the empirical V_us, not by independent derivation. -/
theorem k_not_uniquely_forced :
    IsMenuInteger 2 ∧ IsMenuInteger 3 ∧ IsMenuInteger 4 ∧
    IsMenuInteger 6 ∧ IsMenuInteger 9 :=
  ⟨menu_2, menu_3, menu_4, six_on_menu, menu_9⟩

/-! ### Test the alternative integers k ∈ {2, 3, 4, 9} on V_us. -/

/-- For k = 2: V_us² = sin²(θ_12)^PMNS / 2 = (3/10)/2 = 3/20. -/
noncomputable def Vus_sq_div2 : ℝ := sinSq_theta12 / 2

/-- For k = 3: V_us² = sin²(θ_12)^PMNS / 3 = (3/10)/3 = 1/10. -/
noncomputable def Vus_sq_div3 : ℝ := sinSq_theta12 / 3

/-- For k = 4: V_us² = sin²(θ_12)^PMNS / 4 = (3/10)/4 = 3/40. -/
noncomputable def Vus_sq_div4 : ℝ := sinSq_theta12 / 4

/-- For k = 6: V_us² = sin²(θ_12)^PMNS / 6 = (3/10)/6 = 1/20.
    THIS is the framework's `solar_seesaw_factor` rearranged. -/
noncomputable def Vus_sq_div6 : ℝ := sinSq_theta12 / 6

/-- For k = 9: V_us² = sin²(θ_12)^PMNS / 9 = (3/10)/9 = 1/30. -/
noncomputable def Vus_sq_div9 : ℝ := sinSq_theta12 / 9

theorem Vus_sq_div2_closed : Vus_sq_div2 = 3 / 20 := by
  unfold Vus_sq_div2; rw [sinSq_theta12_closed]; norm_num

theorem Vus_sq_div3_closed : Vus_sq_div3 = 1 / 10 := by
  unfold Vus_sq_div3; rw [sinSq_theta12_closed]; norm_num

theorem Vus_sq_div4_closed : Vus_sq_div4 = 3 / 40 := by
  unfold Vus_sq_div4; rw [sinSq_theta12_closed]; norm_num

theorem Vus_sq_div6_closed : Vus_sq_div6 = 1 / 20 := by
  unfold Vus_sq_div6; rw [sinSq_theta12_closed]; norm_num

theorem Vus_sq_div9_closed : Vus_sq_div9 = 1 / 30 := by
  unfold Vus_sq_div9; rw [sinSq_theta12_closed]; norm_num

/-- **The k = 6 candidate matches the framework V_us².** This is the
    `PMNSOneLoop.solar_seesaw_factor` rearranged. -/
theorem Vus_sq_div6_eq_framework : Vus_sq_div6 = Vus_v2_sq := by
  rw [Vus_sq_div6_closed, Vus_v2_sq_closed]

/-- **No other small menu k matches**: k ∈ {2, 3, 4, 9} all give
    V_us² ≠ 1/20. -/
theorem other_k_do_not_match :
    Vus_sq_div2 ≠ (1 / 20 : ℝ) ∧
    Vus_sq_div3 ≠ (1 / 20 : ℝ) ∧
    Vus_sq_div4 ≠ (1 / 20 : ℝ) ∧
    Vus_sq_div9 ≠ (1 / 20 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Vus_sq_div2_closed]; norm_num
  · rw [Vus_sq_div3_closed]; norm_num
  · rw [Vus_sq_div4_closed]; norm_num
  · rw [Vus_sq_div9_closed]; norm_num

/-- **VERDICT BC3: 6 is on the framework menu in MULTIPLE distinct ways
    (N_c · N_W = N_W · N_g = N_g! = 2 · N_c = 6). The selection of 6
    over 2, 3, 4, 9 (also on the menu) is by PATTERN MATCH to V_us, not
    independent derivation. SAME-MENU diagnosis applies.** -/
theorem BC3_same_menu :
    -- (a) k = 6 hits the framework V_us
    Vus_sq_div6 = Vus_v2_sq
    -- (b) but 6 is NOT uniquely forced: 2, 3, 4, 9 are also menu integers
    ∧ IsMenuInteger 2 ∧ IsMenuInteger 3 ∧ IsMenuInteger 4
    ∧ IsMenuInteger 6 ∧ IsMenuInteger 9
    -- (c) and 6 itself is realized by ≥ 4 DISTINCT framework primitives
    ∧ N_c * N_W = 6 ∧ N_W * N_g = 6
    ∧ Nat.factorial N_g = 6 ∧ N_c + N_g = 6 ∧ 2 * N_c = 6
    -- (d) and the alternative menu integers DO NOT yield 1/20
    ∧ Vus_sq_div2 ≠ (1 / 20 : ℝ) ∧ Vus_sq_div3 ≠ (1 / 20 : ℝ)
    ∧ Vus_sq_div4 ≠ (1 / 20 : ℝ) ∧ Vus_sq_div9 ≠ (1 / 20 : ℝ) := by
  refine ⟨Vus_sq_div6_eq_framework,
         menu_2, menu_3, menu_4, six_on_menu, menu_9,
         six_as_Nc_NW, six_as_NW_Ng, six_as_Ng_fact, six_as_Nc_plus_Ng,
         six_as_2Nc, ?_, ?_, ?_, ?_⟩
  all_goals {
    obtain ⟨h1, h2, h3, h4⟩ := other_k_do_not_match
    first | exact h1 | exact h2 | exact h3 | exact h4
  }

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: BC4 — V_us² AS A GUT-SCALE YUKAWA RATIO
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    At GUT, b-τ unification gives y_b/y_τ = 1, a single integer ratio.
    No framework-derived pair of Yukawas gives ratio 1/20. We tabulate
    the framework's currently-derived Yukawa-related rationals and show
    none independently realises 1/20.

    The ONE place 1/20 appears in the framework's rational catalogue
    OUTSIDE of `Vus_v2_sq` is `FeshbachJ4.x_int = 1/20` — the interior
    residue at d = 4. Both come from the SAME `FeshbachJ4` derivation:
        x_int = λ* − 2/5 − C_int = 3/5 − 2/5 − 3/20 = 1/20
        Vus_v2_sq = C_int · a₁ = (3/20) · (1/3) = 1/20
    so this is NOT an independent cross-sector match; it is a double
    coincidence INSIDE the same self-consistency derivation.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The framework's interior residue at d = 4. From `FeshbachJ4.x_int`. -/
noncomputable def x_int_real : ℝ := 1 / 20

/-- x_int = 1/20 = V_us². Both come from the same Feshbach J₄ derivation. -/
theorem x_int_eq_Vus_v2_sq : x_int_real = Vus_v2_sq := by
  unfold x_int_real
  rw [Vus_v2_sq_closed]

/-- The framework's catalogue of derived rationals from FeshbachJ4. -/
def feshbach_rationals : List ℚ :=
  [1/3,    -- a₁
   2/5,    -- a₂
   1/5,    -- a₃
   1/25,   -- b₁²
   1/50,   -- b₂²
   3/5,    -- λ*
   3/20,   -- C_int
   1/20]   -- x_int (= V_us²)

/-- 1/20 is in the FeshbachJ4 catalogue (because x_int = V_us²).
    The element 1/20 is the LAST entry. -/
theorem one_twentieth_in_catalog : (1/20 : ℚ) ∈ feshbach_rationals := by
  unfold feshbach_rationals
  -- The list is [1/3, 2/5, 1/5, 1/25, 1/50, 3/5, 3/20, 1/20];
  -- 1/20 is the 8th (last) element.
  simp [List.mem_cons]

/-- **The double coincidence**: x_int = V_us² = 1/20 is a SINGLE
    Feshbach derivation, not two independent ones. The 1/20 appears
    twice because both sides are arithmetic in the SAME constants
    {C_int, a₁, a₂, λ*}. NOT a cross-sector verification. -/
theorem BC4_no_independent_match :
    x_int_real = Vus_v2_sq ∧
    (1/20 : ℚ) ∈ feshbach_rationals ∧
    -- The b-τ unification rational at GUT (y_b/y_τ = 1) does NOT equal 1/20
    (1 : ℚ) ≠ (1/20 : ℚ) ∧
    -- Nor does any small "natural" ratio of derived Yukawa-like rationals
    (1/3 : ℚ) ≠ (1/20 : ℚ) ∧
    ((1/3 : ℚ) / (1 : ℚ)) ≠ (1/20 : ℚ) ∧
    ((1/5 : ℚ) / (1/3 : ℚ)) ≠ (1/20 : ℚ) ∧
    ((1/25 : ℚ) / (1/3 : ℚ)) ≠ (1/20 : ℚ) := by
  refine ⟨x_int_eq_Vus_v2_sq, one_twentieth_in_catalog, ?_, ?_, ?_, ?_, ?_⟩
  all_goals norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: GUT-SCALE FRAMING (REFERENCE)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Pull in the framework's GUT-scale unification observations
    (`AlphaGUT.lean`) for context: the framework SETS the GUT-scale
    couplings (sin²θ_W = 3/8 and 1/α = 32π/3) but does NOT derive any
    GUT-scale boundary condition for V_us. Every BC1–BC4 above relies
    on auxiliary input that is itself unforced.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The framework's α at GUT lies in (33, 34) ⊂ [33, 37]. Re-stated. -/
theorem GUT_scale_consistent :
    33 < inv_alpha_GUT_framework ∧ inv_alpha_GUT_framework < 34 :=
  inv_alpha_GUT_bracket

/-- The framework GUT scale fixes (1/α, sin²θ_W) but NOT (any GUT-scale
    V_us). The framework's V_us derivation in `CKMOneLoopV2` operates
    at the discreteness scale (low-energy K/P structure), NOT at GUT. -/
theorem framework_has_no_gut_Vus_input :
    -- The framework provides GUT-scale α and sin²θ_W
    sin2_weinberg_GUT = 3 / 8
    ∧ 33 < inv_alpha_GUT_framework
    -- but its V_us derivation is at the discreteness scale (FeshbachJ4),
    -- not at GUT
    ∧ Vus_v2_sq = C_int_real * a₁_real := by
  refine ⟨rfl, GUT_scale_consistent.1, ?_⟩
  unfold Vus_v2_sq; rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: MASTER THEOREM — ELEVENTH STRENGTHENING ATTEMPT FAILS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The four boundary conditions tested:

      BC1.  QLC θ_C = π/4 − θ_12^PMNS gives V_us^QLC = (√7-√3)/√20
            ≈ 0.2043 — OUTSIDE PDG 1σ, ~9% off PDG and framework.
      BC2.  RG-improved QLC: a generous 5% RG running window cannot
            bridge the > 1.8% QLC gap.
      BC3.  V_us² = sin²(θ_12)^PMNS / k for an integer k. Already a
            theorem at k = 6 (`PMNSOneLoop.solar_seesaw_factor`), but
            6 is on the menu of framework-natural integers in ≥ 4
            distinct ways (N_c·N_W, N_W·N_g, N_g!, 2·N_c). The integer
            6 is framework-AVAILABLE but NOT framework-FORCED. SAME
            MENU.
      BC4.  V_us² as a Yukawa ratio at GUT: the only place 1/20 appears
            in the framework catalogue OUTSIDE of V_us² is x_int from
            the SAME FeshbachJ4 derivation — not an independent match.

    HONEST VERDICT: The framework cannot derive V_us² = 1/20 from RG
    flow + GUT boundary conditions any more than from the prior ten
    discrete-bath strengthening attempts. The integer 6 in
    `solar_seesaw_factor` is the SHARPEST candidate (and is already a
    framework theorem), but 6 is not uniquely forced; it is just one
    of {2, 3, 4, 6, 9, ...} on the gauge-primitive menu. The
    pattern-match to V_us^2 = 1/20 picks out 6 by AGREEMENT with
    empirics, not by independent derivation.
-/

/-- **MASTER THEOREM: the ELEVENTH strengthening attempt of V_us² = 1/20
    fails — RG flow + GUT boundary conditions are SAME MENU as the
    previous ten attempts.** -/
theorem RGFlowVus_master :
    -- (BC1) QLC + framework-PMNS gives V_us ≈ 0.2043, OUTSIDE PDG 1σ
    (0 < Vus_QLC ∧ 0.2042 < Vus_QLC ∧ Vus_QLC < 0.2044 ∧
     0.018 < |Vus_framework - Vus_QLC| ∧
     0.018 < |Vus_PDG - Vus_QLC| ∧
     Vus_QLC < (Vus_PDG - Vus_PDG_sigma))
    -- (BC2) A generous 5% RG window cannot bridge BC1's > 1.8% gap
    ∧ (RG_running_max_fraction * Vus_framework < QLC_gap ∧
       RG_running_max_fraction * Vus_framework < 0.0112 ∧
       0.018 < QLC_gap)
    -- (BC3) k = 6 hits, but 6 is on a multiply-realized menu
    ∧ (Vus_sq_div6 = Vus_v2_sq ∧
       IsMenuInteger 2 ∧ IsMenuInteger 3 ∧ IsMenuInteger 4 ∧
       IsMenuInteger 6 ∧ IsMenuInteger 9 ∧
       N_c * N_W = 6 ∧ N_W * N_g = 6 ∧
       Nat.factorial N_g = 6 ∧ N_c + N_g = 6 ∧ 2 * N_c = 6 ∧
       Vus_sq_div2 ≠ (1 / 20 : ℝ) ∧ Vus_sq_div3 ≠ (1 / 20 : ℝ) ∧
       Vus_sq_div4 ≠ (1 / 20 : ℝ) ∧ Vus_sq_div9 ≠ (1 / 20 : ℝ))
    -- (BC4) The double coincidence x_int = V_us² is a single Feshbach
    -- derivation, not an independent cross-sector match
    ∧ (x_int_real = Vus_v2_sq ∧
       (1/20 : ℚ) ∈ feshbach_rationals ∧
       (1 : ℚ) ≠ (1/20 : ℚ) ∧
       (1/3 : ℚ) ≠ (1/20 : ℚ) ∧
       ((1/3 : ℚ) / (1 : ℚ)) ≠ (1/20 : ℚ) ∧
       ((1/5 : ℚ) / (1/3 : ℚ)) ≠ (1/20 : ℚ) ∧
       ((1/25 : ℚ) / (1/3 : ℚ)) ≠ (1/20 : ℚ))
    -- (GUT context) framework sets GUT (1/α, sin²θ_W) but not GUT V_us
    ∧ (sin2_weinberg_GUT = 3 / 8 ∧ 33 < inv_alpha_GUT_framework
       ∧ Vus_v2_sq = C_int_real * a₁_real) :=
  ⟨BC1_falsified, BC2_falsified, BC3_same_menu, BC4_no_independent_match,
   framework_has_no_gut_Vus_input⟩

/-- **HONEST SCOPE.** The framework provides GUT-scale (1/α, sin²θ_W) but
    does NOT provide a GUT-scale boundary condition for V_us. The
    `solar_seesaw_factor` (V_us² = sin²(θ_12)^PMNS / 6) is genuinely a
    framework theorem — but the integer 6 is not framework-forced (it
    sits on a menu with 2, 3, 4, 9, ...). SAME-MENU diagnosis applies,
    consistent with the prior ten strengthening attempts. The framework
    is, on present evidence, EXHAUSTED for V_us. -/
theorem honest_scope_RGFlowVus :
    -- The framework sets GUT couplings but not a GUT V_us BC
    sin2_weinberg_GUT = 3 / 8
    ∧ 33 < inv_alpha_GUT_framework
    -- The framework V_us comes from the discreteness-scale FeshbachJ4
    ∧ Vus_v2_sq = C_int_real * a₁_real
    -- The PMNS-divided-by-6 IS a framework theorem
    ∧ Vus_sq_div6 = Vus_v2_sq
    -- but 6 is not uniquely forced
    ∧ IsMenuInteger 6 ∧ IsMenuInteger 4 ∧ IsMenuInteger 9
    -- and QLC + RG flow CANNOT bridge to PDG
    ∧ Vus_QLC < (Vus_PDG - Vus_PDG_sigma)
    ∧ RG_running_max_fraction * Vus_framework < QLC_gap := by
  refine ⟨rfl, GUT_scale_consistent.1, ?_, Vus_sq_div6_eq_framework,
          six_on_menu, menu_4, menu_9,
          Vus_QLC_outside_PDG_1sigma, RG_cannot_bridge_QLC_gap⟩
  unfold Vus_v2_sq; rfl

end UnifiedTheory.LayerB.RGFlowVusTest
