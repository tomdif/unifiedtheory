/-
  LayerB/HiggsWTwoBathTest.lean — Two-bath Schur model with FRAMEWORK-FIXED
                                   bath energies (Higgs + W)

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT (Sixth strengthening attempt for V_us = 1/√20)

  `LayerB/CKMSchur8.lean` proved the two-bath Schur model has GL(2)
  freedom: multiple "framework-natural" bath/vertex assignments give
  different V_us². The verdict was that an ADDITIONAL discrete
  identification is needed to pin the bath strengths.

  This file performs that identification with the framework's TWO
  derived gauge-boson scales:

    • Bath A = Higgs sector
        λ_A = (m_H/v)²
        with m_H/v = log(5/3)  [proved in LayerA.HiggsMassDerived]
        ⇒ λ_A = (log(5/3))² ≈ 0.2611
        gA_i = m_i/v  (Yukawa-style vertex, ∝ fermion mass)

    • Bath B = W sector
        λ_B = (m_W/v)² = g_W²/4
        with g_W² = 1 at the GUT scale
            (from LayerA.AlphaGUT.framework_GUT_scale_couplings,
             since g² · sin²θ_W / (4π) = α_GUT and sin²θ_W = 3/8 with
             g₂² = 1 gives α_GUT = 3/(32π))
        ⇒ λ_B = 1/4 = 0.25
        gB_i = g_W = 1 (universal — same for all fermions in SU(2) doublet)

    • λ = 1 (overall normalization, matches CKMSchur8 convention)

  This identification is COMPLETELY DETERMINED — NO free parameters.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST OUTCOME (proved by explicit Lean witnesses)

  THE HIGGS+W TWO-BATH IDENTIFICATION ALSO FAILS to give V_us² = 1/20.

  Closed form V_us in this model:
       V_us = (m_u/v)·(m_s/v)/(1 − (log(5/3))²) + (g_W)²/(1 − 1/4)
            = [Yukawa, ≈ 10⁻⁹] + [Gauge, = 4/3]
            ≈ 4/3 = 1.333

  V_us² ≈ 1.778, vs framework target 1/20 = 0.05, vs PDG 0.0503.
  Off by a factor of ~36 from framework target, ~36 from PDG.

  Even if we use lab values (g_W² ≈ 0.43, lab m_H/v = 0.509):
    Gauge = 0.43/(1 - 0.107) ≈ 0.482
    V_us ≈ 0.482, V_us² ≈ 0.232 ≠ 1/20.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  ADDITIONAL OBSERVATION (the "smuggling" loophole)

  The gauge coupling is FLAVOR-DIAGONAL in the SU(2) gauge basis.
  That means gB matrix elements between different generations VANISH in
  the gauge basis. Off-diagonal SU(2) couplings only emerge AFTER applying
  a CKM rotation — but the CKM matrix is precisely what we're trying to
  derive. Using nonzero off-diagonal gauge couplings would be smuggling
  the answer in.

  We exhibit BOTH possibilities:
    (a) HONEST gauge identification: gauge is flavor-diagonal so V_us
        gauge contribution = 0, leaving only the tiny Yukawa piece.
        Result: V_us ≈ 5 × 10⁻⁹, V_us² ≈ 3 × 10⁻¹⁷.
    (b) NAIVE gauge identification: gauge couples universally to all
        fermions including off-diagonal generations.
        Result: V_us ≈ 4/3, V_us² ≈ 1.78.

  Neither (a) nor (b) gives V_us² = 1/20.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CLASSIFICATION

  Verdict: **FAILURE**. Identifying the two baths with the framework's
  derived Higgs and W sectors does NOT force V_us² = 1/20.

  This is the SIXTH strengthening attempt, and it confirms the structural
  obstruction identified in CKMSchur8: even using bath energies that
  are FULLY framework-derived (no choice at all), the predicted V_us²
  is OFF by orders of magnitude from the framework's claimed target.

  This is informative: it RULES OUT the "Higgs+W = the missing discrete
  identification" hypothesis. Whatever pins V_us² = 1/20 (if anything
  does), it is NOT the framework-derived gauge-boson scales.

  Zero sorry. Zero custom axioms.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import UnifiedTheory.LayerA.HiggsMassDerived
import UnifiedTheory.LayerB.PSectorMass
import UnifiedTheory.LayerB.CKMSchur8
import UnifiedTheory.LayerB.CKMOneLoopV2

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.HiggsWTwoBathTest

open Real
open UnifiedTheory.LayerA.HiggsMassDerived
open UnifiedTheory.LayerB.CKMSchur8
open UnifiedTheory.LayerB.CKMOneLoopV2

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: FRAMEWORK-DERIVED BATH ENERGIES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    λ_A = (m_H/v)² = (log(5/3))²  — Higgs bath energy
        Source: LayerA.HiggsMassDerived: m_H = log(5/3) · v  (tree-level
        prediction from the spectral gap, d=4, matches PDG within 0.5%).

    λ_B = (m_W/v)² = g_W²/4 = 1/4  — W bath energy
        Source: at the GUT scale, g_W² = 1 (from α_GUT = 3/(32π) with
        sin²θ_W = 3/8 and g² · sin²θ_W / (4π) = α_GUT). So m_W = (1/2)v
        gives λ_B = 1/4.

    λ = 1 — overall normalization (same as CKMSchur7/CKMSchur8).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The Higgs-bath energy: λ_A = (m_H/v)² = (log(5/3))². -/
noncomputable def lambda_Higgs : ℝ := (Real.log (5 / 3)) ^ 2

/-- The W-bath energy: λ_B = (m_W/v)² = g_W²/4 = 1/4. -/
noncomputable def lambda_W : ℝ := 1 / 4

/-- Overall spectral parameter (same convention as CKMSchur8). -/
noncomputable def lambda_norm : ℝ := 1

/-- λ_A is positive (sqrt of positive log squared). -/
theorem lambda_Higgs_pos : 0 < lambda_Higgs := by
  unfold lambda_Higgs
  have h : 0 < Real.log (5 / 3) := Real.log_pos (by norm_num : (1 : ℝ) < 5 / 3)
  positivity

/-- λ_A < 1 (since log(5/3) < 1, so (log(5/3))² < 1). -/
theorem lambda_Higgs_lt_one : lambda_Higgs < 1 := by
  unfold lambda_Higgs
  have h1 : Real.log (5 / 3) < 1 := LayerB.PSectorMass.log_five_thirds_lt_one
  have h0 : 0 < Real.log (5 / 3) := Real.log_pos (by norm_num : (1 : ℝ) < 5 / 3)
  nlinarith

/-- λ_A bounds: 1/4 < λ_A < 1. From log(5/3) > 1/2 (so squared > 1/4)
    and log(5/3) < 1 (so squared < 1). -/
theorem lambda_Higgs_bounds : 1 / 4 < lambda_Higgs ∧ lambda_Higgs < 1 := by
  refine ⟨?_, lambda_Higgs_lt_one⟩
  unfold lambda_Higgs
  have hlb := LayerB.PSectorMass.log_five_thirds_gt_half
  have h0 : 0 < Real.log (5 / 3) := Real.log_pos (by norm_num : (1 : ℝ) < 5 / 3)
  nlinarith

/-- λ_B = 1/4 explicitly. -/
theorem lambda_W_value : lambda_W = 1 / 4 := rfl

/-- The two baths have DIFFERENT energies (λ_A > 1/4 = λ_B), so the
    Schur complement is non-degenerate (no rank-collapse). -/
theorem baths_distinct : lambda_W < lambda_Higgs := by
  have ⟨h, _⟩ := lambda_Higgs_bounds
  rw [lambda_W_value]
  exact h

/-- Resolvent definedness: λ ≠ λ_A. Since λ = 1 and λ_A < 1. -/
theorem lambda_ne_lambda_Higgs : lambda_norm ≠ lambda_Higgs := by
  unfold lambda_norm
  have := lambda_Higgs_lt_one
  linarith

/-- Resolvent definedness: λ ≠ λ_B. Since λ = 1 and λ_B = 1/4. -/
theorem lambda_ne_lambda_W : lambda_norm ≠ lambda_W := by
  unfold lambda_norm lambda_W; norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: FERMION YUKAWA COUPLINGS (Bath A vertices)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Yukawa-style vertex: gA_i = m_fermion_i / v.

    Using PDG running masses at scale ~v:
      m_top    ≈ 173 GeV   ⇒  m_t/v ≈ 0.703
      m_charm  ≈ 1.27 GeV  ⇒  m_c/v ≈ 0.00516
      m_up     ≈ 2.2  MeV  ⇒  m_u/v ≈ 9 × 10⁻⁶

      m_bottom ≈ 4.18 GeV  ⇒  m_b/v ≈ 0.017
      m_strange ≈ 95 MeV   ⇒  m_s/v ≈ 4 × 10⁻⁴
      m_down   ≈ 4.7 MeV   ⇒  m_d/v ≈ 1.9 × 10⁻⁵

    For V_us we need:
       gA_up3 = m_u/v ≈ 9 × 10⁻⁶  (index 2 = up, top is 0)
       gA_down2 = m_s/v ≈ 4 × 10⁻⁴ (index 4 = strange, bottom is 3)

    Product gA_u3 · gA_d2 ≈ 3.6 × 10⁻⁹.

    Note: we use rational approximations (small_yukawa_*) for these
    to keep the arithmetic tractable. The exact values do NOT matter
    for the conclusion: any bound m_u/v < 10⁻⁴ and m_s/v < 10⁻³ gives
    Yukawa contribution < 10⁻⁷, vastly below the framework target.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Up-quark Yukawa: m_u/v ≈ 9 × 10⁻⁶. Use 1/100000 = 10⁻⁵ as
    rational upper bound. -/
noncomputable def yukawa_up : ℝ := 1 / 100000

/-- Strange-quark Yukawa: m_s/v ≈ 4 × 10⁻⁴. Use 1/2500 = 4 × 10⁻⁴. -/
noncomputable def yukawa_strange : ℝ := 1 / 2500

/-- These are upper bounds within an order of magnitude. -/
theorem yukawa_up_pos : 0 < yukawa_up := by unfold yukawa_up; norm_num

theorem yukawa_strange_pos : 0 < yukawa_strange := by unfold yukawa_strange; norm_num

/-- Yukawa product is small. -/
theorem yukawa_product_small :
    yukawa_up * yukawa_strange = 1 / 250000000 := by
  unfold yukawa_up yukawa_strange; norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: GAUGE COUPLING (Bath B vertices)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    From LayerA.AlphaGUT: at the unification scale, g₁² = g₂² = g₃² = 1.
    So gB_universal = g_W = 1 (in framework natural units at GUT scale).

    Gauge couplings are FLAVOR-DIAGONAL in the gauge basis.
    Two natural choices:

      (a) HONEST: gB_off-diagonal = 0 (gauge does NOT mix generations)
          ⇒ gB_u3 · gB_d2 = 0 (different generation indices)
          ⇒ Gauge contribution to V_us = 0.

      (b) NAIVE: treat "gauge couples universally" as gB_i = g_W = 1
          for ALL flavors, including off-diagonal pairings.
          ⇒ gB_u3 · gB_d2 = 1.
          But this assumes off-diagonal SU(2) currents, which only
          arise after CKM rotation — circular.

    We compute V_us under BOTH interpretations to be transparent.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Universal SU(2) gauge coupling magnitude g_W = 1 (framework GUT). -/
noncomputable def gauge_W : ℝ := 1

theorem gauge_W_value : gauge_W = 1 := rfl

theorem gauge_W_squared : gauge_W ^ 2 = 1 := by unfold gauge_W; norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: TWO CONFIGURATIONS — HONEST AND NAIVE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Both use the framework-determined bath energies λ_A, λ_B above.
    They differ in the gauge-vertex assignment.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Configuration (a) — HONEST gauge identification.
    Gauge couples flavor-diagonally only, so all OFF-DIAGONAL gB
    couplings vanish. Bath A (Higgs) carries Yukawa-style off-diagonal
    couplings. -/
noncomputable def honestConfig : EightStateCoupled where
  -- Within-sector J₄ entries (irrelevant for V_us cross-sector test, set to baseline)
  a1 := a₁_real
  a2 := 2 / 5
  a3 := 1 / 5
  b1 := 1 / 5
  b2 := 1 / Real.sqrt 50
  -- Bath A = Higgs at λ_A = (log(5/3))²
  lamA := lambda_Higgs
  -- Bath B = W at λ_B = 1/4
  lamB := lambda_W
  -- Bath A vertices: Yukawa-style m_i/v
  gAu1 := 1 / 1                 -- m_top/v ≈ 0.7, but only u3, d2 used here
  gAu2 := 1 / 200               -- m_charm/v ≈ 0.005
  gAu3 := yukawa_up             -- m_up/v ≈ 10⁻⁵
  gAd1 := 1 / 60                -- m_bottom/v ≈ 0.017
  gAd2 := yukawa_strange        -- m_strange/v ≈ 4×10⁻⁴
  gAd3 := 1 / 50000             -- m_down/v ≈ 2×10⁻⁵
  -- Bath B vertices: gauge is flavor-diagonal, so OFF-diagonal entries are 0
  -- (the only nonzero gauge contribution is for same-flavor — but Schur
  -- gives V_us = gBu3·gBd2 mixing different generations, which vanishes)
  gBu1 := 0; gBu2 := 0; gBu3 := 0
  gBd1 := 0; gBd2 := 0; gBd3 := 0
  lam := lambda_norm
  hlamA := lambda_ne_lambda_Higgs
  hlamB := lambda_ne_lambda_W

/-- Configuration (b) — NAIVE gauge identification.
    Gauge couples "universally" with magnitude g_W to ALL fermions in
    the SU(2) doublet, including off-diagonal pairings. -/
noncomputable def naiveConfig : EightStateCoupled where
  a1 := a₁_real
  a2 := 2 / 5
  a3 := 1 / 5
  b1 := 1 / 5
  b2 := 1 / Real.sqrt 50
  lamA := lambda_Higgs
  lamB := lambda_W
  -- Bath A: Yukawa
  gAu1 := 1 / 1
  gAu2 := 1 / 200
  gAu3 := yukawa_up
  gAd1 := 1 / 60
  gAd2 := yukawa_strange
  gAd3 := 1 / 50000
  -- Bath B: universal g_W = 1 across ALL channels
  gBu1 := gauge_W; gBu2 := gauge_W; gBu3 := gauge_W
  gBd1 := gauge_W; gBd2 := gauge_W; gBd3 := gauge_W
  lam := lambda_norm
  hlamA := lambda_ne_lambda_Higgs
  hlamB := lambda_ne_lambda_W

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: V_us CLOSED FORMS (NO FREE PARAMETERS)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- V_us in honest configuration: only Yukawa channel contributes.
    V_us = (m_u/v)·(m_s/v) / (1 − (log(5/3))²) + 0
         = yukawa_up · yukawa_strange / (1 − λ_A). -/
theorem honestConfig_V_us :
    honestConfig.V_us
      = yukawa_up * yukawa_strange / (1 - lambda_Higgs) := by
  rw [V_us_two_bath]
  show yukawa_up * yukawa_strange / (lambda_norm - lambda_Higgs)
       + (0 : ℝ) * 0 / (lambda_norm - lambda_W) = _
  unfold lambda_norm
  ring

/-- V_us in naive configuration: Yukawa + universal gauge.
    V_us = (m_u/v)·(m_s/v)/(1 − λ_A) + g_W²/(1 − 1/4)
         = (Yukawa) + (4/3) · g_W². -/
theorem naiveConfig_V_us :
    naiveConfig.V_us
      = yukawa_up * yukawa_strange / (1 - lambda_Higgs)
      + gauge_W * gauge_W / (1 - lambda_W) := by
  rw [V_us_two_bath]
  show yukawa_up * yukawa_strange / (lambda_norm - lambda_Higgs)
       + gauge_W * gauge_W / (lambda_norm - lambda_W) = _
  unfold lambda_norm
  ring

/-- The naive gauge contribution simplifies: g_W² / (1 - 1/4) = 4/3. -/
theorem naive_gauge_part :
    gauge_W * gauge_W / (1 - lambda_W) = 4 / 3 := by
  unfold gauge_W lambda_W
  norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: V_us COMPARISON WITH PDG AND FRAMEWORK TARGET
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Framework target: V_us² = 1/20 = 0.05, so V_us = √(1/20) ≈ 0.2236.
    PDG observed:     V_us ≈ 0.2243, V_us² ≈ 0.0503.

    HONEST config: V_us ≈ Yukawa_product / (positive number < 1)
                       < (4·10⁻⁹) / (3/4) ≈ 5·10⁻⁹.
       This is FAR BELOW both 1/20 and PDG.

    NAIVE config: V_us ≈ Yukawa + 4/3 ≈ 4/3 = 1.333.
       This is FAR ABOVE both 1/20 and PDG (off by factor ~6).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The honest V_us is positive (Yukawa product > 0, denominator > 0). -/
theorem honestConfig_V_us_pos : 0 < honestConfig.V_us := by
  rw [honestConfig_V_us]
  apply div_pos
  · exact mul_pos yukawa_up_pos yukawa_strange_pos
  · have := lambda_Higgs_lt_one; linarith

/- Upper bound discussion:
   The honest V_us = yukawa_up · yukawa_strange / (1 - lambda_Higgs).
   The numerator is 1/250000000. The denominator 1 - lambda_Higgs is
   bounded below by 1 - (13/25)^2 = 456/625 > 0.7 (using
   log(5/3) < 13/25 from HiggsMassDerived).
   So V_us < (1/250000000) / (456/625) = 625/(250000000 * 456) ≈ 5.5e-9,
   which is vastly less than 1/20 = 0.05. -/

/-- V_us in the honest configuration is FAR BELOW 1/20. -/
theorem honestConfig_V_us_lt_target :
    honestConfig.V_us < 1 / 20 := by
  rw [honestConfig_V_us, yukawa_product_small]
  have hub : Real.log (5 / 3) < 13 / 25 := log_five_thirds_lt_052
  have h0 : 0 < Real.log (5 / 3) := Real.log_pos (by norm_num : (1 : ℝ) < 5 / 3)
  have hlam_ub : lambda_Higgs < 169 / 625 := by
    unfold lambda_Higgs
    nlinarith
  have hd_pos : 0 < 1 - lambda_Higgs := by
    have := lambda_Higgs_lt_one; linarith
  have hd_lb : 456 / 625 < 1 - lambda_Higgs := by linarith
  rw [div_lt_iff₀ hd_pos]
  -- Need: 1/250000000 < (1/20) * (1 - lambda_Higgs)
  -- Since 1 - lambda_Higgs > 456/625, (1/20) * (1 - lambda_Higgs) > 456/12500
  nlinarith [hd_lb]

/-- V_us² in the honest configuration is FAR BELOW 1/20. -/
theorem honestConfig_V_us_sq_lt_target :
    honestConfig.V_us ^ 2 < 1 / 20 := by
  have hpos : 0 < honestConfig.V_us := honestConfig_V_us_pos
  have hlt : honestConfig.V_us < 1 / 20 := honestConfig_V_us_lt_target
  -- V_us^2 < (1/20)^2 = 1/400 < 1/20
  nlinarith [sq_nonneg honestConfig.V_us, hpos, hlt]

/-- The honest V_us² is NOT 1/20. -/
theorem honestConfig_V_us_sq_ne_target :
    honestConfig.V_us ^ 2 ≠ 1 / 20 := by
  intro h
  have := honestConfig_V_us_sq_lt_target
  linarith

/-! ## Naive configuration: V_us ≈ 4/3, far above 1/20 -/

/-- V_us in the naive configuration is GREATER than 1 (far above 1/20). -/
theorem naiveConfig_V_us_gt_one :
    naiveConfig.V_us > 1 := by
  rw [naiveConfig_V_us, naive_gauge_part]
  -- Goal: yukawa_up · yukawa_strange / (1 - λ_A) + 4/3 > 1
  have hpos : 0 < yukawa_up * yukawa_strange / (1 - lambda_Higgs) := by
    apply div_pos
    · exact mul_pos yukawa_up_pos yukawa_strange_pos
    · have := lambda_Higgs_lt_one; linarith
  linarith

/-- V_us² in the naive configuration is GREATER than 1, hence ≠ 1/20. -/
theorem naiveConfig_V_us_sq_gt_one :
    naiveConfig.V_us ^ 2 > 1 := by
  have h := naiveConfig_V_us_gt_one
  nlinarith

theorem naiveConfig_V_us_sq_ne_target :
    naiveConfig.V_us ^ 2 ≠ 1 / 20 := by
  intro h
  have := naiveConfig_V_us_sq_gt_one
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: PDG COMPARISON
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    PDG: |V_us| = 0.2243 ± 0.0008, so V_us² ≈ 0.0503.
    We use rational PDG bounds: 0.0500 < V_us²_PDG < 0.0510.

    Compare:
      honest V_us²  < 1/20 = 0.0500  (BELOW PDG window)
      naive V_us²   > 1.0            (ABOVE PDG window by factor ~20)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The PDG V_us² lower bound (rational approximation). -/
def Vus_sq_PDG_lb : ℚ := 50 / 1000

/-- The PDG V_us² upper bound (rational approximation). -/
def Vus_sq_PDG_ub : ℚ := 51 / 1000

/-- Honest config: V_us² is BELOW the PDG window. -/
theorem honestConfig_below_PDG :
    honestConfig.V_us ^ 2 < (Vus_sq_PDG_lb : ℝ) := by
  unfold Vus_sq_PDG_lb
  have h := honestConfig_V_us_sq_lt_target
  have : ((50 / 1000 : ℚ) : ℝ) = 1 / 20 := by push_cast; norm_num
  rw [this]; exact h

/-- Naive config: V_us² is ABOVE the PDG window. -/
theorem naiveConfig_above_PDG :
    naiveConfig.V_us ^ 2 > (Vus_sq_PDG_ub : ℝ) := by
  unfold Vus_sq_PDG_ub
  have h := naiveConfig_V_us_sq_gt_one
  have h2 : ((51 / 1000 : ℚ) : ℝ) < 1 := by push_cast; norm_num
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: THE OTHER CKM ENTRIES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For honest config: gauge contribution is zero everywhere off-diagonal
    in flavor; Yukawa products dominate. All cross-sector entries are
    of order (m_i/v)·(m_j/v), which is tiny for light-light pairings
    and tiny for Yukawa-suppressed off-diagonal pairings.

    For naive config: every cross-sector entry has the same g_W²/(1-λ_W)
    = 4/3 contribution from gauge, so V_us = V_cb = V_ub = V_ud ≈ 4/3
    plus tiny Yukawa corrections. This is OBVIOUSLY wrong (CKM is not
    democratic) — another confirmation that universal gauge gives a
    flat unrealistic structure.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Naive V_cb closed form. -/
theorem naiveConfig_V_cb :
    naiveConfig.V_cb = (1 / 200) * (1 / 60) / (1 - lambda_Higgs)
                     + gauge_W * gauge_W / (1 - lambda_W) := by
  rw [V_cb_two_bath]
  show (1 / 200 : ℝ) * (1 / 60) / (lambda_norm - lambda_Higgs)
       + gauge_W * gauge_W / (lambda_norm - lambda_W) = _
  unfold lambda_norm
  ring

/-- Naive V_ub closed form. -/
theorem naiveConfig_V_ub :
    naiveConfig.V_ub = yukawa_up * (1 / 60) / (1 - lambda_Higgs)
                     + gauge_W * gauge_W / (1 - lambda_W) := by
  rw [V_ub_two_bath]
  show yukawa_up * (1 / 60) / (lambda_norm - lambda_Higgs)
       + gauge_W * gauge_W / (lambda_norm - lambda_W) = _
  unfold lambda_norm
  ring

/-- Naive: V_us is approximately equal to V_cb and V_ub (all dominated
    by the same 4/3 gauge term). The gauge term is the SAME 4/3 in
    every cross-sector entry — a "democratic" structure that does NOT
    reproduce the observed CKM hierarchy V_ud ≫ V_us ≫ V_cb ≫ V_ub. -/
theorem naive_gives_democratic_CKM :
    naiveConfig.V_us > 1
    ∧ naiveConfig.V_cb > 1
    ∧ naiveConfig.V_ub > 1 := by
  refine ⟨naiveConfig_V_us_gt_one, ?_, ?_⟩
  · rw [naiveConfig_V_cb, naive_gauge_part]
    have hpos : 0 < (1/200 : ℝ) * (1/60) / (1 - lambda_Higgs) := by
      apply div_pos
      · norm_num
      · have := lambda_Higgs_lt_one; linarith
    linarith
  · rw [naiveConfig_V_ub, naive_gauge_part]
    have hpos : 0 < yukawa_up * (1/60) / (1 - lambda_Higgs) := by
      apply div_pos
      · exact mul_pos yukawa_up_pos (by norm_num)
      · have := lambda_Higgs_lt_one; linarith
    linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: SUMMARY THEOREM — Higgs+W identification fails
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER THEOREM (HIGGS+W TWO-BATH FAILS).**

    With bath energies fixed by the framework's two derived gauge-boson
    sectors:

       λ_A = (m_H/v)² = (log(5/3))²  (HiggsMassDerived: m_H = log(5/3) · v)
       λ_B = (m_W/v)² = g_W²/4 = 1/4 (AlphaGUT: g_W² = 1 at GUT)

    and vertex couplings determined by the framework's identification:

       Bath A vertices: gA_i = m_fermion_i / v (Yukawa-style)
       Bath B vertices: gauge-style (universal g_W or zero off-diagonal)

    NO assignment achieves V_us² = 1/20:

      (1) HONEST gauge identification (gauge is flavor-diagonal, so
          off-diagonal gB = 0): V_us = (Yukawa product)/(1 - λ_A)
                                     ≈ 4 × 10⁻⁹ / (≈ 3/4)
                                     ≈ 5 × 10⁻⁹.
          V_us² ≈ 3 × 10⁻¹⁷ ≪ 1/20. **Off by 17 orders of magnitude.**

      (2) NAIVE gauge identification (universal g_W couples all flavors):
          V_us = (Yukawa) + g_W²/(1 - 1/4)
               = (≈ 5 × 10⁻⁹) + 4/3
               ≈ 4/3 ≈ 1.333.
          V_us² ≈ 1.78 ≫ 1/20. **Off by factor of ~36 from target.**

    Neither matches the framework target 1/20 ≈ 0.05.
    Neither matches PDG V_us² ≈ 0.0503.

    Verdict: identifying the two baths with the framework's Higgs and W
    sectors does NOT pin V_us. The strengthening attempt FAILS: framework
    + SM gauge structure does NOT independently force V_us² = 1/20.

    The 1/20 result remains a SELECTION FROM A MENU, not a forced
    consequence of fixing the bath energies via the two derived
    gauge-boson scales. -/
theorem Higgs_W_two_bath_fails :
    -- (1) The bath energies are framework-derived
    lambda_Higgs = (Real.log (5 / 3)) ^ 2
    ∧ lambda_W = 1 / 4
    -- (2) HONEST identification: V_us² far below 1/20
    ∧ honestConfig.V_us ^ 2 < 1 / 20
    -- (3) NAIVE identification: V_us² far above 1/20 (in fact > 1)
    ∧ naiveConfig.V_us ^ 2 > 1
    -- (4) Neither gives V_us² = 1/20
    ∧ honestConfig.V_us ^ 2 ≠ 1 / 20
    ∧ naiveConfig.V_us ^ 2 ≠ 1 / 20
    -- (5) Honest is BELOW PDG window
    ∧ honestConfig.V_us ^ 2 < (Vus_sq_PDG_lb : ℝ)
    -- (6) Naive is ABOVE PDG window
    ∧ naiveConfig.V_us ^ 2 > (Vus_sq_PDG_ub : ℝ)
    -- (7) Naive predicts a "democratic" CKM (V_us ≈ V_cb ≈ V_ub ≈ 4/3)
    --     — qualitatively wrong (real CKM is hierarchical)
    ∧ (naiveConfig.V_us > 1 ∧ naiveConfig.V_cb > 1 ∧ naiveConfig.V_ub > 1) := by
  refine ⟨rfl, lambda_W_value,
          honestConfig_V_us_sq_lt_target,
          naiveConfig_V_us_sq_gt_one,
          honestConfig_V_us_sq_ne_target,
          naiveConfig_V_us_sq_ne_target,
          honestConfig_below_PDG,
          naiveConfig_above_PDG,
          naive_gives_democratic_CKM⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 10: HONEST SCOREBOARD (HIGGS+W RESULTS)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    | Configuration  | V_us            | V_us²    | Matches 1/20? | vs PDG?    |
    |----------------|-----------------|----------|---------------|------------|
    | honestConfig   | ~ 5 × 10⁻⁹      | ~ 3e-17  | NO (way below) | NO (below) |
    | naiveConfig    | ~ 4/3 = 1.33    | ~ 1.78   | NO (way above) | NO (above) |
    | Framework 1/20 | √5/10 ≈ 0.224   | 1/20     | YES (target)   | YES        |
    | PDG observed   | 0.2243 ± 0.0008 | ≈ 0.0503 |                |            |

    THE HONEST READING: identifying the two baths with the framework's
    derived Higgs and W sectors gives V_us² ≪ 1/20 (honest, gauge
    flavor-diagonal) or V_us² ≫ 1/20 (naive, gauge "universal"). Neither
    is the framework target.

    This is a clean FALSIFICATION of the hypothesis "the missing discrete
    identification is Higgs vs W." The framework's two derived gauge-boson
    scales do NOT pin V_us² to 1/20.

    What would be needed: a different bath identification, or an explicit
    framework-side mechanism that produces a vertex coupling of magnitude
    √(C_int · a₁) = √(1/20) for the (top-row, strange-row) cross-sector
    pairing — i.e., the answer needs to come from somewhere OTHER than
    the gauge-boson scales.

    SIXTH STRENGTHENING ATTEMPT VERDICT: FAILURE.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

end UnifiedTheory.LayerB.HiggsWTwoBathTest
