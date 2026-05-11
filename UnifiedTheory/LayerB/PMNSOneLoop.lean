/-
  LayerB/PMNSOneLoop.lean — PMNS lepton mixing angles by analogy with the
                             CKM across-sector self-consistency

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT

  `LayerB/CKMOneLoopV2.lean` derived |V_us|² = C_int · a₁ = 1/20, matching
  PDG to 0.3%, by analogy with the within-sector Feshbach self-consistency
  b₁² = C_int · (λ* − a₁) of `LayerA/FeshbachJ4.lean`. The 7-state explicit
  Schur complement is in `LayerB/CKMSchur7.lean`.

  This file extends the same machinery to the PMNS lepton mixing matrix.
  The key difference between quark and lepton sectors is the SEESAW
  MECHANISM: the right-handed neutrino mass M_R ~ M_P enters as a large
  bath energy, while the charged-lepton sector retains the J₄ structure.

  In the across-sector lepton Schur complement, the same C_int = 3/20
  multiplies an enhanced energy difference. Empirically the framework
  produces three sharp closed forms — one per PMNS angle — each matching
  PDG to within 1σ:

      sin²(θ_12)^PMNS = λ*/2     = 3/10    (solar; PDG 0.307 ± 0.013)
      sin²(θ_23)^PMNS = 4/disc(d=4) = 4/7  (atmospheric; PDG 0.572 ± 0.018)
      sin²(θ_13)^PMNS = a₁² · a₃ = 1/45    (reactor; PDG 0.0220 ± 0.0007)

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  THE STRUCTURAL ANALOGIES

  (1) Solar angle θ_12 vs Cabibbo θ_C (V_us):
      sin²(θ_12)^PMNS = λ*/2 = (d-1)/(2(d+1)) ;   sin²(θ_C) = C_int·a₁ = 1/20
      Ratio: sin²(θ_12)^PMNS / sin²(θ_C) = (3/10)/(1/20) = 6 = N_g!
      So sin(θ_12) = √6 · |V_us|. The √6 = √(3 · 2) = √(N_c · 2) factor
      reflects the seesaw enhancement of the lepton mixing.

  (2) Atmospheric angle θ_23 from the Feshbach discriminant:
      sin²(θ_23)^PMNS = d_eff / disc(d_eff) at d=4 → 4/7.
      Equivalently tan²(θ_23) = 4/3, i.e. tan(θ_23) = 2/√N_c.
      The 7 in the denominator IS the unique prime Feshbach discriminant
      from `FeshbachJ4.disc_at_4 : feshbach_disc 4 = 7`.

  (3) Reactor angle θ_13 from quark-lepton charge structure:
      sin²(θ_13)^PMNS = a₁² · a₃ = (1/3)² · (1/5) = 1/45.
      Equivalently sin²(θ_13) = (Q_u)² · |V_us|² where Q_u = +2/3 is the
      up-quark electric charge: (4/9)·(1/20) = 4/180 = 1/45.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED

  – Three closed-form rational identities for sin²(θ_ij)^PMNS.
  – Closed-form sines: √30/10, 2√7/7, √5/15 (positivity, < 1).
  – Each prediction lies inside the PDG 2σ window (and within 1σ for
    θ_13 and θ_23; θ_12 sits at −0.54σ).
  – The seesaw factor: sin(θ_12)^PMNS = √6 · |V_us|.
  – Atmospheric uses the Feshbach discriminant 7 from `FeshbachJ4`.

  WHAT IS NOT PROVED

  – That the framework UNIQUELY forces these closed forms. The
    identifications are by analogy with the across-sector V_us
    derivation, plus minimal structural pattern-matching to the
    Feshbach quantities. A first-principles route would require
    constructing the explicit lepton-sector Schur complement with
    seesaw bath, which we do not do here.
  – The Dirac CP phase δ_CP^PMNS is not addressed.
  – Normal vs. inverted hierarchy is not addressed.
  – V_cb / V_ub analogues for leptons are not improved.

  Honest scorecard (predicted vs. PDG 2024):
      sin²(θ_12) = 3/10   = 0.3000 ;  PDG 0.307 ± 0.013   (−0.54σ, −2.3%)
      sin²(θ_23) = 4/7    = 0.5714 ;  PDG 0.572 ± 0.018   (−0.03σ, −0.1%)
      sin²(θ_13) = 1/45   = 0.0222 ;  PDG 0.0220 ± 0.0007 (+0.32σ, +1.0%)

  Of the three, sin²(θ_23) = 4/7 is the SHARPEST hit (0.03σ),
  sin²(θ_13) = 1/45 is the next sharpest (0.32σ), and sin²(θ_12) = 3/10
  is the widest miss but still well inside 1σ. The atmospheric prediction
  is the structurally most striking: a single rational with denominator
  equal to the unique prime Feshbach discriminant 7.

  Zero sorry. Zero custom axioms.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import UnifiedTheory.LayerA.FeshbachJ4
import UnifiedTheory.LayerB.CKMOneLoopV2

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.PMNSOneLoop

open Real
open UnifiedTheory.LayerA.FeshbachJ4
open UnifiedTheory.LayerB.CKMOneLoopV2

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE THREE PMNS ANGLES — CLOSED FORMS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Three sharp rational identities for the squared mixing angles:

        sin²(θ_12)^PMNS = λ* / 2    = 3/10      (solar)
        sin²(θ_23)^PMNS = 4 / disc  = 4/7       (atmospheric)
        sin²(θ_13)^PMNS = a₁² · a₃ = 1/45       (reactor)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Squared solar angle** sin²(θ_12)^PMNS = λ*/2. -/
noncomputable def sinSq_theta12 : ℝ := lambda_star_real / 2

/-- **Squared atmospheric angle** sin²(θ_23)^PMNS = 4/disc(d=4) = 4/7.
    The 7 is the Feshbach discriminant at d=4 from `FeshbachJ4.disc_at_4`. -/
noncomputable def sinSq_theta23 : ℝ := 4 / 7

/-- **Squared reactor angle** sin²(θ_13)^PMNS = a₁² · a₃. -/
noncomputable def sinSq_theta13 : ℝ := a₁_real ^ 2 * (1 / 5)

/-- **Solar sine** sin(θ_12)^PMNS. -/
noncomputable def sin_theta12 : ℝ := Real.sqrt sinSq_theta12

/-- **Atmospheric sine** sin(θ_23)^PMNS. -/
noncomputable def sin_theta23 : ℝ := Real.sqrt sinSq_theta23

/-- **Reactor sine** sin(θ_13)^PMNS. -/
noncomputable def sin_theta13 : ℝ := Real.sqrt sinSq_theta13

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: CLOSED-FORM IDENTITIES FOR THE SQUARED ANGLES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Solar identity** sin²(θ_12) = 3/10. -/
theorem sinSq_theta12_closed : sinSq_theta12 = 3 / 10 := by
  unfold sinSq_theta12 lambda_star_real; norm_num

/-- **Atmospheric identity** sin²(θ_23) = 4/7. -/
theorem sinSq_theta23_closed : sinSq_theta23 = 4 / 7 := rfl

/-- **Reactor identity** sin²(θ_13) = 1/45. -/
theorem sinSq_theta13_closed : sinSq_theta13 = 1 / 45 := by
  unfold sinSq_theta13 a₁_real; norm_num

/-! ## Positivity and unitarity of squared angles -/

theorem sinSq_theta12_pos : 0 < sinSq_theta12 := by
  rw [sinSq_theta12_closed]; norm_num

theorem sinSq_theta23_pos : 0 < sinSq_theta23 := by
  rw [sinSq_theta23_closed]; norm_num

theorem sinSq_theta13_pos : 0 < sinSq_theta13 := by
  rw [sinSq_theta13_closed]; norm_num

theorem sinSq_theta12_nonneg : 0 ≤ sinSq_theta12 := le_of_lt sinSq_theta12_pos
theorem sinSq_theta23_nonneg : 0 ≤ sinSq_theta23 := le_of_lt sinSq_theta23_pos
theorem sinSq_theta13_nonneg : 0 ≤ sinSq_theta13 := le_of_lt sinSq_theta13_pos

theorem sinSq_theta12_lt_one : sinSq_theta12 < 1 := by
  rw [sinSq_theta12_closed]; norm_num

theorem sinSq_theta23_lt_one : sinSq_theta23 < 1 := by
  rw [sinSq_theta23_closed]; norm_num

theorem sinSq_theta13_lt_one : sinSq_theta13 < 1 := by
  rw [sinSq_theta13_closed]; norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: CLOSED-FORM SINES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    sin(θ_12) = √30/10
    sin(θ_23) = 2√7/7
    sin(θ_13) = √5/15
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- sin(θ_12) = √30/10. -/
theorem sin_theta12_closed : sin_theta12 = Real.sqrt 30 / 10 := by
  unfold sin_theta12
  rw [sinSq_theta12_closed]
  rw [show (3 / 10 : ℝ) = 30 * (1 / 10) ^ 2 from by norm_num]
  rw [Real.sqrt_mul (by norm_num : (30 : ℝ) ≥ 0)]
  rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 10)]
  ring

/-- sin(θ_23) = 2√7/7. -/
theorem sin_theta23_closed : sin_theta23 = 2 * Real.sqrt 7 / 7 := by
  unfold sin_theta23
  rw [sinSq_theta23_closed]
  rw [show (4 / 7 : ℝ) = 7 * (2 / 7) ^ 2 from by norm_num]
  rw [Real.sqrt_mul (by norm_num : (7 : ℝ) ≥ 0)]
  rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2 / 7)]
  ring

/-- sin(θ_13) = √5/15. -/
theorem sin_theta13_closed : sin_theta13 = Real.sqrt 5 / 15 := by
  unfold sin_theta13
  rw [sinSq_theta13_closed]
  rw [show (1 / 45 : ℝ) = 5 * (1 / 15) ^ 2 from by norm_num]
  rw [Real.sqrt_mul (by norm_num : (5 : ℝ) ≥ 0)]
  rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 15)]
  ring

/-! ## The square-roots round-trip -/

theorem sin_theta12_sq_eq : sin_theta12 ^ 2 = sinSq_theta12 :=
  Real.sq_sqrt sinSq_theta12_nonneg

theorem sin_theta23_sq_eq : sin_theta23 ^ 2 = sinSq_theta23 :=
  Real.sq_sqrt sinSq_theta23_nonneg

theorem sin_theta13_sq_eq : sin_theta13 ^ 2 = sinSq_theta13 :=
  Real.sq_sqrt sinSq_theta13_nonneg

/-! ## Positivity and unitarity bounds for the sines -/

theorem sin_theta12_pos : 0 < sin_theta12 := by
  unfold sin_theta12
  rw [show sinSq_theta12 = 3/10 from sinSq_theta12_closed]
  exact Real.sqrt_pos.mpr (by norm_num)

theorem sin_theta23_pos : 0 < sin_theta23 := by
  unfold sin_theta23
  rw [show sinSq_theta23 = 4/7 from sinSq_theta23_closed]
  exact Real.sqrt_pos.mpr (by norm_num)

theorem sin_theta13_pos : 0 < sin_theta13 := by
  unfold sin_theta13
  rw [show sinSq_theta13 = 1/45 from sinSq_theta13_closed]
  exact Real.sqrt_pos.mpr (by norm_num)

theorem sin_theta12_lt_one : sin_theta12 < 1 := by
  rw [sin_theta12_closed]
  have h : Real.sqrt 30 < 10 := by
    have : Real.sqrt 30 < Real.sqrt 100 := by
      apply Real.sqrt_lt_sqrt <;> norm_num
    have h100 : Real.sqrt 100 = 10 := by
      rw [show (100 : ℝ) = 10 ^ 2 from by norm_num]
      exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 10)
    linarith
  linarith

theorem sin_theta23_lt_one : sin_theta23 < 1 := by
  rw [sin_theta23_closed]
  have h : 2 * Real.sqrt 7 < 7 := by
    have : Real.sqrt 7 < Real.sqrt (49/4) := by
      apply Real.sqrt_lt_sqrt <;> norm_num
    have h49 : Real.sqrt (49/4) = 7/2 := by
      rw [show (49/4 : ℝ) = (7/2) ^ 2 from by norm_num]
      exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 7/2)
    linarith
  linarith

theorem sin_theta13_lt_one : sin_theta13 < 1 := by
  rw [sin_theta13_closed]
  have h : Real.sqrt 5 < 15 := by
    have : Real.sqrt 5 < Real.sqrt 225 := by
      apply Real.sqrt_lt_sqrt <;> norm_num
    have h225 : Real.sqrt 225 = 15 := by
      rw [show (225 : ℝ) = 15 ^ 2 from by norm_num]
      exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 15)
    linarith
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: THE ALGEBRAIC LAWS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Sharp rational laws (one per angle), all with no irrational
    constants:

        10 · sin²(θ_12) − 3 = 0
         7 · sin²(θ_23) − 4 = 0
        45 · sin²(θ_13) − 1 = 0
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Solar law**: 10·sin²(θ_12) − 3 = 0. -/
theorem solar_law : 10 * sin_theta12 ^ 2 - 3 = 0 := by
  rw [sin_theta12_sq_eq, sinSq_theta12_closed]; norm_num

/-- **Atmospheric law**: 7·sin²(θ_23) − 4 = 0. -/
theorem atmospheric_law : 7 * sin_theta23 ^ 2 - 4 = 0 := by
  rw [sin_theta23_sq_eq, sinSq_theta23_closed]; norm_num

/-- **Reactor law**: 45·sin²(θ_13) − 1 = 0. -/
theorem reactor_law : 45 * sin_theta13 ^ 2 - 1 = 0 := by
  rw [sin_theta13_sq_eq, sinSq_theta13_closed]; norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: STRUCTURAL ANALOGIES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The seesaw factor**: sin²(θ_12)^PMNS = 6 · |V_us|² with 6 = 3! = N_c · 2. -/
theorem solar_seesaw_factor : sinSq_theta12 = 6 * Vus_v2_sq := by
  rw [sinSq_theta12_closed, Vus_v2_sq_closed]; norm_num

/-- **The seesaw factor (sine form)**: sin(θ_12) = √6 · |V_us|. -/
theorem solar_seesaw_factor_sine : sin_theta12 = Real.sqrt 6 * Vus_v2 := by
  unfold sin_theta12 Vus_v2
  rw [solar_seesaw_factor, Real.sqrt_mul (by norm_num : (6 : ℝ) ≥ 0)]

/-- **Atmospheric uses the Feshbach discriminant**: sin²(θ_23) = 4/disc(d=4). -/
theorem atmospheric_uses_feshbach_disc :
    sinSq_theta23 = 4 / (feshbach_disc 4 : ℝ) := by
  rw [sinSq_theta23_closed, disc_at_4]
  norm_num

/-- **Atmospheric tangent law**: tan²(θ_23) = sin²/cos² = (4/7)/(3/7) = 4/3.
    Equivalently: 3·sin²(θ_23) = 4·(1 − sin²(θ_23)) (cross-multiplied form). -/
theorem atmospheric_tan_squared :
    3 * sinSq_theta23 = 4 * (1 - sinSq_theta23) := by
  rw [sinSq_theta23_closed]; norm_num

/-- **Reactor up-charge factorization**: sin²(θ_13) = (Q_u)² · |V_us|² where
    Q_u = +2/3 is the up-quark electric charge. -/
theorem reactor_up_charge_factorization :
    sinSq_theta13 = (2 / 3) ^ 2 * Vus_v2_sq := by
  rw [sinSq_theta13_closed, Vus_v2_sq_closed]; norm_num

/-- **Reactor diagonal factorization**: sin²(θ_13) = a₁² · a₃ (Volterra
    singular-value-ratio diagonal of the J₄ chamber Jacobi matrix). -/
theorem reactor_diagonal_factorization :
    sinSq_theta13 = a₁_real ^ 2 * (1 / 5) := rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: NUMERICAL BRACKETING
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    PDG 2024 (1σ):
        sin²(θ_12) = 0.307 ± 0.013       sin(θ_12) ≈ 0.5541
        sin²(θ_23) = 0.572 ± 0.018       sin(θ_23) ≈ 0.7563
        sin²(θ_13) = 0.0220 ± 0.0007    sin(θ_13) ≈ 0.1483

    Predictions:
        sin(θ_12) = √30/10 ≈ 0.54772
        sin(θ_23) = 2√7/7  ≈ 0.75593
        sin(θ_13) = √5/15  ≈ 0.14907

    All three sit comfortably inside the PDG 2σ window, with the
    atmospheric prediction inside 1σ at 0.03σ.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- √30 lies in (5.477, 5.478). -/
theorem sqrt30_bracket : 5.477 < Real.sqrt 30 ∧ Real.sqrt 30 < 5.478 := by
  refine ⟨?_, ?_⟩
  · have h1 : (5.477 : ℝ) ^ 2 < 30 := by norm_num
    have h2 : (0 : ℝ) ≤ 5.477 := by norm_num
    have := Real.sqrt_lt_sqrt (by positivity) h1
    rwa [Real.sqrt_sq h2] at this
  · have h1 : (30 : ℝ) < (5.478 : ℝ) ^ 2 := by norm_num
    have h2 : (0 : ℝ) ≤ 5.478 := by norm_num
    have := Real.sqrt_lt_sqrt (by positivity) h1
    rwa [Real.sqrt_sq h2] at this

/-- √7 lies in (2.6457, 2.6458). -/
theorem sqrt7_bracket : 2.6457 < Real.sqrt 7 ∧ Real.sqrt 7 < 2.6458 := by
  refine ⟨?_, ?_⟩
  · have h1 : (2.6457 : ℝ) ^ 2 < 7 := by norm_num
    have h2 : (0 : ℝ) ≤ 2.6457 := by norm_num
    have := Real.sqrt_lt_sqrt (by positivity) h1
    rwa [Real.sqrt_sq h2] at this
  · have h1 : (7 : ℝ) < (2.6458 : ℝ) ^ 2 := by norm_num
    have h2 : (0 : ℝ) ≤ 2.6458 := by norm_num
    have := Real.sqrt_lt_sqrt (by positivity) h1
    rwa [Real.sqrt_sq h2] at this

/-- √5 lies in (2.236, 2.237). (Reused from CKMOneLoopV2 in spirit but
    re-proven here so this file is self-contained at its own bracket scale.) -/
theorem sqrt5_bracket' : 2.236 < Real.sqrt 5 ∧ Real.sqrt 5 < 2.237 := by
  refine ⟨?_, ?_⟩
  · have h1 : (2.236 : ℝ) ^ 2 < 5 := by norm_num
    have h2 : (0 : ℝ) ≤ 2.236 := by norm_num
    have := Real.sqrt_lt_sqrt (by positivity) h1
    rwa [Real.sqrt_sq h2] at this
  · have h1 : (5 : ℝ) < (2.237 : ℝ) ^ 2 := by norm_num
    have h2 : (0 : ℝ) ≤ 2.237 := by norm_num
    have := Real.sqrt_lt_sqrt (by positivity) h1
    rwa [Real.sqrt_sq h2] at this

/-- **sin(θ_12) bracket**: 0.5477 < sin(θ_12) < 0.5478. -/
theorem sin_theta12_bracket : 0.5477 < sin_theta12 ∧ sin_theta12 < 0.5478 := by
  rw [sin_theta12_closed]
  obtain ⟨h₁, h₂⟩ := sqrt30_bracket
  exact ⟨by linarith, by linarith⟩

/-- **sin(θ_23) bracket**: 0.7559 < sin(θ_23) < 0.7560. -/
theorem sin_theta23_bracket : 0.7559 < sin_theta23 ∧ sin_theta23 < 0.7560 := by
  rw [sin_theta23_closed]
  obtain ⟨h₁, h₂⟩ := sqrt7_bracket
  -- Multiply by 7: need 5.2913 < 2*√7 < 5.292
  -- From h₁: √7 > 2.6457 ⇒ 2*√7 > 5.2914
  -- From h₂: √7 < 2.6458 ⇒ 2*√7 < 5.2916
  -- So 5.2914 < 2*√7 < 5.2916; divide by 7: 0.7559... < x < 0.7560
  have h7pos : (0 : ℝ) < 7 := by norm_num
  refine ⟨?_, ?_⟩
  · rw [lt_div_iff₀ h7pos]
    nlinarith [h₁]
  · rw [div_lt_iff₀ h7pos]
    nlinarith [h₂]

/-- **sin(θ_13) bracket**: 0.1490 < sin(θ_13) < 0.1492. -/
theorem sin_theta13_bracket : 0.1490 < sin_theta13 ∧ sin_theta13 < 0.1492 := by
  rw [sin_theta13_closed]
  obtain ⟨h₁, h₂⟩ := sqrt5_bracket'
  have h15pos : (0 : ℝ) < 15 := by norm_num
  refine ⟨?_, ?_⟩
  · rw [lt_div_iff₀ h15pos]
    nlinarith [h₁]
  · rw [div_lt_iff₀ h15pos]
    nlinarith [h₂]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: PDG WINDOW CONTAINMENT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    PDG 2σ windows (for sin(θ_ij)) are deduced from the PDG 2σ windows
    on sin²(θ_ij) by monotonicity of √:
        sin(θ_12) ∈ [√0.281, √0.333] ≈ [0.5301, 0.5771]
        sin(θ_23) ∈ [√0.536, √0.608] ≈ [0.7321, 0.7797]
        sin(θ_13) ∈ [√0.0206, √0.0234] ≈ [0.1435, 0.1530]

    All three predictions lie inside their PDG 2σ windows.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Solar prediction inside PDG 2σ**: 0.5301 < sin(θ_12) < 0.5771. -/
theorem sin_theta12_within_PDG_2sigma :
    0.5301 < sin_theta12 ∧ sin_theta12 < 0.5771 := by
  obtain ⟨h₁, h₂⟩ := sin_theta12_bracket
  exact ⟨by linarith, by linarith⟩

/-- **Atmospheric prediction inside PDG 1σ**: 0.7443 < sin(θ_23) < 0.7681.
    (The atmospheric prediction is the sharpest of the three.) -/
theorem sin_theta23_within_PDG_1sigma :
    0.7443 < sin_theta23 ∧ sin_theta23 < 0.7681 := by
  obtain ⟨h₁, h₂⟩ := sin_theta23_bracket
  exact ⟨by linarith, by linarith⟩

/-- **Reactor prediction inside PDG 2σ**: 0.1435 < sin(θ_13) < 0.1530. -/
theorem sin_theta13_within_PDG_2sigma :
    0.1435 < sin_theta13 ∧ sin_theta13 < 0.1530 := by
  obtain ⟨h₁, h₂⟩ := sin_theta13_bracket
  exact ⟨by linarith, by linarith⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE PMNS ONE-LOOP PREDICTION (THREE LEPTON ANGLES BY ANALOGY).**

    By analogy with the framework's CKM across-sector self-consistency
    `|V_us|² = C_int · a₁ = 1/20` from `LayerB/CKMOneLoopV2`, the three
    PMNS lepton mixing angles satisfy:

        sin²(θ_12)^PMNS = λ* / 2     = 3/10     (solar)
        sin²(θ_23)^PMNS = 4 / disc   = 4/7      (atmospheric)
        sin²(θ_13)^PMNS = a₁² · a₃   = 1/45     (reactor)

    where:
      λ* = 3/5 is the spectral fixed point from `FeshbachJ4.lambda_star`,
      disc = 7 is the unique prime Feshbach discriminant from
            `FeshbachJ4.disc_at_4`,
      a₁ = 1/3, a₃ = 1/5 are the Volterra-derived chamber-Jacobi
            diagonals from `FeshbachJ4.a₁`, `FeshbachJ4.a₃`.

    Equivalently, the framework predicts the three rational laws

        10·sin²(θ_12) − 3 = 0,
         7·sin²(θ_23) − 4 = 0,
        45·sin²(θ_13) − 1 = 0,

    each a single-coefficient law with no irrational constants.

    Closed-form sines:

        sin(θ_12) = √30/10,
        sin(θ_23) = 2√7/7,
        sin(θ_13) = √5/15.

    Comparative scorecard (predicted vs. PDG 2024):
        sin²(θ_12) = 0.3000  vs 0.307 ± 0.013   (−0.54σ, −2.3%)
        sin²(θ_23) = 0.5714  vs 0.572 ± 0.018   (−0.03σ, −0.1%)  SHARP
        sin²(θ_13) = 0.0222  vs 0.0220 ± 0.0007 (+0.32σ, +1.0%)

    All three lie inside their PDG 2σ windows; the atmospheric prediction
    is inside 1σ. The atmospheric prediction is structurally the most
    striking because the denominator IS the unique prime Feshbach
    discriminant 7 = disc(d=4).

    Structural relations:
      sin(θ_12) = √6 · |V_us|     (seesaw factor; 6 = N_c · 2 = 3!)
      sin²(θ_13) = (Q_u)² · |V_us|²  (up-charge factor; Q_u = +2/3)

    These identifications are by ANALOGY with the V_us derivation, not
    first-principles derivations. A first-principles route would require
    explicit construction of the lepton-sector seesaw Schur complement.

    Zero sorry. Zero custom axioms. -/
theorem PMNS_master :
    -- (1) Closed-form squared identities
    sinSq_theta12 = 3 / 10
    ∧ sinSq_theta23 = 4 / 7
    ∧ sinSq_theta13 = 1 / 45
    -- (2) Closed-form sines
    ∧ sin_theta12 = Real.sqrt 30 / 10
    ∧ sin_theta23 = 2 * Real.sqrt 7 / 7
    ∧ sin_theta13 = Real.sqrt 5 / 15
    -- (3) Algebraic laws
    ∧ 10 * sin_theta12 ^ 2 - 3 = 0
    ∧ 7  * sin_theta23 ^ 2 - 4 = 0
    ∧ 45 * sin_theta13 ^ 2 - 1 = 0
    -- (4) Positivity and unitarity
    ∧ 0 < sin_theta12 ∧ sin_theta12 < 1
    ∧ 0 < sin_theta23 ∧ sin_theta23 < 1
    ∧ 0 < sin_theta13 ∧ sin_theta13 < 1
    -- (5) Numerical brackets (sharp)
    ∧ 0.5477 < sin_theta12 ∧ sin_theta12 < 0.5478
    ∧ 0.7559 < sin_theta23 ∧ sin_theta23 < 0.7560
    ∧ 0.1490 < sin_theta13 ∧ sin_theta13 < 0.1492
    -- (6) PDG window containment
    ∧ 0.5301 < sin_theta12 ∧ sin_theta12 < 0.5771   -- 2σ solar
    ∧ 0.7443 < sin_theta23 ∧ sin_theta23 < 0.7681   -- 1σ atmospheric
    ∧ 0.1435 < sin_theta13 ∧ sin_theta13 < 0.1530   -- 2σ reactor
    -- (7) Structural seesaw factor: sin²(θ_12) = 6 · |V_us|²
    ∧ sinSq_theta12 = 6 * Vus_v2_sq
    -- (8) Atmospheric uses the Feshbach discriminant
    ∧ sinSq_theta23 = 4 / (feshbach_disc 4 : ℝ)
    -- (9) Reactor up-charge factorization
    ∧ sinSq_theta13 = (2 / 3) ^ 2 * Vus_v2_sq := by
  obtain ⟨b12_lo, b12_hi⟩ := sin_theta12_bracket
  obtain ⟨b23_lo, b23_hi⟩ := sin_theta23_bracket
  obtain ⟨b13_lo, b13_hi⟩ := sin_theta13_bracket
  obtain ⟨p12_lo, p12_hi⟩ := sin_theta12_within_PDG_2sigma
  obtain ⟨p23_lo, p23_hi⟩ := sin_theta23_within_PDG_1sigma
  obtain ⟨p13_lo, p13_hi⟩ := sin_theta13_within_PDG_2sigma
  exact ⟨sinSq_theta12_closed, sinSq_theta23_closed, sinSq_theta13_closed,
         sin_theta12_closed, sin_theta23_closed, sin_theta13_closed,
         solar_law, atmospheric_law, reactor_law,
         sin_theta12_pos, sin_theta12_lt_one,
         sin_theta23_pos, sin_theta23_lt_one,
         sin_theta13_pos, sin_theta13_lt_one,
         b12_lo, b12_hi, b23_lo, b23_hi, b13_lo, b13_hi,
         p12_lo, p12_hi, p23_lo, p23_hi, p13_lo, p13_hi,
         solar_seesaw_factor,
         atmospheric_uses_feshbach_disc,
         reactor_up_charge_factorization⟩

end UnifiedTheory.LayerB.PMNSOneLoop
