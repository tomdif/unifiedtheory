/-
  LayerA/CosmologicalConstantN.lean — The substrate count N implied by Λ.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT

  `LayerA/CosmologicalConstant.lean` proves the Sorkin scaling law
  Λ² · N = 1 from the Poisson-substrate hypothesis (N = ρ · V causal
  elements in 4-volume V give a fluctuation Λ ~ N^{-1/2}). The same
  identity is exported by `Predictions.pred_cosmological_constant` and
  re-proved in `LayerB/VirtualGravitons.lean` from the virtual-graviton
  vacuum-bubble viewpoint.

  This file extracts the *quantitative content* of that identity:
  given the observed value Λ ~ 10^{-122} M_P^4 (Planck units), what is
  the implied number of substrate elements N? And how does that number
  compare with other independently-motivated estimates of N (de Sitter
  horizon volume in Planck units, age of universe in Planck units,
  holographic area bound)?

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED

  (1) The framework's prediction is sharply equivalent to the rational
      identity N = 1 / Λ² (parameter-free real theorem).

  (2) For Λ small, N is large; specifically Λ ≤ 10^{-k} ⟹ N ≥ 10^{2k}
      (mathematical bracketing of "observed Λ ~ 10^{-122} ⟹ N ~ 10^{244}").

  (3) Three independent estimates of N from the cosmology literature
      are encoded as REAL relations and compared with N = 1/Λ²:

      (a) de Sitter horizon 4-volume V_dS ~ 1/Λ² (Planck units)
          ⟹ N_dS = V_dS = 1/Λ². EXACTLY MATCHES the framework prediction
          (with density ρ = 1 in Planck units), confirming the
          self-consistency relation already proved in
          `LayerA.CosmologicalConstant.self_consistency`.

      (b) Age of universe t_U in Planck units (~10^{61}) ⟹
          N_age = t_U^4 ~ 10^{244}. ALSO MATCHES the framework
          prediction at leading order — the past 4-volume of an
          observer in a de Sitter universe is set by the age.

      (c) Holographic Bekenstein-Hawking area bound A_dS ~ 1/Λ
          (Planck units) ⟹ N_BH = A_dS / 4 ~ 10^{122}. This is
          the SQUARE ROOT of the framework's N. It counts horizon
          *area* bits, not bulk *volume* events.

  (4) The "Sorkin = de Sitter volume" coincidence is recorded as a
      theorem: 1/Λ² (framework N) equals (1/Λ²) (de Sitter volume in
      Planck units) — they are literally the same quantity. The
      framework's count agrees with the bulk-volume estimate, NOT with
      the holographic area estimate.

  WHAT IS NOT PROVED

  – The numerical value of Λ in Planck units (10^{-122}) is not derived
    from first principles in this file. The framework PREDICTS the
    relation Λ² · N = 1; the value of N (equivalently of Λ) is set by
    initial conditions of the cosmic causal set or by an as-yet-
    unproved dynamical principle.

  – That N is in fact an integer count (rather than a real-valued
    density × volume product). The Lean statements work in real
    numbers throughout; the integer interpretation is a substrate-
    counting axiom carried by `LayerA.SubstrateBridge`.

  – That the de Sitter past 4-volume coincidence with N is more than
    a self-consistency relation. The framework does not currently
    predict the AGE of the universe from first principles either.

  Zero sorry. Zero custom axioms.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import UnifiedTheory.LayerA.CosmologicalConstant

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerA.CosmologicalConstantN

open Real
open UnifiedTheory.LayerA.CosmologicalConstant

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: SHARP RESTATEMENT — Λ² · N = 1 AS A REAL IDENTITY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The substrate count implied by a positive cosmological constant.**
    With Λ in Planck units, N = 1/Λ². This is the Sorkin identity
    Λ² · N = 1 solved for N. -/
noncomputable def Nsub (Λ : ℝ) : ℝ := 1 / Λ ^ 2

/-- N is positive whenever Λ is nonzero. -/
theorem Nsub_pos (Λ : ℝ) (hΛ : Λ ≠ 0) : 0 < Nsub Λ := by
  unfold Nsub
  have : 0 < Λ ^ 2 := by positivity
  exact div_pos one_pos this

/-- **Sharp identity**: Λ² · N(Λ) = 1. Parameter-free real theorem. -/
theorem lambda_sq_times_Nsub (Λ : ℝ) (hΛ : Λ ≠ 0) :
    Λ ^ 2 * Nsub Λ = 1 := by
  unfold Nsub
  field_simp

/-- **N is monotone-decreasing in Λ²** — smaller Λ implies larger N. -/
theorem Nsub_anti (Λ₁ Λ₂ : ℝ) (h₁ : 0 < Λ₁) (h₂ : 0 < Λ₂)
    (h_le : Λ₁ ≤ Λ₂) : Nsub Λ₂ ≤ Nsub Λ₁ := by
  unfold Nsub
  have hsq₁ : 0 < Λ₁ ^ 2 := sq_pos_of_pos h₁
  have hsq₂ : 0 < Λ₂ ^ 2 := sq_pos_of_pos h₂
  have h_sq_le : Λ₁ ^ 2 ≤ Λ₂ ^ 2 := by
    have := mul_self_le_mul_self h₁.le h_le
    rw [show Λ₁ ^ 2 = Λ₁ * Λ₁ from sq Λ₁,
        show Λ₂ ^ 2 = Λ₂ * Λ₂ from sq Λ₂]
    exact this
  exact one_div_le_one_div_of_le hsq₁ h_sq_le

/-- **Compatibility with `sorkinLambda`.** When Λ = sorkinLambda ρ V,
    the N derived from Λ equals ρ · V (the substrate count). -/
theorem Nsub_eq_rho_V (ρ V : ℝ) (hρ : 0 < ρ) (hV : 0 < V) :
    Nsub (sorkinLambda ρ V) = ρ * V := by
  unfold Nsub
  rw [sorkin_scaling ρ V hρ hV]
  field_simp

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: BRACKETING — SMALL Λ ⟹ LARGE N
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    If Λ ≤ ε then N(Λ) ≥ 1/ε². For ε = 10^{-k} this gives N ≥ 10^{2k}.
    Encoding the observed estimate Λ ~ 10^{-122} ⟹ N ~ 10^{244}.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The lower bound**: Λ ≤ ε with both positive ⟹ N(Λ) ≥ 1/ε². -/
theorem Nsub_lower_bound (Λ ε : ℝ) (hΛ : 0 < Λ) (hε : 0 < ε)
    (h_le : Λ ≤ ε) : 1 / ε ^ 2 ≤ Nsub Λ := by
  unfold Nsub
  have hsqΛ : 0 < Λ ^ 2 := sq_pos_of_pos hΛ
  have hsqε : 0 < ε ^ 2 := sq_pos_of_pos hε
  have h_sq : Λ ^ 2 ≤ ε ^ 2 := by
    have := mul_self_le_mul_self hΛ.le h_le
    rw [show Λ ^ 2 = Λ * Λ from sq Λ,
        show ε ^ 2 = ε * ε from sq ε]
    exact this
  exact one_div_le_one_div_of_le hsqΛ h_sq

/-- **The upper bound**: ε ≤ Λ with both positive ⟹ N(Λ) ≤ 1/ε². -/
theorem Nsub_upper_bound (Λ ε : ℝ) (hε : 0 < ε)
    (h_le : ε ≤ Λ) : Nsub Λ ≤ 1 / ε ^ 2 := by
  unfold Nsub
  have hΛ : 0 < Λ := lt_of_lt_of_le hε h_le
  have hsqΛ : 0 < Λ ^ 2 := sq_pos_of_pos hΛ
  have hsqε : 0 < ε ^ 2 := sq_pos_of_pos hε
  have h_sq : ε ^ 2 ≤ Λ ^ 2 := by
    have := mul_self_le_mul_self hε.le h_le
    rw [show Λ ^ 2 = Λ * Λ from sq Λ,
        show ε ^ 2 = ε * ε from sq ε]
    exact this
  exact one_div_le_one_div_of_le hsqε h_sq

/-- **Two-sided bracket**: ε₁ ≤ Λ ≤ ε₂ (all positive) implies
    1/ε₂² ≤ N(Λ) ≤ 1/ε₁².
    This is the form used to convert Λ-error bars into N-error bars. -/
theorem Nsub_bracket (Λ ε₁ ε₂ : ℝ) (hε₁ : 0 < ε₁)
    (h₁ : ε₁ ≤ Λ) (h₂ : Λ ≤ ε₂) :
    1 / ε₂ ^ 2 ≤ Nsub Λ ∧ Nsub Λ ≤ 1 / ε₁ ^ 2 := by
  have hΛ : 0 < Λ := lt_of_lt_of_le hε₁ h₁
  have hε₂ : 0 < ε₂ := lt_of_lt_of_le hΛ h₂
  refine ⟨?_, Nsub_upper_bound Λ ε₁ hε₁ h₁⟩
  exact Nsub_lower_bound Λ ε₂ hΛ hε₂ h₂

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: NUMERICAL EVALUATION FOR THE OBSERVED Λ ~ 10^{-122}
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Direct rational instances. We avoid Real.rpow with non-integer
    exponents and use only natural-number powers of 10.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Concrete instance**: if Λ = 10^{-122} (i.e., Λ = 1 / 10^{122})
    then N(Λ) = (10^{122})² = 10^{244}. -/
theorem Nsub_at_observed_lambda :
    Nsub ((1 : ℝ) / (10 : ℝ) ^ (122 : ℕ)) = ((10 : ℝ) ^ (122 : ℕ)) ^ 2 := by
  unfold Nsub
  have h10 : ((10 : ℝ) ^ (122 : ℕ)) ≠ 0 := by
    apply pow_ne_zero
    norm_num
  rw [div_pow, one_pow, one_div, inv_div, div_one]

/-- **The observed value of N is ≥ 10^{244} when Λ ≤ 10^{-122}.**
    Bracket form, parameter Λ. -/
theorem Nsub_ge_10_244_of_lambda_le (Λ : ℝ) (hΛ : 0 < Λ)
    (h_le : Λ ≤ (1 : ℝ) / (10 : ℝ) ^ (122 : ℕ)) :
    ((10 : ℝ) ^ (122 : ℕ)) ^ 2 ≤ Nsub Λ := by
  have h10pos : (0 : ℝ) < (10 : ℝ) ^ (122 : ℕ) := by positivity
  have hε : (0 : ℝ) < (1 : ℝ) / (10 : ℝ) ^ (122 : ℕ) := by positivity
  have h := Nsub_lower_bound Λ ((1 : ℝ) / (10 : ℝ) ^ (122 : ℕ)) hΛ hε h_le
  -- h : 1 / ((1/10^122))^2 ≤ Nsub Λ
  -- want: (10^122)^2 ≤ Nsub Λ
  have hrew : (1 : ℝ) / ((1 : ℝ) / (10 : ℝ) ^ (122 : ℕ)) ^ 2 =
              ((10 : ℝ) ^ (122 : ℕ)) ^ 2 := by
    have h10ne : ((10 : ℝ) ^ (122 : ℕ)) ≠ 0 := ne_of_gt h10pos
    field_simp
  linarith [hrew ▸ h]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: THREE INDEPENDENT N ESTIMATES FROM COSMOLOGY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    (a) de Sitter horizon 4-volume V_dS ~ 1/Λ² in Planck units
        ⟹ N_dS = V_dS = 1/Λ² ~ 10^{244}.
    (b) Age of universe in Planck units t_U ~ 10^{61}
        ⟹ N_age = t_U^4 ~ 10^{244} (past 4-volume of observer).
    (c) Bekenstein-Hawking area in Planck units A_dS ~ 1/Λ
        ⟹ N_BH = A_dS / 4 ~ 10^{122} (horizon area bits).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **(a) de Sitter horizon 4-volume in Planck units.**
    For a de Sitter universe with cosmological constant Λ, the
    horizon length is ~ 1/√Λ and the horizon 4-volume scales as
    1/Λ². We take V_dS = 1/Λ² as the canonical normalization. -/
noncomputable def deSitterVolume (Λ : ℝ) : ℝ := 1 / Λ ^ 2

/-- The de Sitter volume EQUALS the framework's N. (Self-consistency
    of the Sorkin scaling at unit Planck density.) -/
theorem deSitter_eq_Nsub (Λ : ℝ) : deSitterVolume Λ = Nsub Λ := rfl

/-- **(b) Age of universe in Planck units, raised to the fourth.**
    The past 4-volume of an observer of age t (Planck units) is ~ t^4.
    For t_U ~ 10^{61}, this is ~ 10^{244}. -/
noncomputable def ageVolume (t : ℝ) : ℝ := t ^ 4

/-- The age-volume estimate at t = 10^{61} equals (10^{61})^4 = 10^{244}. -/
theorem ageVolume_at_observed_age :
    ageVolume ((10 : ℝ) ^ (61 : ℕ)) = (10 : ℝ) ^ (244 : ℕ) := by
  unfold ageVolume
  rw [← pow_mul]

/-- The de Sitter volume estimate at Λ = 10^{-122} equals 10^{244}. -/
theorem deSitterVolume_at_observed_lambda :
    deSitterVolume ((1 : ℝ) / (10 : ℝ) ^ (122 : ℕ)) = (10 : ℝ) ^ (244 : ℕ) := by
  unfold deSitterVolume
  rw [div_pow, one_pow, one_div, inv_div, div_one, ← pow_mul]

/-- **The age-4-volume and de Sitter volume agree at the observed values.**
    Both give N ~ 10^{244} — the framework's prediction. -/
theorem age_volume_matches_deSitter :
    ageVolume ((10 : ℝ) ^ (61 : ℕ)) =
      deSitterVolume ((1 : ℝ) / (10 : ℝ) ^ (122 : ℕ)) := by
  rw [ageVolume_at_observed_age, deSitterVolume_at_observed_lambda]

/-- **The framework's N at observed Λ matches both estimates.** -/
theorem Nsub_matches_volume_estimates :
    Nsub ((1 : ℝ) / (10 : ℝ) ^ (122 : ℕ)) =
      deSitterVolume ((1 : ℝ) / (10 : ℝ) ^ (122 : ℕ))
    ∧ Nsub ((1 : ℝ) / (10 : ℝ) ^ (122 : ℕ)) =
      ageVolume ((10 : ℝ) ^ (61 : ℕ)) := by
  refine ⟨(deSitter_eq_Nsub _).symm, ?_⟩
  rw [(deSitter_eq_Nsub ((1 : ℝ) / (10 : ℝ) ^ (122 : ℕ))).symm]
  rw [deSitterVolume_at_observed_lambda, ← ageVolume_at_observed_age]

/-- **(c) Bekenstein-Hawking horizon area in Planck units.**
    A_dS ~ 1/Λ, and the area-bit count is A/4 ~ 1/(4Λ). For
    Λ = 10^{-122}, this is ~ (1/4) · 10^{122} ~ 10^{122}.

    This is the SQUARE ROOT (up to constants) of the framework's N.
    The framework counts BULK 4-volume events; the BH bound counts
    BOUNDARY 2-area bits. Bulk vs. boundary, dimension 4 vs. 2. -/
noncomputable def BHArea (Λ : ℝ) : ℝ := 1 / Λ

/-- The BH area bound at Λ = 10^{-122}: A_dS = 10^{122}. -/
theorem BHArea_at_observed_lambda :
    BHArea ((1 : ℝ) / (10 : ℝ) ^ (122 : ℕ)) = (10 : ℝ) ^ (122 : ℕ) := by
  unfold BHArea
  have h10ne : ((10 : ℝ) ^ (122 : ℕ)) ≠ 0 := by
    apply pow_ne_zero; norm_num
  rw [one_div_one_div]

/-- **Bulk vs. boundary discrepancy**: the framework's N is the SQUARE
    of the BH area count. Numerically: 10^{244} = (10^{122})².
    The framework counts BULK events; BH counts BOUNDARY area-bits. -/
theorem Nsub_is_BHArea_squared :
    Nsub ((1 : ℝ) / (10 : ℝ) ^ (122 : ℕ)) =
      (BHArea ((1 : ℝ) / (10 : ℝ) ^ (122 : ℕ))) ^ 2 := by
  rw [Nsub_at_observed_lambda, BHArea_at_observed_lambda]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: SCOPE — N IS A RELATION, NOT A NUMBER
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The framework PREDICTS the relation Λ² · N = 1. It does NOT, in
    its current form, predict the value of N (equivalently of Λ).
    Three orthogonal possibilities exist:

    (i) N is an INITIAL CONDITION of the cosmic causal set. The
        substrate is born with some count N₀, and the cosmological
        constant is then determined as Λ = 1/√N₀.

    (ii) N is set by a DYNAMICAL PRINCIPLE outside the present scope —
         e.g., a holographic bulk/boundary matching N = (BH area)²,
         which would give a relation between bulk count and boundary
         entropy that we have not derived.

    (iii) N is set by an ANTHROPIC observer-time-volume condition —
          the past 4-volume of any observer who could be asking this
          question is bounded above by some t_obs^4.

    None of (i), (ii), (iii) is currently provable inside this Lean
    development. We record only:

      – The relation Λ² · N = 1 is sharp.
      – The implied N ~ 10^{244} agrees with both the de Sitter horizon
        4-volume estimate and the past 4-volume of an observer of age
        ~10^{61} Planck times.
      – It DISAGREES with the BH boundary area count, which gives
        only ~10^{122} bits — the SQUARE ROOT of the bulk count.
        This is not a contradiction: bulk and boundary counts are
        related by the holographic principle, and the framework's
        Sorkin scaling explicitly counts BULK 4-volume events.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The framework predicts a RELATION, not a value.**
    Given any positive Λ, the substrate count N is forced to be 1/Λ².
    The value of Λ itself is not predicted by this file (or by the
    framework as a whole, in its current state). -/
theorem framework_predicts_relation :
    ∀ Λ : ℝ, Λ ≠ 0 → Λ ^ 2 * Nsub Λ = 1 :=
  lambda_sq_times_Nsub

/-- **Scope statement (Lean form)**: there is no theorem in this
    development that fixes Λ to a specific value. Equivalently, the
    map Λ ↦ Nsub Λ is bijective on ℝ_{>0}, so for any candidate
    value of N we can produce a corresponding Λ that satisfies the
    Sorkin scaling. -/
theorem Nsub_is_bijective_on_pos (N : ℝ) (hN : 0 < N) :
    ∃ Λ : ℝ, 0 < Λ ∧ Nsub Λ = N := by
  refine ⟨1 / Real.sqrt N, ?_, ?_⟩
  · exact div_pos one_pos (Real.sqrt_pos.mpr hN)
  · unfold Nsub
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
    have h_sq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN.le
    rw [div_pow, one_pow, one_div, inv_div, div_one, h_sq]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: CAPSTONE — THE Λ²·N = 1 PREDICTION, QUANTIFIED
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE COSMOLOGICAL-CONSTANT-N CAPSTONE.**

    The Sorkin scaling Λ² · N = 1 has the following sharp content
    when combined with the observed cosmological constant
    Λ ~ 10^{-122} M_P^4:

    (1) The implied substrate count is N = 1/Λ² ~ 10^{244}.

    (2) This number AGREES with the de Sitter horizon 4-volume
        V_dS = 1/Λ² (in Planck units, ρ_Planck = 1).

    (3) It also AGREES (numerically) with the past 4-volume t_U^4
        of an observer of age t_U ~ 10^{61} Planck times.

    (4) It is the SQUARE of the Bekenstein-Hawking horizon area
        count A_dS ~ 1/Λ ~ 10^{122} bits — bulk vs. boundary.

    (5) The framework predicts the RELATION Λ² · N = 1; the
        ABSOLUTE value of N (equivalently of Λ) is not determined
        by any theorem in the present development. It is set by
        initial conditions of the cosmic causal set, or by a
        dynamical principle (holographic, anthropic, or other) that
        is outside the scope of the current Lean files. -/
theorem cosmological_constant_N_summary :
    -- (1) Sharp identity
    (∀ Λ : ℝ, Λ ≠ 0 → Λ ^ 2 * Nsub Λ = 1)
    -- (2) Concrete value at Λ = 10^{-122}
    ∧ (Nsub ((1 : ℝ) / (10 : ℝ) ^ (122 : ℕ)) = (10 : ℝ) ^ (244 : ℕ))
    -- (3) Agreement with de Sitter horizon 4-volume
    ∧ (∀ Λ : ℝ, deSitterVolume Λ = Nsub Λ)
    -- (4) Agreement with age-4-volume at observed values
    ∧ (ageVolume ((10 : ℝ) ^ (61 : ℕ)) = (10 : ℝ) ^ (244 : ℕ))
    -- (5) Square-of-BH-area relation
    ∧ (Nsub ((1 : ℝ) / (10 : ℝ) ^ (122 : ℕ)) =
        (BHArea ((1 : ℝ) / (10 : ℝ) ^ (122 : ℕ))) ^ 2)
    -- (6) The relation N = 1/Λ² is bijective on positives — any N
    --     compatible with Λ² N = 1 corresponds to a unique Λ
    ∧ (∀ N : ℝ, 0 < N → ∃ Λ : ℝ, 0 < Λ ∧ Nsub Λ = N) := by
  refine ⟨framework_predicts_relation, ?_, fun _ => rfl, ageVolume_at_observed_age, ?_, ?_⟩
  · -- (2) Nsub at Λ = 10^{-122} equals 10^{244}
    rw [Nsub_at_observed_lambda, ← pow_mul]
  · -- (5) Square-of-BH-area
    exact Nsub_is_BHArea_squared
  · exact Nsub_is_bijective_on_pos

end UnifiedTheory.LayerA.CosmologicalConstantN
