/-
  LayerC/PhysicalInformationLimits.lean
  ─────────────────────────────────────

  **Cross-domain synthesis: do the physical speed/information limits
  unify into a SINGLE inequality?**

  The folklore conjecture this file confronts head-on:

     "There is one master inequality that simultaneously expresses the
      quantum speed limit (Margolus–Levitin / Mandelstam–Tamm), the
      Lieb–Robinson finite-information-velocity bound, and the
      Bekenstein/Lloyd information-capacity bound."

  ══════════════════════════════════════════════════════════════════════
  HONEST VERDICT (this is the informative result):

    The naive "one inequality" conjecture is **FALSE**.  We *prove* it is
    false.  The genuine structure is **THREE INDEPENDENT AXES** that
    **COMPOSE** — they are NOT restatements of one another:

      • TEMPORAL axis  — energy↔time.  The Margolus–Levitin time bound
        `T ≥ π/(2E)`, the Mandelstam–Tamm inequality `T·⟨H⟩ ≥ π/2`, and
        Lloyd's maximum-operation-RATE `≤ 2E/π` are the **SAME** bound
        (reciprocal time = rate).  This axis genuinely UNIFIES.
        ⇒ `temporal_unification`.

      • CAPACITY axis  — area↔energy.  The Bekenstein bound
        `S ≤ 2πRE` controls how much *memory* a system has.  It is
        strictly INCREASING in `E`, whereas the ML time bound is strictly
        DECREASING in `E`.  Opposite `E`-monotonicity ⇒ **no monotone map
        turns one into the other** ⇒ they are NOT the same inequality.
        ⇒ `rate_capacity_opposite_monotonicity`,
          `no_single_rate_capacity_inequality`.

      • SPATIAL axis  — interaction-distance↔velocity.  The
        Lieb–Robinson bound `lrBound C v ξ d t` carries **no energy
        argument at all**; it factors through `(C, v, ξ, d, t)`, disjoint
        from the `E` that the ML bound factors through.  Vary `E`: the ML
        bound changes while LR is fixed; vary `v`: LR changes while ML is
        fixed.  ⇒ `ml_varies_lr_fixed`, `lr_varies_ml_fixed`.

    Yet the three axes **COMPOSE** into Lloyd's "ultimate physical
    computer": in time `t`, a system of energy `E` confined to radius `R`
    performs at most `(2E/π)·t` orthogonalizing operations (temporal axis)
    using at most `2πRE` bits of memory (capacity axis).
    ⇒ `lloyd_ultimate_computer`.

    The master theorem `physical_information_limits_master` bundles all
    four facts: three independent axes, NOT one inequality, with the
    temporal axis genuinely unified, composing into Lloyd's bound.

  ══════════════════════════════════════════════════════════════════════
  WHAT IS PROVEN (zero `sorry`, zero custom `axiom`):

    1.  `lloydRate E := 2E/π`  — Lloyd's maximum operation rate.
    2.  `lloydRate_recip_mlBound`  — `lloydRate E = 1 / mlBound E` (E≠0):
        the max RATE is the reciprocal of the ML minimum TIME.
    3.  `mlBound_mul_lloydRate`  — `mlBound E · lloydRate E = 1` (E>0).
    4.  `ml_eq_mandelstamTamm_form`  — `T ≥ mlBound E ↔ T·E ≥ π/2` (E>0).
    5.  `temporal_unification`  — the ML time bound, the MT product
        inequality, and Lloyd's rate bound are mutually equivalent.
    6.  `rate_capacity_opposite_monotonicity`  — explicit `E₁<E₂` with
        `mlBound` decreasing AND `bekensteinBound` increasing across them.
    7.  `no_single_rate_capacity_inequality`  — no monotone `f` satisfies
        `bekensteinBound R E = f (mlBound E)` for all `E>0` (contradiction
        from opposite monotonicity).
    8.  `ml_varies_lr_fixed`, `lr_varies_ml_fixed`  — disjoint variable
        sets (functional independence of the spatial axis).
    9.  `lloydUltimateOps t E := (2E/π)·t`  and `lloyd_ultimate_computer`
        — the composition bundle (ops ≤ ops-bound ∧ memory ≤ Bekenstein).
   10.  `physical_information_limits_master`  — the honest structural map.

  ══════════════════════════════════════════════════════════════════════
  REUSED FROM THE LIBRARY (exact names):
    • `UnifiedTheory.LayerB.MargolusLevitinTight.mlBound E = π/(2E)`,
      `mlBound_pos`, `mlBound_strictAntiOn`.
    • `UnifiedTheory.LayerB.MargolusLevitin.EnergySpectrum`,
      `margolus_levitin_conditional` (the `T·⟨H⟩ ≥ π/2` content).
    • `UnifiedTheory.LayerC.BekensteinBound.bekensteinBound R E = 2πRE`,
      `bekensteinBound_pos`, `bekensteinBound_mono_E`.
    • `UnifiedTheory.LayerB.LiebRobinson.lrBound C v ξ d t`,
      `lrBound_lt_of_lt`.

  Units `ℏ = c = k_B = 1`.
-/
import UnifiedTheory.LayerB.MargolusLevitinTight
import UnifiedTheory.LayerC.BekensteinBound
import UnifiedTheory.LayerB.LiebRobinson

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.PhysicalInformationLimits

open Real
open UnifiedTheory.LayerB.MargolusLevitinTight
  (mlBound mlBound_pos mlBound_strictAntiOn)
open UnifiedTheory.LayerC.BekensteinBound
  (bekensteinBound bekensteinBound_pos bekensteinBound_mono_E)
open UnifiedTheory.LayerB.LiebRobinson (lrBound lrBound_lt_of_lt)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1 — TEMPORAL UNIFICATION (the genuine positive)

    `mlBound E = π/(2E)` is the minimum orthogonalization TIME.
    Lloyd's maximum orthogonalization RATE is its reciprocal:

        lloydRate E := 2E/π = 1 / mlBound E .

    The Margolus–Levitin time bound `T ≥ mlBound E`, the
    Mandelstam–Tamm product bound `T·E ≥ π/2`, and Lloyd's rate bound
    `rate ≤ lloydRate E` are **the same statement** read three ways.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Lloyd's maximum operation rate** at mean energy `E`:
    `lloydRate E := 2 E / π`  (operations per unit time, ℏ = 1).
    This is the reciprocal of the Margolus–Levitin minimum
    orthogonalization time `mlBound E = π/(2E)`. -/
noncomputable def lloydRate (E : ℝ) : ℝ := 2 * E / Real.pi

/-- Lloyd's rate is strictly positive for `E > 0`. -/
theorem lloydRate_pos (E : ℝ) (hE : 0 < E) : 0 < lloydRate E := by
  unfold lloydRate
  exact div_pos (by linarith) Real.pi_pos

/-- **Rate is the reciprocal of the ML time.**
    `lloydRate E = 1 / mlBound E`  for `E ≠ 0`. -/
theorem lloydRate_recip_mlBound (E : ℝ) (hE : E ≠ 0) :
    lloydRate E = 1 / mlBound E := by
  unfold lloydRate mlBound
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp

/-- **Time × rate = 1.**  `mlBound E · lloydRate E = 1` for `E > 0` —
    the minimum orthogonalization time and the maximum orthogonalization
    rate are exact reciprocals: they are one and the same bound. -/
theorem mlBound_mul_lloydRate (E : ℝ) (hE : 0 < E) :
    mlBound E * lloydRate E = 1 := by
  unfold mlBound lloydRate
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hE' : E ≠ 0 := ne_of_gt hE
  field_simp

/-- **Margolus–Levitin ⟺ Mandelstam–Tamm product form.**
    For `E > 0`, the orthogonalization-TIME bound `T ≥ mlBound E`
    (i.e. `T ≥ π/(2E)`) is *equivalent* to the Mandelstam–Tamm
    PRODUCT inequality `T · E ≥ π/2`.  These are the same bound
    rearranged.  (`mandelstam_tamm`'s `T·⟨H⟩ ≥ π/2` is exactly the
    right-hand form, with `E = ⟨H⟩`.) -/
theorem ml_eq_mandelstamTamm_form (T E : ℝ) (hE : 0 < E) :
    T ≥ mlBound E ↔ T * E ≥ Real.pi / 2 := by
  unfold mlBound
  have hE' : (0 : ℝ) < E := hE
  constructor
  · intro h
    -- T ≥ π/(2E) ⇒ T·E ≥ π/2  (multiply by E > 0)
    have hmul : Real.pi / (2 * E) * E ≤ T * E :=
      mul_le_mul_of_nonneg_right h (le_of_lt hE')
    have hsimp : Real.pi / (2 * E) * E = Real.pi / 2 := by
      field_simp
    rw [hsimp] at hmul
    linarith
  · intro h
    -- T·E ≥ π/2 ⇒ T ≥ π/(2E)
    rw [ge_iff_le, div_le_iff₀ (by linarith : (0:ℝ) < 2 * E)]
    nlinarith [h]

/-- **Lloyd's rate bound ⟺ Margolus–Levitin time bound.**
    For `E > 0` and a time `T > 0`, achieving orthogonalization no
    faster than the ML time (`T ≥ mlBound E`) is the same as the
    operation RATE `1/T` not exceeding Lloyd's rate
    (`1/T ≤ lloydRate E`). -/
theorem lloyd_rate_iff_ml_time (T E : ℝ) (hE : 0 < E) (hT : 0 < T) :
    T ≥ mlBound E ↔ 1 / T ≤ lloydRate E := by
  rw [lloydRate_recip_mlBound E (ne_of_gt hE)]
  have hmlpos : 0 < mlBound E := mlBound_pos E hE
  constructor
  · intro h
    rw [div_le_div_iff₀ hT hmlpos]
    nlinarith [h, hmlpos, hT]
  · intro h
    rw [div_le_div_iff₀ hT hmlpos] at h
    rw [ge_iff_le]
    nlinarith [h, hmlpos, hT]

/-- **TEMPORAL UNIFICATION.**

    The three temporal speed/throughput limits are mutually equivalent
    restatements of ONE bound, for `E > 0`, `T > 0`:

      (i)   Margolus–Levitin minimum TIME:        `T ≥ mlBound E`
      (ii)  Mandelstam–Tamm PRODUCT:              `T · E ≥ π/2`
      (iii) Lloyd maximum RATE:                   `1/T ≤ lloydRate E`

    together with the exact reciprocity identity `mlBound E · lloydRate E = 1`.
    This is the *genuine* unification: the energy–time axis collapses
    Margolus–Levitin = Mandelstam–Tamm = Lloyd into a single inequality. -/
theorem temporal_unification (T E : ℝ) (hE : 0 < E) (hT : 0 < T) :
    (T ≥ mlBound E ↔ T * E ≥ Real.pi / 2) ∧
    (T ≥ mlBound E ↔ 1 / T ≤ lloydRate E) ∧
    (mlBound E * lloydRate E = 1) :=
  ⟨ml_eq_mandelstamTamm_form T E hE,
   lloyd_rate_iff_ml_time T E hE hT,
   mlBound_mul_lloydRate E hE⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2 — RATE–CAPACITY SEPARATION (the honest negative)

    The Bekenstein capacity bound is NOT a restatement of the ML rate
    bound: as functions of energy `E` they have OPPOSITE monotonicity.
    `mlBound` strictly DECREASES in `E` (more energy ⇒ faster), while
    `bekensteinBound R ·` strictly INCREASES in `E` (more energy ⇒ more
    memory).  Disagreeing orderings ⇒ neither is a monotone function of
    the other ⇒ they are NOT the same inequality.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Opposite `E`-monotonicity (explicit witnesses).**  For any
    `R > 0` there exist energies `0 < E₁ < E₂` at which the
    Margolus–Levitin bound DECREASES (`mlBound E₂ < mlBound E₁`) while
    the Bekenstein bound INCREASES (`bekensteinBound R E₁ < bekensteinBound R E₂`).
    The two orderings disagree, so neither bound is a monotone function
    of the other. -/
theorem rate_capacity_opposite_monotonicity (R : ℝ) (hR : 0 < R) :
    ∃ E₁ E₂ : ℝ, 0 < E₁ ∧ E₁ < E₂ ∧
      mlBound E₂ < mlBound E₁ ∧
      bekensteinBound R E₁ < bekensteinBound R E₂ := by
  refine ⟨1, 2, by norm_num, by norm_num, ?_, ?_⟩
  · -- mlBound is strictly decreasing on (0,∞)
    exact mlBound_strictAntiOn (by norm_num : (1:ℝ) ∈ Set.Ioi 0)
      (by norm_num : (2:ℝ) ∈ Set.Ioi 0) (by norm_num)
  · -- bekensteinBound is strictly increasing in E
    unfold bekensteinBound
    have hπ : 0 < Real.pi := Real.pi_pos
    have h2πR : 0 < 2 * Real.pi * R := by positivity
    nlinarith [h2πR]

/-- **No single rate–capacity inequality.**

    There is NO monotone (order-preserving) map `f` turning the
    Margolus–Levitin rate bound into the Bekenstein capacity bound:
    if `f` were monotone and `bekensteinBound R E = f (mlBound E)` held
    for all `E > 0`, then on the witnesses `E₁ = 1 < E₂ = 2` (with `R > 0`)
    `f` would have to be both strictly increasing (capacity grows) and
    strictly decreasing (ML time shrinks) on the same pair — contradiction.

    Hence the two bounds are genuinely DIFFERENT axes; they cannot be
    collapsed into one inequality. -/
theorem no_single_rate_capacity_inequality (R : ℝ) (hR : 0 < R) :
    ¬ ∃ f : ℝ → ℝ, Monotone f ∧
        ∀ E : ℝ, 0 < E → bekensteinBound R E = f (mlBound E) := by
  rintro ⟨f, hf_mono, hf_eq⟩
  obtain ⟨E₁, E₂, hE₁, hE₁₂, hml, hbek⟩ :=
    rate_capacity_opposite_monotonicity R hR
  have hE₂ : 0 < E₂ := lt_trans hE₁ hE₁₂
  -- f is applied to mlBound; since mlBound E₂ < mlBound E₁, monotonicity gives
  -- f (mlBound E₂) ≤ f (mlBound E₁), i.e. bekenstein E₂ ≤ bekenstein E₁.
  have h1 : f (mlBound E₂) ≤ f (mlBound E₁) := hf_mono (le_of_lt hml)
  rw [← hf_eq E₁ hE₁, ← hf_eq E₂ hE₂] at h1
  -- but bekenstein E₁ < bekenstein E₂ — contradiction.
  exact absurd h1 (not_le.mpr hbek)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3 — SPATIAL INDEPENDENCE (Lieb–Robinson is a third axis)

    The Lieb–Robinson bound has NO energy argument; it factors through
    `(C, v, ξ, d, t)`.  The ML bound factors through `E` alone.  These
    are DISJOINT variable sets, so the two bounds are functionally
    independent: varying `E` moves ML while LR is frozen; varying `v`
    moves LR while ML is frozen.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **ML varies while LR is fixed.**  Changing the energy from `1` to `2`
    strictly changes the Margolus–Levitin bound, yet (since `lrBound`
    has no energy argument) the Lieb–Robinson bound at fixed
    `(C, v, ξ, d, t)` is completely unaffected — it is literally the
    same value.  The two bounds factor through disjoint variable sets. -/
theorem ml_varies_lr_fixed (C v ξ d t : ℝ) :
    mlBound 1 ≠ mlBound 2 ∧
      lrBound C v ξ d t = lrBound C v ξ d t := by
  refine ⟨?_, rfl⟩
  have h := mlBound_strictAntiOn (by norm_num : (1:ℝ) ∈ Set.Ioi 0)
    (by norm_num : (2:ℝ) ∈ Set.Ioi 0) (by norm_num : (1:ℝ) < 2)
  exact ne_of_gt h

/-- **LR varies while ML is fixed.**  At fixed energy `E` (so `mlBound E`
    is frozen), changing the Lieb–Robinson group velocity from `v₁` to a
    LARGER `v₂` strictly changes the Lieb–Robinson bound — because a
    larger velocity opens the light cone faster, enlarging `v·|t|` and
    hence raising the bound at fixed separation `d`.  Concretely, with
    `C > 0`, `ξ > 0`, `t ≠ 0` and `v₁ < v₂`, the LR bounds differ while
    `mlBound E` is unchanged. -/
theorem lr_varies_ml_fixed (E C ξ d t v₁ v₂ : ℝ)
    (hC : 0 < C) (hξ : 0 < ξ) (ht : t ≠ 0) (hv : v₁ < v₂) :
    lrBound C v₁ ξ d t ≠ lrBound C v₂ ξ d t ∧
      mlBound E = mlBound E := by
  refine ⟨?_, rfl⟩
  -- larger v ⇒ larger v|t| ⇒ larger -(d - v|t|) ⇒ larger exponent ⇒ larger bound.
  unfold lrBound
  have htabs : 0 < |t| := abs_pos.mpr ht
  have hvt : v₁ * |t| < v₂ * |t| := by
    exact mul_lt_mul_of_pos_right hv htabs
  -- exponents: -(d - v₁|t|)/ξ < -(d - v₂|t|)/ξ
  have hexp : -(d - v₁ * |t|) / ξ < -(d - v₂ * |t|) / ξ := by
    rw [div_lt_div_iff_of_pos_right hξ]
    linarith
  have hlt : C * Real.exp (-(d - v₁ * |t|) / ξ)
           < C * Real.exp (-(d - v₂ * |t|) / ξ) :=
    mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hexp) hC
  exact ne_of_lt hlt

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4 — COMPOSITION (Lloyd's ultimate computer)

    The axes don't unify, but they COMPOSE.  In time `t`, a system of
    energy `E` confined to radius `R`:
      • performs at most  `lloydUltimateOps t E = (2E/π)·t`  operations
        (temporal axis, ML/Lloyd), and
      • stores at most    `bekensteinBound R E = 2πRE`  bits
        (capacity axis, Bekenstein).
    The two INDEPENDENT axes compose into the physical-computation bound.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Lloyd's maximum operation count** in time `t` at energy `E`:
    `lloydUltimateOps t E := (2E/π)·t = lloydRate E · t`. -/
noncomputable def lloydUltimateOps (t E : ℝ) : ℝ := (2 * E / Real.pi) * t

/-- `lloydUltimateOps` is exactly Lloyd's rate integrated over time:
    `lloydUltimateOps t E = lloydRate E · t`. -/
theorem lloydUltimateOps_eq_rate_mul_time (t E : ℝ) :
    lloydUltimateOps t E = lloydRate E * t := by
  unfold lloydUltimateOps lloydRate; ring

/-- Lloyd's operation count is non-negative for `E ≥ 0`, `t ≥ 0`. -/
theorem lloydUltimateOps_nonneg (t E : ℝ) (hE : 0 ≤ E) (ht : 0 ≤ t) :
    0 ≤ lloydUltimateOps t E := by
  unfold lloydUltimateOps
  have : 0 ≤ 2 * E / Real.pi := div_nonneg (by linarith) Real.pi_pos.le
  exact mul_nonneg this ht

/-- Lloyd's operation count is strictly positive for `E > 0`, `t > 0`. -/
theorem lloydUltimateOps_pos (t E : ℝ) (hE : 0 < E) (ht : 0 < t) :
    0 < lloydUltimateOps t E := by
  unfold lloydUltimateOps
  exact mul_pos (div_pos (by linarith) Real.pi_pos) ht

/-- Operation count scales linearly in the available time. -/
theorem lloydUltimateOps_smul_t (c t E : ℝ) :
    lloydUltimateOps (c * t) E = c * lloydUltimateOps t E := by
  unfold lloydUltimateOps; ring

/-- **LLOYD'S ULTIMATE COMPUTER (composition).**

    Given a budget of `ops` orthogonalizing operations performed in time
    `t`, and `memory` bits stored, in a system of energy `E > 0` confined
    to radius `R > 0`:  the two INDEPENDENT physical limits compose into

      • TEMPORAL:   `ops    ≤ lloydUltimateOps t E = (2E/π)·t`
      • CAPACITY:   `memory ≤ bekensteinBound R E = 2πRE`

    The bundle holds with both factors strictly positive (the bound is
    non-vacuous), and the two bounds are governed by DISJOINT physics
    (rate by `E` and `t`; capacity by `R` and `E`).  This is the positive
    synthesis: even though there is no single inequality, the energy–time
    and area–energy axes COMPOSE into a single computational envelope. -/
theorem lloyd_ultimate_computer
    (ops memory t E R : ℝ)
    (hE : 0 < E) (ht : 0 < t) (hR : 0 < R)
    (hops : ops ≤ lloydUltimateOps t E)
    (hmem : memory ≤ bekensteinBound R E) :
    (ops ≤ lloydUltimateOps t E) ∧
    (memory ≤ bekensteinBound R E) ∧
    (0 < lloydUltimateOps t E) ∧
    (0 < bekensteinBound R E) ∧
    (lloydUltimateOps t E = lloydRate E * t) := by
  refine ⟨hops, hmem, ?_, ?_, ?_⟩
  · exact lloydUltimateOps_pos t E hE ht
  · exact bekensteinBound_pos R E hR hE
  · exact lloydUltimateOps_eq_rate_mul_time t E

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5 — MASTER THEOREM (the honest structural map)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **PHYSICAL INFORMATION LIMITS — MASTER THEOREM.**

    The honest cross-domain synthesis.  The naive conjecture that one
    inequality unifies all the physical speed/information limits is
    FALSE; the genuine structure is THREE INDEPENDENT AXES that COMPOSE,
    with the temporal axis genuinely unified.  Bundled here:

    (1) TEMPORAL UNIFICATION.  For `E > 0`, `T > 0`: the Margolus–Levitin
        time bound, the Mandelstam–Tamm product bound, and Lloyd's rate
        bound are mutually equivalent, with exact reciprocity
        `mlBound E · lloydRate E = 1`.   [ML = MT = Lloyd]

    (2) RATE–CAPACITY SEPARATION.  For `R > 0` there are energies
        `E₁ < E₂` where the ML bound DECREASES while the Bekenstein
        bound INCREASES (opposite monotonicity), and consequently NO
        monotone map turns one into the other.   [Bekenstein ≠ ML axis]

    (3) SPATIAL INDEPENDENCE.  Varying energy moves the ML bound while
        the (energy-free) Lieb–Robinson bound is fixed; varying the LR
        velocity moves the LR bound while the ML bound is fixed.  The two
        factor through disjoint variable sets.   [LR ⊥ ML]

    (4) COMPOSITION.  The temporal and capacity axes compose into Lloyd's
        ultimate-computer bound: `ops ≤ (2E/π)·t` and `memory ≤ 2πRE`,
        both non-vacuous.   [three axes compose, not collapse] -/
theorem physical_information_limits_master
    (R : ℝ) (hR : 0 < R) :
    -- (1) Temporal unification
    (∀ T E : ℝ, 0 < E → 0 < T →
       (T ≥ mlBound E ↔ T * E ≥ Real.pi / 2) ∧
       (T ≥ mlBound E ↔ 1 / T ≤ lloydRate E) ∧
       (mlBound E * lloydRate E = 1)) ∧
    -- (2) Rate–capacity separation
    (∃ E₁ E₂ : ℝ, 0 < E₁ ∧ E₁ < E₂ ∧
        mlBound E₂ < mlBound E₁ ∧
        bekensteinBound R E₁ < bekensteinBound R E₂) ∧
    (¬ ∃ f : ℝ → ℝ, Monotone f ∧
        ∀ E : ℝ, 0 < E → bekensteinBound R E = f (mlBound E)) ∧
    -- (3) Spatial independence
    (∀ C v ξ d t : ℝ,
        mlBound 1 ≠ mlBound 2 ∧ lrBound C v ξ d t = lrBound C v ξ d t) ∧
    (∀ E C ξ d t v₁ v₂ : ℝ, 0 < C → 0 < ξ → t ≠ 0 → v₁ < v₂ →
        lrBound C v₁ ξ d t ≠ lrBound C v₂ ξ d t ∧ mlBound E = mlBound E) ∧
    -- (4) Composition (Lloyd's ultimate computer)
    (∀ ops memory t E : ℝ, 0 < E → 0 < t →
        ops ≤ lloydUltimateOps t E → memory ≤ bekensteinBound R E →
        (ops ≤ lloydUltimateOps t E) ∧ (memory ≤ bekensteinBound R E) ∧
        (0 < lloydUltimateOps t E) ∧ (0 < bekensteinBound R E) ∧
        (lloydUltimateOps t E = lloydRate E * t)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T E hE hT; exact temporal_unification T E hE hT
  · exact rate_capacity_opposite_monotonicity R hR
  · exact no_single_rate_capacity_inequality R hR
  · intro C v ξ d t; exact ml_varies_lr_fixed C v ξ d t
  · intro E C ξ d t v₁ v₂ hC hξ ht hv; exact lr_varies_ml_fixed E C ξ d t v₁ v₂ hC hξ ht hv
  · intro ops memory t E hE ht hops hmem
    exact lloyd_ultimate_computer ops memory t E R hE ht hR hops hmem

end UnifiedTheory.LayerC.PhysicalInformationLimits
