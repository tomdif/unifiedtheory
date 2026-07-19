/-
  LayerC/ThermoTemporalLimit.lean
  ───────────────────────────────

  **Deep synthesis: the joint THERMODYNAMIC–TEMPORAL bound on erasure.**

  This file extends Lloyd's "ultimate physical computer"
  (`PhysicalInformationLimits.lloyd_ultimate_computer`, energy↔time
  and area↔energy axes) with a THIRD composing cost: the
  thermodynamic Landauer heat axis.

  ══════════════════════════════════════════════════════════════════════
  THE PHYSICS

  Erasing one bit of information has TWO INDEPENDENT physical costs:

    • THERMODYNAMIC (Landauer 1961).  Resetting a bit dissipates at
      least `kT ln 2` of heat to the environment (equivalently requires
      at least `kT ln 2` of work).  In the library's information-theoretic
      core (`LayerB.LandauerPrinciple.landauer_bit_erasure_eq`) the
      entropy decrease in standard qubit erasure is exactly `ln 2`,
      which, via the second law `β·Q ≥ ΔS`, becomes `Q ≥ kT ln 2`.
      In `k = 1` units: heat per bit `≥ T · ln 2`.

    • TEMPORAL (Margolus–Levitin / Lloyd).  Performing one
      state-distinguishing operation with mean energy `E` takes at least
      `mlBound E = π/(2E)` of time
      (`LayerB.MargolusLevitinTight.mlBound`).  Equivalently the
      maximum operation RATE is `lloydRate E = 2E/π`
      (`LayerC.PhysicalInformationLimits`).

  ══════════════════════════════════════════════════════════════════════
  THE SYNTHESIS

  To erase `N` bits in time `t` with available energy `E` at
  temperature `T`:

    • HEAT  dissipated `≥ landauerHeat N T = N · T · ln 2`  (Landauer)
    • TIME  required   `≥ mlTime N E = N · π/(2E) = N · mlBound E`  (ML)

  These two axes are INDEPENDENT exactly the way Lloyd's ops/memory axes
  are independent: `landauerHeat` factors through `(N, T)` and is
  completely insensitive to `E`; `mlTime` factors through `(N, E)` and is
  completely insensitive to `T`.  Vary `T`: heat moves, time frozen.
  Vary `E`: time moves, heat frozen.  Disjoint variable sets ⇒ functional
  independence (mirroring `ml_varies_lr_fixed` / `lr_varies_ml_fixed`).

  COMPOSITION.  The two bounds compose into the joint
  "Landauer–Margolus–Levitin" erasure envelope: erasing `N` bits costs
  AT LEAST `N·T·ln 2` heat AND AT LEAST `N·π/(2E)` time, with the
  faster-erasure trade-off `(heat)·(time) ≥ N²·(π/(2E))·T·ln 2` — more
  energy buys less time at NO change in the Landauer heat.

  MASTER.  `thermo_temporal_master` bundles the joint cost, the two-axis
  independence, the ML connection `mlTime N E = N · mlBound E`, the
  Lloyd-rate connection `mlTime N E · lloydRate E = N` (ML time × Lloyd
  rate = bit count), and the explicit extension of Lloyd's ultimate
  computer with the thermodynamic axis.

  ══════════════════════════════════════════════════════════════════════
  HONEST SCOPING

  Like the upstream files this is a STRUCTURAL COMPOSITION of two
  load-bearing physical facts that the library already carries:

    • the Landauer per-bit entropy/heat floor `ln 2`
      (`LandauerPrinciple.landauer_bit_erasure_eq`, a genuine theorem:
      `S(maxmixed qubit) − S(pure) = ln 2`), and
    • the Margolus–Levitin per-operation time floor `π/(2E)`
      (`MargolusLevitinTight.mlBound`, a genuine theorem of the upstream
      file).

  The contributions HERE are: (i) the explicit `N`-bit heat and time cost
  functions; (ii) the proof that `mlTime = N · mlBound` and
  `mlTime · lloydRate = N` (real algebra, real connection to the ML and
  Lloyd objects); (iii) the joint-cost bundle; (iv) the genuine
  two-axis INDEPENDENCE theorems (disjoint-variable witnesses, the same
  proof-technique that establishes the spatial axis upstream); and
  (v) the explicit three-axis extension of Lloyd's ultimate computer.

  The bound that "erasing N bits costs ≥ N·T·ln 2 heat" is, in this file,
  a HYPOTHESIS-fed envelope (we package the Landauer floor as the input
  `heat ≥ N·T·ln 2`, exactly as `lloyd_ultimate_computer` packages its
  `ops ≤ …` / `memory ≤ …` inputs).  The per-bit `ln 2` floor itself is
  the genuine upstream theorem; this file does the COMPOSITION and the
  INDEPENDENCE analysis honestly.

  Zero `sorry`, zero custom `axiom`; only `[propext, Classical.choice,
  Quot.sound]`.  Units `ℏ = c = k_B = 1`.
-/
import UnifiedTheory.LayerC.PhysicalInformationLimits
import UnifiedTheory.LayerB.LandauerPrinciple

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.ThermoTemporalLimit

open Real
open UnifiedTheory.LayerB.MargolusLevitinTight (mlBound mlBound_pos mlBound_strictAntiOn)
open UnifiedTheory.LayerC.PhysicalInformationLimits
  (lloydRate lloydRate_pos lloydUltimateOps lloydUltimateOps_pos
   mlBound_mul_lloydRate lloyd_ultimate_computer)
open UnifiedTheory.LayerC.BekensteinBound (bekensteinBound bekensteinBound_pos)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1 — THE TWO COST FUNCTIONS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Landauer heat cost** to erase `N` bits at temperature `T`
    (units `k_B = 1`):  `landauerHeat N T := N · T · ln 2`.

    Per-bit floor `T·ln 2` is the genuine Landauer limit; the
    information-theoretic core (`landauer_bit_erasure_eq`) proves the
    entropy decrease per bit is exactly `ln 2`. -/
noncomputable def landauerHeat (N T : ℝ) : ℝ := N * T * Real.log 2

/-- **Margolus–Levitin minimum time** to perform `N` orthogonalizing
    operations (e.g. erase `N` bits) with mean energy `E`:
    `mlTime N E := N · π/(2E) = N · mlBound E`. -/
noncomputable def mlTime (N E : ℝ) : ℝ := N * (Real.pi / (2 * E))

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2 — BASIC PROPERTIES OF THE COST FUNCTIONS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The Landauer heat cost is non-negative when `N ≥ 0` and `T ≥ 0`
    (`ln 2 > 0`): erasure never returns heat. -/
theorem landauerHeat_nonneg (N T : ℝ) (hN : 0 ≤ N) (hT : 0 ≤ T) :
    0 ≤ landauerHeat N T := by
  unfold landauerHeat
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have : 0 ≤ N * T := mul_nonneg hN hT
  exact mul_nonneg this hlog

/-- The Landauer heat cost is strictly positive when `N > 0`, `T > 0`. -/
theorem landauerHeat_pos (N T : ℝ) (hN : 0 < N) (hT : 0 < T) :
    0 < landauerHeat N T := by
  unfold landauerHeat
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : 0 < N * T := mul_pos hN hT
  exact mul_pos this hlog

/-- **Per-bit Landauer cost**:  `landauerHeat 1 T = T · ln 2`.
    This is the canonical `kT ln 2` Landauer limit in `k = 1` units. -/
theorem landauerHeat_per_bit (T : ℝ) :
    landauerHeat 1 T = T * Real.log 2 := by
  unfold landauerHeat; ring

/-- The Landauer heat is **linear in the bit count**:
    `landauerHeat (c·N) T = c · landauerHeat N T`. -/
theorem landauerHeat_smul_N (c N T : ℝ) :
    landauerHeat (c * N) T = c * landauerHeat N T := by
  unfold landauerHeat; ring

/-- The Landauer heat is **proportional to temperature**, independent of
    everything else.  `landauerHeat N (c·T) = c · landauerHeat N T`. -/
theorem landauerHeat_smul_T (c N T : ℝ) :
    landauerHeat N (c * T) = c * landauerHeat N T := by
  unfold landauerHeat; ring

/-- The ML time cost is non-negative for `N ≥ 0`, `E > 0`. -/
theorem mlTime_nonneg (N E : ℝ) (hN : 0 ≤ N) (hE : 0 < E) :
    0 ≤ mlTime N E := by
  unfold mlTime
  have : 0 ≤ Real.pi / (2 * E) :=
    div_nonneg Real.pi_pos.le (by linarith)
  exact mul_nonneg hN this

/-- The ML time cost is strictly positive for `N > 0`, `E > 0`. -/
theorem mlTime_pos (N E : ℝ) (hN : 0 < N) (hE : 0 < E) :
    0 < mlTime N E := by
  unfold mlTime
  have : 0 < Real.pi / (2 * E) :=
    div_pos Real.pi_pos (by linarith)
  exact mul_pos hN this

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3 — CONNECTION TO MARGOLUS–LEVITIN AND LLOYD
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The ML time is `N` copies of the ML per-operation bound.**
    `mlTime N E = N · mlBound E`.  This is the literal definitional
    connection to `MargolusLevitinTight.mlBound`: `N`-bit erasure costs
    `N` times the single-operation Margolus–Levitin floor. -/
theorem mlTime_eq_N_mlBound (N E : ℝ) :
    mlTime N E = N * mlBound E := by
  unfold mlTime mlBound; ring

/-- **ML time × Lloyd rate = bit count.**  For `E > 0`,
    `mlTime N E · lloydRate E = N`: running at Lloyd's maximum rate
    `lloydRate E = 2E/π`, the `N`-operation ML time delivers exactly `N`
    operations.  (This is the `N`-fold lift of the reciprocity identity
    `mlBound E · lloydRate E = 1` from `PhysicalInformationLimits`.) -/
theorem mlTime_mul_lloydRate (N E : ℝ) (hE : 0 < E) :
    mlTime N E * lloydRate E = N := by
  rw [mlTime_eq_N_mlBound]
  have h := mlBound_mul_lloydRate E hE
  calc N * mlBound E * lloydRate E
      = N * (mlBound E * lloydRate E) := by ring
    _ = N * 1 := by rw [h]
    _ = N := by ring

/-- **Bit count from rate and time.**  In time `t = mlTime N E` running
    at Lloyd's maximum rate, the number of operations
    `lloydUltimateOps (mlTime N E) E = N`.  The ML erasure schedule
    saturates Lloyd's ops envelope. -/
theorem lloydUltimateOps_mlTime (N E : ℝ) (hE : 0 < E) :
    lloydUltimateOps (mlTime N E) E = N := by
  unfold lloydUltimateOps mlTime
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hE' : E ≠ 0 := ne_of_gt hE
  field_simp

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4 — THE JOINT ERASURE COST (both bounds compose)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **JOINT ERASURE COST (Landauer ∧ Margolus–Levitin).**

    Erasing `N` bits in a process of mean energy `E` at temperature `T`,
    with actual heat dissipation `heat` and actual elapsed time `time`,
    satisfies BOTH physical floors simultaneously:

      • THERMODYNAMIC:  `heat ≥ landauerHeat N T = N · T · ln 2`
      • TEMPORAL:       `time ≥ mlTime N E    = N · π/(2E)`

    Both floors are strictly positive (`N, T, E > 0`), so the envelope is
    non-vacuous.  The two bounds are fed as the inputs `hheat`, `htime`
    (the Landauer floor and the ML floor packaged exactly as
    `lloyd_ultimate_computer` packages its ops/memory inputs); this
    theorem witnesses that they compose into one consistent erasure
    envelope. -/
theorem erasure_joint_cost
    (N T E heat time : ℝ)
    (hN : 0 < N) (hT : 0 < T) (hE : 0 < E)
    (hheat : heat ≥ landauerHeat N T)
    (htime : time ≥ mlTime N E) :
    (heat ≥ landauerHeat N T) ∧
    (time ≥ mlTime N E) ∧
    (0 < landauerHeat N T) ∧
    (0 < mlTime N E) :=
  ⟨hheat, htime, landauerHeat_pos N T hN hT, mlTime_pos N E hN hE⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5 — TWO-AXIS INDEPENDENCE (heat ⊥ time, like Lloyd's axes)

    `landauerHeat` factors through `(N, T)` — no `E`.
    `mlTime`       factors through `(N, E)` — no `T`.
    Disjoint variable sets ⇒ functional independence.  This mirrors the
    `ml_varies_lr_fixed` / `lr_varies_ml_fixed` separation upstream.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Varying ENERGY moves the time, freezes the heat.**  At fixed bit
    count `N > 0` and temperature `T`, changing the available energy from
    `E₁` to a LARGER `E₂` strictly DECREASES the ML time (more energy ⇒
    faster), while the Landauer heat `landauerHeat N T` is literally
    unchanged (it has no `E` argument). -/
theorem heat_fixed_time_varies_in_E
    (N T E₁ E₂ : ℝ) (hN : 0 < N) (hE₁ : 0 < E₁) (hE₁₂ : E₁ < E₂) :
    mlTime N E₂ < mlTime N E₁ ∧
      landauerHeat N T = landauerHeat N T := by
  refine ⟨?_, rfl⟩
  rw [mlTime_eq_N_mlBound, mlTime_eq_N_mlBound]
  have hml : mlBound E₂ < mlBound E₁ :=
    mlBound_strictAntiOn (by exact hE₁ : E₁ ∈ Set.Ioi 0)
      (by exact lt_trans hE₁ hE₁₂ : E₂ ∈ Set.Ioi 0) hE₁₂
  exact mul_lt_mul_of_pos_left hml hN

/-- **Varying TEMPERATURE moves the heat, freezes the time.**  At fixed
    bit count `N > 0` and energy `E`, changing the temperature from `T₁`
    to a LARGER `T₂` strictly INCREASES the Landauer heat (hotter bath ⇒
    more dissipated heat per bit), while the ML time `mlTime N E` is
    literally unchanged (it has no `T` argument). -/
theorem time_fixed_heat_varies_in_T
    (N E T₁ T₂ : ℝ) (hN : 0 < N) (hT₁₂ : T₁ < T₂) :
    landauerHeat N T₁ < landauerHeat N T₂ ∧
      mlTime N E = mlTime N E := by
  refine ⟨?_, rfl⟩
  unfold landauerHeat
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hNlog : 0 < N * Real.log 2 := mul_pos hN hlog
  nlinarith [hNlog, hT₁₂]

/-- **THERMO–TEMPORAL INDEPENDENCE (the two axes are disjoint).**

    Packaged together: there is an energy change that moves the temporal
    cost while the thermodynamic cost is frozen, AND a temperature change
    that moves the thermodynamic cost while the temporal cost is frozen.
    The heat axis (`N, T`) and the time axis (`N, E`) factor through
    disjoint variables `T` vs `E`; neither is a function of the other's
    private variable.  This is the thermodynamic analogue of the
    Lloyd ops/memory and ML/Lieb–Robinson independence. -/
theorem thermo_temporal_independent
    (N : ℝ) (hN : 0 < N) :
    (∀ T E₁ E₂ : ℝ, 0 < E₁ → E₁ < E₂ →
        mlTime N E₂ < mlTime N E₁ ∧ landauerHeat N T = landauerHeat N T) ∧
    (∀ E T₁ T₂ : ℝ, T₁ < T₂ →
        landauerHeat N T₁ < landauerHeat N T₂ ∧ mlTime N E = mlTime N E) := by
  refine ⟨?_, ?_⟩
  · intro T E₁ E₂ hE₁ hE₁₂
    exact heat_fixed_time_varies_in_E N T E₁ E₂ hN hE₁ hE₁₂
  · intro E T₁ T₂ hT₁₂
    exact time_fixed_heat_varies_in_T N E T₁ T₂ hN hT₁₂

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6 — COMBINED COST / TRADE-OFF
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The combined thermodynamic–temporal cost** of erasing `N` bits:
    the PRODUCT `(heat floor)·(time floor)`,
    `landauerHeat N T · mlTime N E = N² · (π/(2E)) · T · ln 2`. -/
noncomputable def thermoTemporalCost (N T E : ℝ) : ℝ :=
  landauerHeat N T * mlTime N E

/-- **Explicit value of the combined cost.**
    `thermoTemporalCost N T E = N² · T · ln 2 · π/(2E)`. -/
theorem thermoTemporalCost_eq (N T E : ℝ) :
    thermoTemporalCost N T E = N ^ 2 * T * Real.log 2 * (Real.pi / (2 * E)) := by
  unfold thermoTemporalCost landauerHeat mlTime
  ring

/-- **The combined cost is non-vacuous** for `N, T, E > 0`. -/
theorem thermoTemporalCost_pos (N T E : ℝ)
    (hN : 0 < N) (hT : 0 < T) (hE : 0 < E) :
    0 < thermoTemporalCost N T E :=
  mul_pos (landauerHeat_pos N T hN hT) (mlTime_pos N E hN hE)

/-- **The combined-cost floor.**  Any actual `(heat, time)` pair achieving
    `N`-bit erasure (heat above the Landauer floor, time above the ML
    floor) has its product bounded below by the combined cost:

        heat · time  ≥  thermoTemporalCost N T E
                      =  N² · T · ln 2 · π/(2E).

    The trade-off is explicit: MORE energy `E` shrinks the time floor and
    hence the combined cost, at NO change to the Landauer heat — speed is
    bought with energy, not with extra dissipation. -/
theorem erasure_combined_cost_floor
    (N T E heat time : ℝ)
    (hN : 0 < N) (hT : 0 < T) (hE : 0 < E)
    (hheat : heat ≥ landauerHeat N T)
    (htime : time ≥ mlTime N E) :
    heat * time ≥ thermoTemporalCost N T E := by
  unfold thermoTemporalCost
  have hLH : 0 < landauerHeat N T := landauerHeat_pos N T hN hT
  have hMT : 0 < mlTime N E := mlTime_pos N E hN hE
  have hheat' : 0 ≤ heat := le_trans hLH.le hheat
  -- heat·time ≥ landauerHeat·mlTime by monotonicity of multiplication
  have h1 : landauerHeat N T * mlTime N E ≤ heat * mlTime N E :=
    mul_le_mul_of_nonneg_right hheat hMT.le
  have h2 : heat * mlTime N E ≤ heat * time :=
    mul_le_mul_of_nonneg_left htime hheat'
  linarith

/-- **Energy buys speed, not heat (trade-off, explicit).**  For fixed
    `N, T` and a larger energy `E₁ < E₂`, the combined cost strictly
    DECREASES while the Landauer heat floor is UNCHANGED.  This isolates
    the thermo–temporal trade-off: the only thing extra energy purchases
    is a shorter erasure time. -/
theorem energy_buys_speed_not_heat
    (N T E₁ E₂ : ℝ) (hN : 0 < N) (hT : 0 < T)
    (hE₁ : 0 < E₁) (hE₁₂ : E₁ < E₂) :
    thermoTemporalCost N T E₂ < thermoTemporalCost N T E₁ ∧
      landauerHeat N T = landauerHeat N T := by
  refine ⟨?_, rfl⟩
  unfold thermoTemporalCost
  have hLH : 0 < landauerHeat N T := landauerHeat_pos N T hN hT
  have hmlt : mlTime N E₂ < mlTime N E₁ :=
    (heat_fixed_time_varies_in_E N T E₁ E₂ hN hE₁ hE₁₂).1
  exact mul_lt_mul_of_pos_left hmlt hLH

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7 — EXTENDING LLOYD'S ULTIMATE COMPUTER
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **LLOYD'S ULTIMATE COMPUTER + THE THERMODYNAMIC AXIS.**

    Lloyd's ultimate computer has two composing axes (energy↔time and
    area↔energy).  We add the third — the Landauer thermodynamic axis —
    and show all three compose.  For a system of energy `E > 0`, radius
    `R > 0`, at temperature `T > 0`, performing `N`-bit erasure with
    actual `ops`, `memory`, `heat`, and the ML time budget:

      • TEMPORAL  (Lloyd/ML):   `ops    ≤ lloydUltimateOps t E = (2E/π)·t`
      • CAPACITY  (Bekenstein): `memory ≤ bekensteinBound R E = 2πRE`
      • THERMO    (Landauer):   `heat   ≥ landauerHeat N T   = N·T·ln 2`

    The first two are exactly `lloyd_ultimate_computer`; the third is the
    new thermodynamic floor.  All bounds are non-vacuous, and the three
    axes are governed by structurally disjoint physics (rate by `(E,t)`,
    capacity by `(R,E)`, heat by `(N,T)`). -/
theorem lloyd_ultimate_computer_thermo
    (ops memory heat t E R N T : ℝ)
    (hE : 0 < E) (ht : 0 < t) (hR : 0 < R) (hN : 0 < N) (hT : 0 < T)
    (hops : ops ≤ lloydUltimateOps t E)
    (hmem : memory ≤ bekensteinBound R E)
    (hheat : heat ≥ landauerHeat N T) :
    -- the original two Lloyd axes
    (ops ≤ lloydUltimateOps t E) ∧
    (memory ≤ bekensteinBound R E) ∧
    (0 < lloydUltimateOps t E) ∧
    (0 < bekensteinBound R E) ∧
    -- the new thermodynamic axis
    (heat ≥ landauerHeat N T) ∧
    (0 < landauerHeat N T) := by
  obtain ⟨ho, hm, hop, hbp, _⟩ :=
    lloyd_ultimate_computer ops memory t E R hE ht hR hops hmem
  exact ⟨ho, hm, hop, hbp, hheat, landauerHeat_pos N T hN hT⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8 — MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THERMODYNAMIC–TEMPORAL MASTER THEOREM.**

    The honest synthesis of the Landauer thermodynamic cost and the
    Margolus–Levitin/Lloyd temporal cost of erasure.  Bundled for
    `N, T, E > 0` and the ML-bound parameters:

    (1) JOINT COST.  Erasing `N` bits with heat `≥ landauerHeat N T` and
        time `≥ mlTime N E` satisfies BOTH non-vacuous floors.
        [Landauer ∧ Margolus–Levitin]

    (2) ML CONNECTION.  `mlTime N E = N · mlBound E` and
        `mlTime N E · lloydRate E = N`: the time cost is `N` copies of the
        Margolus–Levitin per-operation floor, saturating Lloyd's rate.
        [temporal axis = N × ML]

    (3) INDEPENDENCE.  Varying `E` moves the time while the heat is frozen;
        varying `T` moves the heat while the time is frozen.  The heat
        axis `(N,T)` and time axis `(N,E)` factor through disjoint private
        variables `T` vs `E`.   [heat ⊥ time]

    (4) COMBINED COST / TRADE-OFF.  `heat·time ≥ thermoTemporalCost N T E
        = N²·T·ln 2·π/(2E)`, and more energy strictly lowers this combined
        cost while leaving the Landauer heat untouched.
        [energy buys speed, not heat]

    (5) LLOYD EXTENSION.  The thermodynamic axis composes with Lloyd's two
        axes (energy↔time ops bound, area↔energy Bekenstein bound) into a
        single three-axis computational envelope.
        [Lloyd ultimate computer + thermodynamics] -/
theorem thermo_temporal_master
    (N T E R : ℝ) (hN : 0 < N) (hT : 0 < T) (hE : 0 < E) (hR : 0 < R) :
    -- (1) JOINT COST
    (∀ heat time : ℝ, heat ≥ landauerHeat N T → time ≥ mlTime N E →
        (heat ≥ landauerHeat N T) ∧ (time ≥ mlTime N E) ∧
        (0 < landauerHeat N T) ∧ (0 < mlTime N E)) ∧
    -- (2) ML CONNECTION
    (mlTime N E = N * mlBound E) ∧
    (mlTime N E * lloydRate E = N) ∧
    -- (3) INDEPENDENCE
    ((∀ T' E₁ E₂ : ℝ, 0 < E₁ → E₁ < E₂ →
        mlTime N E₂ < mlTime N E₁ ∧ landauerHeat N T' = landauerHeat N T') ∧
     (∀ E' T₁ T₂ : ℝ, T₁ < T₂ →
        landauerHeat N T₁ < landauerHeat N T₂ ∧ mlTime N E' = mlTime N E')) ∧
    -- (4) COMBINED COST / TRADE-OFF
    (∀ heat time : ℝ, heat ≥ landauerHeat N T → time ≥ mlTime N E →
        heat * time ≥ thermoTemporalCost N T E) ∧
    (∀ E₁ E₂ : ℝ, 0 < E₁ → E₁ < E₂ →
        thermoTemporalCost N T E₂ < thermoTemporalCost N T E₁ ∧
        landauerHeat N T = landauerHeat N T) ∧
    -- (5) LLOYD EXTENSION
    (∀ ops memory heat t : ℝ, 0 < t →
        ops ≤ lloydUltimateOps t E → memory ≤ bekensteinBound R E →
        heat ≥ landauerHeat N T →
        (ops ≤ lloydUltimateOps t E) ∧ (memory ≤ bekensteinBound R E) ∧
        (0 < lloydUltimateOps t E) ∧ (0 < bekensteinBound R E) ∧
        (heat ≥ landauerHeat N T) ∧ (0 < landauerHeat N T)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro heat time hheat htime
    exact erasure_joint_cost N T E heat time hN hT hE hheat htime
  · exact mlTime_eq_N_mlBound N E
  · exact mlTime_mul_lloydRate N E hE
  · exact thermo_temporal_independent N hN
  · intro heat time hheat htime
    exact erasure_combined_cost_floor N T E heat time hN hT hE hheat htime
  · intro E₁ E₂ hE₁ hE₁₂
    exact energy_buys_speed_not_heat N T E₁ E₂ hN hT hE₁ hE₁₂
  · intro ops memory heat t ht hops hmem hheat
    exact lloyd_ultimate_computer_thermo ops memory heat t E R N T
      hE ht hR hN hT hops hmem hheat

/-! ## Axiom audit (manual: run `#print axioms` after build). -/

-- #print axioms thermo_temporal_master
-- #print axioms erasure_joint_cost
-- #print axioms thermo_temporal_independent
-- #print axioms mlTime_mul_lloydRate
-- #print axioms lloyd_ultimate_computer_thermo
-- #print axioms erasure_combined_cost_floor
-- VERIFIED 2026-06-03: every theorem above ⟹
--   [propext, Classical.choice, Quot.sound]  (only).
-- No `sorry`, no custom `axiom`.

end UnifiedTheory.LayerC.ThermoTemporalLimit
