/-
  UnifiedTheory/LayerC/QuarkLeptonUnification.lean
  ────────────────────────────────────────────────

  **Why quarks and leptons must coexist — gauge-anomaly cancellation
  FORCES the full quark + lepton content together.**

  A Standard-Model generation is split into two sectors:

    * `quarkSector  = [Q, uᶜ, dᶜ]`   (the colored fermions);
    * `leptonSector = [L, eᶜ]`        (the colorless fermions).

  The companion file `AnomalyCancellation.lean` proves that the FULL
  generation `smGeneration = quarkSector ++ leptonSector` is anomaly
  free.  Here we prove the SHARPER, structural fact: **neither sector
  is anomaly free on its own.**  In exact rational arithmetic:

    * `[SU(2)]²U(1)` :  quarks give `+1/2`, leptons give `−1/2`
                       (each nonzero; sum `0`).
    * `[U(1)]³`      :  quarks give `−3/4`, leptons give `+3/4`
                       (each nonzero; sum `0`).

  So a hypothetical world with ONLY quarks (no leptons) or ONLY
  leptons (no quarks) is QUANTUM-MECHANICALLY INCONSISTENT — it carries
  an uncancelled gauge anomaly.  Quantum consistency therefore REQUIRES
  the quark and lepton sectors together.  This is the genuine
  "why quarks and leptons come together" result.

  ## Standing constraint
  Zero `sorry`, zero custom `axiom`.  Every claim is a theorem closed
  by exact rational computation, reusing the definitions of
  `AnomalyCancellation.lean` verbatim.
-/

import UnifiedTheory.LayerC.AnomalyCancellation

namespace UnifiedTheory.LayerC.QuarkLeptonUnification

open UnifiedTheory.LayerC.AnomalyCancellation

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE TWO SECTORS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The **quark sector**: the colored chiral fermions of one
    generation — `Q` (quark doublet), `uᶜ`, `dᶜ`.  Reuses the exact
    `WeylFermion` data from `AnomalyCancellation`. -/
def quarkSector : List WeylFermion := [Q, uc, dc]

/-- The **lepton sector**: the colorless chiral fermions of one
    generation — `L` (lepton doublet) and `eᶜ`. -/
def leptonSector : List WeylFermion := [L, ec]

/-- The two sectors concatenated rebuild exactly one full generation. -/
theorem sectors_eq_generation :
    quarkSector ++ leptonSector = smGeneration := rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: EXACT PER-SECTOR ANOMALY VALUES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-! ### [SU(2)]² U(1) — only the weak doublets contribute. -/

/-- Quarks alone: `[SU(2)]²U(1) = 3·(1/6) = 1/2` (only `Q` is a
    doublet, with color multiplicity `3`). -/
theorem quarkSector_su2sq_val : su2sq_u1_anomaly quarkSector = 1/2 := by
  unfold su2sq_u1_anomaly quarkSector
  simp [Q, uc, dc, WeylFermion.isDoublet]
  norm_num

/-- Leptons alone: `[SU(2)]²U(1) = 1·(−1/2) = −1/2` (only `L` is a
    doublet, color multiplicity `1`). -/
theorem leptonSector_su2sq_val : su2sq_u1_anomaly leptonSector = -1/2 := by
  unfold su2sq_u1_anomaly leptonSector
  simp [L, ec, WeylFermion.isDoublet]

/-! ### [U(1)]³ — every state contributes `(totalMult)·Y³`. -/

/-- Quarks alone: `[U(1)]³ = 6·(1/6)³ + 3·(−2/3)³ + 3·(1/3)³ = −3/4`. -/
theorem quarkSector_u1cubed_val : u1cubed_anomaly quarkSector = -3/4 := by
  unfold u1cubed_anomaly quarkSector
  simp [Q, uc, dc, WeylFermion.totalMult]
  norm_num

/-- Leptons alone: `[U(1)]³ = 2·(−1/2)³ + 1·(1)³ = 3/4`. -/
theorem leptonSector_u1cubed_val : u1cubed_anomaly leptonSector = 3/4 := by
  unfold u1cubed_anomaly leptonSector
  simp [L, ec, WeylFermion.totalMult]
  norm_num

/-! ### [SU(3)]² U(1) and grav²U(1) DO cancel within each sector
    (so they are NOT what forces coexistence — recorded for honesty). -/

/-- The color anomaly cancels within the quark sector alone
    (`2·(1/6) + (−2/3) + (1/3) = 0`); leptons are colorless so it is
    trivially zero for them. -/
theorem quarkSector_su3sq_zero : su3sq_u1_anomaly quarkSector = 0 := by
  unfold su3sq_u1_anomaly quarkSector
  simp [Q, uc, dc, WeylFermion.isColored]
  norm_num

theorem leptonSector_su3sq_zero : su3sq_u1_anomaly leptonSector = 0 := by
  unfold su3sq_u1_anomaly leptonSector
  simp [L, ec, WeylFermion.isColored]

/-- The gravitational anomaly cancels within EACH sector separately
    (quarks: `1 − 2 + 1 = 0`; leptons: `−1 + 1 = 0`). -/
theorem quarkSector_grav_zero : grav_u1_anomaly quarkSector = 0 := by
  unfold grav_u1_anomaly quarkSector
  simp [Q, uc, dc, WeylFermion.totalMult]
  norm_num

theorem leptonSector_grav_zero : grav_u1_anomaly leptonSector = 0 := by
  unfold grav_u1_anomaly leptonSector
  simp [L, ec, WeylFermion.totalMult]
  norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: NEITHER SECTOR IS ANOMALY FREE ALONE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Quarks alone fail `[SU(2)]²U(1)`.** -/
theorem quarks_alone_su2_anomalous : su2sq_u1_anomaly quarkSector ≠ 0 := by
  rw [quarkSector_su2sq_val]; norm_num

/-- **Leptons alone fail `[SU(2)]²U(1)`.** -/
theorem leptons_alone_su2_anomalous : su2sq_u1_anomaly leptonSector ≠ 0 := by
  rw [leptonSector_su2sq_val]; norm_num

/-- **Quarks alone fail `[U(1)]³`.** -/
theorem quarks_alone_u1cubed_anomalous : u1cubed_anomaly quarkSector ≠ 0 := by
  rw [quarkSector_u1cubed_val]; norm_num

/-- **Leptons alone fail `[U(1)]³`.** -/
theorem leptons_alone_u1cubed_anomalous : u1cubed_anomaly leptonSector ≠ 0 := by
  rw [leptonSector_u1cubed_val]; norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: TOGETHER THEY CANCEL
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The two sectors' `[SU(2)]²U(1)` contributions are exact opposites:
    `(+1/2) + (−1/2) = 0`. -/
theorem quark_lepton_su2_cancel :
    su2sq_u1_anomaly quarkSector + su2sq_u1_anomaly leptonSector = 0 := by
  rw [quarkSector_su2sq_val, leptonSector_su2sq_val]; norm_num

/-- The two sectors' `[U(1)]³` contributions are exact opposites:
    `(−3/4) + (3/4) = 0`. -/
theorem quark_lepton_u1cubed_cancel :
    u1cubed_anomaly quarkSector + u1cubed_anomaly leptonSector = 0 := by
  rw [quarkSector_u1cubed_val, leptonSector_u1cubed_val]; norm_num

/-- The `[SU(2)]²U(1)` anomaly of the UNION (full generation) is zero,
    proved directly on the concatenated list. -/
theorem union_su2sq_zero :
    su2sq_u1_anomaly (quarkSector ++ leptonSector) = 0 := by
  rw [sectors_eq_generation]; exact su2sq_u1_cancels

/-- The `[U(1)]³` anomaly of the UNION (full generation) is zero. -/
theorem union_u1cubed_zero :
    u1cubed_anomaly (quarkSector ++ leptonSector) = 0 := by
  rw [sectors_eq_generation]; exact u1cubed_cancels

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: THE HEADLINE — UNIFICATION IS FORCED
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **UNIFICATION FORCED (`[SU(2)]²U(1)` channel).**

    Neither the quark sector nor the lepton sector is `[SU(2)]²U(1)`
    anomaly free on its own, yet their union is.  A generation with
    only quarks (no leptons) or only leptons (no quarks) is anomalous;
    quantum consistency requires both together. -/
theorem quark_lepton_unification_forced :
    su2sq_u1_anomaly quarkSector ≠ 0 ∧
    su2sq_u1_anomaly leptonSector ≠ 0 ∧
    su2sq_u1_anomaly (quarkSector ++ leptonSector) = 0 :=
  ⟨quarks_alone_su2_anomalous, leptons_alone_su2_anomalous, union_su2sq_zero⟩

/-- **UNIFICATION FORCED (`[U(1)]³` channel).** Same structural fact in
    the cubic-hypercharge anomaly: each sector nonzero, union zero. -/
theorem quark_lepton_unification_forced_cubic :
    u1cubed_anomaly quarkSector ≠ 0 ∧
    u1cubed_anomaly leptonSector ≠ 0 ∧
    u1cubed_anomaly (quarkSector ++ leptonSector) = 0 :=
  ⟨quarks_alone_u1cubed_anomalous, leptons_alone_u1cubed_anomalous,
   union_u1cubed_zero⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The full structural statement that gauge-anomaly cancellation
    forces quarks and leptons to coexist, as a single `Prop`:

      (I)   in BOTH the `[SU(2)]²U(1)` and `[U(1)]³` channels, the
            quark sector ALONE is anomalous;
      (II)  in BOTH channels, the lepton sector ALONE is anomalous;
      (III) in BOTH channels, the UNION (full generation) cancels;
      (IV)  and the cancellations are by exact opposite contributions. -/
def Unification_Forced_Target : Prop :=
  -- (I) quarks alone anomalous, both channels
  (su2sq_u1_anomaly quarkSector ≠ 0 ∧ u1cubed_anomaly quarkSector ≠ 0) ∧
  -- (II) leptons alone anomalous, both channels
  (su2sq_u1_anomaly leptonSector ≠ 0 ∧ u1cubed_anomaly leptonSector ≠ 0) ∧
  -- (III) union cancels, both channels
  (su2sq_u1_anomaly (quarkSector ++ leptonSector) = 0 ∧
   u1cubed_anomaly  (quarkSector ++ leptonSector) = 0) ∧
  -- (IV) cancellation by exact opposites
  (su2sq_u1_anomaly quarkSector + su2sq_u1_anomaly leptonSector = 0 ∧
   u1cubed_anomaly  quarkSector + u1cubed_anomaly  leptonSector = 0)

/-- **QUARK–LEPTON UNIFICATION MASTER THEOREM.**

    Gauge-anomaly cancellation forces quarks and leptons to coexist:
    each sector carries an uncancelled `[SU(2)]²U(1)` AND `[U(1)]³`
    anomaly on its own, the two sectors' anomalies are exact opposites,
    and only their union — the complete quark + lepton generation — is
    quantum-mechanically consistent. -/
theorem unification_master : Unification_Forced_Target :=
  ⟨⟨quarks_alone_su2_anomalous, quarks_alone_u1cubed_anomalous⟩,
   ⟨leptons_alone_su2_anomalous, leptons_alone_u1cubed_anomalous⟩,
   ⟨union_su2sq_zero, union_u1cubed_zero⟩,
   ⟨quark_lepton_su2_cancel, quark_lepton_u1cubed_cancel⟩⟩

/-! ### Axiom audit.  `#print axioms unification_master` reports only
    `[propext, Classical.choice, Quot.sound]` — the three standard Lean
    axioms — confirming no `sorry` and no custom axioms. -/

end UnifiedTheory.LayerC.QuarkLeptonUnification
