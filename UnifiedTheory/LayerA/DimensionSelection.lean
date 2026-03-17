/-
  LayerA/DimensionSelection.lean — Ehrenfest dimension selection: why 3+1

  Formalizes the classical Ehrenfest argument (1917) that d = 3 spatial
  dimensions is uniquely selected by requiring BOTH:
    (1) Stable Keplerian orbits (requires d < 4, excludes d >= 4)
    (2) Clean wave propagation / Huygens' principle (requires odd d >= 3)

  Combined, these select d = 3 as the unique spatial dimension, giving
  spacetime dimension 3 + 1 = 4.

  All proofs are by decidable arithmetic — ZERO sorry.
-/
import Mathlib.Tactic.Linarith

namespace UnifiedTheory.LayerA.DimensionSelection

/-! ### Orbital stability -/

/-- In d spatial dimensions, the gravitational potential goes as r^{2-d}.
    A circular orbit is stable under radial perturbations iff the effective
    potential has a local minimum, which requires the exponent condition
    d - 2 < 2, i.e., d < 4.  We also require d >= 2 for orbits to exist
    (need at least a plane).  So orbital stability holds iff 2 <= d <= 3. -/
def orbitalStability (d : ℕ) : Prop := 2 ≤ d ∧ d ≤ 3

instance (d : ℕ) : Decidable (orbitalStability d) :=
  inferInstanceAs (Decidable (2 ≤ d ∧ d ≤ 3))

/-- d = 3 admits stable orbits. -/
theorem orbitalStability_three : orbitalStability 3 := by
  unfold orbitalStability; omega

/-- d = 2 admits stable orbits (but fails wave propagation). -/
theorem orbitalStability_two : orbitalStability 2 := by
  unfold orbitalStability; omega

/-- d = 1 does not admit orbits (not enough dimensions). -/
theorem not_orbitalStability_one : ¬orbitalStability 1 := by
  unfold orbitalStability; omega

/-- d >= 4 does not admit stable orbits (perturbations grow). -/
theorem not_orbitalStability_of_ge_four (d : ℕ) (hd : 4 ≤ d) :
    ¬orbitalStability d := by
  unfold orbitalStability; omega

/-- d = 0 does not admit orbits. -/
theorem not_orbitalStability_zero : ¬orbitalStability 0 := by
  unfold orbitalStability; omega

/-! ### Wave propagation (Huygens' principle) -/

/-- In d spatial dimensions, the wave equation admits clean (sharp)
    signal propagation — Huygens' principle — iff d is odd and d >= 3.

    - d = 1: waves propagate without attenuation but also without
      sharp wavefronts in the physical sense (trivial 1D).
    - d = 2: signals have "tails" (no clean Huygens' principle).
    - d = 3: clean sharp propagation (Huygens' holds).
    - d = 4: even, fails Huygens'.
    - d = 5: odd >= 3 so Huygens' holds, but orbits are unstable.
    - d = 7, 9, ...: same as d = 5. -/
def waveHuygens (d : ℕ) : Prop := 3 ≤ d ∧ d % 2 = 1

instance (d : ℕ) : Decidable (waveHuygens d) :=
  inferInstanceAs (Decidable (3 ≤ d ∧ d % 2 = 1))

/-- d = 3 admits clean wave propagation. -/
theorem waveHuygens_three : waveHuygens 3 := by
  unfold waveHuygens; omega

/-- d = 1 does not satisfy our wave propagation criterion. -/
theorem not_waveHuygens_one : ¬waveHuygens 1 := by
  unfold waveHuygens; omega

/-- d = 2 does not satisfy Huygens' principle (even dimension). -/
theorem not_waveHuygens_two : ¬waveHuygens 2 := by
  unfold waveHuygens; omega

/-- d = 5 satisfies Huygens' principle (odd >= 3). -/
theorem waveHuygens_five : waveHuygens 5 := by
  unfold waveHuygens; omega

/-- d = 4 does not satisfy Huygens' principle (even). -/
theorem not_waveHuygens_four : ¬waveHuygens 4 := by
  unfold waveHuygens; omega

/-! ### The Ehrenfest selection: d = 3 is unique -/

/-- A spatial dimension is **physically selected** if it admits both
    stable orbits and clean wave propagation. -/
def physicallySelected (d : ℕ) : Prop := orbitalStability d ∧ waveHuygens d

instance (d : ℕ) : Decidable (physicallySelected d) :=
  inferInstanceAs (Decidable (orbitalStability d ∧ waveHuygens d))

/-- d = 3 is physically selected. -/
theorem physicallySelected_three : physicallySelected 3 := by
  exact ⟨orbitalStability_three, waveHuygens_three⟩

/-- d = 3 is the UNIQUE physically selected dimension.
    Proof: orbitalStability requires d <= 3, waveHuygens requires d >= 3,
    so d = 3 is forced. The oddness condition is automatically satisfied. -/
theorem unique_physicallySelected (d : ℕ) (h : physicallySelected d) : d = 3 := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  omega

/-- Equivalent formulation: d = 3 iff physically selected. -/
theorem physicallySelected_iff (d : ℕ) : physicallySelected d ↔ d = 3 := by
  constructor
  · exact unique_physicallySelected d
  · rintro rfl; exact physicallySelected_three

/-! ### Spacetime dimension consequence -/

/-- The spacetime dimension is spatial dimension + 1 (for time). -/
def spacetimeDim (d : ℕ) : ℕ := d + 1

/-- The physically selected spacetime dimension is 4 = 3 + 1. -/
theorem spacetime_is_four (d : ℕ) (h : physicallySelected d) :
    spacetimeDim d = 4 := by
  have := unique_physicallySelected d h
  subst this
  rfl

/-- No other spacetime dimension is physically selected. -/
theorem spacetime_unique (n : ℕ) (h : ∃ d, physicallySelected d ∧ spacetimeDim d = n) :
    n = 4 := by
  obtain ⟨d, hd, hst⟩ := h
  have := unique_physicallySelected d hd
  subst this
  exact hst.symm

/-! ### Exhaustive case analysis for small d -/

/-- For d in {0, 1, 2, 4, 5, 6, 7}, d is NOT physically selected.
    This provides explicit verification for all small cases. -/
theorem not_physicallySelected_zero : ¬physicallySelected 0 := by
  unfold physicallySelected orbitalStability; omega

theorem not_physicallySelected_one : ¬physicallySelected 1 := by
  unfold physicallySelected orbitalStability; omega

theorem not_physicallySelected_two : ¬physicallySelected 2 := by
  unfold physicallySelected waveHuygens; omega

theorem not_physicallySelected_four : ¬physicallySelected 4 := by
  unfold physicallySelected orbitalStability; omega

theorem not_physicallySelected_five : ¬physicallySelected 5 := by
  unfold physicallySelected orbitalStability; omega

theorem not_physicallySelected_six : ¬physicallySelected 6 := by
  unfold physicallySelected orbitalStability; omega

theorem not_physicallySelected_seven : ¬physicallySelected 7 := by
  unfold physicallySelected orbitalStability; omega

end UnifiedTheory.LayerA.DimensionSelection
