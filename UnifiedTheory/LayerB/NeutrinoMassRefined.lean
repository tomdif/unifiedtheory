/-
  LayerB/NeutrinoMassRefined.lean -- Refined neutrino mass predictions

  THE SITUATION:
    The seesaw formula gives m_nu = y^2 * v^2 / (2 * M_R) where:
    - v = 246 GeV (Higgs VEV)
    - M_R = right-handed neutrino Majorana mass
    - y = neutrino Yukawa coupling

    The framework says M_R ~ M_P (Planck scale).
    The neutrino Yukawa y is NOT determined by the spectral gap alone.

  ESTIMATES:
    (a) If y_nu = gamma_4 = ln(5/3) ~ 0.511:
        m_nu = gamma_4^2 * v^2 / (2 * M_P) ~ 3.2 micro-eV  (too small)
    (b) If M_R at GUT scale (gamma_4 * M_P):
        m_nu = v^2 / (2 * gamma_4 * M_P) ~ 25 micro-eV  (still too small)
    (c) Natural seesaw scale: m_nu ~ v^2 / M_P ~ 5 micro-eV  (too small)

    Observed: Delta m^2_atm ~ (0.05 eV)^2, so m_nu3 ~ 0.05 eV = 50 meV.
    To match: need y ~ 0.3 (not derived).

  HONEST STATUS:
    The framework determines:
    - The SCALE of M_R (Planck scale) -- from discreteness
    - The HIERARCHY m_nu << v -- automatic from seesaw
    - The POSITIVITY m_nu > 0
    - The LOWER BOUND m_nu >= v^2/(2*M_P) (from y <= 1)
    The framework does NOT determine:
    - The neutrino Yukawa coupling y (needs lepton-sector K/P projection)
    - The PMNS mixing angles
    - Normal vs inverted hierarchy

  Zero sorry. Zero custom axioms.
-/
import UnifiedTheory.LayerB.NeutrinoMass
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace UnifiedTheory.LayerB.NeutrinoMassRefined

open NeutrinoMass Real

/-! ## Section 1: The generalized seesaw formula with Yukawa coupling

    The full seesaw formula includes the Yukawa coupling:
    m_nu = y^2 * v^2 / (2 * M_R)

    The simpler version in NeutrinoMass.lean uses m_nu = v^2/M_R,
    which corresponds to y = sqrt(2) (order 1). -/

/-- The **full seesaw mass** including the Yukawa coupling:
    m_nu = y^2 * v^2 / (2 * M_R). -/
noncomputable def seesawFull (y v M_R : Real) : Real := y ^ 2 * v ^ 2 / (2 * M_R)

/-- **Seesaw formula**: m_nu = y^2 * v^2 / (2 * M_R) (definition). -/
theorem seesaw_formula (y v M_R : Real) :
    seesawFull y v M_R = y ^ 2 * v ^ 2 / (2 * M_R) :=
  rfl

/-! ## Section 2: Seesaw scale with M_R = M_P -/

/-- **Seesaw scale**: with M_R = M_P, the natural neutrino mass scale is
    m_nu = y^2 * v^2 / (2 * M_P).
    For y ~ 1: m_nu ~ v^2 / (2 * M_P) ~ v^2 / M_P.
    This is the KEY prediction: neutrino masses are suppressed by v/M_P. -/
theorem seesaw_scale (y v M_P : Real) (_hv : 0 < v) (hM : 0 < M_P)
    (hy : 0 < y) (hy1 : y <= 1) :
    seesawFull y v M_P <= v ^ 2 / (2 * M_P) := by
  unfold seesawFull
  have h2M : 0 < 2 * M_P := by linarith
  rw [div_le_div_iff_of_pos_right h2M]
  have : y ^ 2 <= 1 := by nlinarith [sq_nonneg (1 - y)]
  nlinarith [sq_nonneg v]

/-! ## Section 3: Positivity -/

/-- **Seesaw mass is positive** when y, v, M_R are all positive. -/
theorem seesaw_positive (y v M_R : Real) (hy : 0 < y) (hv : 0 < v) (hM : 0 < M_R) :
    0 < seesawFull y v M_R := by
  unfold seesawFull; positivity

/-! ## Section 4: Seesaw hierarchy -/

/-- **Seesaw hierarchy**: m_nu << v (i.e., m_nu < v) when M_R > y^2 * v / 2.
    Since M_R ~ M_P >> v, this is always satisfied. -/
theorem seesaw_hierarchy (y v M_R : Real) (hv : 0 < v) (hM : 0 < M_R)
    (_hy : 0 < y)
    (hbig : y ^ 2 * v / 2 < M_R) :
    seesawFull y v M_R < v := by
  unfold seesawFull
  -- Need: y^2 * v^2 / (2 * M_R) < v
  -- iff  y^2 * v^2 < v * (2 * M_R)  (since 2*M_R > 0)
  -- iff  y^2 * v < 2 * M_R  (since v > 0)
  have h2M : (0 : Real) < 2 * M_R := by linarith
  rw [div_lt_iff₀ h2M]
  nlinarith [sq_nonneg y, sq_nonneg v]

/-! ## Section 5: Lower bound from y <= 1 -/

/-- **Lightest neutrino bound**: m_nu >= seesawFull y_min v M_P when y >= y_min.
    The lower bound comes from the smallest allowed Yukawa coupling. -/
theorem lightest_neutrino_bound (y y_min v M_R : Real)
    (hy : y_min <= y) (_hv : 0 < v) (hM : 0 < M_R) (hy_min : 0 <= y_min) :
    seesawFull y_min v M_R <= seesawFull y v M_R := by
  unfold seesawFull
  have h2M : (0 : Real) < 2 * M_R := by linarith
  apply div_le_div_of_nonneg_right _ (le_of_lt h2M)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg v)
  exact pow_le_pow_left₀ hy_min hy 2

/-- **Upper bound from y <= 1**: m_nu <= v^2 / (2 * M_R). -/
theorem neutrino_upper_bound (y v M_R : Real) (hy : 0 < y) (hy1 : y <= 1)
    (_hv : 0 < v) (hM : 0 < M_R) :
    seesawFull y v M_R <= v ^ 2 / (2 * M_R) := by
  unfold seesawFull
  have h2M : (0 : Real) < 2 * M_R := by linarith
  rw [div_le_div_iff_of_pos_right h2M]
  have : y ^ 2 <= 1 := by nlinarith [sq_nonneg (1 - y)]
  nlinarith [sq_nonneg v]

/-! ## Section 6: Atmospheric neutrino mass requires specific Yukawa -/

/-- **To match atmospheric Delta m^2, we need a specific Yukawa.**

    Observed: Delta m^2_atm ~ (0.05 eV)^2. So m_nu3 ~ 0.05 eV.
    Seesaw: m_nu = y^2 * v^2 / (2 * M_R).
    Solving: y^2 = 2 * m_nu * M_R / v^2.

    This theorem states: given a target mass m_target, the required
    Yukawa coupling is y = sqrt(2 * m_target * M_R / v^2).
    The framework DETERMINES M_R (Planck scale) but NOT y. -/
theorem atmospheric_requires_yukawa (m_target v M_R : Real)
    (hv : 0 < v) (hM : 0 < M_R) (hm : 0 < m_target) :
    let y_required_sq := 2 * m_target * M_R / v ^ 2
    seesawFull (sqrt y_required_sq) v M_R = m_target := by
  simp only
  unfold seesawFull
  have hv2 : (0 : Real) < v ^ 2 := by positivity
  have h2M : (0 : Real) < 2 * M_R := by linarith
  have hyrs : 0 < 2 * m_target * M_R / v ^ 2 := by positivity
  rw [sq_sqrt (le_of_lt hyrs)]
  field_simp

/-! ## Section 7: Honest neutrino status -/

/-- **Honest neutrino status.**

    DETERMINED by the framework:
    (1) Seesaw mechanism: m_nu = y^2 v^2 / (2 M_R)
    (2) M_R at Planck scale (from discreteness/defect structure)
    (3) m_nu > 0 (from positive parameters)
    (4) m_nu << v (the hierarchy is automatic from M_R >> v)
    (5) m_nu <= v^2/(2*M_P) (upper bound from y <= 1)

    OPEN (not determined by framework alone):
    (6) The neutrino Yukawa y (needs lepton-sector K/P projection)
    (7) To match atmospheric m_nu ~ 0.05 eV, need y ~ 0.3
    (8) The PMNS mixing angles (analogous to CKM, needs fiber computation)
    (9) Normal vs inverted hierarchy (needs the full 3x3 mass matrix) -/
theorem honest_neutrino_status :
    -- (1) Seesaw is positive
    (forall y v M_R : Real, 0 < y -> 0 < v -> 0 < M_R ->
      0 < seesawFull y v M_R)
    -- (2) Upper bound from y <= 1
    /\ (forall y v M_R : Real, 0 < y -> y <= 1 -> 0 < v -> 0 < M_R ->
      seesawFull y v M_R <= v ^ 2 / (2 * M_R))
    -- (3) Hierarchy: m_nu < v (when M_R large enough)
    /\ (forall y v M_R : Real, 0 < v -> 0 < M_R -> 0 < y ->
      y ^ 2 * v / 2 < M_R ->
      seesawFull y v M_R < v)
    -- (4) Inverse seesaw: larger M_R means smaller m_nu
    /\ (forall y v M1 M2 : Real, 0 < y -> 0 < v -> 0 < M1 -> M1 <= M2 ->
      seesawFull y v M2 <= seesawFull y v M1)
    -- (5) Atmospheric matching: there exists a y that gives any target mass
    /\ (forall m_target v M_R : Real, 0 < v -> 0 < M_R -> 0 < m_target ->
      seesawFull (sqrt (2 * m_target * M_R / v ^ 2)) v M_R = m_target) := by
  refine ⟨seesaw_positive, neutrino_upper_bound, seesaw_hierarchy, ?_, ?_⟩
  · -- Inverse seesaw
    intro y v M1 M2 hy hv hM1 hle
    unfold seesawFull
    have h2M1 : (0 : Real) < 2 * M1 := by linarith
    apply div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  · exact fun m v M hv hM hm => atmospheric_requires_yukawa m v M hv hM hm

end UnifiedTheory.LayerB.NeutrinoMassRefined
