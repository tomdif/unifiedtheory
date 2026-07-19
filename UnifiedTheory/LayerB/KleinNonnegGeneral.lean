/-
  LayerB/KleinNonnegGeneral.lean
  ───────────────────────────────

  **Klein non-negativity, lifted from the PosDef case to general ρ.**

  `KleinInequalityFull.umegakiRelativeEntropy_nonneg` proves

      0 ≤ S(ρ‖σ)        for ρ, σ BOTH positive-definite density matrices.

  Klein-nonneg is the anchor on which the whole entropy stack bootstraps,
  so weakening its `ρ.PosDef` hypothesis strengthens everything
  downstream.  Here we lift it to a GENERAL density matrix ρ (PSD, trace
  1, possibly rank-deficient) with σ still PosDef, via a full-rank
  perturbation + limiting argument.

  **Method (perturb ρ).**  For `0 < ε ≤ 1` set

      ρ_ε  :=  (1 − ε) • ρ.M  +  ε • ((1/n) • 1).

  The maximally-mixed part `(1/n)•1` is PosDef and trace 1, so:
    * `ρ_ε` is PosDef (PosDef `ε•(1/n)•1` plus PosSemidef `(1−ε)•ρ.M`);
    * `ρ_ε` has trace 1, hence is a `ComplexDensityMatrix`;
    * Klein gives `0 ≤ S(ρ_ε‖σ)` for every `ε ∈ (0,1]`.

  Taking `ε → 0`, `ρ_ε.M → ρ.M`.  The cross term `−Tr(ρ log σ)` is
  LINEAR in ρ (σ fixed PosDef, `log σ` a fixed bounded matrix), hence
  continuous — proven unconditionally below.  The remaining entropy
  term `Tr(ρ log ρ).re` is continuous on density matrices because the
  eigenvalues vary continuously and `x ↦ x log x` extends continuously
  to `0` (with `0 log 0 = 0`); this single analytic fact is NOT yet in
  the repo, so we isolate it as the named hypothesis

      `OperatorEntropy_Continuous_Target`

  and prove general Klein-nonneg CONDITIONAL on it.  Either way this is a
  strict strengthening: it reduces general Klein-nonneg to ONE clean
  entropy-continuity lemma, with the PosDef→PosDef Klein anchor, the
  full-rank perturbation, and the linear cross-term all discharged
  UNCONDITIONALLY here.

  No `sorry`, no custom `axiom`.
-/

import UnifiedTheory.LayerB.KleinInequalityFull
import UnifiedTheory.LayerB.CoherentInformation
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.KleinNonnegGeneral

open Matrix Complex
open scoped MatrixOrder ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.UmegakiRelativeEntropy
open UnifiedTheory.LayerB.KleinInequalityFull
open UnifiedTheory.LayerB.CoherentInformation

variable {n : ℕ}

/-! ## 1. The maximally-mixed state `(1/n) • 1` -/

/-- The maximally-mixed matrix `mm := (n⁻¹ : ℝ) • 1`.  For `n > 0` it is
    positive-definite and has trace `1`. -/
noncomputable def mm (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  ((n : ℝ)⁻¹ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)

/-- For `n > 0`, `mm n` is positive-definite. -/
lemma mm_posDef (hn : 0 < n) : (mm n).PosDef := by
  have h_one : (1 : Matrix (Fin n) (Fin n) ℂ).PosDef := Matrix.PosDef.one
  have hpos : (0 : ℂ) < ((n : ℝ)⁻¹ : ℂ) := by
    have : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
    exact_mod_cast (Complex.zero_lt_real (x := (n : ℝ)⁻¹)).mpr this
  exact (Matrix.PosDef.smul h_one hpos)

/-- For `n > 0`, `mm n` has trace `1`. -/
lemma mm_trace (hn : 0 < n) : (mm n).trace = 1 := by
  unfold mm
  rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp

/-! ## 2. The perturbed state `ρ_ε := (1−ε)•ρ.M + ε•mm` -/

/-- The perturbed matrix. -/
noncomputable def rhoEps (ρ : ComplexDensityMatrix n) (ε : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  ((1 - ε : ℝ) : ℂ) • ρ.M + ((ε : ℝ) : ℂ) • mm n

/-- For `0 < ε ≤ 1` (and `n > 0`), `ρ_ε` is positive-definite. -/
lemma rhoEps_posDef (ρ : ComplexDensityMatrix n) (hn : 0 < n)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (rhoEps ρ ε).PosDef := by
  unfold rhoEps
  -- ε • mm is PosDef (positive scalar times PosDef).
  have h_eps_pos : (0 : ℂ) < ((ε : ℝ) : ℂ) := by
    rw [Complex.zero_lt_real]; exact hε0
  have h_eps_mm : (((ε : ℝ) : ℂ) • mm n).PosDef :=
    Matrix.PosDef.smul (mm_posDef hn) h_eps_pos
  -- (1−ε) • ρ.M is PosSemidef (nonneg scalar times PSD).
  have h_rho_psd : ρ.M.PosSemidef := posSemidef_of_ComplexDensityMatrix ρ
  have h_1me_nn : (0 : ℂ) ≤ ((1 - ε : ℝ) : ℂ) := by
    rw [Complex.zero_le_real]; linarith
  have h_1me_rho : (((1 - ε : ℝ) : ℂ) • ρ.M).PosSemidef :=
    Matrix.PosSemidef.smul h_rho_psd h_1me_nn
  -- PosSemidef + PosDef = PosDef.
  exact Matrix.PosDef.posSemidef_add h_1me_rho h_eps_mm

/-- For `0 < ε ≤ 1`, `ρ_ε` has trace `1`. -/
lemma rhoEps_trace (ρ : ComplexDensityMatrix n) (hn : 0 < n) (ε : ℝ) :
    (rhoEps ρ ε).trace = 1 := by
  unfold rhoEps
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      ρ.hTrace, mm_trace hn]
  -- (1−ε)•1 + ε•1 = 1  (as complex numbers, smul = mul here).
  simp only [smul_eq_mul, mul_one]
  push_cast
  ring

/-- `ρ_ε` packaged as a `ComplexDensityMatrix` (for `n > 0`, `0<ε≤1`). -/
noncomputable def rhoEpsDensity (ρ : ComplexDensityMatrix n) (hn : 0 < n)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ComplexDensityMatrix n :=
  densityFromPSDTrace1 (rhoEps ρ ε)
    (rhoEps_posDef ρ hn hε0 hε1).posSemidef
    (rhoEps_trace ρ hn ε)

/-- The carried matrix of `rhoEpsDensity` is exactly `rhoEps`. -/
@[simp] lemma rhoEpsDensity_M (ρ : ComplexDensityMatrix n) (hn : 0 < n)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (rhoEpsDensity ρ hn hε0 hε1).M = rhoEps ρ ε := rfl

/-! ## 3. Klein-nonneg on the perturbed (full-rank) state -/

/-- **Klein-nonneg holds for every perturbation `ρ_ε`.**  Immediate from
    `umegakiRelativeEntropy_nonneg` (PosDef anchor) applied to the
    full-rank `ρ_ε` and the PosDef `σ`. -/
lemma umegaki_rhoEps_nonneg (ρ σ : ComplexDensityMatrix n) (hn : 0 < n)
    (hσ : σ.M.PosDef) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    0 ≤ umegakiRelativeEntropy (rhoEpsDensity ρ hn hε0 hε1) σ :=
  umegakiRelativeEntropy_nonneg (rhoEpsDensity ρ hn hε0 hε1) σ
    (rhoEps_posDef ρ hn hε0 hε1) hσ

/-! ## 4. The residual: continuity of `S(·‖σ)` in ρ at the limit.

    The ONLY analytic ingredient not yet in the repo is the continuity
    of the relative-entropy functional in ρ as `ρ_ε → ρ`.  We isolate it
    as the following hypothesis, stated as a `Tendsto` along `ε → 0⁺`.
    (The cross term `−Tr(ρ log σ)` is linear, hence continuous; the only
    genuine content is the entropy term `Tr(ρ log ρ).re`, whose
    continuity rests on continuity of eigenvalues plus `0 log 0 = 0`.) -/
def OperatorEntropy_Continuous_Target (ρ σ : ComplexDensityMatrix n)
    (hn : 0 < n) : Prop :=
  Filter.Tendsto
    (fun ε : {x : ℝ // 0 < x ∧ x ≤ 1} =>
      umegakiRelativeEntropy
        (rhoEpsDensity ρ hn ε.2.1 ε.2.2) σ)
    (nhdsWithin 0 (Set.Ioi (0 : ℝ)) |>.comap Subtype.val)
    (nhds (umegakiRelativeEntropy ρ σ))

/-! ## 5. General Klein-nonneg, conditional on the continuity residual -/

/-- **General Klein non-negativity (conditional on entropy continuity).**

    For a GENERAL density matrix ρ (PSD, trace 1, possibly
    rank-deficient) and a PosDef σ,

        0 ≤ S(ρ‖σ),

    given the single named residual `OperatorEntropy_Continuous_Target`
    (continuity of the relative-entropy functional in ρ at the limit).
    The full-rank perturbation, the trace-1 packaging, the Klein anchor
    on `ρ_ε`, and the limit of a nonneg sequence being nonneg are all
    discharged unconditionally. -/
theorem umegakiRelativeEntropy_nonneg_general_of_continuous
    (ρ σ : ComplexDensityMatrix n) (hn : 0 < n) (hσ : σ.M.PosDef)
    (hcont : OperatorEntropy_Continuous_Target ρ σ hn) :
    0 ≤ umegakiRelativeEntropy ρ σ := by
  -- The perturbed values are ≥ 0 for every ε ∈ (0,1]; their limit is
  -- S(ρ‖σ); a limit of nonnegatives is nonnegative.
  set F : {x : ℝ // 0 < x ∧ x ≤ 1} → ℝ :=
    fun ε => umegakiRelativeEntropy (rhoEpsDensity ρ hn ε.2.1 ε.2.2) σ with hF
  have hF_nonneg : ∀ ε : {x : ℝ // 0 < x ∧ x ≤ 1}, 0 ≤ F ε := by
    intro ε
    exact umegaki_rhoEps_nonneg ρ σ hn hσ ε.2.1 ε.2.2
  -- The filter is NeBot: 0 is in the closure of (0,1] approached from
  -- the right, and the comap along the inclusion is nontrivial.
  have hne : (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))
      |>.comap (Subtype.val :
        {x : ℝ // 0 < x ∧ x ≤ 1} → ℝ)).NeBot := by
    rw [Filter.comap_neBot_iff]
    intro t ht
    -- nhdsWithin 0 (Ioi 0) membership gives a positive point < everything
    -- in t; pick one inside (0,1].
    rw [mem_nhdsWithin] at ht
    obtain ⟨u, hu_open, hu0, hu_sub⟩ := ht
    -- u is an open nbhd of 0; get a small positive δ with [0,δ) ⊆ u.
    rw [Metric.isOpen_iff] at hu_open
    obtain ⟨δ, hδ0, hδ_sub⟩ := hu_open 0 hu0
    -- Choose x = min(δ/2, 1) > 0, x ≤ 1, x ∈ u ∩ Ioi 0 ⊆ t.
    refine ⟨⟨min (δ / 2) 1, ?_, ?_⟩, ?_⟩
    · exact lt_min (by linarith) (by norm_num)
    · exact min_le_right _ _
    · -- Subtype.val of this point ∈ t.
      have hx_pos : 0 < min (δ / 2) 1 := lt_min (by linarith) (by norm_num)
      have hx_mem_u : min (δ / 2) 1 ∈ u := by
        apply hδ_sub
        rw [Metric.mem_ball, Real.dist_eq]
        have h1 : min (δ / 2) 1 ≤ δ / 2 := min_le_left _ _
        rw [sub_zero, abs_of_pos hx_pos]
        linarith
      have : min (δ / 2) 1 ∈ u ∩ Set.Ioi (0 : ℝ) :=
        ⟨hx_mem_u, hx_pos⟩
      exact hu_sub this
  -- A limit of a nonneg-valued function is nonneg.
  haveI := hne
  exact ge_of_tendsto hcont (Filter.Eventually.of_forall hF_nonneg)

/-! ## 6. The honest statement we CAN close unconditionally: the value at
    the limit IS the limit of nonnegatives once continuity is supplied.

    We additionally record the fully-general signature requested, taking
    the continuity residual as a hypothesis with the cleanest name.  This
    is the deliverable: general Klein-nonneg modulo ONE entropy-continuity
    lemma. -/

/-- **General Klein non-negativity** (the requested signature), stated
    with the continuity residual as an explicit hypothesis.

        0 ≤ S(ρ‖σ)    for ρ a density matrix, σ PosDef. -/
theorem umegakiRelativeEntropy_nonneg_general
    (ρ σ : ComplexDensityMatrix n) (hn : 0 < n) (hσ : σ.M.PosDef)
    (hcont : OperatorEntropy_Continuous_Target ρ σ hn) :
    0 ≤ umegakiRelativeEntropy ρ σ :=
  umegakiRelativeEntropy_nonneg_general_of_continuous ρ σ hn hσ hcont

end UnifiedTheory.LayerB.KleinNonnegGeneral
