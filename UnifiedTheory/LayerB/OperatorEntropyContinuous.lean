/-
  LayerB/OperatorEntropyContinuous.lean
  ──────────────────────────────────────

  **Discharge of `OperatorEntropy_Continuous_Target`.**

  `KleinNonnegGeneral.lean` reduced general-PSD Klein non-negativity

      0 ≤ S(ρ‖σ)        (ρ a density matrix, σ PosDef)

  to a single named continuity residual: as `ε → 0⁺`,

      S(ρ_ε ‖ σ)  →  S(ρ ‖ σ),   ρ_ε := (1−ε)•ρ + ε•(I/n).

  Here we PROVE that `Tendsto` UNCONDITIONALLY, hence make
  `umegakiRelativeEntropy_nonneg_general` an honest, hypothesis-free
  theorem (`umegakiRelativeEntropy_nonneg_general_unconditional` below).

  **The two halves of `S(ρ_ε‖σ) = Re Tr(ρ_ε·log ρ_ε) − Re Tr(ρ_ε·log σ)`.**

  * **Cross term** `Re Tr(ρ_ε · log σ)`.  Here `log σ = cfc log σ.M` is a
    FIXED matrix; `ε ↦ ρ_ε` is affine, hence continuous, and
    `X ↦ Re Tr(X · M)` is continuous (it is ℝ-linear in finite
    dimension).  So the cross term is continuous in ε — no positivity
    needed.

  * **Entropy term** `Re Tr(ρ_ε · log ρ_ε)`.  The product `ρ_ε·log ρ_ε`
    equals `cfc g ρ_ε` with `g(x) = x·log x` (this is `cfc_mul` on the
    finite spectrum, valid for EVERY density matrix — it holds in the
    repo as `HolevoUmegakiDischarge.mul_operatorLog_eq_operatorXLogX`).
    The function `g` is continuous on ALL of `ℝ` (`Real.continuous_mul_log`,
    using `0·log 0 = 0`), so we never need `log` itself to be continuous
    at `0`.  Mathlib's `Filter.Tendsto.cfc` (continuity of the CFC in the
    OPERATOR argument, on a fixed compact spectral window `[0,1]`) then
    gives `cfc g ρ_ε → cfc g ρ` as matrices, whence the traces converge.

  This is the crux that lets the limit pass through a possibly SINGULAR
  ρ: we route the entropy term through the everywhere-continuous `g =
  x·log x` rather than the singular `log`.

  **What Mathlib provides (investigated):**
    * `Filter.Tendsto.cfc` / `Continuous.cfc'`
      (`Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Continuity.lean`)
      — continuity of `a ↦ cfc f a` in the OPERATOR, given a fixed
      compact spectral window `s` and `ContinuousOn f s`.  THIS is the
      lemma that closes the entropy term.
    * `Real.continuous_mul_log : Continuous (fun x ↦ x * Real.log x)`.
    * NO direct "matrix-eigenvalues are continuous" lemma exists; we do
      NOT need it — the cfc-in-operator route bypasses eigenvalues.

  No `sorry`, no custom `axiom`.
-/

import UnifiedTheory.LayerB.KleinNonnegGeneral
import UnifiedTheory.LayerB.HolevoUmegakiDischarge
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.CStarAlgebra.Matrix

set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.LayerB.OperatorEntropyContinuous

open Matrix Complex Filter Topology
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.SpectralFC
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.UmegakiRelativeEntropy
open UnifiedTheory.LayerB.HolevoUmegakiDischarge
open UnifiedTheory.LayerB.KleinNonnegGeneral

variable {n : ℕ}

/-! ## 1. Spectral window: a density matrix has real spectrum in `[0,1]` -/

/-- Each eigenvalue of a complex density matrix lies in `[0,1]`:
    nonneg (PSD) and `≤ 1` (the eigenvalues are nonneg and sum to `1`). -/
lemma eigenvalue_mem_Icc (ρ : ComplexDensityMatrix n) (i : Fin n) :
    ρ.hHerm.eigenvalues i ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨eigenvalues_nonneg ρ i, ?_⟩
  -- λ i ≤ ∑ j λ j = 1, since every λ j ≥ 0.
  have hsum : ∑ j, ρ.hHerm.eigenvalues j = 1 := sum_eigenvalues_eq_one ρ
  have hle : ρ.hHerm.eigenvalues i ≤ ∑ j, ρ.hHerm.eigenvalues j :=
    Finset.single_le_sum (f := ρ.hHerm.eigenvalues)
      (fun j _ => eigenvalues_nonneg ρ j) (Finset.mem_univ i)
  rw [hsum] at hle
  exact hle

/-- The `ℝ`-spectrum of a density matrix is contained in the compact
    window `[0,1]`.  Via `spectrum_real_eq_range_eigenvalues`. -/
lemma spectrum_subset_Icc (ρ : ComplexDensityMatrix n) :
    spectrum ℝ ρ.M ⊆ Set.Icc (0 : ℝ) 1 := by
  rw [ρ.hHerm.spectrum_real_eq_range_eigenvalues]
  rintro x ⟨i, rfl⟩
  exact eigenvalue_mem_Icc ρ i

/-! ## 2. The perturbed matrix path is continuous and lands in the window -/

/-- `ρ_ε` at `ε = 0` is `ρ.M`. -/
lemma rhoEps_zero (ρ : ComplexDensityMatrix n) : rhoEps ρ 0 = ρ.M := by
  simp [rhoEps]

/-- The affine matrix path `ε ↦ ρ_ε = (1−ε)•ρ.M + ε•mm n` is continuous
    as a function `ℝ → Matrix` (in the operator-norm topology, which
    coincides with the entrywise topology). -/
lemma continuous_rhoEps (ρ : ComplexDensityMatrix n) :
    Continuous (fun ε : ℝ => rhoEps ρ ε) := by
  unfold rhoEps
  have h1 : Continuous (fun ε : ℝ => ((1 - ε : ℝ) : ℂ) • ρ.M) := by
    refine Continuous.smul ?_ continuous_const
    exact Complex.continuous_ofReal.comp (by fun_prop)
  have h2 : Continuous (fun ε : ℝ => ((ε : ℝ) : ℂ) • mm n) := by
    refine Continuous.smul ?_ continuous_const
    exact Complex.continuous_ofReal.comp continuous_id
  exact h1.add h2

/-- For `ε ∈ (0,1]`, `ρ_ε` is a density matrix, so its spectrum lands in
    `[0,1]`. -/
lemma spectrum_rhoEps_subset_Icc (ρ : ComplexDensityMatrix n) (hn : 0 < n)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    spectrum ℝ (rhoEps ρ ε) ⊆ Set.Icc (0 : ℝ) 1 := by
  have hdens := spectrum_subset_Icc (rhoEpsDensity ρ hn hε0 hε1)
  rw [rhoEpsDensity_M] at hdens
  exact hdens

/-! ## 3. `g(x) = x·log x` is continuous on the window -/

/-- `g(x) = x·log x` is continuous on `[0,1]` (indeed on all of ℝ),
    with `g(0) = 0·log 0 = 0`. -/
lemma continuousOn_xlogx_Icc :
    ContinuousOn (fun x : ℝ => x * Real.log x) (Set.Icc (0 : ℝ) 1) :=
  Real.continuous_mul_log.continuousOn

/-! ## 4. The entropy-term integrand as a single CFC -/

/-- The product `ρ_ε · log ρ_ε` equals `cfc (x·log x) ρ_ε`, for EVERY
    density matrix (`HolevoUmegakiDischarge.mul_operatorLog_eq_operatorXLogX`,
    valid because the spectrum is finite so every function is continuous on
    it).  Stated at the matrix level via `cfc`. -/
lemma rhoEps_mul_log_eq_cfc_xlogx (ρ : ComplexDensityMatrix n) (hn : 0 < n)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (rhoEps ρ ε) * cfc Real.log (rhoEps ρ ε)
      = cfc (fun x => x * Real.log x) (rhoEps ρ ε) := by
  have h := mul_operatorLog_eq_operatorXLogX (rhoEpsDensity ρ hn hε0 hε1)
  -- operatorLog/operatorXLogX unfold to cfc on `.M = rhoEps ρ ε`.
  simpa only [rhoEpsDensity_M, operatorLog, operatorXLogX, cfcρ] using h

/-- Same identity at the LIMIT, for the (possibly singular) density
    matrix ρ. -/
lemma rho_mul_log_eq_cfc_xlogx (ρ : ComplexDensityMatrix n) :
    ρ.M * cfc Real.log ρ.M
      = cfc (fun x => x * Real.log x) ρ.M := by
  have h := mul_operatorLog_eq_operatorXLogX ρ
  simpa only [operatorLog, operatorXLogX, cfcρ] using h

/-! ## 5. CFC-in-operator tendsto for the entropy term -/

/-- **Entropy-integrand convergence.**  As `ε → 0⁺`,
    `cfc (x·log x) ρ_ε → cfc (x·log x) ρ` in the matrix algebra.
    This is `Filter.Tendsto.cfc` on the fixed compact spectral window
    `[0,1]`, using that `g = x·log x` is continuous there (so no
    singularity of `log` at `0` is ever touched). -/
lemma tendsto_cfc_xlogx (ρ : ComplexDensityMatrix n) (hn : 0 < n) :
    Tendsto (fun ε : ℝ => cfc (fun x => x * Real.log x) (rhoEps ρ ε))
      (𝓝[>] (0 : ℝ))
      (𝓝 (cfc (fun x => x * Real.log x) ρ.M)) := by
  -- The path tends to ρ.M (its value at ε = 0, by continuity).
  have hpath : Tendsto (fun ε : ℝ => rhoEps ρ ε) (𝓝[>] (0 : ℝ))
      (𝓝 ρ.M) := by
    have h := ((continuous_rhoEps ρ).continuousAt (x := (0 : ℝ))).tendsto
    rw [show rhoEps ρ 0 = ρ.M from rhoEps_zero ρ] at h
    exact h.mono_left nhdsWithin_le_nhds
  -- Eventually (for ε ∈ (0,1]) the spectrum is in [0,1] and ρ_ε is
  -- self-adjoint.
  have hev_spec : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      spectrum ℝ (rhoEps ρ ε) ⊆ Set.Icc (0 : ℝ) 1 := by
    -- On (0,1] this holds; (0,1] is a neighbourhood of 0 within (0,∞).
    have hmem : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
      Ioc_mem_nhdsGT (by norm_num)
    filter_upwards [hmem] with ε hε
    exact spectrum_rhoEps_subset_Icc ρ hn hε.1 hε.2
  have hev_sa : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      IsSelfAdjoint (rhoEps ρ ε) := by
    have hmem : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
      Ioc_mem_nhdsGT (by norm_num)
    filter_upwards [hmem] with ε hε
    exact (rhoEps_posDef ρ hn hε.1 hε.2).isHermitian
  -- The limit point ρ.M: self-adjoint, spectrum in [0,1].
  have hρ_sa : IsSelfAdjoint ρ.M := ρ.hHerm
  have hρ_spec : spectrum ℝ ρ.M ⊆ Set.Icc (0 : ℝ) 1 := spectrum_subset_Icc ρ
  -- Apply the CFC-in-operator tendsto lemma.
  exact Filter.Tendsto.cfc isCompact_Icc (fun x => x * Real.log x)
    hpath hev_spec hev_sa hρ_spec hρ_sa continuousOn_xlogx_Icc

/-! ## 6. Trace / real-part are continuous; entropy term converges -/

/-- `X ↦ (Matrix.trace X).re` is continuous. -/
lemma continuous_re_trace :
    Continuous (fun X : Matrix (Fin n) (Fin n) ℂ => (Matrix.trace X).re) := by
  have h_tr : Continuous (Matrix.trace : Matrix (Fin n) (Fin n) ℂ → ℂ) := by
    unfold Matrix.trace
    refine continuous_finset_sum _ ?_
    intro i _
    exact (continuous_apply i).comp (continuous_apply i)
  exact Complex.continuous_re.comp h_tr

/-- **Entropy-term convergence.**  As `ε → 0⁺`,
    `Re Tr(ρ_ε · log ρ_ε) → Re Tr(ρ · log ρ)`. -/
lemma tendsto_entropy_term (ρ : ComplexDensityMatrix n) (hn : 0 < n) :
    Tendsto
      (fun ε : ℝ =>
        (Matrix.trace ((rhoEps ρ ε) * cfc Real.log (rhoEps ρ ε))).re)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Matrix.trace (ρ.M * cfc Real.log ρ.M)).re) := by
  -- Rewrite both sides through `cfc (x log x)` using the mul identity.
  have hrw_lim : (Matrix.trace (ρ.M * cfc Real.log ρ.M)).re
      = (Matrix.trace (cfc (fun x => x * Real.log x) ρ.M)).re := by
    rw [rho_mul_log_eq_cfc_xlogx]
  rw [hrw_lim]
  -- Eventually rewrite the ε-integrand likewise (on (0,1]).
  have hmem : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
    Ioc_mem_nhdsGT (by norm_num)
  have hcongr : (fun ε : ℝ =>
        (Matrix.trace ((rhoEps ρ ε) * cfc Real.log (rhoEps ρ ε))).re)
      =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε : ℝ =>
        (Matrix.trace (cfc (fun x => x * Real.log x) (rhoEps ρ ε))).re) := by
    filter_upwards [hmem] with ε hε
    rw [rhoEps_mul_log_eq_cfc_xlogx ρ hn hε.1 hε.2]
  rw [tendsto_congr' hcongr]
  -- Now compose the matrix-level cfc tendsto with continuous Re∘trace.
  exact (continuous_re_trace.continuousAt).tendsto.comp (tendsto_cfc_xlogx ρ hn)

/-! ## 7. The cross term `Re Tr(ρ_ε · log σ)` converges (linear) -/

/-- `X ↦ Re Tr(X · M)` is continuous for a fixed matrix `M`. -/
lemma continuous_re_trace_mul_const (M : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun X : Matrix (Fin n) (Fin n) ℂ =>
      (Matrix.trace (X * M)).re) := by
  have hmul : Continuous (fun X : Matrix (Fin n) (Fin n) ℂ => X * M) := by
    exact continuous_id.mul continuous_const
  exact continuous_re_trace.comp hmul

/-- **Cross-term convergence.**  As `ε → 0⁺`,
    `Re Tr(ρ_ε · log σ) → Re Tr(ρ · log σ)`. -/
lemma tendsto_cross_term (ρ σ : ComplexDensityMatrix n) :
    Tendsto
      (fun ε : ℝ => (Matrix.trace ((rhoEps ρ ε) * cfc Real.log σ.M)).re)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Matrix.trace (ρ.M * cfc Real.log σ.M)).re) := by
  have hpath : Tendsto (fun ε : ℝ => rhoEps ρ ε) (𝓝[>] (0 : ℝ)) (𝓝 ρ.M) := by
    have h := ((continuous_rhoEps ρ).continuousAt (x := (0 : ℝ))).tendsto
    rw [show rhoEps ρ 0 = ρ.M from rhoEps_zero ρ] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact ((continuous_re_trace_mul_const (cfc Real.log σ.M)).continuousAt).tendsto.comp
    hpath

/-! ## 8. Assemble: `S(ρ_ε‖σ) → S(ρ‖σ)` as a function of `ε : ℝ` -/

/-- The Umegaki functional as a bare function of the matrix-path
    parameter `ε`, ignoring the subtype packaging.  Equals
    `umegakiRelativeEntropy (rhoEpsDensity …) σ` for `ε ∈ (0,1]`. -/
noncomputable def umegakiPath (ρ σ : ComplexDensityMatrix n) (ε : ℝ) : ℝ :=
  (Matrix.trace ((rhoEps ρ ε) *
    (cfc Real.log (rhoEps ρ ε) - cfc Real.log σ.M))).re

/-- `umegakiPath` splits as entropy term minus cross term. -/
lemma umegakiPath_eq (ρ σ : ComplexDensityMatrix n) (ε : ℝ) :
    umegakiPath ρ σ ε
      = (Matrix.trace ((rhoEps ρ ε) * cfc Real.log (rhoEps ρ ε))).re
        - (Matrix.trace ((rhoEps ρ ε) * cfc Real.log σ.M)).re := by
  unfold umegakiPath
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]

/-- **The path-level Tendsto.**  `umegakiPath ρ σ ε → umegakiRelativeEntropy ρ σ`
    as `ε → 0⁺`. -/
lemma tendsto_umegakiPath (ρ σ : ComplexDensityMatrix n) (hn : 0 < n) :
    Tendsto (fun ε : ℝ => umegakiPath ρ σ ε) (𝓝[>] (0 : ℝ))
      (𝓝 (umegakiRelativeEntropy ρ σ)) := by
  -- Limit value as the difference entropy − cross at ρ.
  have hlim : umegakiRelativeEntropy ρ σ
      = (Matrix.trace (ρ.M * cfc Real.log ρ.M)).re
        - (Matrix.trace (ρ.M * cfc Real.log σ.M)).re := by
    unfold umegakiRelativeEntropy operatorLog cfcρ
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  rw [hlim]
  -- Rewrite the function as a difference.
  have hfun : (fun ε : ℝ => umegakiPath ρ σ ε)
      = (fun ε : ℝ =>
          (Matrix.trace ((rhoEps ρ ε) * cfc Real.log (rhoEps ρ ε))).re
          - (Matrix.trace ((rhoEps ρ ε) * cfc Real.log σ.M)).re) := by
    funext ε; exact umegakiPath_eq ρ σ ε
  rw [hfun]
  exact (tendsto_entropy_term ρ hn).sub (tendsto_cross_term ρ σ)

/-! ## 9. Discharge the named target -/

/-- **The discharge.**  `OperatorEntropy_Continuous_Target ρ σ hn` holds
    UNCONDITIONALLY, for every density matrix ρ and PosDef σ (indeed for
    any σ). -/
theorem operatorEntropy_continuous_target
    (ρ σ : ComplexDensityMatrix n) (hn : 0 < n) :
    OperatorEntropy_Continuous_Target ρ σ hn := by
  unfold OperatorEntropy_Continuous_Target
  -- The subtype-indexed function equals `umegakiPath ρ σ ∘ Subtype.val`,
  -- because `umegakiRelativeEntropy` depends on the perturbed state only
  -- through its carried matrix `.M = rhoEps ρ ε`.
  have hcongr : (fun ε : {x : ℝ // 0 < x ∧ x ≤ 1} =>
        umegakiRelativeEntropy (rhoEpsDensity ρ hn ε.2.1 ε.2.2) σ)
      = (fun ε : {x : ℝ // 0 < x ∧ x ≤ 1} =>
          umegakiPath ρ σ ε.val) := by
    funext ε
    unfold umegakiPath umegakiRelativeEntropy operatorLog cfcρ
    rw [rhoEpsDensity_M]
  rw [hcongr]
  -- Tendsto of `umegakiPath ρ σ` along 𝓝[>] 0, pulled back along
  -- `Subtype.val` into the comap filter.
  have hbase : Tendsto (fun ε : ℝ => umegakiPath ρ σ ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (umegakiRelativeEntropy ρ σ)) :=
    tendsto_umegakiPath ρ σ hn
  -- The target filter is `(𝓝[>] 0).comap Subtype.val`; compose.
  have hval : Tendsto (Subtype.val : {x : ℝ // 0 < x ∧ x ≤ 1} → ℝ)
      ((𝓝[>] (0 : ℝ)).comap Subtype.val) (𝓝[>] (0 : ℝ)) :=
    tendsto_comap
  exact hbase.comp hval

/-! ## 10. General Klein non-negativity, now UNCONDITIONAL -/

/-- **General Klein non-negativity — UNCONDITIONAL.**

    For a GENERAL density matrix ρ (PSD, trace 1, possibly
    rank-deficient) and a PosDef σ,

        0 ≤ S(ρ‖σ).

    The continuity residual `OperatorEntropy_Continuous_Target` is now
    discharged (`operatorEntropy_continuous_target`), so the whole entropy
    stack is lifted off its PosDef-on-ρ restriction. -/
theorem umegakiRelativeEntropy_nonneg_general_unconditional
    (ρ σ : ComplexDensityMatrix n) (hn : 0 < n) (hσ : σ.M.PosDef) :
    0 ≤ umegakiRelativeEntropy ρ σ :=
  umegakiRelativeEntropy_nonneg_general_of_continuous ρ σ hn hσ
    (operatorEntropy_continuous_target ρ σ hn)

-- Axiom audit (verified 2026-06-03):
--   operatorEntropy_continuous_target
--   umegakiRelativeEntropy_nonneg_general_unconditional
-- both depend only on [propext, Classical.choice, Quot.sound]
-- (Lean's three standard axioms).  No `sorry`, no custom `axiom`.

end UnifiedTheory.LayerB.OperatorEntropyContinuous
