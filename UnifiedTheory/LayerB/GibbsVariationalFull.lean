/-
  LayerB/GibbsVariationalFull.lean
  ─────────────────────────────────

  **Discharge of the Gibbs gap identity (★) as a REAL theorem.**

  This file turns the named-`Prop` hole

      `FreeEnergy_RelEntropy_Identity_Target`   (the gap identity ★)

  of `GibbsVariational.lean` into an honest theorem for the *specific*
  Gibbs reference state `ρ_β = exp(-βH)/Z`, by proving the operator
  logarithm identity

      `log ρ_β = -βH - (log Z) · I`                              (LOG)

  via the continuous functional calculus (`cfc` composition
  `log ∘ (exp(-β·)/Z) = (x ↦ -βx - log Z)`), and then computing the
  free-energy gap algebraically.

  Concretely, with `T = 1/β` (so `β = 1/T`), for ANY positive-definite
  state ρ we show

      F(ρ) - F(ρ_β)  =  T · S(ρ ‖ ρ_β) ,

  i.e. `FreeEnergy_RelEntropy_Identity_Target ρ (gibbsDensity β H) H T`.
  Feeding this into the already-proved Klein engine
  `gibbs_variational_of_gap` makes the full variational principle

      F(ρ)  ≥  F(ρ_β)  =  -T log Z

  an UNCONDITIONAL theorem (modulo the positive-definiteness of ρ,
  which Klein genuinely requires for faithfulness/finiteness).

  ## What is genuinely assembled (no new scope)

    * `gibbsDensity β H hH`  — `ρ_β` packaged as a `ComplexDensityMatrix`
                               (PSD + trace 1 via `densityFromPSDTrace1`).
    * `gibbsDensity_posDef`  — `ρ_β` is positive definite.
    * `operatorLog_gibbsDensity`        — the (LOG) identity.
    * `re_trace_mul_operatorLog_gibbs`  — `Re Tr(ρ · log ρ_β)
                                            = -β·⟨H⟩_ρ - log Z`.
    * `freeEnergy_gibbs_eq`             — `F(ρ_β) = -T log Z`.
    * `gibbs_gap_identity`             — discharges (★).
    * `gibbs_variational_principle`     — `F(ρ_β) ≤ F(ρ)` and
                                          `Gibbs_Variational_Target`.

  STANDING CONSTRAINT: zero `sorry`, zero custom `axiom`.
-/

import UnifiedTheory.LayerB.GibbsVariational
import UnifiedTheory.LayerB.KMSCondition
import UnifiedTheory.LayerB.HolevoUmegakiDischarge
import UnifiedTheory.LayerB.CoherentInformation
import UnifiedTheory.LayerB.KleinEquality
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.GibbsVariationalFull

open Matrix Complex
open scoped ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.SpectralFC
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.UmegakiRelativeEntropy
open UnifiedTheory.LayerB.GibbsVariational
open UnifiedTheory.LayerB.KMSCondition
open UnifiedTheory.LayerB.HolevoUmegakiDischarge
open UnifiedTheory.LayerB.CoherentInformation

variable {n : ℕ}

/-! ## 0. Scalar helper: `algebraMap ℝ (Matrix _ _ ℂ) r = (r : ℂ) • 1`. -/

private lemma algebraMap_real_matrix_eq_smul_one (r : ℝ) :
    algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ) r
      = (r : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [Algebra.algebraMap_eq_smul_one]
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul]

/-- Real-scalar and complex-scalar action agree on a complex matrix. -/
private lemma smul_R_C (a : ℝ) (M : Matrix (Fin n) (Fin n) ℂ) :
    (a : ℝ) • M = (a : ℂ) • M := by
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul]

/-! ## 1. The Boltzmann operator is positive definite. -/

/-- `exp(-βH) = U · diag(exp(-β λ)) · star U` is positive definite:
    the diagonal entries `exp(-β λ_i) > 0` make the diagonal PosDef,
    and unitary conjugation preserves PosDef. -/
theorem boltzmannOp_posDef
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    (boltzmannOp β H).PosDef := by
  classical
  set U : Matrix.unitaryGroup (Fin n) ℂ := hH.eigenvectorUnitary with hU_def
  set d : Fin n → ℝ := fun i => Real.exp (-β * hH.eigenvalues i) with hd_def
  set D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) with hD_def
  have hd_pos : ∀ i, 0 < d i := fun i => Real.exp_pos _
  -- D is PosDef.
  have hD_PD : D.PosDef := by
    rw [hD_def]
    rw [Matrix.posDef_diagonal_iff]
    intro i
    exact_mod_cast hd_pos i
  -- spectral form of boltzmannOp.
  have h_spec : boltzmannOp β H = U.val * D * star U.val := by
    rw [boltzmannOp_spectral β H hH, hU_def, hD_def, hd_def]
  rw [h_spec]
  -- U * D * star U = (star U)ᴴ * D * (star U); conjugation by an
  -- invertible matrix preserves PosDef.
  have hUUstar : U.val * (star U.val) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp U.property
  have hUstarU : (star U.val) * U.val = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.property
  have hU_unit : IsUnit ((star U.val) : Matrix (Fin n) (Fin n) ℂ) := by
    refine ⟨⟨star U.val, U.val, ?_, ?_⟩, rfl⟩
    · exact hUstarU
    · exact hUUstar
  have hU_inj : Function.Injective ((star U.val) : Matrix (Fin n) (Fin n) ℂ).mulVec :=
    Matrix.mulVec_injective_of_isUnit hU_unit
  have h_conjTranspose : (star U.val).conjTranspose = U.val := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have key := hD_PD.conjTranspose_mul_mul_same (B := star U.val) hU_inj
  rw [h_conjTranspose] at key
  exact key

/-! ## 2. `Tr(exp(-βH)/Z) = 1` and the Gibbs density matrix. -/

/-- `gibbsState β H` is positive definite when `Z > 0`. -/
theorem gibbsState_posDef
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (hZ : 0 < partitionFunction β H) :
    (gibbsState β H).PosDef := by
  unfold gibbsState
  have hc : (0 : ℝ) < 1 / partitionFunction β H := by positivity
  exact (boltzmannOp_posDef β H hH).smul (by exact_mod_cast hc)

/-- `Tr(gibbsState β H) = 1` when `Z > 0`. -/
theorem trace_gibbsState_eq_one
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (hZ : 0 < partitionFunction β H) :
    (gibbsState β H).trace = 1 := by
  unfold gibbsState
  rw [Matrix.trace_smul, trace_boltzmannOp_eq_Z_cast β H hH]
  rw [smul_eq_mul]
  have hZ' : (partitionFunction β H : ℝ) ≠ 0 := ne_of_gt hZ
  rw [one_div]
  push_cast
  rw [inv_mul_cancel₀ (by exact_mod_cast hZ')]

/-- **The Gibbs state packaged as a `ComplexDensityMatrix`** (PosDef
    ⟹ PSD, trace 1).  Requires `Z(β,H) > 0`. -/
noncomputable def gibbsDensity
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (hZ : 0 < partitionFunction β H) :
    ComplexDensityMatrix n :=
  densityFromPSDTrace1 (gibbsState β H)
    (gibbsState_posDef β H hH hZ).posSemidef
    (trace_gibbsState_eq_one β H hH hZ)

@[simp] theorem gibbsDensity_M
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (hZ : 0 < partitionFunction β H) :
    (gibbsDensity β H hH hZ).M = gibbsState β H := rfl

theorem gibbsDensity_posDef
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (hZ : 0 < partitionFunction β H) :
    (gibbsDensity β H hH hZ).M.PosDef := by
  rw [gibbsDensity_M]
  exact gibbsState_posDef β H hH hZ

/-! ## 3. The operator-log identity `log ρ_β = -βH - (log Z)·I`. -/

/-- **Composition step**: `cfc Real.log (cfc g H) = cfc (Real.log ∘ g) H`
    for `g x = exp(-βx)/Z`, valid because `g` maps the spectrum into the
    positive reals where `log` is continuous, and both functions are
    continuous on the (finite) spectrum. -/
private lemma cfc_log_comp_gibbs
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (Z : ℝ) :
    cfc Real.log (cfc (fun x => Real.exp (-β * x) / Z) H)
      = cfc (fun x => Real.log (Real.exp (-β * x) / Z)) H := by
  have hSA : IsSelfAdjoint H := hH
  have hg_cont : ContinuousOn (fun x => Real.exp (-β * x) / Z)
      (spectrum ℝ H) := (Set.toFinite _).continuousOn _
  have hlog_cont : ContinuousOn Real.log
      ((fun x => Real.exp (-β * x) / Z) '' spectrum ℝ H) :=
    (Set.toFinite _).continuousOn _
  rw [← cfc_comp Real.log (fun x => Real.exp (-β * x) / Z) H hSA hlog_cont hg_cont]
  rfl

/-- **The operator logarithm of the Gibbs state**:

      `log ρ_β = -βH - (log Z) · I`.

    Proof: `ρ_β = cfc g H` with `g x = exp(-βx)/Z`; the cfc composition
    rewrites `log ρ_β = cfc (log ∘ g) H`, and `log(exp(-βx)/Z) =
    -βx - log Z` (using `Z > 0`), which is the affine cfc
    `-β • H - (log Z) • I`. -/
theorem operatorLog_gibbsDensity
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (hZ : 0 < partitionFunction β H) :
    operatorLog (gibbsDensity β H hH hZ)
      = ((-β : ℂ)) • H
          - ((Real.log (partitionFunction β H) : ℂ))
              • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  set Z : ℝ := partitionFunction β H with hZ_def
  have hSA : IsSelfAdjoint H := hH
  -- Unfold operatorLog and the Gibbs state.
  unfold operatorLog cfcρ
  rw [gibbsDensity_M]
  -- gibbsState β H = cfc (fun x => exp(-βx)/Z) H.
  have h_gibbs_cfc :
      gibbsState β H = cfc (fun x => Real.exp (-β * x) / Z) H := by
    unfold gibbsState boltzmannOp
    rw [← hZ_def]
    -- exp(-βx)/Z = (1/Z) • exp(-βx)  (as a function), so cfc factors the scalar out.
    have hfun :
        (fun x => Real.exp (-β * x) / Z)
          = (fun x => (1 / Z) • Real.exp (-β * x)) := by
      funext x; rw [smul_eq_mul, div_eq_mul_inv, mul_comm, one_div]
    rw [hfun, cfc_smul (R := ℝ) (S := ℝ) (1 / Z) (fun x => Real.exp (-β * x)) H
          (hf := (Set.toFinite _).continuousOn _)]
    exact (smul_R_C (1 / Z) _).symm
  rw [h_gibbs_cfc, cfc_log_comp_gibbs β H hH Z]
  -- log(exp(-βx)/Z) = -βx - log Z  (Z > 0).
  have hZ_pos : 0 < Z := by rw [hZ_def]; exact hZ
  have hlogfun :
      (fun x => Real.log (Real.exp (-β * x) / Z))
        = (fun x => (-β) * x - Real.log Z) := by
    funext x
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hZ_pos),
        Real.log_exp]
  rw [hlogfun]
  -- cfc (fun x => -β*x - log Z) H = (-β) • H - (log Z) • I.
  have hcont_lin : ContinuousOn (fun x : ℝ => (-β) * x) (spectrum ℝ H) := by fun_prop
  have hcont_const : ContinuousOn (fun _ : ℝ => Real.log Z) (spectrum ℝ H) :=
    continuousOn_const
  rw [cfc_sub (R := ℝ) (fun x : ℝ => (-β) * x) (fun _ : ℝ => Real.log Z) H
        hcont_lin hcont_const]
  -- cfc (fun x => -β*x) H = (-β) • H, via cfc_smul and cfc_id.
  have h_lin :
      cfc (fun x : ℝ => (-β) * x) H = ((-β : ℂ)) • H := by
    have hfun2 : (fun x : ℝ => (-β) * x) = (fun x : ℝ => (-β) • x) := by
      funext x; rw [smul_eq_mul]
    rw [hfun2, cfc_smul (R := ℝ) (S := ℝ) (-β) (fun x : ℝ => x) H
          (hf := continuousOn_id), cfc_id' ℝ H]
    rw [smul_R_C (-β) H]; push_cast; ring_nf
  -- cfc (fun _ => log Z) H = (log Z) • I.
  have h_const :
      cfc (fun _ : ℝ => Real.log Z) H
        = ((Real.log Z : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [cfc_const (R := ℝ) (Real.log Z) H hSA, algebraMap_real_matrix_eq_smul_one]
  rw [h_lin, h_const, hZ_def]

/-! ## 4. `Re Tr(ρ · log ρ_β) = -β⟨H⟩_ρ - log Z`. -/

/-- **The cross term.**  For any density matrix ρ,

      `Re Tr(ρ · log ρ_β)  =  -β · ⟨H⟩_ρ  -  log Z`.

    Direct from the log identity `log ρ_β = -βH - (log Z)·I`,
    `Tr(ρ·I) = Tr ρ = 1`, and `⟨H⟩_ρ = Re Tr(ρ·H)`. -/
theorem re_trace_mul_operatorLog_gibbs
    (ρ : ComplexDensityMatrix n)
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (hZ : 0 < partitionFunction β H) :
    (Matrix.trace (ρ.M * operatorLog (gibbsDensity β H hH hZ))).re
      = -β * ρ.expectation H - Real.log (partitionFunction β H) := by
  rw [operatorLog_gibbsDensity β H hH hZ]
  -- ρ.M * ((-β)•H - (log Z)•I) = (-β)•(ρ.M*H) - (log Z)•(ρ.M*I)
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
      Complex.sub_re, smul_eq_mul, smul_eq_mul, Complex.mul_re, Complex.mul_re,
      ρ.hTrace]
  -- Now ⟨H⟩ = Re Tr(ρ H), and (-β : ℂ).re = -β, .im = 0; Tr ρ = 1.
  simp only [Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
             Complex.one_re, Complex.one_im, neg_zero, zero_mul, mul_zero, sub_zero,
             mul_one]
  rfl

/-! ## 5. The free energy of the Gibbs state is `-T log Z`. -/

/-- **`F(ρ_β) = -T log Z`.**

    `S(ρ_β) = β⟨H⟩ + log Z` (from `re_trace_mul_operatorLog` applied to
    ρ_β itself together with the cross-term lemma at ρ = ρ_β), hence
    `F(ρ_β) = ⟨H⟩ - T(β⟨H⟩ + log Z) = -T log Z` (using `Tβ = 1`). -/
theorem freeEnergy_gibbs_eq
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (hZ : 0 < partitionFunction β H) (T : ℝ) (hTβ : T * β = 1) :
    freeEnergy (gibbsDensity β H hH hZ) H T
      = gibbsMinimum T (partitionFunction β H) := by
  -- S(σ) = β⟨H⟩_σ + log Z.
  have hS : vonNeumannEntropy (gibbsDensity β H hH hZ)
              = β * (gibbsDensity β H hH hZ).expectation H
                + Real.log (partitionFunction β H) := by
    have h1 : (Matrix.trace ((gibbsDensity β H hH hZ).M
                * operatorLog (gibbsDensity β H hH hZ))).re
                = -vonNeumannEntropy (gibbsDensity β H hH hZ) :=
      re_trace_mul_operatorLog (gibbsDensity β H hH hZ)
    have h2 : (Matrix.trace ((gibbsDensity β H hH hZ).M
                * operatorLog (gibbsDensity β H hH hZ))).re
                = -β * (gibbsDensity β H hH hZ).expectation H
                    - Real.log (partitionFunction β H) :=
      re_trace_mul_operatorLog_gibbs (gibbsDensity β H hH hZ) β H hH hZ
    linarith [h1, h2]
  -- F(σ) = ⟨H⟩ - T·S(σ) = ⟨H⟩ - T(β⟨H⟩ + log Z) = -T log Z.
  unfold freeEnergy gibbsMinimum
  rw [hS]
  have hTb : T * (β * (gibbsDensity β H hH hZ).expectation H)
              = (gibbsDensity β H hH hZ).expectation H := by
    rw [← mul_assoc, hTβ, one_mul]
  nlinarith [hTb]

/-! ## 6. THE GAP IDENTITY (★) — discharged as a real theorem. -/

/-- **The Gibbs gap identity (★).**

      `F(ρ) - F(ρ_β)  =  T · S(ρ ‖ ρ_β)`        (`T = 1/β`, i.e. `Tβ = 1`).

    This is exactly `FreeEnergy_RelEntropy_Identity_Target ρ ρ_β H T`,
    the previously-deferred named-`Prop` hole of `GibbsVariational.lean`,
    now PROVED for the specific Gibbs state `ρ_β = gibbsDensity β H`. -/
theorem gibbs_gap_identity
    (ρ : ComplexDensityMatrix n)
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (hZ : 0 < partitionFunction β H) (T : ℝ) (hTβ : T * β = 1) :
    FreeEnergy_RelEntropy_Identity_Target ρ (gibbsDensity β H hH hZ) H T := by
  unfold FreeEnergy_RelEntropy_Identity_Target
  set σ := gibbsDensity β H hH hZ with hσ_def
  -- S(ρ‖σ) = Re Tr(ρ log ρ) - Re Tr(ρ log σ) = -S(ρ) + β⟨H⟩ + log Z.
  have h_umeg :
      umegakiRelativeEntropy ρ σ
        = -vonNeumannEntropy ρ + β * ρ.expectation H
            + Real.log (partitionFunction β H) := by
    unfold umegakiRelativeEntropy
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re,
        re_trace_mul_operatorLog ρ]
    rw [hσ_def, re_trace_mul_operatorLog_gibbs ρ β H hH hZ]
    ring
  rw [h_umeg]
  -- F(σ) = -T log Z.
  have hFσ : freeEnergy σ H T = gibbsMinimum T (partitionFunction β H) := by
    rw [hσ_def]; exact freeEnergy_gibbs_eq β H hH hZ T hTβ
  rw [hFσ]
  unfold freeEnergy gibbsMinimum
  -- ⟨H⟩ - T·S(ρ) - (-T log Z) = T(-S(ρ) + β⟨H⟩ + log Z), using Tβ=1.
  have hTb : T * (β * ρ.expectation H) = ρ.expectation H := by
    rw [← mul_assoc, hTβ, one_mul]
  nlinarith [hTb]

/-! ## 7. THE FULL VARIATIONAL PRINCIPLE — unconditional (modulo PosDef). -/

/-- **Gibbs variational principle, real theorem.**

      `F(ρ_β)  ≤  F(ρ)`     for every positive-definite state ρ,
                            at non-negative temperature `T = 1/β`.

    Proof: the gap identity `gibbs_gap_identity` discharges the
    hypothesis of the already-proved Klein engine
    `gibbs_variational_of_gap`.  The only remaining genuine
    side-conditions are positive-definiteness of ρ (Klein requires it
    for faithfulness/finiteness) and `0 ≤ T`. -/
theorem gibbs_variational_principle
    (ρ : ComplexDensityMatrix n)
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (hZ : 0 < partitionFunction β H)
    (T : ℝ) (hTβ : T * β = 1) (hT : 0 ≤ T)
    (hρ_pos : ρ.M.PosDef) :
    freeEnergy (gibbsDensity β H hH hZ) H T ≤ freeEnergy ρ H T :=
  gibbs_variational_of_gap ρ (gibbsDensity β H hH hZ) H T hρ_pos
    (gibbsDensity_posDef β H hH hZ) hT
    (gibbs_gap_identity ρ β H hH hZ T hTβ)

/-- **Gibbs variational principle against the closed form.**

      `-T log Z  ≤  F(ρ)`,    i.e. `Gibbs_Variational_Target` holds. -/
theorem gibbs_variational_target
    (ρ : ComplexDensityMatrix n)
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (hZ : 0 < partitionFunction β H)
    (T : ℝ) (hTβ : T * β = 1) (hT : 0 ≤ T)
    (hρ_pos : ρ.M.PosDef) :
    Gibbs_Variational_Target ρ H T (partitionFunction β H) :=
  gibbs_variational_target_of_gap ρ (gibbsDensity β H hH hZ) H T
    (partitionFunction β H) hρ_pos (gibbsDensity_posDef β H hH hZ) hT
    (gibbs_gap_identity ρ β H hH hZ T hTβ)
    (freeEnergy_gibbs_eq β H hH hZ T hTβ)

/-! ## 7b. UNIQUENESS of the Gibbs minimiser (faithfulness). -/

/-- **Uniqueness of the Gibbs state.**  At positive temperature the free
    energy is minimised *uniquely* by the Gibbs state: if a
    positive-definite state `ρ` attains the Gibbs free energy, then it
    *is* the Gibbs state.

      `F(ρ) = F(ρ_β)  ⟹  ρ.M = (ρ_β).M`.

    Proof: the gap identity `F(ρ) − F(ρ_β) = T · S(ρ‖ρ_β)` turns
    `F(ρ) = F(ρ_β)` into `S(ρ‖ρ_β) = 0` (using `T ≠ 0`, which follows
    from `T·β = 1`); the strict equality case of Klein
    (`umegakiRelativeEntropy_eq_zero_imp`) then forces `ρ.M = (ρ_β).M`. -/
theorem gibbs_state_unique
    (ρ : ComplexDensityMatrix n)
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (hZ : 0 < partitionFunction β H)
    (T : ℝ) (hTβ : T * β = 1)
    (hρ_pos : ρ.M.PosDef)
    (hF : freeEnergy ρ H T = freeEnergy (gibbsDensity β H hH hZ) H T) :
    ρ.M = (gibbsDensity β H hH hZ).M := by
  set σ := gibbsDensity β H hH hZ with hσ_def
  -- T ≠ 0 from T·β = 1.
  have hT_ne : T ≠ 0 := by
    intro h; rw [h, zero_mul] at hTβ; exact zero_ne_one hTβ
  -- Gap identity: F(ρ) − F(σ) = T · S(ρ‖σ).
  have hgap : freeEnergy ρ H T - freeEnergy σ H T
                = T * umegakiRelativeEntropy ρ σ :=
    gibbs_gap_identity ρ β H hH hZ T hTβ
  -- F(ρ) = F(σ) ⟹ T · S = 0 ⟹ S = 0.
  rw [hF, sub_self] at hgap
  have hS_zero : umegakiRelativeEntropy ρ σ = 0 := by
    rcases mul_eq_zero.mp hgap.symm with hT0 | hS
    · exact absurd hT0 hT_ne
    · exact hS
  -- Faithfulness.
  exact UnifiedTheory.LayerB.KleinEquality.umegakiRelativeEntropy_eq_zero_imp
    ρ σ hρ_pos (gibbsDensity_posDef β H hH hZ) hS_zero

/-- **Variational characterisation of the Gibbs state, packaged as an
    iff.**  For a positive-definite state at positive temperature,
    attaining the minimal free energy is *equivalent* to being the
    Gibbs state. -/
theorem gibbs_free_energy_eq_iff
    (ρ : ComplexDensityMatrix n)
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (hZ : 0 < partitionFunction β H)
    (T : ℝ) (hTβ : T * β = 1)
    (hρ_pos : ρ.M.PosDef) :
    freeEnergy ρ H T = freeEnergy (gibbsDensity β H hH hZ) H T
      ↔ ρ.M = (gibbsDensity β H hH hZ).M := by
  constructor
  · exact gibbs_state_unique ρ β H hH hZ T hTβ hρ_pos
  · intro hM
    -- ρ.M = σ.M ⟹ same eigenvalues ⟹ same von Neumann entropy and
    -- same ⟨H⟩, hence same free energy.  We argue directly through the
    -- gap identity: S(ρ‖σ) = 0, so F(ρ) − F(σ) = T·0 = 0.
    set σ := gibbsDensity β H hH hZ with hσ_def
    have hgap : freeEnergy ρ H T - freeEnergy σ H T
                  = T * umegakiRelativeEntropy ρ σ :=
      gibbs_gap_identity ρ β H hH hZ T hTβ
    have hS_zero : umegakiRelativeEntropy ρ σ = 0 := by
      rw [(UnifiedTheory.LayerB.KleinEquality.umegakiRelativeEntropy_eq_zero_iff
            ρ σ hρ_pos (gibbsDensity_posDef β H hH hZ))]
      exact hM
    rw [hS_zero, mul_zero] at hgap
    linarith

/-! ## 8. Axiom audit. -/

#print axioms operatorLog_gibbsDensity
#print axioms gibbs_gap_identity
#print axioms gibbs_variational_principle
#print axioms gibbs_variational_target
#print axioms gibbs_state_unique
#print axioms gibbs_free_energy_eq_iff

end UnifiedTheory.LayerB.GibbsVariationalFull
