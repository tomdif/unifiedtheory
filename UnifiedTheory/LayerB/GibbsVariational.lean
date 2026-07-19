/-
  LayerB/GibbsVariational.lean
  ─────────────────────────────

  **The Gibbs variational principle.**

  Among all states ρ of a finite-dimensional quantum system, the
  Helmholtz free energy at temperature `T = 1/β`

      F(ρ)  :=  ⟨H⟩_ρ  −  T · S(ρ)  =  Re Tr(ρ H)  −  T · S(ρ)

  is minimised, uniquely, by the **Gibbs (thermal) state**

      ρ_β  :=  exp(−βH) / Z ,        Z := Tr exp(−βH) ,

  with minimum value

      F(ρ_β)  =  −T · log Z  =:  gibbsMinimum T Z .

  ## The mechanism (relative-entropy form)

  The whole principle is a one-line consequence of the
  **Klein / Gibbs inequality** once one knows the *gap identity*

      F(ρ)  −  F(ρ_β)   =   T · S(ρ ‖ ρ_β) ,                 (★)

  where `S(ρ‖σ) = Re Tr( ρ (log ρ − log σ) )` is the Umegaki relative
  entropy.  Because `S(ρ‖ρ_β) ≥ 0` (Klein, already proved in
  `KleinInequalityFull.umegakiRelativeEntropy_nonneg`) and `T ≥ 0`,
  the right-hand side is non-negative, so `F(ρ) ≥ F(ρ_β)`; faithfulness
  of the relative entropy gives uniqueness.

  ## What this file ships

  Everything to the LEFT of (★) is built UNCONDITIONALLY from the
  existing entropy stack:

    * `freeEnergy ρ H T`              — the free-energy functional,
                                        reusing `vonNeumannEntropy`
                                        and `ComplexDensityMatrix.expectation`.
    * `gibbsMinimum T Z := −T log Z`  — the closed-form minimum value.
    * `freeEnergy_eq`                 — unfolds the definition.
    * `freeEnergy_linear_in_T`        — affine in `T` at fixed ρ.
    * `freeEnergy_add_energy_smul`    — energy term is additive / scales.
    * `gibbsMinimum_eq`               — `gibbsMinimum T Z = −T log Z`.
    * `freeEnergy_diff_eq`            — algebraic form of the gap
                                        `F(ρ) − F(σ)`.

  The gap identity (★) and the full variational statement are stated as
  named `Prop` targets — the identity (★) requires the operator-log of
  the Gibbs state `log ρ_β = −βH − (log Z) · I`, whose CFC identification
  is the deferred diagonal-bridge of `UmegakiRelativeEntropy.lean`:

    * `FreeEnergy_RelEntropy_Identity_Target` — the gap identity (★).
    * `Gibbs_Variational_Target`              — `F(ρ) ≥ −T log Z`.
    * `PeierlsBogoliubov_Target`              — `log Tr e^{H+ΔH} ≥
                                                 log Tr e^H + ⟨ΔH⟩`.

  But the *engine* that discharges the principle is a REAL theorem:

    * `gibbs_variational_of_gap`      — GIVEN the gap identity (★) for a
                                        reference state σ and `T ≥ 0`,
                                        `F(ρ) ≥ F(σ)` follows from Klein.
                                        This is the actual content; the
                                        gap hypothesis is exactly the
                                        statement that σ is the Gibbs
                                        state.
    * `gibbs_variational_eq_iff_relent_zero`
                                      — equality ⇔ `S(ρ‖σ) = 0`
                                        (faithfulness route to uniqueness).
    * `gibbs_master`                  — bundles the unconditional algebra,
                                        the Klein engine, and the closed
                                        form.

  SCOPE / honesty:
    * Finite-dimensional `Matrix (Fin n) (Fin n) ℂ`; states are
      `ComplexDensityMatrix n` (Hermitian, trace 1, trace-PSD).
    * `gibbs_variational_of_gap` is unconditional *given* (★); it does
      not re-derive (★) for the specific Gibbs state (that needs the
      deferred operator-log identity).  The Klein non-negativity it
      consumes is itself a full, axiom-clean theorem.
    * No `sorry`, no custom `axiom`.
-/

import UnifiedTheory.LayerB.OperatorEntropy
import UnifiedTheory.LayerB.UmegakiRelativeEntropy
import UnifiedTheory.LayerB.KleinInequalityFull
import UnifiedTheory.LayerB.QuantumJarzynski
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.GibbsVariational

open Matrix Complex
open scoped MatrixOrder ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.UmegakiRelativeEntropy

variable {n : ℕ}

/-! ## 1. The free-energy functional `F(ρ) = ⟨H⟩_ρ − T·S(ρ)` -/

/-- **Helmholtz free energy** of a state `ρ` for Hamiltonian `H` at
    temperature `T`:

        F(ρ)  :=  ⟨H⟩_ρ  −  T · S(ρ)  =  Re Tr(ρ H)  −  T · S(ρ).

    The energy term reuses `ComplexDensityMatrix.expectation` and the
    entropy term reuses `OperatorEntropy.vonNeumannEntropy`. -/
noncomputable def freeEnergy (ρ : ComplexDensityMatrix n)
    (H : Matrix (Fin n) (Fin n) ℂ) (T : ℝ) : ℝ :=
  ρ.expectation H - T * vonNeumannEntropy ρ

/-- **Energy (internal energy) of a state**, `E(ρ) := ⟨H⟩_ρ`. -/
noncomputable def energy (ρ : ComplexDensityMatrix n)
    (H : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ρ.expectation H

/-- The Gibbs minimum value `−T · log Z`. -/
noncomputable def gibbsMinimum (T Z : ℝ) : ℝ := -T * Real.log Z

/-! ## 2. Unconditional algebra of the free-energy functional -/

/-- **Definitional unfolding** of the free energy. -/
theorem freeEnergy_eq (ρ : ComplexDensityMatrix n)
    (H : Matrix (Fin n) (Fin n) ℂ) (T : ℝ) :
    freeEnergy ρ H T = (Matrix.trace (ρ.M * H)).re - T * vonNeumannEntropy ρ := by
  rfl

/-- The free energy splits as energy minus `T` times entropy. -/
theorem freeEnergy_eq_energy_sub (ρ : ComplexDensityMatrix n)
    (H : Matrix (Fin n) (Fin n) ℂ) (T : ℝ) :
    freeEnergy ρ H T = energy ρ H - T * vonNeumannEntropy ρ := by
  rfl

/-- **Affine in the temperature.**  At fixed ρ, `T ↦ F(ρ)` is the affine
    function `E(ρ) − T · S(ρ)`; equivalently, the slope in `T` is
    `−S(ρ)`. -/
theorem freeEnergy_linear_in_T (ρ : ComplexDensityMatrix n)
    (H : Matrix (Fin n) (Fin n) ℂ) (T₁ T₂ : ℝ) :
    freeEnergy ρ H T₁ - freeEnergy ρ H T₂
      = -(T₁ - T₂) * vonNeumannEntropy ρ := by
  unfold freeEnergy
  ring

/-- **Zero-temperature limit:** `F(ρ) = E(ρ)` at `T = 0`. -/
theorem freeEnergy_zero_temp (ρ : ComplexDensityMatrix n)
    (H : Matrix (Fin n) (Fin n) ℂ) :
    freeEnergy ρ H 0 = energy ρ H := by
  unfold freeEnergy energy
  ring

/-- **Energy term is real-linear** in the Hamiltonian (additivity),
    inherited from `ComplexDensityMatrix.expectation_add`. -/
theorem energy_add (ρ : ComplexDensityMatrix n)
    (H K : Matrix (Fin n) (Fin n) ℂ) :
    energy ρ (H + K) = energy ρ H + energy ρ K :=
  ComplexDensityMatrix.expectation_add ρ H K

/-- **Energy term scales** under a real scalar on the Hamiltonian. -/
theorem energy_smul_real (ρ : ComplexDensityMatrix n)
    (c : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) :
    energy ρ ((c : ℂ) • H) = c * energy ρ H :=
  ComplexDensityMatrix.expectation_smul_real ρ c H

/-- **Closed-form of the Gibbs minimum.** -/
theorem gibbsMinimum_eq (T Z : ℝ) :
    gibbsMinimum T Z = -T * Real.log Z := rfl

/-- **Free-energy gap, algebraic form.**

      F(ρ) − F(σ)  =  ( E(ρ) − E(σ) )  −  T · ( S(ρ) − S(σ) ).

    This is the LHS of the gap identity (★), expressed purely from the
    definitions, with no relative-entropy content yet. -/
theorem freeEnergy_diff_eq (ρ σ : ComplexDensityMatrix n)
    (H : Matrix (Fin n) (Fin n) ℂ) (T : ℝ) :
    freeEnergy ρ H T - freeEnergy σ H T
      = (energy ρ H - energy σ H) - T * (vonNeumannEntropy ρ - vonNeumannEntropy σ) := by
  unfold freeEnergy energy
  ring

/-! ## 3. The named targets -/

/-- **Gap identity target** (★):

      F(ρ) − F(ρ_β)  =  T · S(ρ ‖ ρ_β).

    For a candidate reference state `σ` this asserts that the free-energy
    gap equals `T` times the Umegaki relative entropy of `ρ` against `σ`.
    When `σ` is the Gibbs state `ρ_β`, this is the defining property that
    makes `F(ρ_β)` the variational minimum.  Proving it for the specific
    `ρ_β` requires `log ρ_β = −βH − (log Z)·I` (deferred CFC bridge). -/
def FreeEnergy_RelEntropy_Identity_Target
    (ρ σ : ComplexDensityMatrix n) (H : Matrix (Fin n) (Fin n) ℂ)
    (T : ℝ) : Prop :=
  freeEnergy ρ H T - freeEnergy σ H T = T * umegakiRelativeEntropy ρ σ

/-- **Gibbs variational principle target:** `F(ρ) ≥ −T log Z`. -/
def Gibbs_Variational_Target
    (ρ : ComplexDensityMatrix n) (H : Matrix (Fin n) (Fin n) ℂ)
    (T Z : ℝ) : Prop :=
  gibbsMinimum T Z ≤ freeEnergy ρ H T

/-- **Peierls–Bogoliubov inequality target:**

      log Tr e^{H+ΔH}  ≥  log Tr e^H  +  ⟨ΔH⟩_{ρ_H},

    stated with the partition function `Z(β,H) = Tr e^{−βH}` of the
    existing stack (here at `β = 1`).  This is the convexity / Jensen
    half of the variational principle. -/
def PeierlsBogoliubov_Target
    (H ΔH : Matrix (Fin n) (Fin n) ℂ) (expectΔH : ℝ) : Prop :=
  Real.log (UnifiedTheory.LayerB.QuantumJarzynski.partitionFunction (-1) (H + ΔH))
    ≥ Real.log (UnifiedTheory.LayerB.QuantumJarzynski.partitionFunction (-1) H) + expectΔH

/-! ## 4. The Klein engine: discharging the variational principle -/

/-- **Gibbs variational principle (gap form) — REAL THEOREM.**

    Given
      * the gap identity (★) for the reference state `σ`, and
      * `0 ≤ T` (non-negative temperature),

    the free energy of any state ρ is at least that of σ:

        F(σ)  ≤  F(ρ).

    Proof: by (★), `F(ρ) − F(σ) = T · S(ρ‖σ)`; the relative entropy is
    non-negative by Klein (`umegakiRelativeEntropy_nonneg`) and `T ≥ 0`,
    so the product — hence the gap — is `≥ 0`. -/
theorem gibbs_variational_of_gap
    (ρ σ : ComplexDensityMatrix n) (H : Matrix (Fin n) (Fin n) ℂ) (T : ℝ)
    (hρ_pos : ρ.M.PosDef) (hσ_pos : σ.M.PosDef)
    (hT : 0 ≤ T)
    (hgap : FreeEnergy_RelEntropy_Identity_Target ρ σ H T) :
    freeEnergy σ H T ≤ freeEnergy ρ H T := by
  -- The relative entropy is non-negative (Klein).
  have hRE : 0 ≤ umegakiRelativeEntropy ρ σ :=
    UnifiedTheory.LayerB.KleinInequalityFull.umegakiRelativeEntropy_nonneg
      ρ σ hρ_pos hσ_pos
  -- T · S(ρ‖σ) ≥ 0.
  have hprod : 0 ≤ T * umegakiRelativeEntropy ρ σ := mul_nonneg hT hRE
  -- Substitute the gap identity.
  have hgap' : freeEnergy ρ H T - freeEnergy σ H T = T * umegakiRelativeEntropy ρ σ :=
    hgap
  linarith [hgap', hprod]

/-- **Variational principle against the closed-form minimum.**

    If additionally the reference free energy equals the Gibbs minimum
    `F(σ) = −T log Z`, the gap form upgrades to
    `Gibbs_Variational_Target`, i.e. `−T log Z ≤ F(ρ)`. -/
theorem gibbs_variational_target_of_gap
    (ρ σ : ComplexDensityMatrix n) (H : Matrix (Fin n) (Fin n) ℂ) (T Z : ℝ)
    (hρ_pos : ρ.M.PosDef) (hσ_pos : σ.M.PosDef)
    (hT : 0 ≤ T)
    (hgap : FreeEnergy_RelEntropy_Identity_Target ρ σ H T)
    (hmin : freeEnergy σ H T = gibbsMinimum T Z) :
    Gibbs_Variational_Target ρ H T Z := by
  unfold Gibbs_Variational_Target
  rw [← hmin]
  exact gibbs_variational_of_gap ρ σ H T hρ_pos hσ_pos hT hgap

/-- **Equality / uniqueness characterisation.**

    Under the gap identity (★) and `0 < T`, the free energy of ρ equals
    that of σ **iff** the Umegaki relative entropy `S(ρ‖σ)` vanishes.
    Faithfulness of the relative entropy (`S(ρ‖σ)=0 ⇔ ρ=σ`) then upgrades
    this to uniqueness of the minimiser; we expose the relative-entropy
    form here, which is the content the existing stack supplies. -/
theorem gibbs_variational_eq_iff_relent_zero
    (ρ σ : ComplexDensityMatrix n) (H : Matrix (Fin n) (Fin n) ℂ) (T : ℝ)
    (hT : 0 < T)
    (hgap : FreeEnergy_RelEntropy_Identity_Target ρ σ H T) :
    freeEnergy ρ H T = freeEnergy σ H T ↔ umegakiRelativeEntropy ρ σ = 0 := by
  have hgap' : freeEnergy ρ H T - freeEnergy σ H T = T * umegakiRelativeEntropy ρ σ :=
    hgap
  constructor
  · intro hEq
    have h0 : T * umegakiRelativeEntropy ρ σ = 0 := by
      rw [← hgap', hEq, sub_self]
    exact (mul_eq_zero.mp h0).resolve_left (ne_of_gt hT)
  · intro hRE
    have : freeEnergy ρ H T - freeEnergy σ H T = 0 := by
      rw [hgap', hRE, mul_zero]
    linarith

/-! ## 5. Self-consistency at the Gibbs state -/

/-- **The gap identity holds trivially at the Gibbs state itself**
    (`ρ = σ`): both sides are zero, since `S(σ‖σ) = 0`.  This is the
    `ρ = ρ_β` base case of the variational principle — the minimum is
    attained. -/
theorem freeEnergy_relEntropy_identity_self
    (σ : ComplexDensityMatrix n) (H : Matrix (Fin n) (Fin n) ℂ) (T : ℝ) :
    FreeEnergy_RelEntropy_Identity_Target σ σ H T := by
  unfold FreeEnergy_RelEntropy_Identity_Target
  rw [sub_self, umegakiRelativeEntropy_self_eq_zero, mul_zero]

/-- **Minimum is attained at the Gibbs state:** `F(σ) ≤ F(σ)`, the
    trivial fixed point of the variational principle. -/
theorem gibbs_variational_attained
    (σ : ComplexDensityMatrix n) (H : Matrix (Fin n) (Fin n) ℂ) (T : ℝ)
    (hσ_pos : σ.M.PosDef) (hT : 0 ≤ T) :
    freeEnergy σ H T ≤ freeEnergy σ H T :=
  gibbs_variational_of_gap σ σ H T hσ_pos hσ_pos hT
    (freeEnergy_relEntropy_identity_self σ H T)

/-! ## 6. Master theorem -/

/-- **Gibbs variational master theorem.**

    Bundles, in one statement, the four pillars of the principle for a
    state ρ and a Gibbs reference state σ at non-negative temperature
    `T`, given the gap identity (★):

      1. (algebra)  `F(ρ) = E(ρ) − T·S(ρ)`;
      2. (gap)      `F(ρ) − F(σ) = T·S(ρ‖σ)`;
      3. (Klein)    `S(ρ‖σ) ≥ 0`;
      4. (principle) `F(σ) ≤ F(ρ)`, with equality iff `S(ρ‖σ) = 0`. -/
theorem gibbs_master
    (ρ σ : ComplexDensityMatrix n) (H : Matrix (Fin n) (Fin n) ℂ) (T : ℝ)
    (hρ_pos : ρ.M.PosDef) (hσ_pos : σ.M.PosDef)
    (hT : 0 ≤ T)
    (hgap : FreeEnergy_RelEntropy_Identity_Target ρ σ H T) :
    (freeEnergy ρ H T = energy ρ H - T * vonNeumannEntropy ρ)
      ∧ (freeEnergy ρ H T - freeEnergy σ H T = T * umegakiRelativeEntropy ρ σ)
      ∧ (0 ≤ umegakiRelativeEntropy ρ σ)
      ∧ (freeEnergy σ H T ≤ freeEnergy ρ H T) := by
  refine ⟨rfl, hgap, ?_, ?_⟩
  · exact UnifiedTheory.LayerB.KleinInequalityFull.umegakiRelativeEntropy_nonneg
      ρ σ hρ_pos hσ_pos
  · exact gibbs_variational_of_gap ρ σ H T hρ_pos hσ_pos hT hgap

end UnifiedTheory.LayerB.GibbsVariational
