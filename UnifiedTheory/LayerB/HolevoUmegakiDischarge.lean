/-
  LayerB/HolevoUmegakiDischarge.lean
  ───────────────────────────────────

  **Discharges the `HolevoUmegakiForm` hypothesis** declared in
  `HolevoBoundQuantum.lean`.

  The two forms of the quantum Holevo χ quantity,

      χ(E)  =  S(ρ̄)  −  ∑_a p_a · S(ρ_a)             (entropy-difference)
            =  ∑_a p_a · S(ρ_a ‖ ρ̄)                   (average-Umegaki)

  agree as a *theorem*, not just a hypothesis.  The key analytic
  input that was deferred when `HolevoBoundQuantum.lean` was
  written is the identity

      Re Tr( ρ · log ρ )  =  −S(ρ),

  which lifts the cfc-style entropy `S(ρ) = −(operatorXLogX ρ).trace.re`
  (from `OperatorEntropy.vonNeumannEntropy_eq_neg_re_trace_xlogx`)
  to the matrix-product form `ρ · operatorLog ρ` via cfc
  multiplicativity:

      ρ · cfc log ρ  =  cfc id ρ · cfc log ρ
                     =  cfc (id · log) ρ            (by `cfc_mul`)
                     =  cfc (x · log x) ρ
                     =  operatorXLogX ρ.

  Combined with the linearity of the trace through the ensemble
  average ρ̄ = ∑ p_a · ρ_a, this gives the full Umegaki form by a
  clean algebraic calculation.

  WHAT IS PROVEN (no sorry, no custom axioms):
    1. `mul_operatorLog_eq_operatorXLogX`
                          — ρ · log ρ = (x · log x)(ρ).
    2. `re_trace_mul_operatorLog`
                          — Re Tr(ρ · log ρ) = −S(ρ).
    3. `trace_ensembleAverageQuantum_mul`
                          — Tr(ρ̄ · X) = ∑_a (p_a : ℂ) · Tr(ρ_a · X).
    4. `re_trace_ensembleAverageQuantum_mul`
                          — same after `.re`.
    5. `holevoUmegakiForm_holds`
                          — discharges `HolevoUmegakiForm α n`.

  After this file, `HolevoUmegakiForm` is no longer a hypothesis —
  the conditional Holevo bound in `HolevoBoundQuantum.lean`
  becomes a theorem conditional ONLY on
  `QuantumRelativeEntropyMonotonicity` (Lindblad-Uhlmann).
-/

import UnifiedTheory.LayerB.HolevoBoundQuantum
import UnifiedTheory.LayerB.OperatorEntropy
import UnifiedTheory.LayerB.UmegakiRelativeEntropy

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.HolevoUmegakiDischarge

open Matrix Complex
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.SpectralFC
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.UmegakiRelativeEntropy
open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.HolevoBoundQuantum

variable {n : ℕ} {α : Type*} [Fintype α]

/-! ## 1. The operator-multiplication identity: ρ · log ρ = (x · log x)(ρ) -/

/-- **CFC multiplicativity on `ρ`.**  For a Hermitian density
    matrix ρ, `ρ · log ρ` equals the operator `x · log x` applied to
    ρ via the continuous functional calculus.  Proof: every function
    on the (finite) spectrum is continuous there, so `cfc_mul`
    applies; then `cfc id = id` collapses the `id`-factor. -/
lemma mul_operatorLog_eq_operatorXLogX (ρ : ComplexDensityMatrix n) :
    ρ.M * operatorLog ρ = operatorXLogX ρ := by
  unfold operatorLog operatorXLogX cfcρ
  -- Goal: ρ.M * cfc Real.log ρ.M = cfc (fun x => x * Real.log x) ρ.M.
  have hSA : IsSelfAdjoint ρ.M := ρ.hHerm
  have h_id_cont : ContinuousOn (id : ℝ → ℝ) (spectrum ℝ ρ.M) :=
    continuous_id.continuousOn
  have h_log_cont : ContinuousOn Real.log (spectrum ℝ ρ.M) :=
    (Set.toFinite _).continuousOn _
  -- (id * Real.log) factors via `cfc_mul`; then `cfc id ρ.M = ρ.M`.
  have h_mul :
      cfc (fun x => x * Real.log x) ρ.M
        = cfc (id : ℝ → ℝ) ρ.M * cfc Real.log ρ.M :=
    cfc_mul (id : ℝ → ℝ) Real.log ρ.M h_id_cont h_log_cont
  rw [h_mul, cfc_id ℝ ρ.M]

/-- **Re Tr(ρ · log ρ) = −S(ρ).**  Combines
    `mul_operatorLog_eq_operatorXLogX` with
    `vonNeumannEntropy_eq_neg_re_trace_xlogx`. -/
theorem re_trace_mul_operatorLog (ρ : ComplexDensityMatrix n) :
    (Matrix.trace (ρ.M * operatorLog ρ)).re = -vonNeumannEntropy ρ := by
  rw [mul_operatorLog_eq_operatorXLogX,
      vonNeumannEntropy_eq_neg_re_trace_xlogx]
  ring

/-! ## 2. Linearity of the trace through the ensemble average -/

/-- **Trace is linear in the first argument over the ensemble
    average.**  `Tr(ρ̄ · X) = ∑_a (p_a : ℂ) · Tr(ρ_a · X)`. -/
lemma trace_ensembleAverageQuantum_mul
    (E : QuantumEnsemble α n) (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace ((ensembleAverageQuantum E).M * X)
      = ∑ a, ((E.weight.p a : ℝ) : ℂ)
              * Matrix.trace ((E.state a).M * X) := by
  rw [ensembleAverageQuantum_M, Finset.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Matrix.smul_mul, Matrix.trace_smul]
  rfl

/-- **Real-part specialisation of `trace_ensembleAverageQuantum_mul`.** -/
lemma re_trace_ensembleAverageQuantum_mul
    (E : QuantumEnsemble α n) (X : Matrix (Fin n) (Fin n) ℂ) :
    (Matrix.trace ((ensembleAverageQuantum E).M * X)).re
      = ∑ a, E.weight.p a
              * (Matrix.trace ((E.state a).M * X)).re := by
  rw [trace_ensembleAverageQuantum_mul, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-! ## 3. The HolevoUmegakiForm discharge -/

/-- **The HolevoUmegakiForm equivalence holds.**  The
    entropy-difference and average-Umegaki forms of the quantum
    Holevo χ agree:

      `S(ρ̄) − ∑ p_a · S(ρ_a)  =  ∑ p_a · S(ρ_a ‖ ρ̄)`. -/
theorem holevoUmegakiForm_holds (α : Type*) [Fintype α] (n : ℕ) :
    HolevoUmegakiForm α n := by
  intro E
  unfold holevoChiQuantum umegakiRelativeEntropy
  -- For brevity, name the ensemble average.
  set avg := ensembleAverageQuantum E with h_avg_def
  -- Per-summand: Re Tr(ρ_a · (log ρ_a − log avg))
  --            = -S(ρ_a) - Re Tr(ρ_a · log avg).
  have h_per_a : ∀ a,
      (Matrix.trace ((E.state a).M
                      * (operatorLog (E.state a) - operatorLog avg))).re
        = -vonNeumannEntropy (E.state a)
          - (Matrix.trace ((E.state a).M * operatorLog avg)).re := by
    intro a
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re,
        re_trace_mul_operatorLog]
  -- Apply per-summand identity, distribute over the sum.
  have h_sum_rewrite :
      ∑ a, E.weight.p a *
            (Matrix.trace ((E.state a).M
                            * (operatorLog (E.state a) - operatorLog avg))).re
        = -∑ a, E.weight.p a * vonNeumannEntropy (E.state a)
          - ∑ a, E.weight.p a
                 * (Matrix.trace ((E.state a).M * operatorLog avg)).re := by
    rw [show (∑ a, E.weight.p a *
              (Matrix.trace ((E.state a).M
                              * (operatorLog (E.state a) - operatorLog avg))).re)
            = ∑ a, (-(E.weight.p a * vonNeumannEntropy (E.state a))
                    - E.weight.p a
                        * (Matrix.trace ((E.state a).M * operatorLog avg)).re) from by
              apply Finset.sum_congr rfl; intro a _
              rw [h_per_a]; ring]
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [h_sum_rewrite]
  -- Collapse the second sum to a trace through `avg` via linearity.
  rw [← re_trace_ensembleAverageQuantum_mul]
  -- Re Tr(avg · log avg) = -S(avg).
  rw [re_trace_mul_operatorLog]
  -- Final: S(avg) − ∑ p_a S(ρ_a) = -∑ p_a S(ρ_a) − (-S(avg))
  ring

end UnifiedTheory.LayerB.HolevoUmegakiDischarge
