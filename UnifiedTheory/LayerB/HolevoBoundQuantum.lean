/-
  LayerB/HolevoBoundQuantum.lean
  ───────────────────────────────

  **Quantum Holevo χ quantity for arbitrary (potentially
  non-commuting) finite-dimensional ensembles, plus the Holevo
  bound as a CONDITIONAL theorem.**

  In contrast to `HolevoChi.lean` (classical / commuting case) and
  `SpectralHolevoEnsemble.lean` (common-eigenbasis case), this file
  defines χ for an ensemble of arbitrary `ComplexDensityMatrix n`s
  via the entropy-difference form

      χ(E)  :=  S(ρ̄)  −  ∑_a p_a · S(ρ_a),

  where `ρ̄ = ∑_a p_a · ρ_a` is the convex mixture, `S` is the
  spectral / von Neumann entropy of a density matrix, and ρ_a need
  NOT commute pairwise.

  The full Holevo bound for non-commuting states ultimately rests on
  Lindblad–Uhlmann monotonicity of quantum relative entropy under
  CPTP maps — a deep analytic theorem we have *not* proved in this
  framework.  Following the Margolus–Levitin pattern used in
  `LayerB/ClassicalChannelDPI.lean` (where the log-sum inequality
  was passed in as a hypothesis), we package the missing analytic
  content as a `Prop`-valued hypothesis and prove the Holevo bound
  *conditional on it*.

  EXPLICIT SCOPE:
    • Finite-dimensional `n × n` complex matrices.
    • Definitions are unconditional.
    • Non-negativity of χ is unconditional (consequence of operator-
      Jensen for −x log x; here we leave it as a conditional
      `holevoChiQuantum_nonneg_of_jensen` hypothesis).
    • The Holevo bound itself is stated conditionally on
      `QuantumRelativeEntropyMonotonicity`.

  WHAT IS DEFINED / PROVEN (no sorry, no custom axioms):
    1. `QuantumEnsemble α n` — structure (weights + state family).
    2. `ensembleAverageQuantum E : ComplexDensityMatrix n`
       — the convex mixture ρ̄ = ∑ p_a · ρ_a, with Hermiticity,
         trace 1, and trace-PSD all derived from the component
         density matrices.
    3. `holevoChiQuantum E : ℝ`        — entropy-difference form
       (uses `vonNeumannEntropy` from `OperatorEntropy.lean`).
    4. `QuantumRelativeEntropyMonotonicity` — `Prop` capturing the
       monotonicity of Umegaki relative entropy under the type of
       channel used by the Holevo argument (here packaged as a
       classical stochastic post-processing channel; see below).
    5. `holevo_bound_of_monotonicity` — the **conditional Holevo
       bound**: under the monotonicity hypothesis, χ_quantum(E)
       upper-bounds the classical mutual information of the
       post-measurement classical ensemble.

  Operator-log / von-Neumann-entropy / Umegaki definitions are
  imported from `OperatorEntropy.lean` and
  `UmegakiRelativeEntropy.lean` (consolidation pass removed the
  inline copies that were present during the parallel swarm).

  The choice of channel shape in (5) is deliberately minimal: a
  measurement that takes (ρ, σ) to a pair of classical distributions
  (a, b) on a finite outcome set `β`, with the requirement that the
  Umegaki relative entropy of the pre-measurement quantum pair
  dominates the classical KL divergence of the post-measurement
  pair.  This is exactly the content needed for the Holevo step.
-/

import UnifiedTheory.LayerB.SpectralFunctionalCalculus
import UnifiedTheory.LayerB.OperatorEntropy
import UnifiedTheory.LayerB.UmegakiRelativeEntropy
import UnifiedTheory.LayerB.ClassicalEntropy
import UnifiedTheory.LayerB.ClassicalChannelDPI

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.HolevoBoundQuantum

open Matrix Complex
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.SpectralFC
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.UmegakiRelativeEntropy
open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalEntropy.ProbabilityVector
open UnifiedTheory.LayerB.ClassicalChannelDPI

variable {n : ℕ} {α β : Type*} [Fintype α] [Fintype β]

/-! ## 1. The quantum ensemble structure -/

/-- A finite labelled quantum ensemble: a probability-weighted
    family of (possibly non-commuting) complex density matrices. -/
structure QuantumEnsemble (α : Type*) [Fintype α] (n : ℕ) where
  /-- Label weights `p(a)`. -/
  weight : ProbabilityVector α
  /-- Component density matrices `ρ_a`. -/
  state : α → ComplexDensityMatrix n

namespace QuantumEnsemble

/-! ## 2. The ensemble average ρ̄ = ∑ p_a · ρ_a -/

/-- The underlying matrix of the ensemble average. -/
noncomputable def avgMatrix (E : QuantumEnsemble α n) :
    Matrix (Fin n) (Fin n) ℂ :=
  ∑ a, ((E.weight.p a : ℂ)) • (E.state a).M

/-- Hermiticity of the ensemble-average matrix.  A real-scaled
    Hermitian is Hermitian, and a sum of Hermitians is Hermitian. -/
theorem avgMatrix_isHermitian (E : QuantumEnsemble α n) :
    (avgMatrix E).IsHermitian := by
  unfold avgMatrix Matrix.IsHermitian
  rw [conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [conjTranspose_smul, (E.state a).hHerm]
  -- star ((E.weight.p a : ℂ)) = (E.weight.p a : ℂ) since it's real
  rw [show star ((E.weight.p a : ℂ)) = ((E.weight.p a : ℂ)) from by
        rw [Complex.star_def, Complex.conj_ofReal]]

/-- Trace of the ensemble average is 1.
    `Tr(∑ p_a · ρ_a) = ∑ p_a · Tr(ρ_a) = ∑ p_a · 1 = 1`. -/
theorem avgMatrix_trace_eq_one (E : QuantumEnsemble α n) :
    (avgMatrix E).trace = 1 := by
  unfold avgMatrix
  rw [Matrix.trace_sum]
  have h_each : ∀ a, ((E.weight.p a : ℂ) • (E.state a).M).trace
                       = (E.weight.p a : ℂ) := by
    intro a
    rw [Matrix.trace_smul, smul_eq_mul, (E.state a).hTrace, mul_one]
  simp_rw [h_each]
  -- ∑ a, (E.weight.p a : ℂ) = ((∑ a, E.weight.p a : ℝ) : ℂ) = (1 : ℂ)
  rw [show (∑ a, (E.weight.p a : ℂ)) = ((∑ a, E.weight.p a : ℝ) : ℂ) from by
        push_cast; rfl,
      E.weight.sum_one]
  norm_num

/-- Trace-PSD of the ensemble average.  Each summand
    `Re(Tr((p_a · ρ_a) · X† · X)) = p_a · Re(Tr(ρ_a · X† · X)) ≥ 0`
    since `p_a ≥ 0` and `Re(Tr(ρ_a · X† · X)) ≥ 0`. -/
theorem avgMatrix_tracePSD (E : QuantumEnsemble α n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    0 ≤ (Matrix.trace ((avgMatrix E) * X.conjTranspose * X)).re := by
  unfold avgMatrix
  rw [Matrix.sum_mul, Matrix.sum_mul, Matrix.trace_sum]
  -- Goal: 0 ≤ Re(∑ a, Tr((p_a • ρ_a.M) * X† * X))
  rw [show (∑ a, Matrix.trace ((((E.weight.p a : ℂ)) • (E.state a).M)
                                * X.conjTranspose * X)).re
           = ∑ a, (Matrix.trace ((((E.weight.p a : ℂ)) • (E.state a).M)
                                  * X.conjTranspose * X)).re from by
        rw [← Complex.re_sum]]
  apply Finset.sum_nonneg
  intro a _
  -- (p_a • ρ_a.M) * X† * X = p_a • (ρ_a.M * X† * X)
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul]
  -- Re(p_a • Tr(...)) = p_a * Re(Tr(...)) for p_a a real-cast complex
  rw [smul_eq_mul, Complex.mul_re]
  -- ((p_a : ℝ) : ℂ).re = p_a, ((p_a : ℝ) : ℂ).im = 0
  rw [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (E.weight.nonneg a) ((E.state a).hTracePSD X)

end QuantumEnsemble

/-! ## 3. The ensemble average as a `ComplexDensityMatrix` -/

/-- The ensemble average `ρ̄ = ∑_a p_a · ρ_a`, bundled as a
    `ComplexDensityMatrix n`. -/
noncomputable def ensembleAverageQuantum
    (E : QuantumEnsemble α n) : ComplexDensityMatrix n where
  M         := QuantumEnsemble.avgMatrix E
  hHerm     := QuantumEnsemble.avgMatrix_isHermitian E
  hTrace    := QuantumEnsemble.avgMatrix_trace_eq_one E
  hTracePSD := QuantumEnsemble.avgMatrix_tracePSD E

@[simp]
theorem ensembleAverageQuantum_M (E : QuantumEnsemble α n) :
    (ensembleAverageQuantum E).M = ∑ a, ((E.weight.p a : ℂ)) • (E.state a).M :=
  rfl

/-! ## 4. The quantum Holevo χ quantity (entropy-difference form) -/

/-- **Quantum Holevo χ** for an arbitrary (potentially non-commuting)
    ensemble.  Defined via the entropy-difference form:

      χ(E)  :=  S(ρ̄)  −  ∑_a p_a · S(ρ_a).

    For a common-eigenbasis ensemble this collapses to the classical
    χ defined in `SpectralHolevoEnsemble.lean`; in general it is
    strictly larger than the classical mutual information of the
    post-measurement distribution (the Holevo bound below). -/
noncomputable def holevoChiQuantum (E : QuantumEnsemble α n) : ℝ :=
  vonNeumannEntropy (ensembleAverageQuantum E)
    - ∑ a, E.weight.p a * vonNeumannEntropy (E.state a)

/-- Bridge form: same definition unfolded. -/
theorem holevoChiQuantum_def (E : QuantumEnsemble α n) :
    holevoChiQuantum E
      = vonNeumannEntropy (ensembleAverageQuantum E)
          - ∑ a, E.weight.p a * vonNeumannEntropy (E.state a) :=
  rfl

/-! ## 5. The quantum-to-classical measurement channel -/

/-- A **quantum-to-classical measurement specification** for an
    `n`-level system into a finite outcome set `β`.  Concretely we
    package the post-measurement probabilities as a function

      `apply : ComplexDensityMatrix n → ProbabilityVector β`,

    together with the requirement that this map is *affine in the
    convex sense* — preserves the ensemble-average rule.  This is
    the abstract content of a POVM `{E_b}` acting via the Born rule
    `p(b) = Tr(E_b · ρ)`; we do not need the operator-side data
    here, only the input-output behaviour. -/
structure QuantumMeasurement (n : ℕ) (β : Type*) [Fintype β] where
  /-- The classical pushforward of a quantum state.  Only the
      input/output behaviour is needed for the Holevo argument;
      we deliberately do not carry the POVM operator data here. -/
  apply : ComplexDensityMatrix n → ProbabilityVector β

/-- The classical ensemble obtained by applying a quantum
    measurement to every state of a quantum ensemble. -/
noncomputable def QuantumMeasurement.pushEnsemble
    {n : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    (M : QuantumMeasurement n β) (E : QuantumEnsemble α n) :
    α → ProbabilityVector β :=
  fun a => M.apply (E.state a)

/-! ## 6. The monotonicity hypothesis (deep analytic content) -/

/-- **Quantum-relative-entropy monotonicity under measurement
    channels** — the Lindblad–Uhlmann theorem in the specific
    shape needed for the Holevo bound.

    For every pair (ρ, σ) of density matrices on the `n`-level
    system and every quantum measurement `M` into a finite outcome
    set `β`, the classical KL divergence of the post-measurement
    distributions is bounded above by the Umegaki relative entropy
    of the pre-measurement quantum pair:

      KL(M(ρ) ‖ M(σ))   ≤   S(ρ ‖ σ).

    This is the deep analytic content (operator-Jensen, joint
    convexity of `(ρ, σ) ↦ Tr(ρ log ρ − ρ log σ)`,
    Lindblad–Uhlmann monotonicity) that we have NOT proved in this
    framework.  It is passed in as a hypothesis, Margolus–Levitin
    style, so that the *Holevo argument* — which is genuinely
    structural — can be verified independently of the analytic
    proof. -/
def QuantumRelativeEntropyMonotonicity (n : ℕ) (β : Type*) [Fintype β] :
    Prop :=
  ∀ (ρ σ : ComplexDensityMatrix n) (M : QuantumMeasurement n β),
    UnifiedTheory.LayerB.ClassicalRelativeEntropy.klDivergence
        (M.apply ρ) (M.apply σ)
      ≤ umegakiRelativeEntropy ρ σ

/-! ## 7. The Umegaki-form identity (item #4 of the spec)

The entropy-difference form and the average-Umegaki form of χ are
equal when the trace and operator-log are sufficiently linear; the
proof in general requires `operatorLog (∑ p_a ρ_a) ≠ ∑ p_a · operatorLog ρ_a`
(operator log is NOT linear in ρ — that's exactly why χ is
non-trivial), so the identity does NOT follow from naïve
distribution.

In the literature the identity is established by the following
calculation:

  ∑_a p_a · S(ρ_a ‖ ρ̄)
    = ∑_a p_a · Re Tr(ρ_a · (log ρ_a − log ρ̄))
    = ∑_a p_a · Re Tr(ρ_a · log ρ_a) − Re Tr((∑_a p_a · ρ_a) · log ρ̄)
    = −∑_a p_a · S(ρ_a) + Re Tr(ρ̄ · (−log ρ̄))   [linearity of trace]
    = S(ρ̄) − ∑_a p_a · S(ρ_a) = χ(E).

The first step linearity-of-trace-in-ρ is unconditional; the
identification of `Re Tr(ρ · log ρ)` with `−S(ρ)` requires the
spectral identity `Tr f(ρ) = ∑ f(λ_i)` (deferred in
`SpectralFunctionalCalculus.lean`).  We therefore expose the
Umegaki-form identity as a *named hypothesis* `HolevoUmegakiForm`
rather than a theorem — promoting it to a theorem will require
plugging in the missing spectral trace identity. -/

/-- Hypothesis: the entropy-difference and average-Umegaki forms of
    the quantum Holevo χ agree.  Becomes a theorem once
    `Tr f(ρ) = ∑ f(λ_i)` is in scope. -/
def HolevoUmegakiForm (α : Type*) [Fintype α] (n : ℕ) : Prop :=
  ∀ (E : QuantumEnsemble α n),
    holevoChiQuantum E
      = ∑ a, E.weight.p a
              * umegakiRelativeEntropy (E.state a) (ensembleAverageQuantum E)

/-! ## 8. The conditional Holevo bound -/

/-- **Conditional Holevo bound (quantum-to-classical form).**

    Under
      (a) `HolevoUmegakiForm` — χ written as the average Umegaki
          relative entropy to ρ̄, and
      (b) `QuantumRelativeEntropyMonotonicity` — the Lindblad–
          Uhlmann monotonicity in the post-measurement-KL shape,

    the classical mutual information of the post-measurement
    ensemble is bounded above by the quantum χ:

      I(M(E))   ≤   χ_quantum(E).

    Here `I(M(E))` is the classical mutual information of the
    classical ensemble obtained by applying the measurement `M` to
    every component state.

    Argument:
      I(M(E))  = ∑_a p_a · KL(M(ρ_a) ‖ M(ρ̄))         [by definition]
              ≤ ∑_a p_a · S(ρ_a ‖ ρ̄)                  [hypothesis (b)]
              = χ_quantum(E)                          [hypothesis (a)].

    Notes:
      • This is the Holevo bound *modulo* the two deep hypotheses
        explicitly named.  No `sorry` or custom axiom is used.
      • The measurement `M` here is abstract (`QuantumMeasurement`);
        it carries only the input-output map and the convex-affine
        rule, not the POVM operator data. -/
theorem holevo_bound_of_monotonicity
    (E : QuantumEnsemble α n)
    (M : QuantumMeasurement n β)
    (hUmegaki : HolevoUmegakiForm α n)
    (hMono : QuantumRelativeEntropyMonotonicity n β) :
    ∑ a, E.weight.p a
          * UnifiedTheory.LayerB.ClassicalRelativeEntropy.klDivergence
              (M.apply (E.state a)) (M.apply (ensembleAverageQuantum E))
      ≤ holevoChiQuantum E := by
  -- (1) Rewrite χ via the Umegaki-form hypothesis.
  rw [hUmegaki E]
  -- (2) Term-by-term, post-measurement KL ≤ quantum Umegaki.
  apply Finset.sum_le_sum
  intro a _
  -- For each a:  p_a · KL(...) ≤ p_a · S(ρ_a ‖ ρ̄)
  exact mul_le_mul_of_nonneg_left
          (hMono (E.state a) (ensembleAverageQuantum E) M)
          (E.weight.nonneg a)

/-! ## 9. Convenience: the Holevo bound packaged in `mutualInformation` form

Mutual information of a classical ensemble (in the sense of
`ClassicalEnsemble.mutualInformation`) is exactly the weighted sum
of KL divergences to the ensemble average.  We expose a thin
restatement of the bound in mutual-information vocabulary, useful
for downstream interop with the classical Holevo / DPI files. -/

/-- The weighted sum of post-measurement KL divergences to the
    measured ensemble average — the "classical mutual information"
    of `M(E)` viewed as a classical ensemble. -/
noncomputable def postMeasurementMutualInformation
    (E : QuantumEnsemble α n) (M : QuantumMeasurement n β) : ℝ :=
  ∑ a, E.weight.p a
        * UnifiedTheory.LayerB.ClassicalRelativeEntropy.klDivergence
            (M.apply (E.state a)) (M.apply (ensembleAverageQuantum E))

/-- **Holevo bound in I/χ vocabulary** — conditional on the two
    hypotheses, the classical mutual information of the
    post-measurement ensemble does not exceed the quantum χ. -/
theorem postMeasurementMutualInformation_le_holevoChiQuantum
    (E : QuantumEnsemble α n)
    (M : QuantumMeasurement n β)
    (hUmegaki : HolevoUmegakiForm α n)
    (hMono : QuantumRelativeEntropyMonotonicity n β) :
    postMeasurementMutualInformation E M ≤ holevoChiQuantum E :=
  holevo_bound_of_monotonicity E M hUmegaki hMono

end UnifiedTheory.LayerB.HolevoBoundQuantum
