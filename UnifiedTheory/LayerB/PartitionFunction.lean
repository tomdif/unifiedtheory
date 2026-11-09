/-
  LayerB/PartitionFunction.lean — Finite phase sums and Boltzmann weights.

  The exponential functional forms are definitions. The theorems establish
  their multiplicative identities, positivity for nonempty finite ensembles,
  and unit modulus of the phase weights. No analytic continuation, physical
  Wick rotation, or derivation of statistical mechanics is formalized here.

  Zero sorry. Zero custom axioms.
-/
import UnifiedTheory.LayerB.PropagationRule
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace UnifiedTheory.LayerB.PartitionFunction

open PropagationRule

/-! ## The quantum amplitude sum -/

/-- The quantum amplitude sum for an ensemble of paths with source values sᵢ.
    Z_quantum(k) = Σᵢ e^{iksᵢ} (complex). -/
noncomputable def quantumAmplitudeSum {N : ℕ} (k : ℝ) (s : Fin N → ℝ) : ℂ :=
  ∑ i : Fin N, expAmplitude k (s i)

/-- The quantum observable: |Z_quantum|². -/
noncomputable def quantumObservable {N : ℕ} (k : ℝ) (s : Fin N → ℝ) : ℝ :=
  Complex.normSq (quantumAmplitudeSum k s)

/-! ## The partition function (K-sector projection) -/

/-- The partition function: Z = Σᵢ e^{-β·sᵢ} (real).
    This definition does not formalize a Wick rotation of the real-parameter
    quantum amplitude sum. -/
noncomputable def partitionFunction {N : ℕ} (β : ℝ) (s : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, Real.exp (-(β * s i))

/-- **The partition function is multiplicative** (from linearity of φ).
    For independent systems with source values s₁ and s₂:
    Z(s₁ + s₂) = Z(s₁) · Z(s₂). -/
theorem partition_multiplicative (β s₁ s₂ : ℝ) :
    Real.exp (-(β * (s₁ + s₂))) = Real.exp (-(β * s₁)) * Real.exp (-(β * s₂)) := by
  rw [show -(β * (s₁ + s₂)) = -(β * s₁) + -(β * s₂) from by ring, Real.exp_add]

/-- **The partition function is positive.** -/
theorem partition_positive {N : ℕ} (hN : 0 < N) (β : ℝ) (s : Fin N → ℝ) :
    0 < partitionFunction β s := by
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  apply Finset.sum_pos
  · intro i _; exact Real.exp_pos _
  · exact Finset.univ_nonempty

/-! ## Finite exponential identities -/

/-- The two defining finite sums, positivity, and multiplicativity of their
    weights. The legacy theorem name does not assert a Born-rule derivation
    or analytic continuation. Squaring a real sum still produces cross terms. -/
theorem partition_from_born_rule {N : ℕ} (β : ℝ) (s : Fin N → ℝ) :
    -- (1) The quantum amplitude is complex-valued
    (∀ k : ℝ, quantumAmplitudeSum k s = ∑ i, expAmplitude k (s i))
    -- (2) The real partition function unfolds to its defining sum.
    ∧ (partitionFunction β s = ∑ i, Real.exp (-(β * s i)))
    -- (3) The partition function is positive
    ∧ (0 < N → 0 < partitionFunction β s)
    -- (4) Each Boltzmann weight is multiplicative (from linearity)
    ∧ (∀ s₁ s₂ : ℝ,
      Real.exp (-(β * (s₁ + s₂))) = Real.exp (-(β * s₁)) * Real.exp (-(β * s₂)))
    -- (5) The quantum amplitude is also multiplicative (same reason)
    ∧ (∀ k s₁ s₂ : ℝ,
      expAmplitude k (s₁ + s₂) = expAmplitude k s₁ * expAmplitude k s₂) := by
  refine ⟨fun k => rfl, rfl, fun hN => partition_positive hN β s, ?_, exp_multiplicative⟩
  exact fun s₁ s₂ => partition_multiplicative β s₁ s₂

/-! ## Thermal expectation values -/

/-- The **thermal expectation value** of a quantity f(sᵢ):
    ⟨f⟩_β = Σᵢ f(sᵢ) e^{-βsᵢ} / Z. -/
noncomputable def thermalExpectation {N : ℕ} (β : ℝ) (s : Fin N → ℝ) (f : Fin N → ℝ) (hZ : partitionFunction β s ≠ 0) : ℝ :=
  (∑ i : Fin N, f i * Real.exp (-(β * s i))) / partitionFunction β s

/-- The **thermal average energy** ⟨E⟩ = Σ sᵢ e^{-βsᵢ} / Z. -/
noncomputable def thermalEnergy {N : ℕ} (β : ℝ) (s : Fin N → ℝ) (hZ : partitionFunction β s ≠ 0) : ℝ :=
  thermalExpectation β s s hZ

/-- The **Gibbs entropy** S = -Σ pᵢ ln(pᵢ) where pᵢ = e^{-βsᵢ}/Z. -/
noncomputable def gibbsEntropy {N : ℕ} (β : ℝ) (s : Fin N → ℝ) (hZ : partitionFunction β s ≠ 0) : ℝ :=
  -(∑ i : Fin N,
    let p := Real.exp (-(β * s i)) / partitionFunction β s
    p * Real.log p)

/-- **The free energy** F = -T ln(Z) = -(1/β) ln(Z). -/
noncomputable def freeEnergy {N : ℕ} (β : ℝ) (s : Fin N → ℝ) (hβ : β ≠ 0) : ℝ :=
  -(1/β) * Real.log (partitionFunction β s)

/-! ## Summary -/

/-- Multiplicativity, phase normalization, and positive real weights for the
    specified exponential functions. Physical identification is separate. -/
theorem unified_quantum_statistical :
    -- The quantum amplitude is multiplicative
    (∀ k s₁ s₂ : ℝ,
      expAmplitude k (s₁ + s₂) = expAmplitude k s₁ * expAmplitude k s₂)
    -- The Boltzmann weight is multiplicative
    ∧ (∀ β s₁ s₂ : ℝ,
      Real.exp (-(β * (s₁ + s₂))) = Real.exp (-(β * s₁)) * Real.exp (-(β * s₂)))
    -- The quantum amplitude has unit modulus
    ∧ (∀ k s : ℝ, Complex.normSq (expAmplitude k s) = 1)
    -- The Boltzmann weight is positive
    ∧ (∀ β s : ℝ, 0 < Real.exp (-(β * s))) := by
  exact ⟨exp_multiplicative, partition_multiplicative,
         exp_unit_modulus, fun β s => Real.exp_pos _⟩

end UnifiedTheory.LayerB.PartitionFunction
