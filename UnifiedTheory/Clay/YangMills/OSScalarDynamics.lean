/- Actual OS time evolution of the subsequential bare scalar Wilson hierarchy.
This constructs strongly continuous positive symmetric contractions on its
reflected Hilbert quotient. Nontriviality, renormalized Yang--Mills fields,
a self-adjoint unbounded generator, and a mass gap are not asserted. -/
import UnifiedTheory.Clay.YangMills.OSPositiveTimeKernel
import UnifiedTheory.Clay.YangMills.OSStrongContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.OSScalarDynamics
noncomputable section
open MeasureTheory ContinuumControl PeriodicLattice4 PeriodicCellSampling
open OSPositiveTimeKernel PositiveKernelForm KernelHilbertCompletion
open ExplicitLatticeScales WilsonReflectedTensor
open scoped NNReal

/-- The operator acts on the actual positive-time reflected-kernel Hilbert
completion and implements forward translations of every admissible test. -/
structure Evolution (W : Hierarchy) (plane : Plane) (hp : Positive W plane) where
  operator : ℝ≥0 → Hilbert (positiveKernel W plane hp) →L[ℂ] Hilbert (positiveKernel W plane hp)
  canonical_action : ∀ t i, operator t (canonical (positiveKernel W plane hp) i) =
    canonical (positiveKernel W plane hp) (shift t i)
  zero : ∀ v, operator 0 v = v
  add : ∀ s t v, operator s (operator t v) = operator (s+t) v
  contraction : ∀ t v, ‖operator t v‖ ≤ ‖v‖
  symmetric : ∀ t v w, inner ℂ (operator t v) w = inner ℂ v (operator t w)
  positive : ∀ t v, 0 ≤ (inner ℂ v (operator t v)).re
  strongly_continuous : ∀ v, Continuous (fun t => operator t v)

/-- All operator properties, including null-space descent and contraction,
are derived from reflection positivity, stationarity, and the bare bound. -/
def evolution (W : Hierarchy) (plane : Plane) (B : ℝ≥0)
    (hp : Positive W plane) (ht : Stationary W) (hb : Bounded W B) :
    Evolution W plane hp where
  operator := OSKernelShift.operator _ (shiftData W plane B hp ht hb)
  canonical_action := OSKernelShift.operator_canonical _ _
  zero := OSKernelShift.operator_zero _ _
  add := OSKernelShift.operator_add _ _
  contraction := OSKernelShift.operator_contraction _ _
  symmetric := OSStrongContinuity.operator_symmetric _ _
  positive := OSStrongContinuity.operator_positive _ _
  strongly_continuous := OSStrongContinuity.operator_continuous _ _
    (kernel_shift_continuous W plane)

theorem null_descent (W : Hierarchy) (plane : Plane) (B : ℝ≥0)
    (hp : Positive W plane) (ht : Stationary W) (hb : Bounded W B)
    (t : ℝ≥0) (x : Formal (positiveKernel W plane hp))
    (hx : embed (positiveKernel W plane hp) x = 0) :
    embed (positiveKernel W plane hp)
      (OSKernelShift.formal _ (shiftData W plane B hp ht hb) t x) = 0 :=
  OSKernelShift.formal_null _ _ t x hx

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- No stationary or positive limiting hierarchy is assumed here: the same
actual vanishing-mesh Wilson subsequence supplies it and its OS evolution. -/
theorem exists_candidate_dynamics (plane : Plane) (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : RegulatedGauge.ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re)
    (B : ℝ≥0) (hB : ∀ g, ‖χ g‖ ≤ B) (beta offset : ℕ → ℝ) :
    ∃ (W : Hierarchy) (phi : ℕ → ℕ), StrictMono phi ∧
      WeakConvergence
        (fun k => realHierarchy G (2 * halfPeriod (phi k)) (spacing (phi k))
          plane χ hcχ B hB (beta (phi k)) (offset (phi k))) W ∧
      (∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x) ∧
      Bounded W B ∧ Stationary W ∧
      ∃ hp : Positive W plane, Nonempty (Evolution W plane hp) := by
  obtain ⟨W,phi,hphi,hW,hn,hb,ht,hp⟩ :=
    BareSchwingerCandidate.exists_candidate G plane χ hcχ hχ hinv B hB beta offset
  let hp' : Positive W plane := positive_of_finite_form W plane hp
  exact ⟨W,phi,hphi,hW,hn,hb,ht,hp',⟨evolution W plane B hp' ht hb⟩⟩

end
end UnifiedTheory.Clay.YangMills.OSScalarDynamics
