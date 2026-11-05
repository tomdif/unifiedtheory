/- One-sided actual Wilson tuning. A proved high-coefficient tail supplies
the upper endpoint, so a positive lower endpoint suffices for selection.
That positive endpoint is explicit and remains unproved on a physical
ultraviolet trajectory; this file does not certify such a trajectory. -/
import UnifiedTheory.Clay.YangMills.ProposedCouplingTail
import UnifiedTheory.Clay.YangMills.WilsonReflectedTuning

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.ProposedCouplingSelection
noncomputable section
open Filter ContinuumControl PeriodicLattice4 WilsonCrossingKernel
open CellReflectionCovariance ReflectedWilsonRenormalization ProposedCouplingTail
open AffineWilsonSmearing WilsonReflectedTensor
open scoped Topology

variable (d : Type*) [Fintype d] [Nonempty d] [DecidableEq d]
  (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (N : ℕ) [NeZero N]

theorem signal_continuous (L a : ℝ) (plane : Plane)
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (Z : ℂ) (f : CorrelationTest 1) :
    Continuous (signal d G N L a plane ρ Z f) := by
  have hχ := UnitaryCharacterObservables.unitaryCharacter_continuous ρ hρ
  have hψ := realPart_continuous G (unitaryCharacter ρ) hχ
  have haff : Continuous (affineCharacter (realPartCharacter G (unitaryCharacter ρ))
      (Fintype.card d) (((a ^ 4)⁻¹ : ℝ) : ℂ)) :=
    continuous_const.mul (hψ.sub continuous_const)
  exact continuous_const.mul (Complex.continuous_re.comp
    (WilsonReflectedTuning.reflectedForm_continuous G N a plane _ haff _ hχ
      (Fintype.card d) f f))

/-- The small endpoint is constructed, not an additional bracket premise.
The only fluctuation premise is a positive actual signal at `start`. -/
theorem exists_tuned_above (L a : ℝ) (ha : 0 < a) (plane : Plane)
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (Z : ℂ) (f : CorrelationTest 1) (start target : ℝ) (ht : 0 < target)
    (hs : target < signal d G N L a plane ρ Z f start) :
    ∃ beta, start < beta ∧ signal d G N L a plane ρ Z f beta = target := by
  obtain ⟨stop, hstop, hsmall⟩ :=
    exists_small_endpoint d G N L a ha plane ρ hρ Z f start target ht
  have he : signal d G N L a plane ρ Z f stop < target :=
    (le_abs_self _).trans_lt hsmall
  obtain ⟨beta, hb, heq⟩ := intermediate_value_Icc' hstop.le
    (signal_continuous d G N L a plane ρ hρ Z f).continuousOn ⟨he.le, hs.le⟩
  refine ⟨beta, lt_of_le_of_ne hb.1 ?_, heq⟩
  intro h
  subst beta
  exact hs.ne' heq

/-- A uniform positive endpoint along a diverging proposed branch would
supply an actual tuned sequence. It is not derived from a variance chosen
normalization, and the endpoint hypothesis is not asserted to hold. -/
theorem positive_endpoint_trajectory (period : ℕ → ℕ) [∀ k, NeZero (period k)]
    (L a : ℕ → ℝ) (ha : ∀ k, 0 < a k) (plane : Plane)
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (Z : ℕ → ℂ) (f : CorrelationTest 1) (start : ℕ → ℝ)
    (hstart : Tendsto start atTop atTop) (target : ℝ) (ht : 0 < target)
    (hs : ∀ k, target < signal d G (period k) (L k) (a k) plane ρ (Z k) f (start k)) :
    ∃ beta : ℕ → ℝ, (∀ k, start k < beta k) ∧
      (∀ k, signal d G (period k) (L k) (a k) plane ρ (Z k) f (beta k) = target) ∧
      Tendsto beta atTop atTop := by
  have he (k : ℕ) := exists_tuned_above d G (period k) (L k) (a k) (ha k)
    plane ρ hρ (Z k) f (start k) target ht (hs k)
  choose beta hb hsignal using he
  exact ⟨beta, hb, hsignal, tendsto_atTop_mono (fun k => (hb k).le) hstart⟩

end
end UnifiedTheory.Clay.YangMills.ProposedCouplingSelection
