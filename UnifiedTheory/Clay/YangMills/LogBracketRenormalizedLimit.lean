/- Logarithmic bracket selection for the actual affine Wilson hierarchy.
Only tuned level-set points require common all-order bounds. The selected
coefficient inherits the bracket's logarithmic slope by a proved squeeze.
Actual endpoint signs and common estimates remain analytic inputs; this does
not identify a physical slope or construct an unconditional continuum theory. -/
import UnifiedTheory.Clay.YangMills.TunedRenormalizedLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.LogBracketRenormalizedLimit
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4 LocalFields WilsonCrossingKernel
open CellReflectionCovariance ReflectedWilsonRenormalization UnitaryCharacterObservables
open WilsonReflectedTensor CellSpacetimeTranslation SchwartzTranslations
open KernelHilbertCompletion UltrafilterHierarchyCompactness RenormalizedFullOSLimit
open TunedRenormalizedLimit
open scoped Topology NNReal

/-- A vanishing positive lattice spacing supplies a diverging logarithmic clock. -/
theorem log_inverse_tendsto (a : ℕ → ℝ) (ha : ∀ k, 0 < a k)
    (ha0 : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun k => Real.log (1 / a k)) atTop atTop := by
  have hw : Tendsto a atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨ha0, Eventually.of_forall ha⟩
  simpa only [Function.comp_apply, one_div] using
    Real.tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero.comp hw)

/-- Positive asymptotic slope forces the lower bracket to diverge. -/
theorem lower_tendsto (ell lo : ℕ → ℝ) (hell : Tendsto ell atTop atTop)
    (b : ℝ) (hb : 0 < b) (hlo : Tendsto (fun k => lo k / ell k) atTop (𝓝 b)) :
    Tendsto lo atTop atTop := by
  have he : (fun k => (b / 2) * ell k) ≤ᶠ[atTop] lo := by
    filter_upwards [hell.eventually_gt_atTop 0,
      hlo.eventually (lt_mem_nhds (show b / 2 < b by linarith))] with k hk hs
    exact le_of_lt ((lt_div_iff₀ hk).mp hs)
  exact tendsto_atTop_mono' atTop he
    ((tendsto_const_mul_atTop_of_pos (show 0 < b / 2 by positivity)).mpr hell)

/-- Every selection inside an asymptotically narrowing bracket has its slope. -/
theorem selected_slope (ell lo hi beta : ℕ → ℝ) (hell : Tendsto ell atTop atTop)
    (b : ℝ) (hlo : Tendsto (fun k => lo k / ell k) atTop (𝓝 b))
    (hhi : Tendsto (fun k => hi k / ell k) atTop (𝓝 b))
    (hbeta : ∀ k, beta k ∈ Set.Icc (lo k) (hi k)) :
    Tendsto (fun k => beta k / ell k) atTop (𝓝 b) := by
  apply hlo.squeeze' hhi
  · filter_upwards [hell.eventually_ge_atTop 0] with k hk
    exact div_le_div_of_nonneg_right (hbeta k).1 hk
  · filter_upwards [hell.eventually_ge_atTop 0] with k hk
    exact div_le_div_of_nonneg_right (hbeta k).2 hk

variable (d : Type*) [Fintype d] [Nonempty d] [DecidableEq d]
  (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- The same original-action hierarchy is selected within the supplied logarithmic
bracket. Uniform estimates are required only at its tuned level-set points,
not above the lower endpoint or even everywhere in the bracket. An interval-wide
bound specializes by ignoring the signal-equality argument of `hbound`. -/
theorem exists_log_bracket_candidate
    (period : ℕ → ℕ) [∀ k, NeZero (period k)] (a : ℕ → ℝ) (plane : Plane)
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (ha : ∀ k, 0 < a k) (ha0 : Tendsto a atTop (𝓝 0))
    (hlarge : Tendsto (fun k => (period k : ℝ) * a k) atTop atTop)
    (f : CorrelationTest 1) (hf : OSPositiveTimeKernel.Supported 1 f)
    (lo hi : ℕ → ℝ) (horder : ∀ k, lo k ≤ hi k)
    (b : ℝ) (hb : 0 < b)
    (hlo : Tendsto (fun k => lo k / Real.log (1 / a k)) atTop (𝓝 b))
    (hhi : Tendsto (fun k => hi k / Real.log (1 / a k)) atTop (𝓝 b))
    (target : ℝ) (htarget : 0 < target) (center : ℕ → ℝ → ℝ)
    (hsignal_lo : ∀ k, target < ProposedCouplingTail.signal d G (2 * period k)
      1 (a k) plane ρ 1 f (lo k))
    (hsignal_hi : ∀ k, ProposedCouplingTail.signal d G (2 * period k)
      1 (a k) plane ρ 1 f (hi k) < target)
    (p : ∀ m, Seminorm ℂ (CorrelationTest m)) (hp : ∀ m, Continuous (p m))
    (hbound : ∀ (k : ℕ) (beta : ℝ), beta ∈ Set.Icc (lo k) (hi k) →
      ProposedCouplingTail.signal d G (2 * period k) 1 (a k) plane ρ 1 f beta = target →
      ∀ m (g : CorrelationTest m),
        ‖(proposedSequence d G period a plane ρ hρ center (fun _ => beta) k).correlation m g‖
          ≤ p m g) :
    ∃ (beta : ℕ → ℝ) (W : Hierarchy),
      (∀ k, beta k ∈ Set.Icc (lo k) (hi k)) ∧ Tendsto beta atTop atTop ∧
      Tendsto (fun k => beta k / Real.log (1 / a k)) atTop (𝓝 b) ∧
      (∀ k, ProposedCouplingTail.signal d G (2 * period k) 1 (a k) plane ρ 1 f
        (beta k) = target) ∧
      WeakAlong (regulatorUltrafilter : Filter ℕ)
        (proposedSequence d G period a plane ρ hρ center beta) W ∧
      (∀ m g, ‖W.correlation m g‖ ≤ p m g) ∧
      (∀ g : CorrelationTest 0, W.correlation 0 g = ∫ x, g x) ∧
      (∀ (m : ℕ) (v : Spacetime) (g : CorrelationTest m),
        W.correlation m (translationCLM (displacement m v) g) = W.correlation m g) ∧
      ∃ hfull : FullPositiveTimeReflection.Positive W plane,
        ‖fullVacuum W plane hfull‖ = 1 ∧
        ∃ w : Hilbert (FullPositiveTimeReflection.positiveKernel W plane hfull),
          w ≠ 0 ∧ inner ℂ (fullVacuum W plane hfull) w = 0 ∧ target ≤ ‖w‖ ^ 2 := by
  have hell := log_inverse_tendsto a ha ha0
  have hstart := lower_tendsto (fun k => Real.log (1 / a k)) lo hell b hb hlo
  have hbracket (k : ℕ) : target ∈ Set.uIcc
      (ProposedCouplingTail.signal d G (2 * period k) 1 (a k) plane ρ 1 f (lo k))
      (ProposedCouplingTail.signal d G (2 * period k) 1 (a k) plane ρ 1 f (hi k)) := by
    rw [Set.uIcc_of_ge ((hsignal_hi k).le.trans (hsignal_lo k).le)]
    exact ⟨(hsignal_hi k).le, (hsignal_lo k).le⟩
  obtain ⟨beta, hbeta, hs, ht⟩ := WilsonReflectedTuning.bracket_trajectory
    (fun k => ProposedCouplingTail.signal d G (2 * period k) 1 (a k) plane ρ 1 f)
    (fun k => ProposedCouplingSelection.signal_continuous d G (2 * period k)
      1 (a k) plane ρ hρ 1 f) lo hi target horder hbracket hstart
  have hslope := selected_slope (fun k => Real.log (1 / a k)) lo hi beta hell b hlo hhi hbeta
  have hbounds (k m : ℕ) (g : CorrelationTest m) :
      ‖(proposedSequence d G period a plane ρ hρ center beta k).correlation m g‖ ≤ p m g :=
    hbound k (beta k) (hbeta k) (hs k) m g
  have hfloor : ∀ᶠ k in atTop, target ≤ (((a k) ^ 4)⁻¹) ^ 2 *
      (reflectedForm G (2 * period k) (a k) plane (realPartCharacter G (unitaryCharacter ρ))
        (unitaryCharacter ρ) (beta k) (Fintype.card d) f f).re := by
    exact Eventually.of_forall (fun k => by
      rw [← signal_one_eq_scaled d G (2 * period k) (a k) plane ρ hρ]
      exact (hs k).ge)
  obtain ⟨W, hW, hWb, hn, htrans, hfull, hvac, w, hw, ho, hwn⟩ :=
    RenormalizedFullOSLimit.exists_affine_candidate G period a plane (unitaryCharacter ρ)
      (unitaryCharacter_continuous ρ hρ) (unitaryCharacter_class ρ)
      (PeriodicPlaquetteReflection.unitaryCharacter_inverse_re G ρ) beta (fun _ => Fintype.card d)
      ha ha0 hlarge (Fintype.card d) (fun g => unitary_trace_bound (ρ g))
      (fun k => center k (beta k)) (fun k => ((a k) ^ 4)⁻¹) p hp hbounds f hf
      target htarget hfloor
  exact ⟨beta, W, hbeta, ht, hslope, hs, hW, hWb, hn, htrans, hfull, hvac, w, hw, ho, hwn⟩

end
end UnifiedTheory.Clay.YangMills.LogBracketRenormalizedLimit
