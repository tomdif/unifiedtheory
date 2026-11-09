/-
  Exact first-rank test of the literal four-dimensional action-phase ansatz.

  The unsmeared integer bracket is computed from actual open intervals of
  the native causal-order type.  At the one-event parent its antichain and
  chain children have action gaps one and zero.  Thus an amplitude of the
  literal form rho * exp(i * phi * gap), with real rho, is real on the chain.
  Coherent sum one and Born sum one force this two-child law to be
  deterministic, for every real phi.  Nonnegative deterministic witnesses
  exist for every phi, so these local constraints do not select the phase.

  This excludes identifying the existing branching canonical harmonic law
  with that literal ansatz.  It does not exclude branching at later parents,
  a normalized raw-weight ansatz with a complex partition denominator, a
  modified action, or an additional parent-dependent complex phase.
  No continuum curvature coefficient or Einstein equation is asserted.
-/

import UnifiedTheory.Audit.KFCausalSetHarmonicBornRankOneAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBDG4DPhaseRankOne

noncomputable section
open scoped BigOperators
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetTransitionEdges
open UnifiedTheory.Audit.KFCausalSetChiralGrowth
open UnifiedTheory.Audit.KFCausalSetMultiplicityCorrectedRunning
open UnifiedTheory.Audit.KFCausalBornNormalizationTransfer
open UnifiedTheory.Audit.KFCausalSetHarmonicBornRankOneAudit

/-- Number of events strictly between the two endpoints. -/
def openIntervalCount {n : ℕ} (P : CardinalCausalOrder n) (x y : Fin n) : ℕ :=
  (Finset.univ.filter fun z =>
    x ≠ z ∧ z ≠ y ∧ P.rel x z = true ∧ P.rel z y = true).card

/-- Number of strict causal pairs with exactly k intervening events. -/
def intervalLayerCount {n : ℕ} (P : CardinalCausalOrder n) (k : ℕ) : ℕ :=
  (Finset.univ.filter fun xy : Fin n × Fin n =>
    xy.1 ≠ xy.2 ∧ P.rel xy.1 xy.2 = true ∧
      openIntervalCount P xy.1 xy.2 = k).card

/-- The integer bracket used by four_d_action_normalization.py.  The external
dimensionful coefficient and phase per integer unit are not fixed here. -/
def bracket {n : ℕ} (P : CardinalCausalOrder n) : ℤ :=
  n - intervalLayerCount P 0 + 9 * intervalLayerCount P 1 -
    16 * intervalLayerCount P 2 + 8 * intervalLayerCount P 3

/-- The two native extensions of the one-event causal order. -/
def rankOneChild (member : Bool) : CardinalCausalOrder 2 :=
  precursorOneElementExtension (cardinalCausalAntichain 1)
    (rankOneCausalPast member)

def rankOneGap (member : Bool) : ℤ :=
  bracket (rankOneChild member) - bracket (cardinalCausalAntichain 1)

theorem rankOne_brackets :
    bracket (cardinalCausalAntichain 1) = 1 ∧
      bracket (rankOneChild false) = 2 ∧
      bracket (rankOneChild true) = 1 := by
  decide

theorem rankOne_gaps : rankOneGap false = 1 ∧ rankOneGap true = 0 := by
  dsimp only [rankOneGap]
  rw [rankOne_brackets.1, rankOne_brackets.2.1, rankOne_brackets.2.2]
  norm_num

/-- Literal action-phase amplitudes, before any complex partition division. -/
def rankOneAmplitude (phi : ℝ) (rho : Bool → ℝ) (member : Bool) : ℂ :=
  (rho member : ℂ) *
    Complex.exp (Complex.I * (phi : ℂ) * (rankOneGap member : ℂ))

theorem rankOne_amplitudes (phi : ℝ) (rho : Bool → ℝ) :
    rankOneAmplitude phi rho false =
        (rho false : ℂ) * Complex.exp (Complex.I * (phi : ℂ)) ∧
      rankOneAmplitude phi rho true = (rho true : ℂ) := by
  simp [rankOneAmplitude, rankOne_gaps.1, rankOne_gaps.2]

private theorem binary_real_deterministic (z : ℂ) (r : ℝ)
    (hcoherent : z + (r : ℂ) = 1)
    (hborn : Complex.normSq z + Complex.normSq (r : ℂ) = 1) :
    (z = 0 ∧ r = 1) ∨ (z = 1 ∧ r = 0) := by
  have hz : z = 1 - (r : ℂ) := eq_sub_iff_add_eq.mpr hcoherent
  have hr : r * (r - 1) = 0 := by
    rw [hz] at hborn
    norm_num [Complex.normSq_apply] at hborn
    nlinarith
  rcases mul_eq_zero.mp hr with hr | hr
  · right
    exact ⟨by simpa [hr] using hz, hr⟩
  · left
    have hr1 : r = 1 := sub_eq_zero.mp hr
    exact ⟨by simpa [hr1] using hz, hr1⟩

/-- Both conservation laws force a deterministic first causal choice, at
every real phase.  Real prefactors suffice; positivity is not needed. -/
theorem rankOne_biNormalized_deterministic (phi : ℝ) (rho : Bool → ℝ)
    (hcoherent : ∑ member, rankOneAmplitude phi rho member = 1)
    (hborn : ∑ member, Complex.normSq (rankOneAmplitude phi rho member) = 1) :
    (rankOneAmplitude phi rho false = 0 ∧ rankOneAmplitude phi rho true = 1) ∨
      (rankOneAmplitude phi rho false = 1 ∧ rankOneAmplitude phi rho true = 0) := by
  have hc : rankOneAmplitude phi rho false + (rho true : ℂ) = 1 := by
    simpa only [Fintype.sum_bool, rankOne_amplitudes phi rho |>.2, add_comm]
      using hcoherent
  have hb : Complex.normSq (rankOneAmplitude phi rho false) +
      Complex.normSq (rho true : ℂ) = 1 := by
    simpa only [Fintype.sum_bool, rankOne_amplitudes phi rho |>.2, add_comm]
      using hborn
  rcases binary_real_deterministic _ _ hc hb with h | h
  · exact Or.inl ⟨h.1, by rw [(rankOne_amplitudes phi rho).2, h.2]; norm_num⟩
  · exact Or.inr ⟨h.1, by rw [(rankOne_amplitudes phi rho).2, h.2]; norm_num⟩

theorem rankOne_no_fullSupport (phi : ℝ) (rho : Bool → ℝ)
    (hcoherent : ∑ member, rankOneAmplitude phi rho member = 1)
    (hborn : ∑ member, Complex.normSq (rankOneAmplitude phi rho member) = 1) :
    ¬ ∀ member, rankOneAmplitude phi rho member ≠ 0 := by
  intro hfull
  rcases rankOne_biNormalized_deterministic phi rho hcoherent hborn with h | h
  · exact hfull false h.1
  · exact hfull true h.2

/-- Every real phase has an exact nonnegative local witness.  This theorem
does not provide an all-rank branching extension of that witness. -/
theorem every_phase_has_local_witness (phi : ℝ) :
    ∃ rho : Bool → ℝ,
      (∀ member, 0 ≤ rho member) ∧
      (∑ member, rankOneAmplitude phi rho member) = 1 ∧
      (∑ member, Complex.normSq (rankOneAmplitude phi rho member)) = 1 := by
  refine ⟨fun member => if member then 1 else 0, ?_, ?_, ?_⟩
  · intro member
    cases member <;> norm_num
  · simp [rankOneAmplitude, rankOne_gaps.1, rankOne_gaps.2]
  · simp [rankOneAmplitude, rankOne_gaps.2]

/-- The actual harmonic chain amplitude cannot have the zero-gap action
phase form, regardless of phase or real prefactor. -/
theorem harmonic_timid_not_literal_action_phase (chirality : Fin 2)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch 1)
    (phi : ℝ) (rho : Bool → ℝ) :
    (harmonicCriticalCausalSetGrowthLaw chirality).transition
        1 pathPrefix rankOneTimidChild ≠ rankOneAmplitude phi rho true := by
  rw [harmonicCritical_rankOne_timid_closed, (rankOne_amplitudes phi rho).2]
  intro he
  have hi := congrArg Complex.im he
  fin_cases chirality <;>
    norm_num [UnifiedTheory.Audit.KFCausalSetBellCausality.chiralMaximalEventPhase]
      at hi

/-- The canonical Born correction preserves the branching rank-one law;
therefore it also cannot be the literal unsmeared action-phase law. -/
theorem canonicalHarmonic_not_literal_action_phase (chirality : Fin 2)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch 1)
    (phi : ℝ) (rho : Bool → ℝ) :
    ¬ ∀ member,
      (canonicalHarmonicBornNormalizedGrowthLaw chirality).transition 1 pathPrefix
          (causalTransitionTarget (cardinalCausalAntichain 1) (rankOneCausalPast member)) =
        rankOneAmplitude phi rho member := by
  intro h
  have ht := h true
  rw [canonicalHarmonicBorn_rankOne_transition_eq_raw] at ht
  exact harmonic_timid_not_literal_action_phase chirality pathPrefix phi rho ht

/-- Complex partition normalization does bypass the literal-ansatz
obstruction: the raw weights one and the opposite quarter turn give exactly
the canonical harmonic pair after division by their sum. -/
theorem complex_normalization_recovers_harmonic (chirality : Fin 2)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch 1) :
    (canonicalHarmonicBornNormalizedGrowthLaw chirality).transition
          1 pathPrefix rankOneTimidChild =
        1 / (1 - KFCausalSetBellCausality.chiralMaximalEventPhase chirality) ∧
      (canonicalHarmonicBornNormalizedGrowthLaw chirality).transition
          1 pathPrefix rankOneGregariousChild =
        -KFCausalSetBellCausality.chiralMaximalEventPhase chirality /
          (1 - KFCausalSetBellCausality.chiralMaximalEventPhase chirality) := by
  simp only [canonicalHarmonicBorn_rankOne_transition_eq_raw,
    harmonicCritical_rankOne_timid_closed, harmonicCritical_rankOne_gregarious_closed]
  fin_cases chirality <;>
    norm_num [KFCausalSetBellCausality.chiralMaximalEventPhase,
      Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq_apply]

/-- The bypass is genuinely complex normalization, so it does not preserve
real prefactors in the original literal action-phase expression. -/
theorem normalizing_partition_nonreal (chirality : Fin 2) :
    (1 - KFCausalSetBellCausality.chiralMaximalEventPhase chirality).im ≠ 0 := by
  fin_cases chirality <;>
    norm_num [KFCausalSetBellCausality.chiralMaximalEventPhase]

#print axioms rankOne_brackets
#print axioms rankOne_gaps
#print axioms rankOne_amplitudes
#print axioms rankOne_biNormalized_deterministic
#print axioms rankOne_no_fullSupport
#print axioms every_phase_has_local_witness
#print axioms harmonic_timid_not_literal_action_phase
#print axioms canonicalHarmonic_not_literal_action_phase
#print axioms complex_normalization_recovers_harmonic
#print axioms normalizing_partition_nonreal

end
end UnifiedTheory.Audit.KFCausalBDG4DPhaseRankOne
