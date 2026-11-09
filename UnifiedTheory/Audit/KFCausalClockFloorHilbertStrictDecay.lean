/- Strict clock-expectation decrease for every nonzero Hilbert state.
Finite-time spectral exposure rules out equality without differentiating
the state or assigning it an energy or momentum domain. Strict decrease
does not identify the infinite-time limit with zero. -/
import UnifiedTheory.Audit.KFCausalClockFloorHilbertObservationBudget
import UnifiedTheory.Audit.KFCausalClockFloorSpectralFaithfulness

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorHilbertStrictDecay
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorAveragedEvolution (evolution)
open KFCausalClockFloorFrozenClockLoss (expectation)
open KFCausalClockFloorLocalizedSpectrum (orbitObservation)
open KFCausalClockFloorHilbertObservationBudget
open KFCausalClockFloorDefectOperator (defectOperator defectOperator_coe)

theorem expectation_density (ε : ℝ) (hε : 0 < ε) (f v : Hilbert)
    (he : (fun x => ‖f x‖) =ᵐ[volume] fun x => ‖v x‖) :
    expectation ε hε f = expectation ε hε v := by
  unfold expectation
  rw [KFCausalClockFloorInitialDriftPairing.real_multiplier_pairing
    volume _ _ _ (defectOperator_coe ε hε f),
    KFCausalClockFloorInitialDriftPairing.real_multiplier_pairing
      volume _ _ _ (defectOperator_coe ε hε v)]
  apply integral_congr_ae
  filter_upwards [he] with x hx
  rw [hx]

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "U" => evolution ε hε h hne hb m g k
local notation "B" => orbitObservation ε hε h hne
local notation "X" => expectation ε hε

theorem positive_exposure (s a b : ℝ) (hab : a < b) (f : Hilbert) (hf : f ≠ 0) :
    ∃ n : ℕ, 0 < exposure ε hε h hne hb m g k (-(n:ℝ)) s a b f := by
  have hu : U s a f ≠ 0 := by
    intro hz
    exact hf ((U s a).injective (hz.trans (map_zero (U s a)).symm))
  obtain ⟨n,hn⟩ := KFCausalClockFloorSpectralFaithfulness.exists_positive_observation
    ε hε h hne (U s a f) hu
  refine ⟨n,?_⟩
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f := fun _ : ℝ => (0:ℝ))
    (g := fun t => Real.exp (2*t)*‖B (-(n:ℝ)) (U s t f)‖^2)
    hab continuous_const.continuousOn
    (integrand_continuous ε hε h hne hb m g k (-(n:ℝ)) s f).continuousOn
    (fun t _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
    ⟨a,⟨le_rfl,hab.le⟩,mul_pos (Real.exp_pos _) hn⟩
  simpa only [intervalIntegral.integral_zero] using hi

theorem expectation_strictAnti (hk : 0 < k) (s : ℝ) (f : Hilbert) (hf : f ≠ 0) :
    StrictAnti (fun t => X (U s t f)) := by
  intro a b hab
  obtain ⟨n,hn⟩ := positive_exposure ε hε h hne hb m g k s a b hab f hf
  have hx := hn.trans_le (hilbert_budget ε hε h hne hb m g k hk (-(n:ℝ)) s a b hab.le f)
  have hc : 0 < bound ε k (-(n:ℝ)) := by unfold bound; positivity
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hc).mp hx)

theorem density_ne (hk : 0 < k) (s a b : ℝ) (hab : a < b) (f : Hilbert) (hf : f ≠ 0) :
    ¬ ((fun x => ‖U s a f x‖) =ᵐ[volume] fun x => ‖U s b f x‖) := by
  intro he
  have hx := expectation_density ε hε (U s a f) (U s b f) he
  exact (expectation_strictAnti ε hε h hne hb m g k hk s f hf hab).ne hx.symm

theorem no_chart_phase_return (hk : 0 < k) (s a b r : ℝ) (hab : a < b)
    (f : Hilbert) (hf : f ≠ 0) :
    U s b f ≠ KFCausalClockFloorChartModulation.modulation ε r (U s a f) := by
  intro he
  apply density_ne ε hε h hne hb m g k hk s a b hab f hf
  rw [he]
  exact (KFCausalClockFloorChartModulation.modulation_density ε r (U s a f)).symm

theorem expectation_limit (hk : 0 < k) (s : ℝ) (f : Hilbert) (hf : f ≠ 0) :
    ∃ ℓ : ℝ, 0 ≤ ℓ ∧ (∀ t, ℓ < X (U s t f)) ∧
      Tendsto (fun t => X (U s t f)) atTop (𝓝 ℓ) := by
  let F : ℝ → ℝ := fun t => X (U s t f)
  have hs : StrictAnti F := expectation_strictAnti ε hε h hne hb m g k hk s f hf
  have h0 (t : ℝ) : 0 ≤ F t :=
    KFCausalClockFloorStrictQuantumLimit.expectation_nonnegative ε hε (U s t f)
  have hbd : BddBelow (Set.range F) := ⟨0,by rintro _ ⟨t,rfl⟩; exact h0 t⟩
  refine ⟨⨅ t, F t,le_ciInf h0,?_,tendsto_atTop_ciInf hs.antitone hbd⟩
  intro t
  exact (ciInf_le hbd (t+1)).trans_lt (hs (by linarith : t < t+1))

#print axioms expectation_density
#print axioms positive_exposure
#print axioms expectation_strictAnti
#print axioms density_ne
#print axioms no_chart_phase_return
#print axioms expectation_limit
end
end UnifiedTheory.Audit.KFCausalClockFloorHilbertStrictDecay
