/- Vanishing TOTAL clock-localized upper spectral mass on the same
reachable-state frozen windows whose lengths exceed the square-root scale.
All thresholds share one sequence; the vacuum coupling must be positive. -/
import UnifiedTheory.Audit.KFCausalClockFloorLocalizedSpectrum
import UnifiedTheory.Audit.KFCausalClockFloorSelectedDissipation

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorSelectedSpectrum
noncomputable section
open Filter MeasureTheory
open scoped Topology
open KFCausalClockFloorAveragedFormTransport (FormSpace embedding energyOutput)
open KFCausalClockFloorLocalizedSpectrum (orbitObservation)
open KFCausalClockFloorFastTimeEnergy (physicalTime)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "J" => embedding ε hε h hne hb m g k 0
local notation "O" => energyOutput ε hε h hne hb m g k 0
local notation "C" => KFCausalClockFloorQuantumVelocityOutput.classicalOutput ε hε
local notation "B" => orbitObservation ε hε h hne
local notation "aState" => KFCausalClockFloorFrozenComparison.actual ε hε h hne hb m g k
local notation "F" => KFCausalClockFloorFrozenFastEvolution.evolution ε hε h hne hb m g k
local notation "P" => KFCausalClockFloorMovingFreeze.actual ε hε h hne hb m g k
local notation "Q" => KFCausalClockFloorMovingFreeze.frozen ε hε h hne hb m g k
local notation "D" => KFCausalClockFloorDefectOperator.defectOperator ε hε
local notation "rho" => KFCausalClockFloorResidualDefect.residual ε hε h hne hb m g k
local notation "det" => KFCausalClockFloorMovingDissipation.detector ε hε h hne hb m g k

theorem frozen_integral_bound (hk : 0 < k) (U L R : ℝ) (hL : 0 ≤ L) (v : V) :
    (∫ t in 0..L, ‖B R (J (F U t v))‖^2) ≤
      (128*ε*Real.exp (-R)/k)*(∫ t in 0..L, det (F U t v)) := by
  have hf := KFCausalClockFloorFrozenFastEvolution.evolution_continuous ε hε h hne hb m g k U v
  have ho := (O).continuous.comp hf
  have hd : Continuous (fun t => det (F U t v)) :=
    (Complex.continuous_re.comp (ho.inner (((C).compLpL 2 _).continuous.comp ho))).neg.div_const 2
  have hc := (((B R).continuous.comp ((J).continuous.comp hf)).norm).pow 2
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_mono_on hL (hc.intervalIntegrable 0 L)
    ((continuous_const.mul hd).intervalIntegrable 0 L)
    (fun t _ => KFCausalClockFloorLocalizedSpectrum.form_bound ε hε h hne hb m g k R hk _)

theorem sequence_total_limit (hk : 0 < k) (a R : ℝ) (v : V) (U L : ℕ → ℝ)
    (hpos : ∀ n, 0 < U n ∧ 0 ≤ L n) (hU : Tendsto U atTop atTop)
    (herr : Tendsto (fun n => P a (U n) (L n) (J v)-Q a (U n) (L n) (J v)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t in 0..L n, ‖B R (J (F (U n) t (aState a (U n) v)))‖^2)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun n => intervalIntegral.integral_nonneg_of_forall (hpos n).2
    (fun _ => sq_nonneg _))
    (fun n => frozen_integral_bound ε hε h hne hb m g k hk (U n) (L n) R (hpos n).2 _)
  simpa only [mul_zero] using
    (KFCausalClockFloorSelectedDissipation.sequence_total_limit ε hε h hne hb m g k
      a v U L hpos hU herr).const_mul (128*ε*Real.exp (-R)/k)

theorem exists_windows (hk : 0 < k) (a : ℝ) (ha : 0 < a) (v : V) :
    ∃ U L : ℕ → ℝ, (∀ n, 0 < U n ∧ 0 < L n) ∧ Tendsto U atTop atTop ∧ Tendsto L atTop atTop ∧
      Tendsto (fun n => (L n)^2/U n) atTop atTop ∧
      Tendsto (fun n => L n/U n) atTop (𝓝 0) ∧
      TendstoUniformlyOn (fun n r => P a (U n) (r*L n) (J v)-Q a (U n) (r*L n) (J v))
        (fun _ => 0) atTop (Set.Icc 0 1) ∧
      TendstoUniformlyOn (fun n r => ‖D (Q a (U n) (r*L n) (J v))‖)
        (fun _ => rho (physicalTime a) (J v)) atTop (Set.Icc 0 1) ∧
      Tendsto (fun n => ∫ t in 0..L n, det (F (U n) t (aState a (U n) v))) atTop (𝓝 0) ∧
      (∀ R : ℝ, Tendsto (fun n => ∫ t in 0..L n,
        ‖B R (J (F (U n) t (aState a (U n) v)))‖^2) atTop (𝓝 0)) := by
  apply Exists.imp _ (KFCausalClockFloorSelectedDissipation.exists_supercritical_windows
    ε hε h hne hb m g k a ha v)
  intro U hx
  apply Exists.imp _ hx
  intro L hp
  refine ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2.1,hp.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.1,hp.2.2.2.2.2.2.2,?_⟩
  intro R
  apply sequence_total_limit ε hε h hne hb m g k hk a R v U L
    (fun n => ⟨(hp.1 n).1,(hp.1 n).2.le⟩) hp.2.1
  simpa only [one_mul] using hp.2.2.2.2.2.1.tendsto_at
    (show (1:ℝ) ∈ Set.Icc 0 1 from ⟨zero_le_one,le_rfl⟩)

#print axioms frozen_integral_bound
#print axioms sequence_total_limit
#print axioms exists_windows
end
end UnifiedTheory.Audit.KFCausalClockFloorSelectedSpectrum
