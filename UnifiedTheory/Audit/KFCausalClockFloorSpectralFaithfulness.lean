/- The countable family of localized upper spectral observations
separates every physical Hilbert state. No momentum domain is needed. -/
import UnifiedTheory.Audit.KFCausalClockFloorStaticNegativeEscape

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorSpectralFaithfulness
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorLocalizedSpectrum (observation orbitObservation)
open KFCausalClockFloorWeightedClockControl (weighted)
open KFCausalClockFloorFourierCoordinates (coupledFourier)
open KFCausalClockFloorFourierMultiplier (symbol)
open KFCausalClockFloorExponential (symbol_measurable)
open KFCausalClockFloorOrbitVacuumGraph (physicalOrbit)
open KFCausalBornLocalization (mask mask_coe)

theorem observation_separates (ε : ℝ) (hε : 0 < ε) (h : ℝ) (f : Hilbert)
    (hf : ∀ n : ℕ, observation ε hε h (-(n:ℝ)) f = 0) : f = 0 := by
  let q := coupledFourier ε hε (weighted ε hε f)
  have hz (n : ℕ) : mask volume {p | -(n:ℝ) ≤ symbol h p}
      (measurableSet_le measurable_const (symbol_measurable h)) q = 0 := hf n
  have hq : q = 0 := by
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [ae_all_iff.mpr (fun n : ℕ =>
      (mask_coe volume {p | -(n:ℝ) ≤ symbol h p}
        (measurableSet_le measurable_const (symbol_measurable h)) q).symm.trans
          (Lp.eq_zero_iff_ae_eq_zero.mp (hz n)))] with p hp
    obtain ⟨n,hn⟩ := exists_nat_gt (-symbol h p)
    have hm : p ∈ {p | -(n:ℝ) ≤ symbol h p} := by
      change -(n:ℝ) ≤ symbol h p
      linarith
    simpa only [Set.indicator_of_mem hm] using hp n
  have hw : weighted ε hε f = 0 :=
    (coupledFourier ε hε).injective (hq.trans (map_zero (coupledFourier ε hε)).symm)
  exact (KFCausalClockFloorStaticNegativeEscape.weighted_injective ε hε)
    (hw.trans (map_zero (weighted ε hε)).symm)

theorem orbit_separates (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
    (f : Hilbert) (hf : ∀ n : ℕ, orbitObservation ε hε h hne (-(n:ℝ)) f = 0) :
    f = 0 := by
  have hz : physicalOrbit h hne f = 0 := by
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    have ha (n : ℕ) : ∀ᵐ θ ∂KFCausalUnitIntervalOrbit.angleMeasure,
        observation ε hε h (-(n:ℝ)) (physicalOrbit h hne f θ) = 0 := by
      have he : (observation ε hε h (-(n:ℝ))).compLp (physicalOrbit h hne f) = 0 := hf n
      filter_upwards [(observation ε hε h (-(n:ℝ))).coeFn_compLp (physicalOrbit h hne f),
        Lp.eq_zero_iff_ae_eq_zero.mp he] with θ hθ hz
      exact hθ.symm.trans hz
    filter_upwards [ae_all_iff.mpr ha] with θ hθ
    exact observation_separates ε hε h _ hθ
  exact (physicalOrbit h hne).injective (hz.trans (map_zero (physicalOrbit h hne)).symm)

theorem exists_positive_observation (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
    (f : Hilbert) (hf : f ≠ 0) :
    ∃ n : ℕ, 0 < ‖orbitObservation ε hε h hne (-(n:ℝ)) f‖^2 := by
  by_contra! hn
  apply hf
  apply orbit_separates ε hε h hne f
  intro n
  have he : ‖orbitObservation ε hε h hne (-(n:ℝ)) f‖^2 = 0 :=
    le_antisymm (hn n) (sq_nonneg _)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp he)

#print axioms observation_separates
#print axioms orbit_separates
#print axioms exists_positive_observation
end
end UnifiedTheory.Audit.KFCausalClockFloorSpectralFaithfulness
