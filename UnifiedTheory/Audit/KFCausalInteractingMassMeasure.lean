/- A probability mass law constructed from the actual interacting resolvent.
The seed is normalized after applying R, so it lies in the actual Hamiltonian
domain. The law has a positive mass threshold and recovers every resolvent
moment of that seed. Calling this a physical particle mass is not a theorem. -/
import UnifiedTheory.Audit.KFCausalInteractingCorrelationReconstruction
import UnifiedTheory.Audit.KFCausalResolventMassMeasure

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalInteractingMassMeasure
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalInteractingCorrelationReconstruction

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hpos : 0 < h)
  (hb : |h| ≤ Real.pi*ε/3) (m g k t : ℝ)
local notation "hw" => KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hpos.ne' hw m g k t
local notation "R" => physicalResolvent ε hε h hpos hb m g k t

theorem resolvent_selfAdjoint : IsSelfAdjoint R :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (resolvent_symmetric ε hε h hpos hb m g k t)

theorem resolvent_nonnegative : 0 ≤ R := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive R).mpr
  refine ⟨resolvent_symmetric ε hε h hpos hb m g k t, ?_⟩
  intro f
  exact KFCausalPositiveResolventBounds.resolvent_positive H R 1 zero_lt_one
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hpos.ne' hw m g k t 1 zero_lt_one)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_selfAdjoint ε hε h hpos.ne' hw m g k t)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hpos.ne' hw m g k t) f

theorem resolvent_norm_bound (hk : 0 < k) : ‖R‖ ≤ (1 + ε/2)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  simpa only [div_eq_mul_inv, mul_comm] using
    KFCausalInteractingEnergyFloor.resolvent_norm_le ε hε h hpos hb m g k hk t 1 zero_lt_one f

def normalizedSource (z : Hilbert) : Hilbert := ((‖R z‖⁻¹ : ℝ) : ℂ) • z
def normalizedSeed (z : Hilbert) : Hilbert := R (normalizedSource ε hε h hpos hb m g k t z)

theorem normalizedSeed_norm (z : Hilbert) (hz : z ≠ 0) :
    ‖normalizedSeed ε hε h hpos hb m g k t z‖ = 1 := by
  have hn : R z ≠ 0 := fun he => hz
    ((resolvent_injective ε hε h hpos hb m g k t) (by simpa only [map_zero] using he))
  simp only [normalizedSeed, normalizedSource, map_smul, norm_smul, Complex.norm_real,
    Real.norm_eq_abs,
    abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hn)]

theorem normalizedSeed_in_domain (z : Hilbert) :
    normalizedSeed ε hε h hpos hb m g k t z ∈ (H).domain :=
  (hamiltonian_domain_iff ε hε h hpos hb m g k t _).mpr
    ⟨normalizedSource ε hε h hpos hb m g k t z, rfl⟩

def physicalMassLaw (z : Hilbert) : Measure ℝ :=
  KFCausalResolventMassMeasure.massLaw R
    (resolvent_selfAdjoint ε hε h hpos hb m g k t)
    (normalizedSource ε hε h hpos hb m g k t z)

instance (z : Hilbert) : IsFiniteMeasure (physicalMassLaw ε hε h hpos hb m g k t z) := by
  unfold physicalMassLaw
  infer_instance

theorem physicalMassLaw_probability (z : Hilbert) (hz : z ≠ 0) :
    IsProbabilityMeasure (physicalMassLaw ε hε h hpos hb m g k t z) :=
  KFCausalResolventMassMeasure.mass_probability R _ _
    (normalizedSeed_norm ε hε h hpos hb m g k t z hz)

theorem physicalMassLaw_threshold (hk : 0 < k) (z : Hilbert) (hz : z ≠ 0) :
    ∀ᵐ s ∂physicalMassLaw ε hε h hpos hb m g k t z, (ε/2)^2 ≤ s := by
  letI : Nontrivial Hilbert := ⟨⟨z, 0, hz⟩⟩
  exact KFCausalResolventMassMeasure.mass_lower_ae R _ _
    (resolvent_nonnegative ε hε h hpos hb m g k t) (ε/2) (by positivity)
    (resolvent_norm_bound ε hε h hpos hb m g k t hk)

theorem physicalMassLaw_moments (hk : 0 < k) (z : Hilbert) (hz : z ≠ 0) (n : ℕ) :
    ∫ s, ((1 + Real.sqrt s)⁻¹)^n ∂physicalMassLaw ε hε h hpos hb m g k t z =
      (inner ℂ (normalizedSeed ε hε h hpos hb m g k t z)
        ((R^n) (normalizedSeed ε hε h hpos hb m g k t z))).re := by
  letI : Nontrivial Hilbert := ⟨⟨z, 0, hz⟩⟩
  exact KFCausalResolventMassMeasure.mass_moments R _ _
    (resolvent_nonnegative ε hε h hpos hb m g k t) (ε/2) (by positivity)
    (resolvent_norm_bound ε hε h hpos hb m g k t hk) n

end
end UnifiedTheory.Audit.KFCausalInteractingMassMeasure
