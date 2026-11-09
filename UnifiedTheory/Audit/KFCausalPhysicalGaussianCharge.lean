/- A constructed Gaussian family in the actual physical zero-charge
sector. The Fourier normalization determines the charged width. This
is a charge-domain theorem, not Hamiltonian energy-domain membership. -/
import UnifiedTheory.Audit.KFCausalChargeGaussianIdentities
import UnifiedTheory.Audit.KFCausalStandingChargeOperator
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalPhysicalGaussianCharge
noncomputable section
open MeasureTheory Filter
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (euclideanPullback euclideanPullback_coe)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalPhysicalMixedCoordinates
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow
open UnifiedTheory.Audit.KFCausalStandingChargeOperator
open UnifiedTheory.Audit.KFCausalChargeGaussianProducts
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalChargeGaussianIdentities

def state (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (g : ℝ → ℂ)
    (hc : Continuous g) (hg : MemLp g 2 volume) : Hilbert :=
  pairedState ((gaussian_memLp 2 α hα).toLp (gaussian 2 α))
    ((spectator_memLp α β hα hβ g hc hg).toLp (spectator α β g))

theorem state_position_coe (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (g : ℝ → ℂ)
    (hc : Continuous g) (hg : MemLp g 2 volume) :
    euclideanPullback (state α β hα hβ g hc hg) =ᵐ[volume] positionProfile α β g := by
  filter_upwards [pairedState_position_coe (gaussian 2 α) (spectator α β g)
    (gaussian_memLp 2 α hα) (spectator_memLp α β hα hβ g hc hg)] with x hx
  exact hx.trans (paired_profile_identity α β g x)

theorem state_configuration_coe (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (g : ℝ → ℂ)
    (hc : Continuous g) (hg : MemLp g 2 volume) :
    state α β hα hβ g hc hg =ᵐ[volume] configurationProfile α β g := by
  have ha : (fun x : KFCausalEuclideanConfiguration.Space =>
      (state α β hα hβ g hc hg) (KFCausalEuclideanConfiguration.split x)) =ᵐ[volume]
      fun x => configurationProfile α β g (KFCausalEuclideanConfiguration.split x) := by
    filter_upwards [euclideanPullback_coe (state α β hα hβ g hc hg),
      state_position_coe α β hα hβ g hc hg] with x hx hp
    exact hx.symm.trans (hp.trans (configurationProfile_split α β g x).symm)
  have ht := KFCausalEuclideanConfiguration.split_preserves_volume.symm.quasiMeasurePreserving.ae ha
  filter_upwards [ht] with x hx
  simpa only [MeasurableEquiv.apply_symm_apply] using hx

theorem configurationProfile_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (g : ℝ → ℂ)
    (hc : Continuous g) (hg : MemLp g 2 volume) : MemLp (configurationProfile α β g) 2 volume :=
  (Lp.memLp (state α β hα hβ g hc hg)).ae_eq (state_configuration_coe α β hα hβ g hc hg)

theorem state_ne_zero (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (g : ℝ → ℂ)
    (hc : Continuous g) (hg : MemLp g 2 volume) (h0 : g 0 ≠ 0) :
    state α β hα hβ g hc hg ≠ 0 := by
  intro h
  have hs := state_configuration_coe α β hα hβ g hc hg
  rw [h] at hs
  have hz : configurationProfile α β g =ᵐ[volume] (fun _ => (0:ℂ)) := by
    filter_upwards [hs,Lp.coeFn_zero ℂ 2 (volume : Measure Configuration)] with x hx hzero
    exact hx.symm.trans hzero
  have he := Measure.eq_of_ae_eq hz (configurationProfile_continuous α β g hc) continuous_const
  have hv := congrFun he (0,0)
  rw [configurationProfile_zero] at hv
  exact h0 hv

theorem state_chargeCoordinates (α β c : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hmatch : Real.pi^2/α = α*c^2) (g : ℝ → ℂ)
    (hc : Continuous g) (hg : MemLp g 2 volume) :
    chargeCoordinates (state α β hα hβ g hc hg) =ᵐ[volume]
      fun x => ((Real.pi/α:ℝ):ℂ)*profile α β c g x := by
  have hm := mixedCoordinates_functions_coe (gaussian 2 α) (spectator α β g)
    (gaussian_integrable 2 α hα) (gaussian_memLp 2 α hα) (spectator_memLp α β hα hβ g hc hg)
  filter_upwards [coordinates_coe 2 4 (mixedCoordinates (state α β hα hβ g hc hg)),
    (split_preserves_volume 2 4).quasiMeasurePreserving.ae hm] with x hx hp
  exact hx.trans (hp.trans (mixed_profile_identity α β c hα hmatch g x))

theorem state_fixed (hbar : ℝ) (hh : hbar ≠ 0) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hmatch : Real.pi^2/α = α*(momentumScale hbar)^2) (g : ℝ → ℂ)
    (hc : Continuous g) (hg : MemLp g 2 volume) (θ : ℝ) :
    action hbar hh θ (state α β hα hβ g hc hg) = state α β hα hβ g hc hg := by
  apply chargeCoordinates.injective
  rw [action_coordinates]
  exact action_fixed_of_profile α β (momentumScale hbar) (momentumScale_ne_zero hbar hh)
    g ((Real.pi/α:ℝ):ℂ) _ (state_chargeCoordinates α β _ hα hβ hmatch g hc hg) θ

def groundState (hbar : ℝ) (hh : hbar ≠ 0) (β : ℝ) (hβ : 0 < β) (g : ℝ → ℂ)
    (hc : Continuous g) (hg : MemLp g 2 volume) : Hilbert :=
  state (groundWidth hbar) β (groundWidth_positive hbar hh) hβ g hc hg

theorem groundState_coe (hbar : ℝ) (hh : hbar ≠ 0) (β : ℝ) (hβ : 0 < β) (g : ℝ → ℂ)
    (hc : Continuous g) (hg : MemLp g 2 volume) :
    groundState hbar hh β hβ g hc hg =ᵐ[volume] configurationProfile (groundWidth hbar) β g :=
  state_configuration_coe _ β (groundWidth_positive hbar hh) hβ g hc hg

theorem groundState_mem_zeroSector (hbar : ℝ) (hh : hbar ≠ 0) (β : ℝ) (hβ : 0 < β)
    (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume) :
    groundState hbar hh β hβ g hc hg ∈ zeroSector hbar hh := by
  intro θ
  exact state_fixed hbar hh _ β (groundWidth_positive hbar hh) hβ
    (groundWidth_matching hbar hh) g hc hg θ

theorem groundState_charge_zero (hbar : ℝ) (hh : hbar ≠ 0) (β : ℝ) (hβ : 0 < β)
    (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume) :
    (groundState hbar hh β hβ g hc hg,0) ∈ (standingCharge hbar hh).graph :=
  (standingCharge_zero_iff hbar hh _).mpr (groundState_mem_zeroSector hbar hh β hβ g hc hg)

theorem groundState_ne_zero (hbar : ℝ) (hh : hbar ≠ 0) (β : ℝ) (hβ : 0 < β)
    (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume) (h0 : g 0 ≠ 0) :
    groundState hbar hh β hβ g hc hg ≠ 0 :=
  state_ne_zero _ β (groundWidth_positive hbar hh) hβ g hc hg h0

theorem groundState_projection (hbar : ℝ) (hh : hbar ≠ 0) (β : ℝ) (hβ : 0 < β)
    (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume) :
    zeroProjection hbar hh (groundState hbar hh β hβ g hc hg) = groundState hbar hh β hβ g hc hg :=
  zeroProjection_fixes hbar hh _ (groundState_mem_zeroSector hbar hh β hβ g hc hg)

theorem exists_nonzero_zeroSector (hbar : ℝ) (hh : hbar ≠ 0) :
    ∃ f : Hilbert, f ≠ 0 ∧ f ∈ zeroSector hbar hh := by
  let g := KFCausalGaussianSliceDomain.gaussian (1:ℂ)
  have hc : Continuous g := KFCausalGaussianSliceDomain.gaussian_continuous _
  have hg : MemLp g 2 volume := (KFCausalGaussianSliceDomain.gaussian_memLp_iff _).mpr (by norm_num)
  have h0 : g 0 ≠ 0 := Complex.exp_ne_zero _
  exact ⟨groundState hbar hh 1 (by norm_num) g hc hg,
    groundState_ne_zero hbar hh 1 (by norm_num) g hc hg h0,
    groundState_mem_zeroSector hbar hh 1 (by norm_num) g hc hg⟩

#print axioms state_position_coe
#print axioms state_configuration_coe
#print axioms configurationProfile_memLp
#print axioms state_ne_zero
#print axioms state_chargeCoordinates
#print axioms state_fixed
#print axioms groundState_coe
#print axioms groundState_mem_zeroSector
#print axioms groundState_charge_zero
#print axioms groundState_ne_zero
#print axioms groundState_projection
#print axioms exists_nonzero_zeroSector

end
end UnifiedTheory.Audit.KFCausalPhysicalGaussianCharge
