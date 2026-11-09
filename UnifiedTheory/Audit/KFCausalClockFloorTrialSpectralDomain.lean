/- The nonzero physical charge-zero trial belongs to the actual revised
ordered exponential/inverse-clock domain. The full Fourier estimate is
connected to the maximal longitudinal spectral operator, with its energy.
No membership in the remaining Hamiltonian factor domains is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorFullFourierEnergy
import UnifiedTheory.Audit.KFCausalClockFloorExponential
import UnifiedTheory.Audit.KFCausalOrderedOperatorComposition

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalClockFloorChargeTrialBridge (dressedTrial_eq)
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian
open UnifiedTheory.Audit.KFCausalClockFloorGroupedCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf
open UnifiedTheory.Audit.KFCausalClockFloorTrialUnitary
open UnifiedTheory.Audit.KFCausalClockFloorGaussianL1
open UnifiedTheory.Audit.KFCausalClockFloorFullFourierEnergy
open UnifiedTheory.Audit.KFCausalClockFloorFourierCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorFourierMultiplier
open UnifiedTheory.Audit.KFCausalClockFloorExponential
open UnifiedTheory.Audit.KFCausalL2FourierIntegral
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition
open UnifiedTheory.Audit.KFCausalStandingChargeOperator

def spectralInput (ε a hbar : ℝ) : Space → ℂ :=
  euclideanLine ε a (groundWidth hbar) (neutralWidth hbar) 0 ∘ euclideanSplit

theorem spectralInput_integrable (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    Integrable (spectralInput ε a hbar) :=
  euclideanSplit_preserves_volume.integrable_comp_of_integrable
    (euclideanLine_integrable ε a _ _ 0 hε ha (groundWidth_positive hbar hh)
      (neutralWidth_positive hbar hh) (neutralWidth_bound hbar) (by simp; positivity))

theorem spectralInput_memLp (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    MemLp (spectralInput ε a hbar) 2 :=
  (euclideanLine_memLp ε a _ _ 0 hε ha (groundWidth_positive hbar hh)
    (neutralWidth_positive hbar hh) (neutralWidth_bound hbar) (by simp; positivity)).comp_measurePreserving
      euclideanSplit_preserves_volume

theorem inverse_damped_euclidean_coe (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    euclideanPullback ((coordinates ε hε).symm (dampedState ε a hbar hε ha hh)) =ᵐ[volume]
      spectralInput ε a hbar := by
  filter_upwards [euclideanPullback_coe ((coordinates ε hε).symm (dampedState ε a hbar hε ha hh)),
    split_preserves_volume.quasiMeasurePreserving.ae (inverse_dampedState_coe ε a hbar hε ha hh)]
    with x hx hy
  apply (hx.trans hy).trans
  have he := inverse_dampedProfile_grouping ε a hbar hε (grouping (split x))
  rw [MeasurableEquiv.symm_apply_apply] at he
  have hl := congrFun (dressedTrial_eq ε a hbar hε) (grouping (split x))
  change _ = line ε a (groundWidth hbar) (neutralWidth hbar) 0 (pairGrouping (euclideanSplit x))
  rw [pairGrouping_euclideanSplit]
  exact he.trans hl

theorem inverse_damped_euclidean_eq (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    euclideanPullback ((coordinates ε hε).symm (dampedState ε a hbar hε ha hh)) =
      (spectralInput_memLp ε a hbar hε ha hh).toLp (spectralInput ε a hbar) := by
  apply Lp.ext
  exact (inverse_damped_euclidean_coe ε a hbar hε ha hh).trans
    (spectralInput_memLp ε a hbar hε ha hh).coeFn_toLp.symm

theorem dampedState_fourier_coe (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    coupledFourier ε hε (dampedState ε a hbar hε ha hh) =ᵐ[volume] 𝓕 (spectralInput ε a hbar) := by
  change (Lp.fourierTransformₗᵢ Space ℂ)
    (euclideanPullback ((coordinates ε hε).symm (dampedState ε a hbar hε ha hh))) =ᵐ[volume] _
  rw [inverse_damped_euclidean_eq]
  exact fourier_toLp_coe _ (spectralInput_integrable ε a hbar hε ha hh)
    (spectralInput_memLp ε a hbar hε ha hh)

theorem dampedState_half_domain (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) :
    dampedState ε a hbar hε ha hh ∈ (longitudinalExponential ε hε hbar (1/2)).domain := by
  apply (half_exponential_domain ε hε hbar _).mpr
  apply (full_fourier_integrable ε a _ _ hbar hε ha (groundWidth_positive hbar hh)
    (neutralWidth_positive hbar hh) (neutralWidth_bound hbar) hbound).congr
  filter_upwards [dampedState_fourier_coe ε a hbar hε ha hh] with k hk
  rw [hk]
  rfl

theorem dampedState_half_energy (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) :
    ‖longitudinalExponential ε hε hbar (1/2)
      ⟨dampedState ε a hbar hε ha hh,dampedState_half_domain ε a hbar hε ha hh hbound⟩‖^2 =
      ∫ z : ℝ × KFCausalClockFloorShearBounds.Grouped,
        ‖line ε a (groundWidth hbar) (neutralWidth hbar) (-hbar/2) z‖^2 := by
  rw [half_exponential_energy]
  calc
    _ = ∫ k : Space, Real.exp (2*Real.pi*hbar*k 0)*‖(𝓕 (spectralInput ε a hbar)) k‖^2 := by
      apply integral_congr_ae
      filter_upwards [dampedState_fourier_coe ε a hbar hε ha hh] with k hk
      rw [hk]
      rfl
    _ = _ := full_fourier_shifted_energy ε a _ _ hbar hε ha (groundWidth_positive hbar hh)
      (neutralWidth_positive hbar hh) (neutralWidth_bound hbar) hbound

def orderedExponential (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) : Hilbert →ₗ.[ℂ] Hilbert :=
  composition (longitudinalExponential ε hε hbar (1/2)) (inverseClockHalf ε)

def reversedExponential (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) : Hilbert →ₗ.[ℂ] Hilbert :=
  composition (inverseClockHalf ε) (longitudinalExponential ε hε hbar (1/2))

theorem reversed_domain (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (f : Hilbert) :
    f ∈ (reversedExponential ε hε hbar).domain ↔
      f ∈ (longitudinalExponential ε hε hbar (1/2)).domain := by
  rw [reversedExponential,composition_domain]
  constructor
  · rintro ⟨g,hg,_⟩
    exact LinearPMap.mem_domain_of_mem_graph hg
  · intro hf
    exact ⟨_,(longitudinalExponential ε hε hbar (1/2)).mem_graph ⟨f,hf⟩,
      inverseClockHalf_domain ε hε _⟩

theorem orderedExponential_closable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) :
    (orderedExponential ε hε hbar).IsClosable := by
  apply composition_closable _ _ (longitudinal_exponential_selfAdjoint ε hε hbar (1/2))
    (inverseClockHalf_selfAdjoint ε)
  apply (longitudinal_exponential_dense ε hε hbar (1/2)).mono
  intro f hf
  exact (reversed_domain ε hε hbar f).mpr hf

theorem trialState_ordered_domain (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) :
    trialState ε a hbar hε ha hh ∈ (orderedExponential ε hε hbar).domain := by
  apply (composition_domain _ _ _).mpr
  exact ⟨dampedState ε a hbar hε ha hh,dampedState_graph ε a hbar hε ha hh,
    dampedState_half_domain ε a hbar hε ha hh hbound⟩

theorem trialState_ordered_graph (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) :
    (trialState ε a hbar hε ha hh,longitudinalExponential ε hε hbar (1/2)
      ⟨dampedState ε a hbar hε ha hh,dampedState_half_domain ε a hbar hε ha hh hbound⟩) ∈
        (orderedExponential ε hε hbar).graph := by
  apply (composition_graph _ _ _ _).mpr
  exact ⟨dampedState ε a hbar hε ha hh,dampedState_graph ε a hbar hε ha hh,
    (longitudinalExponential ε hε hbar (1/2)).mem_graph
      ⟨dampedState ε a hbar hε ha hh,dampedState_half_domain ε a hbar hε ha hh hbound⟩⟩

theorem trialState_ordered_energy (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) :
    ‖orderedExponential ε hε hbar
      ⟨trialState ε a hbar hε ha hh,trialState_ordered_domain ε a hbar hε ha hh hbound⟩‖^2 =
      ∫ z : ℝ × KFCausalClockFloorShearBounds.Grouped,
        ‖line ε a (groundWidth hbar) (neutralWidth hbar) (-hbar/2) z‖^2 := by
  have he := (orderedExponential ε hε hbar).mem_graph_snd_inj'
    ((orderedExponential ε hε hbar).mem_graph
      ⟨trialState ε a hbar hε ha hh,trialState_ordered_domain ε a hbar hε ha hh hbound⟩)
    (trialState_ordered_graph ε a hbar hε ha hh hbound) rfl
  change orderedExponential ε hε hbar
      ⟨trialState ε a hbar hε ha hh,trialState_ordered_domain ε a hbar hε ha hh hbound⟩ = _ at he
  rw [he]
  exact dampedState_half_energy ε a hbar hε ha hh hbound

theorem exists_nonzero_charge_zero_ordered (ε hbar : ℝ) (hε : 0 < ε)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) :
    ∃ f : Hilbert, f ≠ 0 ∧ f ∈ zeroSector hbar hh ∧ f ∈ (orderedExponential ε hε hbar).domain :=
  ⟨trialState ε 1 hbar hε zero_lt_one hh,trialState_ne_zero ε 1 hbar hε zero_lt_one hh,
    trialState_mem_zeroSector ε 1 hbar hε zero_lt_one hh,
    trialState_ordered_domain ε 1 hbar hε zero_lt_one hh hbound⟩

#print axioms spectralInput_integrable
#print axioms spectralInput_memLp
#print axioms inverse_damped_euclidean_coe
#print axioms inverse_damped_euclidean_eq
#print axioms dampedState_fourier_coe
#print axioms dampedState_half_domain
#print axioms dampedState_half_energy
#print axioms reversed_domain
#print axioms orderedExponential_closable
#print axioms trialState_ordered_domain
#print axioms trialState_ordered_graph
#print axioms trialState_ordered_energy
#print axioms exists_nonzero_charge_zero_ordered

end
end UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain
