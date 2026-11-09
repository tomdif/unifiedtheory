/- A nonzero invariant state in the natural domains of all eight revised
energy factors. This constructs admissible states; it does not assert
density, closed-form completion, or Hamiltonian evolution. -/
import UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum
import UnifiedTheory.Audit.KFCausalClockFloorTrialMatter

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorCommonDomain
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf
open UnifiedTheory.Audit.KFCausalClockFloorTrialClockEnergy
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum
open UnifiedTheory.Audit.KFCausalClockFloorTrialMatter
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain
open UnifiedTheory.Audit.KFCausalPhysicalField
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare
open UnifiedTheory.Audit.KFCausalStandingChargeOperator

def energyFactor (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) : Fin 8 → Hilbert →ₗ.[ℂ] Hilbert :=
  ![clockHalf ε,clockMomentum ε hbar (v 0),clockMomentum ε hbar (v 1),
    clockMomentum ε hbar (v 2),clockMomentum ε hbar (v 3),
    matterFactor ε hε hbar (physicalField l),matterFactor ε hε hbar (fieldSquare l),
    orderedExponential ε hε hbar]

def commonEnergyDomain (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) : Submodule ℂ Hilbert :=
  ⨅ i, (energyFactor ε hε hbar v l i).domain

theorem commonEnergyDomain_iff (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (f : Hilbert) :
    f ∈ commonEnergyDomain ε hε hbar v l ↔ ∀ i, f ∈ (energyFactor ε hε hbar v l i).domain :=
  Submodule.mem_iInf _

theorem trialState_commonEnergyDomain (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    trialState ε a hbar hε ha hh ∈ commonEnergyDomain ε hε hbar v l := by
  apply (commonEnergyDomain_iff ε hε hbar v l _).mpr
  intro i
  fin_cases i
  · exact trialState_clockHalf_domain ε a hbar hε ha hh
  · exact trialState_clockMomentum_domain ε a hbar hε ha hh (v 0)
  · exact trialState_clockMomentum_domain ε a hbar hε ha hh (v 1)
  · exact trialState_clockMomentum_domain ε a hbar hε ha hh (v 2)
  · exact trialState_clockMomentum_domain ε a hbar hε ha hh (v 3)
  · exact trialState_linearMatter_domain ε a hbar hε ha hh hbound l
  · exact trialState_quadraticMatter_domain ε a hbar hε ha hh hbound l
  · exact trialState_ordered_domain ε a hbar hε ha hh hbound

theorem exists_nonzero_charge_zero_common (ε hbar : ℝ) (hε : 0 < ε)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    ∃ f : Hilbert, f ≠ 0 ∧ f ∈ zeroSector hbar hh ∧
      f ∈ commonEnergyDomain ε hε hbar v l ∧ (f,0) ∈ (standingCharge hbar hh).graph :=
  ⟨trialState ε 1 hbar hε zero_lt_one hh,trialState_ne_zero ε 1 hbar hε zero_lt_one hh,
    trialState_mem_zeroSector ε 1 hbar hε zero_lt_one hh,
    trialState_commonEnergyDomain ε 1 hbar hε zero_lt_one hh hbound v l,
    trialState_charge_zero ε 1 hbar hε zero_lt_one hh⟩

theorem exists_unit_charge_zero_common (ε hbar : ℝ) (hε : 0 < ε)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    ∃ f : Hilbert, ‖f‖ = 1 ∧ f ∈ zeroSector hbar hh ∧
      f ∈ commonEnergyDomain ε hε hbar v l ∧ (f,0) ∈ (standingCharge hbar hh).graph := by
  obtain ⟨f,hf,hz,he,_⟩ := exists_nonzero_charge_zero_common ε hbar hε hh hbound v l
  let c : ℂ := (‖f‖⁻¹:ℝ)
  have hn : ‖c • f‖ = 1 := by
    rw [norm_smul]
    simp only [c,Complex.norm_real,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _)]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hf)
  have hz' := (zeroSector hbar hh).smul_mem c hz
  exact ⟨c • f,hn,hz',(commonEnergyDomain ε hε hbar v l).smul_mem c he,
    (standingCharge_zero_iff hbar hh _).mpr hz'⟩

theorem invariant_commonDomain_ne_bot (ε hbar : ℝ) (hε : 0 < ε)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    zeroSector hbar hh ⊓ commonEnergyDomain ε hε hbar v l ≠ ⊥ := by
  obtain ⟨f,hf,hz,he,_⟩ := exists_nonzero_charge_zero_common ε hbar hε hh hbound v l
  intro h
  have hi : f ∈ zeroSector hbar hh ⊓ commonEnergyDomain ε hε hbar v l := ⟨hz,he⟩
  rw [h] at hi
  exact hf (by simpa using hi)

#print axioms commonEnergyDomain_iff
#print axioms trialState_commonEnergyDomain
#print axioms exists_nonzero_charge_zero_common
#print axioms exists_unit_charge_zero_common
#print axioms invariant_commonDomain_ne_bot

end
end UnifiedTheory.Audit.KFCausalClockFloorCommonDomain
