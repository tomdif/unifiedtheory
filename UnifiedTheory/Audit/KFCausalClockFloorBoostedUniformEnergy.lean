/- A uniform bound for all eight actual unaveraged energy factors on the
normalized canonical momentum boosts. The budget is independent of h at
fixed positive floor, clock width, momentum and couplings. Charge averaging,
Hamiltonian operator-domain membership and evolved estimates are not asserted. -/
import UnifiedTheory.Audit.KFCausalClockFloorBoostedMatterLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalClockFloorBoostedUniformEnergy
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalPhysicalMomentumModulation (modulation)
open UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics (positionFrequency)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization
open UnifiedTheory.Audit.KFCausalClockFloorSemiclassicalStates (unitTrial)
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf (clockHalf)
open UnifiedTheory.Audit.KFCausalClockFloorTrialClockEnergy (trialState_clockHalf_domain)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum (clockMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorKineticModulation (clockHalf_graph_modulation)
open UnifiedTheory.Audit.KFCausalClockFloorStrongInitialOutput
open UnifiedTheory.Audit.KFCausalClockFloorBoostedKineticLimit
open UnifiedTheory.Audit.KFCausalClockFloorBoostedCommonDomain
open UnifiedTheory.Audit.KFCausalClockFloorBoostedExponentialBound
open UnifiedTheory.Audit.KFCausalClockFloorBoostedMatterBounds
open UnifiedTheory.Audit.KFCausalClockFloorBoostedMatterLimit
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms
open UnifiedTheory.Audit.KFCausalClockFloorGaussianEnergyBounds (stripMass_nonnegative)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain
open UnifiedTheory.Audit.KFCausalClockFloorJointEnergy
open UnifiedTheory.Audit.KFCausalClockFloorTrialUniformEnergy (energyPolynomial energyPolynomial_mono)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)

def clockOutput (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (l : Configuration →L[ℝ] ℝ) : Hilbert :=
  modulation (h⁻¹ • l) ((‖trialState ε a h hε ha hh‖⁻¹:ℝ) • clockHalf ε
    ⟨trialState ε a h hε ha hh,trialState_clockHalf_domain ε a h hε ha hh⟩)

theorem clockOutput_graph (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (l : Configuration →L[ℝ] ℝ) :
    (boostedState ε a h hε ha hh l,clockOutput ε a h hε ha hh l) ∈ (clockHalf ε).graph :=
  clockHalf_graph_modulation ε (h⁻¹ • l) _ _
    (((clockHalf ε).graph.restrictScalars ℝ).smul_mem (‖trialState ε a h hε ha hh‖⁻¹)
      ((clockHalf ε).mem_graph ⟨_,trialState_clockHalf_domain ε a h hε ha hh⟩))

theorem clockOutput_mass (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (l : Configuration →L[ℝ] ℝ) :
    ‖clockOutput ε a h hε ha hh l‖^2 = halfMass ε a/clockMass ε a := by
  rw [clockOutput,(modulation (h⁻¹ • l)).norm_map,norm_smul,mul_pow,Real.norm_eq_abs,abs_inv,
    abs_of_nonneg (norm_nonneg _),inv_pow,← div_eq_inv_mul,
    trial_clockHalf_mass ε a h hε ha hh _
      ((clockHalf ε).mem_graph ⟨_,trialState_clockHalf_domain ε a h hε ha hh⟩),trial_norm_square]
  exact mul_div_mul_right _ _ (gaussianMass_positive _ _ (groundWidth_positive h hh)
    (neutralWidth_positive h hh)).ne'

theorem clock_output_mass (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (l : Configuration →L[ℝ] ℝ) (g : Hilbert)
    (hg : (boostedState ε a h hε ha hh l,g) ∈ (clockHalf ε).graph) :
    ‖g‖^2 = halfMass ε a/clockMass ε a := by
  have he := (clockHalf ε).mem_graph_snd_inj' hg (clockOutput_graph ε a h hε ha hh l) rfl
  dsimp only [Prod.snd] at he
  rw [he,clockOutput_mass]

def kineticBudget (ε a : ℝ) (v : Transverse) (l : Configuration →L[ℝ] ℝ) : ℝ :=
  2*(kineticMass ε a v+(l (0,v))^2*dampedMass ε a)/clockMass ε a

theorem boostedOutput_bound (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (h1 : |h| ≤ 1) (v : Transverse) (l : Configuration →L[ℝ] ℝ) :
    ‖boostedOutput ε a h hε ha hh v l‖^2 ≤ kineticBudget ε a v l := by
  have hx : |h| *kineticMass ε a v ≤ kineticMass ε a v := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right h1 (kineticMass_nonnegative ε a v)
  have hb : ‖baseOutput ε a h hε ha hh v‖^2 ≤ kineticMass ε a v/clockMass ε a :=
    (baseOutput_rate ε a h hε ha hh v).trans
      (div_le_div_of_nonneg_right hx (clockMass_positive ε a hε ha).le)
  have hc : ‖(l (0,v):ℂ) • normalizedDamped ε a h hε ha hh‖^2 =
      (l (0,v))^2*(dampedMass ε a/clockMass ε a) := by
    rw [norm_smul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,normalizedDamped_norm_square]
  rw [boostedOutput,(modulation (h⁻¹ • l)).norm_map]
  have hn := pow_le_pow_left₀ (norm_nonneg _)
    (norm_add_le (baseOutput ε a h hε ha hh v) ((l (0,v):ℂ) • normalizedDamped ε a h hε ha hh)) 2
  have hs := sq_nonneg (‖baseOutput ε a h hε ha hh v‖-
    ‖(l (0,v):ℂ) • normalizedDamped ε a h hε ha hh‖)
  unfold kineticBudget
  rw [mul_div_assoc,add_div,mul_div_assoc]
  nlinarith only [hb,hc,hn,hs]

theorem kinetic_output_bound (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (h1 : |h| ≤ 1) (v : Transverse) (l : Configuration →L[ℝ] ℝ) (g : Hilbert)
    (hg : (boostedState ε a h hε ha hh l,g) ∈ (clockMomentum ε h v).graph) :
    ‖g‖^2 ≤ kineticBudget ε a v l := by
  have he := (clockMomentum ε h v).mem_graph_snd_inj' hg
    (boostedOutput_graph ε a h hε ha hh v l) rfl
  dsimp only [Prod.snd] at he
  rw [he]
  exact boostedOutput_bound ε a h hε ha hh h1 v l

def boostedCommon (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) : commonEnergyDomain ε hε h v l :=
  ⟨boostedState ε a h hε ha hh (positionFrequency p.1 p.2),
    boostedState_commonEnergyDomain ε a h hε ha hh hb p v l⟩

def factorBudget (ε a : ℝ) (p : Configuration) (v : Fin 4 → Transverse)
    (l : Transverse →L[ℝ] ℝ) : Fin 8 → ℝ :=
  ![halfMass ε a/clockMass ε a,
    kineticBudget ε a (v 0) (positionFrequency p.1 p.2),
    kineticBudget ε a (v 1) (positionFrequency p.1 p.2),
    kineticBudget ε a (v 2) (positionFrequency p.1 p.2),
    kineticBudget ε a (v 3) (positionFrequency p.1 p.2),
    (exponentialMass ε a p+quadraticBudget ε a p l)/clockMass ε a,
    quadraticBudget ε a p l/clockMass ε a,exponentialMass ε a p/clockMass ε a]

theorem boosted_factor_graph (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8) :
    (boostedState ε a h hε ha hh (positionFrequency p.1 p.2),
      factorValue ε hε h v l (boostedCommon ε a h hε ha hh hb p v l) i) ∈
      (energyFactor ε hε h v l i).graph :=
  (energyFactor ε hε h v l i).mem_graph
    ⟨_,(Submodule.mem_iInf _).mp (boostedCommon ε a h hε ha hh hb p v l).property i⟩

theorem boosted_factor_bound (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (h1 : |h| ≤ 1) (p : Configuration)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8) :
    ‖factorValue ε hε h v l (boostedCommon ε a h hε ha hh hb p v l) i‖^2 ≤
      factorBudget ε a p v l i := by
  have hg (j : Fin 8) := boosted_factor_graph ε a h hε ha hh hb p v l j
  fin_cases i
  · exact (clock_output_mass ε a h hε ha hh _ _ (hg 0)).le
  · exact kinetic_output_bound ε a h hε ha hh h1 (v 0) _ _ (hg 1)
  · exact kinetic_output_bound ε a h hε ha hh h1 (v 1) _ _ (hg 2)
  · exact kinetic_output_bound ε a h hε ha hh h1 (v 2) _ _ (hg 3)
  · exact kinetic_output_bound ε a h hε ha hh h1 (v 3) _ _ (hg 4)
  · apply (linear_output_rate ε a h hε ha hh hb h1 p l _ (hg 5)).trans
    apply div_le_div_of_nonneg_right _ (clockMass_positive ε a hε ha).le
    have he : 0 ≤ exponentialMass ε a p := mul_nonneg (by positivity) (stripMass_nonnegative ε a)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right h1
      (add_nonneg he (quadraticBudget_nonnegative ε a p l))
  · apply (quadratic_output_rate ε a h hε ha hh hb h1 p l _ (hg 6)).trans
    apply div_le_div_of_nonneg_right _ (clockMass_positive ε a hε ha).le
    have hs : h^2 ≤ 1 := by nlinarith [sq_abs h,abs_nonneg h]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hs (quadraticBudget_nonnegative ε a p l)
  · exact ordered_boost_output_bound ε a h hε ha hh hb h1 p _ (hg 7)

def energyBudget (ε a : ℝ) (p : Configuration) (v : Fin 4 → Transverse)
    (l : Transverse →L[ℝ] ℝ) (m g κ t : ℝ) : ℝ :=
  energyPolynomial m g κ t (factorBudget ε a p v l)

theorem seed_energy_bound (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (h1 : |h| ≤ 1) (p : Configuration)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (m g κ t : ℝ)
    (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ) :
    seedEnergy ε hε h v l m g κ t (boostedCommon ε a h hε ha hh hb p v l) ≤
      energyBudget ε a p v l m g κ t :=
  energyPolynomial_mono m g κ t hm hg hκ _ _ (boosted_factor_bound ε a h hε ha hh hb h1 p v l)

theorem form_energy_bound (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (h1 : |h| ≤ 1) (p : Configuration) (m g κ t : ℝ)
    (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ) :
    ‖KFCausalClosedGraphForm.energyOutput _ (formVector ε a h hε ha hh hb p m g κ t)‖^2 ≤
      energyBudget ε a p modelDirections pointField m g κ t := by
  rw [formVector_energy ε a h hε ha hh hb p m g κ t hm hg hκ]
  exact seed_energy_bound ε a h hε ha hh hb h1 p modelDirections pointField m g κ t hm hg hκ

#print axioms clockOutput_graph
#print axioms clockOutput_mass
#print axioms clock_output_mass
#print axioms boostedOutput_bound
#print axioms kinetic_output_bound
#print axioms boosted_factor_graph
#print axioms boosted_factor_bound
#print axioms seed_energy_bound
#print axioms form_energy_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorBoostedUniformEnergy
