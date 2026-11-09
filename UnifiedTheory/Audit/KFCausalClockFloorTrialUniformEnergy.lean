/- A Planck-independent bound for the full eight-factor seed energy of the
explicit invariant trial, relative to its transverse Gaussian mass. -/
import UnifiedTheory.Audit.KFCausalClockFloorTrialMatterEnergy
import UnifiedTheory.Audit.KFCausalClockFloorJointEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorTrialUniformEnergy
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms
open UnifiedTheory.Audit.KFCausalClockFloorTrialMatterEnergy
open UnifiedTheory.Audit.KFCausalClockFloorGaussianEnergyBounds
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain
open UnifiedTheory.Audit.KFCausalClockFloorJointEnergy
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)

def trialCommon (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) : commonEnergyDomain ε hε hbar v l :=
  ⟨trialState ε a hbar hε ha hh,trialState_commonEnergyDomain ε a hbar hε ha hh hb v l⟩

def factorBudget (ε a : ℝ) (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) : Fin 8 → ℝ :=
  ![halfMass ε a,kineticMass ε a (v 0),kineticMass ε a (v 1),kineticMass ε a (v 2),
    kineticMass ε a (v 3),stripMass ε a+quadraticMass ε a l,quadraticMass ε a l,stripMass ε a]

theorem factorBudget_nonnegative (ε a : ℝ) (v : Fin 4 → Transverse)
    (l : Transverse →L[ℝ] ℝ) (i : Fin 8) : 0 ≤ factorBudget ε a v l i := by
  fin_cases i
  · exact halfMass_nonnegative ε a
  · exact kineticMass_nonnegative ε a (v 0)
  · exact kineticMass_nonnegative ε a (v 1)
  · exact kineticMass_nonnegative ε a (v 2)
  · exact kineticMass_nonnegative ε a (v 3)
  · exact add_nonneg (stripMass_nonnegative ε a) (quadraticMass_nonnegative ε a l)
  · exact quadraticMass_nonnegative ε a l
  · exact stripMass_nonnegative ε a

theorem trial_factor_bound (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3) (hh1 : |hbar| ≤ 1)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8) :
    ‖factorValue ε hε hbar v l (trialCommon ε a hbar hε ha hh hb v l) i‖^2 ≤
      factorBudget ε a v l i*gaussianMass (groundWidth hbar) (neutralWidth hbar) := by
  let f := trialCommon ε a hbar hε ha hh hb v l
  have hg (j : Fin 8) : ((f:Hilbert),factorValue ε hε hbar v l f j) ∈
      (energyFactor ε hε hbar v l j).graph :=
    (energyFactor ε hε hbar v l j).mem_graph ⟨f,(Submodule.mem_iInf _).mp f.property j⟩
  fin_cases i
  · exact (trial_clockHalf_mass ε a hbar hε ha hh _ (hg 0)).le
  · exact trial_momentum_mass ε a hbar hε ha hh hh1 (v 0) _ (hg 1)
  · exact trial_momentum_mass ε a hbar hε ha hh hh1 (v 1) _ (hg 2)
  · exact trial_momentum_mass ε a hbar hε ha hh hh1 (v 2) _ (hg 3)
  · exact trial_momentum_mass ε a hbar hε ha hh hh1 (v 3) _ (hg 4)
  · exact trial_linearMatter_bound ε a hbar hε ha hh hb hh1 l _ (hg 5)
  · exact trial_quadraticMatter_bound ε a hbar hε ha hh hb hh1 l _ (hg 6)
  · have he := (orderedExponential ε hε hbar).mem_graph_snd_inj' (hg 7)
      (trialState_shifted_graph ε a hbar hε ha hh hb) rfl
    exact (congrArg (fun g : Hilbert => ‖g‖^2) he).le.trans
      (shiftedOutput_mass_bound ε a hbar hε ha hh hb)

def energyPolynomial (mass2 quartic vacuum t : ℝ) (F : Fin 8 → ℝ) : ℝ :=
  (F 0+F 1+F 2)/2+Real.exp (2*t)*((F 3+F 4)/2+mass2/2*F 5+quartic/4*F 6+vacuum*F 7)

theorem energyPolynomial_mono (mass2 quartic vacuum t : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum)
    (F B : Fin 8 → ℝ) (h : ∀ i, F i ≤ B i) :
    energyPolynomial mass2 quartic vacuum t F ≤ energyPolynomial mass2 quartic vacuum t B := by
  unfold energyPolynomial
  gcongr <;> apply h

theorem energyPolynomial_scale (mass2 quartic vacuum t M : ℝ) (F : Fin 8 → ℝ) :
    energyPolynomial mass2 quartic vacuum t (fun i => F i*M) =
      energyPolynomial mass2 quartic vacuum t F*M := by unfold energyPolynomial; ring

def energyBudget (ε a : ℝ) (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ)
    (mass2 quartic vacuum t : ℝ) : ℝ :=
  energyPolynomial mass2 quartic vacuum t (factorBudget ε a v l)

theorem energyBudget_nonnegative (ε a : ℝ) (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ)
    (mass2 quartic vacuum t : ℝ) (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    0 ≤ energyBudget ε a v l mass2 quartic vacuum t := by
  have h := energyPolynomial_mono mass2 quartic vacuum t hm hq hv (fun _ => 0)
    (factorBudget ε a v l) (factorBudget_nonnegative ε a v l)
  simpa only [energyPolynomial,zero_add,add_zero,zero_div,mul_zero,energyBudget] using h

theorem trial_seed_energy_bound (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3) (hh1 : |hbar| ≤ 1)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ)
    (mass2 quartic vacuum t : ℝ) (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    seedEnergy ε hε hbar v l mass2 quartic vacuum t (trialCommon ε a hbar hε ha hh hb v l) ≤
      energyBudget ε a v l mass2 quartic vacuum t*gaussianMass (groundWidth hbar) (neutralWidth hbar) :=
  (energyPolynomial_mono mass2 quartic vacuum t hm hq hv _ _
    (trial_factor_bound ε a hbar hε ha hh hb hh1 v l)).trans_eq
      (energyPolynomial_scale mass2 quartic vacuum t _ _)

#print axioms factorBudget_nonnegative
#print axioms trial_factor_bound
#print axioms energyPolynomial_mono
#print axioms energyPolynomial_scale
#print axioms energyBudget_nonnegative
#print axioms trial_seed_energy_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorTrialUniformEnergy
