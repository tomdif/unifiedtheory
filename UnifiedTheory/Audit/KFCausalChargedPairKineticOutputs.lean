/- Actual half-clock and four ordered transverse momentum outputs of the
paired state. Polynomial derivatives are connected to maximal operator
graphs before any pairing cancellation is used. -/
import UnifiedTheory.Audit.KFCausalChargedPairDifferential
import UnifiedTheory.Audit.KFCausalChargedPairHamiltonianForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalChargedPairKineticOutputs
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalClockFloorShearBounds (physicalGaussian)
open KFCausalChargedPairCoordinates (pairPolynomial)
open KFCausalChargedPairDifferential
open KFCausalTransverseTrialDerivative (derivative)
open KFCausalChargedPairDomain (state state_coe output_graph)
open KFCausalChargedPairHamiltonianForm (pairedFactors)
open KFCausalClockFloorInvariantTrial
  (clockFunction clockFunction_memLp neutralWidth neutralWidth_positive)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorTrialClockEnergy
  (halfClockFunction halfClockFunction_memLp dampedClockFunction dampedClockFunction_memLp)
open KFCausalClockFloorClockHalf
  (clockHalf clockHalf_graph halfWeight inverseClockHalf inverseClockHalf_graph inverseWeight)
open KFCausalClockFloorTrialMomentum (clockMomentum)
open KFCausalPhysicalTransverseMomentum (transverseMomentum)
open KFCausalTransverseMomentumDerivative (derivative_momentum_graph)
open KFCausalOrderedOperatorComposition (composition_graph)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)

def momentumIndex : Fin 4 → Fin 8 := ![1,2,3,4]

def profileState (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (g : ℝ → ℂ) (hg : MemLp g 2 volume) : Hilbert :=
  (profile_memLp α β hα hβ g hg).toLp (profile α β g)

theorem profileState_coe (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (g : ℝ → ℂ) (hg : MemLp g 2 volume) :
    profileState α β hα hβ g hg =ᵐ[volume] profile α β g :=
  (profile_memLp α β hα hβ g hg).coeFn_toLp

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => neutralWidth_positive h hh
local notation "ψ" => state ε a h hε ha hh
local notation "gd" => dampedClockFunction ε a
local notation "hgd" => dampedClockFunction_memLp ε a hε ha

def halfState : Hilbert :=
  profileState α β hα hβ (halfClockFunction ε a) (halfClockFunction_memLp ε a hε ha)

def dampedState : Hilbert := profileState α β hα hβ gd hgd

def momentumState (v : Transverse) : Hilbert :=
  (-Complex.I*(h:ℂ)) • (derivative_memLp α β hα hβ gd hgd v).toLp (derivative v (profile α β gd))

theorem halfState_graph : (ψ,halfState ε a h hε ha hh) ∈ (clockHalf ε).graph := by
  apply (clockHalf_graph ε _ _).mpr
  filter_upwards [profileState_coe α β hα hβ (halfClockFunction ε a)
      (halfClockFunction_memLp ε a hε ha),state_coe ε a h hε ha hh] with x hx hy
  change halfState ε a h hε ha hh x = _ at hx
  rw [hx,hy]
  simp only [profile,KFCausalChargedPairDomain.pairedProfile,halfClockFunction,halfWeight]
  ring

theorem dampedState_graph : (ψ,dampedState ε a h hε ha hh) ∈ (inverseClockHalf ε).graph := by
  apply (inverseClockHalf_graph ε _ _).mpr
  filter_upwards [profileState_coe α β hα hβ gd hgd,state_coe ε a h hε ha hh] with x hx hy
  change dampedState ε a h hε ha hh x = _ at hx
  rw [hx,hy]
  simp only [profile,KFCausalChargedPairDomain.pairedProfile,dampedClockFunction,
    inverseWeight,halfWeight,Complex.ofReal_inv]
  ring

theorem dampedState_momentum_graph (v : Transverse) :
    (dampedState ε a h hε ha hh,momentumState ε a h hε ha hh v) ∈
      (transverseMomentum h v).graph :=
  derivative_momentum_graph h (profile α β gd) v (profile_memLp α β hα hβ gd hgd)
    (derivative_memLp α β hα hβ gd hgd v) (profile_transverse_differentiable α β gd)

theorem momentumState_graph (v : Transverse) :
    (ψ,momentumState ε a h hε ha hh v) ∈ (clockMomentum ε h v).graph := by
  apply (composition_graph _ _ _ _).mpr
  exact ⟨_,dampedState_graph ε a h hε ha hh,dampedState_momentum_graph ε a h hε ha hh v⟩

theorem momentumState_coe (v : Transverse) :
    momentumState ε a h hε ha hh v =ᵐ[volume] fun x =>
      (-Complex.I*(h:ℂ))*gd x.1*(derivativePolynomial α β v x.2:ℂ)*physicalGaussian α β x.2 := by
  filter_upwards [Lp.coeFn_smul (-Complex.I*(h:ℂ))
    ((derivative_memLp α β hα hβ gd hgd v).toLp (derivative v (profile α β gd))),
    (derivative_memLp α β hα hβ gd hgd v).coeFn_toLp] with x hx hy
  change ((-Complex.I*(h:ℂ)) •
    (derivative_memLp α β hα hβ gd hgd v).toLp (derivative v (profile α β gd)) : Hilbert) x = _
  rw [hx,Pi.smul_apply,smul_eq_mul,hy,profile_derivative]
  ring

variable (hb : |h| ≤ 2*Real.pi*ε/3)

theorem halfOutput_eq : pairedFactors ε a h hε ha hh hb 0 = halfState ε a h hε ha hh :=
  (clockHalf ε).mem_graph_snd_inj'
    (output_graph ε a h hε ha hh hb modelDirections pointField 0)
    (halfState_graph ε a h hε ha hh) rfl

theorem momentumFactor_eq (j : Fin 4) :
    energyFactor ε hε h modelDirections pointField (momentumIndex j) =
      clockMomentum ε h (modelDirections j) := by
  fin_cases j <;> rfl

theorem momentumOutput_eq (j : Fin 4) :
    pairedFactors ε a h hε ha hh hb (momentumIndex j) =
      momentumState ε a h hε ha hh (modelDirections j) := by
  have hp := output_graph ε a h hε ha hh hb modelDirections pointField (momentumIndex j)
  rw [momentumFactor_eq] at hp
  exact (clockMomentum ε h (modelDirections j)).mem_graph_snd_inj' hp
    (momentumState_graph ε a h hε ha hh (modelDirections j)) rfl

theorem halfOutput_coe :
    pairedFactors ε a h hε ha hh hb 0 =ᵐ[volume] profile α β (halfClockFunction ε a) := by
  rw [halfOutput_eq]
  exact profileState_coe α β hα hβ (halfClockFunction ε a) (halfClockFunction_memLp ε a hε ha)

theorem momentumOutput_coe (j : Fin 4) :
    pairedFactors ε a h hε ha hh hb (momentumIndex j) =ᵐ[volume] fun x =>
      (-Complex.I*(h:ℂ))*gd x.1*(derivativePolynomial α β (modelDirections j) x.2:ℂ)*
        physicalGaussian α β x.2 := by
  rw [momentumOutput_eq]
  exact momentumState_coe ε a h hε ha hh (modelDirections j)

#print axioms profileState_coe
#print axioms halfState_graph
#print axioms dampedState_graph
#print axioms dampedState_momentum_graph
#print axioms momentumState_graph
#print axioms momentumState_coe
#print axioms halfOutput_eq
#print axioms momentumFactor_eq
#print axioms momentumOutput_eq
#print axioms halfOutput_coe
#print axioms momentumOutput_coe
end
end UnifiedTheory.Audit.KFCausalChargedPairKineticOutputs
