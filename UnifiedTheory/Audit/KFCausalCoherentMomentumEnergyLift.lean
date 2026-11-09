/- Both a coherent-span vector and its actual pure-clock momentum lift
into the existing full averaged eight-factor energy form. The output
pairing retains every ordered factor. No evolution identity is assumed. -/
import UnifiedTheory.Audit.KFCausalCoherentMomentumFullOrbit
import UnifiedTheory.Audit.KFCausalClockFloorAveragedDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCoherentMomentumEnergyLift
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output jointGraph)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalClockFloorJointEnergy (closedEnergy closedEnergy_graph)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections energyWeight)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action group action_strong_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure orbit orbitState_coe)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (mass2 quartic vacuum t : ℝ)
local notation "hp" => hamiltonian_bound ε h hb
local notation "D" => KFCausalClockFloorFormHamiltonian.formData ε hε h hp mass2 quartic vacuum t
local notation "Base" => KFCausalClosedGraphForm.FormSpace D
local notation "J" => KFCausalClosedGraphForm.embedding D
local notation "A" => KFCausalClosedGraphForm.energyOutput D
local notation "Full" => AveragedSpace ε hε h hp hh mass2 quartic vacuum t
local notation "embed" => embedding ε hε h hp hh mass2 quartic vacuum t
local notation "out" => energyOutput ε hε h hp hh mass2 quartic vacuum t
local notation "F" => energyFactor ε hε h modelDirections pointField

def weightedOutput (g : Fin 8 → ℝ → Hilbert) (θ : ℝ) : Output (Fin 8) Hilbert :=
  WithLp.toLp 2 (fun i => energyWeight mass2 quartic vacuum t i • g i θ)

theorem weightedOutput_continuous (g : Fin 8 → ℝ → Hilbert) (hc : ∀ i, Continuous (g i)) :
    Continuous (weightedOutput mass2 quartic vacuum t g) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin 8 => Hilbert)).comp
    (continuous_pi (fun i => (hc i).const_smul _))

include hb in
theorem weightedOutput_graph (f : Hilbert) (g : Fin 8 → ℝ → Hilbert)
    (hg : ∀ θ i, (action h hh (2*Real.pi*θ) f,g i θ) ∈ (F i).graph) (θ : ℝ) :
    (action h hh (2*Real.pi*θ) f,weightedOutput mass2 quartic vacuum t g θ) ∈
      (closedEnergy ε hε h modelDirections pointField mass2 quartic vacuum t).graph := by
  rw [closedEnergy_graph ε hε h modelDirections pointField mass2 quartic vacuum t hp]
  apply (jointGraph F (energyWeight mass2 quartic vacuum t)).le_topologicalClosure
  intro i
  exact (F i).graph.smul_mem _ (hg θ i)

def orbitVector (f : Hilbert) (g : Fin 8 → ℝ → Hilbert)
    (hg : ∀ θ i, (action h hh (2*Real.pi*θ) f,g i θ) ∈ (F i).graph) (θ : ℝ) : Base :=
  ⟨WithLp.toLp 2 (action h hh (2*Real.pi*θ) f,weightedOutput mass2 quartic vacuum t g θ),
    weightedOutput_graph ε h hε hh hb mass2 quartic vacuum t f g hg θ⟩

theorem orbitVector_continuous (f : Hilbert) (g : Fin 8 → ℝ → Hilbert) (hc : ∀ i, Continuous (g i))
    (hg : ∀ θ i, (action h hh (2*Real.pi*θ) f,g i θ) ∈ (F i).graph) :
    Continuous (orbitVector ε h hε hh hb mass2 quartic vacuum t f g hg) := by
  apply Continuous.subtype_mk
  exact (WithLp.prod_continuous_toLp 2 Hilbert (Output (Fin 8) Hilbert)).comp
    (((action_strong_continuous h hh f).comp (continuous_const.mul continuous_id)).prodMk
      (weightedOutput_continuous mass2 quartic vacuum t g hc))

def orbitLift (f : Hilbert) (g : Fin 8 → ℝ → Hilbert) (hc : ∀ i, Continuous (g i))
    (hg : ∀ θ i, (action h hh (2*Real.pi*θ) f,g i θ) ∈ (F i).graph) : Lp Base 2 angleMeasure :=
  (continuous_angle_memLp _ (orbitVector_continuous ε h hε hh hb mass2 quartic vacuum t f g hc hg)).toLp
    (orbitVector ε h hε hh hb mass2 quartic vacuum t f g hg)

theorem orbitLift_compatibility (f : Hilbert) (g : Fin 8 → ℝ → Hilbert) (hc : ∀ i, Continuous (g i))
    (hg : ∀ θ i, (action h hh (2*Real.pi*θ) f,g i θ) ∈ (F i).graph) :
    (J).compLp (orbitLift ε h hε hh hb mass2 quartic vacuum t f g hc hg) = orbit (group h hh) (2*Real.pi) f := by
  apply Lp.ext
  filter_upwards [(J).coeFn_compLp (orbitLift ε h hε hh hb mass2 quartic vacuum t f g hc hg),
    (continuous_angle_memLp _ (orbitVector_continuous ε h hε hh hb mass2 quartic vacuum t f g hc hg)).coeFn_toLp,
    orbitState_coe (group h hh) (2*Real.pi) f] with θ hJ hv ho
  change orbitLift ε h hε hh hb mass2 quartic vacuum t f g hc hg θ = _ at hv
  rw [hJ,hv]
  exact ho.symm

def lift (f : Hilbert) (g : Fin 8 → ℝ → Hilbert) (hc : ∀ i, Continuous (g i))
    (hg : ∀ θ i, (action h hh (2*Real.pi*θ) f,g i θ) ∈ (F i).graph) : Full :=
  ⟨WithLp.toLp 2 (f,orbitLift ε h hε hh hb mass2 quartic vacuum t f g hc hg),by
    change (J).compLp (orbitLift ε h hε hh hb mass2 quartic vacuum t f g hc hg)-orbit (group h hh) (2*Real.pi) f = 0
    exact sub_eq_zero.mpr (orbitLift_compatibility ε h hε hh hb mass2 quartic vacuum t f g hc hg)⟩

theorem lift_embedding (f : Hilbert) (g : Fin 8 → ℝ → Hilbert) (hc : ∀ i, Continuous (g i))
    (hg : ∀ θ i, (action h hh (2*Real.pi*θ) f,g i θ) ∈ (F i).graph) :
    embed (lift ε h hε hh hb mass2 quartic vacuum t f g hc hg) = f := rfl

theorem lift_output_coe (f : Hilbert) (g : Fin 8 → ℝ → Hilbert) (hc : ∀ i, Continuous (g i))
    (hg : ∀ θ i, (action h hh (2*Real.pi*θ) f,g i θ) ∈ (F i).graph) :
    out (lift ε h hε hh hb mass2 quartic vacuum t f g hc hg) =ᵐ[angleMeasure]
      weightedOutput mass2 quartic vacuum t g := by
  filter_upwards [(A).coeFn_compLp (orbitLift ε h hε hh hb mass2 quartic vacuum t f g hc hg),
    (continuous_angle_memLp _ (orbitVector_continuous ε h hε hh hb mass2 quartic vacuum t f g hc hg)).coeFn_toLp]
    with θ hA hv
  change orbitLift ε h hε hh hb mass2 quartic vacuum t f g hc hg θ = _ at hv
  change (A).compLp (orbitLift ε h hε hh hb mass2 quartic vacuum t f g hc hg) θ = _
  rw [hA,hv]
  rfl

theorem lift_pairing (f b : Hilbert) (g v : Fin 8 → ℝ → Hilbert)
    (hc : ∀ i, Continuous (g i)) (hd : ∀ i, Continuous (v i))
    (hg : ∀ θ i, (action h hh (2*Real.pi*θ) f,g i θ) ∈ (F i).graph)
    (hv : ∀ θ i, (action h hh (2*Real.pi*θ) b,v i θ) ∈ (F i).graph) :
    inner ℂ (out (lift ε h hε hh hb mass2 quartic vacuum t f g hc hg))
      (out (lift ε h hε hh hb mass2 quartic vacuum t b v hd hv)) =
        ∫ θ, ∑ i : Fin 8, inner ℂ (energyWeight mass2 quartic vacuum t i • g i θ)
          (energyWeight mass2 quartic vacuum t i • v i θ) ∂angleMeasure := by
  apply (L2.inner_def (𝕜 := ℂ) _ _).trans
  apply integral_congr_ae
  filter_upwards [lift_output_coe ε h hε hh hb mass2 quartic vacuum t f g hc hg,
    lift_output_coe ε h hε hh hb mass2 quartic vacuum t b v hd hv] with θ hθ hθ'
  exact (congrArg₂ (inner ℂ) hθ hθ').trans (PiLp.inner_apply _ _)

theorem actual_momentum_lift (a : ℝ) (ha : 0 < a) (f : Hilbert)
    (hf : f ∈ coherentSpan ε a h hε ha hh) (b : Hilbert) (hB : (f,b) ∈ (pureMomentum ε hε h).graph) :
    ∃ v : Full, embed v = b := by
  exact (KFCausalCoherentMomentumFullOrbit.actual_outputs ε a h hε ha hh hb modelDirections pointField f hf b hB).elim
    fun g hr => ⟨lift ε h hε hh hb mass2 quartic vacuum t b g hr.1 hr.2.2,rfl⟩

theorem actual_momentum_energy_domain (a : ℝ) (ha : 0 < a) (f : Hilbert)
    (hf : f ∈ coherentSpan ε a h hε ha hh) (b : Hilbert) (hB : (f,b) ∈ (pureMomentum ε hε h).graph) :
    b ∈ (energyOperator ε hε h hp hh mass2 quartic vacuum t).domain :=
  (energy_domain ε hε h hp hh mass2 quartic vacuum t b).mpr
    (actual_momentum_lift ε h hε hh hb mass2 quartic vacuum t a ha f hf b hB)

theorem coherent_momentum_lifts (a : ℝ) (ha : 0 < a) (f : Hilbert)
    (hf : f ∈ coherentSpan ε a h hε ha hh) :
    ∃ (b : Hilbert) (u v : Full), (f,b) ∈ (pureMomentum ε hε h).graph ∧ embed u = f ∧ embed v = b := by
  let hd := KFCausalCoherentMomentumFactorL2.coherentSpan_le_pureDomain ε a h hε ha hh hf
  let b := pureMomentum ε hε h ⟨f,hd⟩
  have hB : (f,b) ∈ (pureMomentum ε hε h).graph := (pureMomentum ε hε h).mem_graph ⟨f,hd⟩
  have hu := (energy_domain ε hε h hp hh mass2 quartic vacuum t f).mp
    (KFCausalClockFloorAveragedDensity.coherentSpan_le_energy_domain ε a h hε ha hh hb mass2 quartic vacuum t hf)
  exact hu.elim fun u hu' => (actual_momentum_lift ε h hε hh hb mass2 quartic vacuum t a ha f hf b hB).elim
    fun v hv => ⟨b,u,v,hB,hu',hv⟩

#print axioms weightedOutput_continuous
#print axioms weightedOutput_graph
#print axioms orbitVector_continuous
#print axioms orbitLift_compatibility
#print axioms lift_embedding
#print axioms lift_output_coe
#print axioms lift_pairing
#print axioms actual_momentum_lift
#print axioms actual_momentum_energy_domain
#print axioms coherent_momentum_lifts
end
end UnifiedTheory.Audit.KFCausalCoherentMomentumEnergyLift
