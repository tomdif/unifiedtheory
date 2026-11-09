/- Actual nonconstant charge-orbit second outputs represent the original
averaged Hamiltonian. The output is the integral of the inverse-rotated
weighted second outputs; no zero-charge hypothesis or composite closedness
is used. Concrete displaced packets instantiate these primitive graphs. -/
import UnifiedTheory.Audit.KFCausalFixedStrongHamiltonian

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalAveragedSecondOrbitGraph
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPhysicalCircleAction (action action_joint_continuous action_reverse)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalPhysicalEnergyFactors (modelDirections energyWeight)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalEnergyReverseFactors (reverseFactor factor_pairing)
open KFCausalJointSecondPairing (weighted secondWeighted joint_closure_pairing)
open KFCausalCoherentMomentumEnergyLift (lift lift_output_coe)
open KFCausalClockFloorAveragedEnergy
open KFCausalClockFloorAveragedHamiltonian (hamiltonian hamiltonian_domain_characterization)

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum t : ℝ)
local notation "hp" => hamiltonian_bound ε h hb
local notation "D" => KFCausalClockFloorFormHamiltonian.formData ε hε h hp mass2 quartic vacuum t
local notation "Base" => KFCausalClosedGraphForm.FormSpace D
local notation "J" => KFCausalClosedGraphForm.embedding D
local notation "A" => KFCausalClosedGraphForm.energyOutput D
local notation "Full" => AveragedSpace ε hε h hp hh mass2 quartic vacuum t
local notation "embed" => embedding ε hε h hp hh mass2 quartic vacuum t
local notation "out" => energyOutput ε hε h hp hh mass2 quartic vacuum t
local notation "F" => energyFactor ε hε h modelDirections pointField
local notation "R" => reverseFactor ε hε h modelDirections pointField
local notation "c" => energyWeight mass2 quartic vacuum t

def orbitSecond (z : Fin 8 → ℝ → Hilbert) (θ : ℝ) : Hilbert :=
  action h hh (-(2*Real.pi*θ)) (secondWeighted c (fun i => z i θ))

def secondOutput (z : Fin 8 → ℝ → Hilbert) : Hilbert :=
  ∫ θ, orbitSecond h hh mass2 quartic vacuum t z θ ∂angleMeasure

private theorem weighted_continuous {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (weights : Fin 8 → ℂ) (z : Fin 8 → ℝ → X) (hReverseOrbit : ∀ i, Continuous (z i)) :
    Continuous (fun θ : ℝ => ∑ i : Fin 8, (star (weights i)*weights i) • z i θ) :=
  continuous_finset_sum _ (fun i _ => (hReverseOrbit i).const_smul (star (weights i)*weights i))

theorem orbitSecond_continuous (z : Fin 8 → ℝ → Hilbert)
    (hReverseOrbit : ∀ i, Continuous (z i)) :
    Continuous (orbitSecond h hh mass2 quartic vacuum t z) := by
  have hc : Continuous (fun θ : ℝ => secondWeighted c (fun i => z i θ)) :=
    weighted_continuous c z hReverseOrbit
  have ht : Continuous (fun θ : ℝ => -(2*Real.pi*θ)) :=
    (continuous_const.mul continuous_id).neg
  have hpaircont : Continuous (fun θ : ℝ => (-(2*Real.pi*θ),secondWeighted c (fun i => z i θ))) := ht.prodMk hc
  have hj := (action_joint_continuous h hh).comp hpaircont
  simpa only [Function.comp_def,orbitSecond] using hj

private theorem orbit_form_pairing {H E K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (U : KFCausalUnitaryOrbitAverage.StrongUnitaryGroup H) (T : ℝ)
    (j0 : E →L[ℂ] H) (a0 : E →L[ℂ] K)
    (u v : KFCausalAveragedFormSpace.FormSpace U T j0) (q : ℝ → K) (z : ℝ → H)
    (hu : KFCausalAveragedFormProjection.averagedOutput U T j0 a0 u =ᵐ[angleMeasure] q)
    (hpair : ∀ θ x, inner ℂ (q θ) (a0 x)=inner ℂ (z θ) (j0 x))
    (hi : Integrable (fun θ => U.action (-(T*θ)) (z θ)) angleMeasure) :
    inner ℂ (KFCausalAveragedFormProjection.averagedOutput U T j0 a0 u)
      (KFCausalAveragedFormProjection.averagedOutput U T j0 a0 v) =
      inner ℂ (∫ θ, U.action (-(T*θ)) (z θ) ∂angleMeasure)
        (KFCausalAveragedFormSpace.embedding U T j0 v) := by
  apply (L2.inner_def (𝕜 := ℂ) _ _).trans
  calc
    _ = ∫ θ, inner ℂ (U.action (-(T*θ)) (z θ))
        (KFCausalAveragedFormSpace.embedding U T j0 v) ∂angleMeasure := by
      apply integral_congr_ae
      filter_upwards [hu,a0.coeFn_compLp (KFCausalAveragedFormSpace.sectionMap U T j0 v),
        KFCausalAveragedFormSpace.compatibility_ae U T j0 v] with θ hq hA hJ
      have he := hpair θ (KFCausalAveragedFormSpace.sectionMap U T j0 v θ)
      have hrev : U.action (-(T*θ))
          (U.action (T*θ) (KFCausalAveragedFormSpace.embedding U T j0 v)) =
            KFCausalAveragedFormSpace.embedding U T j0 v := by
        rw [U.compose,add_neg_cancel,U.initial]
      have hinner := (U.action (-(T*θ))).inner_map_map (z θ)
        (U.action (T*θ) (KFCausalAveragedFormSpace.embedding U T j0 v))
      rw [hrev] at hinner
      exact (congrArg₂ (inner ℂ) hq hA).trans
        (he.trans ((congrArg (inner ℂ (z θ)) hJ).trans hinner.symm))
    _ = _ := by
      calc
        _ = ∫ θ, star (inner ℂ (KFCausalAveragedFormSpace.embedding U T j0 v)
            (U.action (-(T*θ)) (z θ))) ∂angleMeasure := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun θ => (inner_conj_symm _ _).symm)
        _ = _ := by
          change (∫ θ, (starRingEnd ℂ) (inner ℂ (KFCausalAveragedFormSpace.embedding U T j0 v)
            (U.action (-(T*θ)) (z θ))) ∂angleMeasure) = _
          rw [integral_conj,integral_inner hi,inner_conj_symm]

variable (f : Hilbert) (g z : Fin 8 → ℝ → Hilbert)
  (hc : ∀ i, Continuous (g i)) (hd : ∀ i, Continuous (z i))
  (hForwardOrbit : ∀ θ i, (action h hh (2*Real.pi*θ) f,g i θ) ∈
    (energyFactor ε hε h modelDirections pointField i).graph)
  (hReverseOrbit : ∀ θ i, (g i θ,z i θ) ∈
    (reverseFactor ε hε h modelDirections pointField i).graph)

include hc hd hForwardOrbit hReverseOrbit in
theorem averaged_pairing (v : Full) :
    inner ℂ (out (lift ε h hε hh hb mass2 quartic vacuum t f g hc hForwardOrbit)) (out v) =
      inner ℂ (secondOutput h hh mass2 quartic vacuum t z) (embed v) := by
  have hm : MemLp (orbitSecond h hh mass2 quartic vacuum t z) 2 angleMeasure :=
    continuous_angle_memLp _ (orbitSecond_continuous h hh mass2 quartic vacuum t z hd)
  have hi : Integrable (orbitSecond h hh mass2 quartic vacuum t z) angleMeasure :=
    hm.integrable (by norm_num)
  have hbase (θ : ℝ) (x : Base) :
      inner ℂ (weighted c (fun i => g i θ)) (A x) =
        inner ℂ (secondWeighted c (fun i => z i θ)) (J x) :=
    KFCausalFixedStrongHamiltonian.base_pairing ε h hε hb mass2 quartic vacuum t
      (fun i => g i θ) (fun i => z i θ) (fun i => hReverseOrbit θ i) x
  have hout : out (lift ε h hε hh hb mass2 quartic vacuum t f g hc hForwardOrbit) =ᵐ[angleMeasure]
      fun θ => weighted c (fun i => g i θ) :=
    by
    simpa only [KFCausalCoherentMomentumEnergyLift.weightedOutput,weighted] using
      lift_output_coe ε h hε hh hb mass2 quartic vacuum t f g hc (fun θ i => hForwardOrbit θ i)
  have h0 := orbit_form_pairing (H := Hilbert) (E := Base)
    (K := KFCausalFiniteJointGraph.Output (Fin 8) Hilbert)
    (KFCausalPhysicalCircleAction.group h hh) (2*Real.pi) J A
  have h1 := h0 (lift ε h hε hh hb mass2 quartic vacuum t f g hc hForwardOrbit) v
  have h2 := h1 (fun θ => weighted c (fun i => g i θ))
    (fun θ => secondWeighted c (fun i => z i θ))
  have h3 := h2 hout
  have h4 := h3 hbase
  have hi' : Integrable (fun θ => (KFCausalPhysicalCircleAction.group h hh).action (-(2*Real.pi*θ)) (secondWeighted c (fun i => z i θ))) angleMeasure := by
    simpa only [KFCausalPhysicalCircleAction.group, orbitSecond] using hi
  have hresult := h4 hi'
  exact hresult

include hc hd hForwardOrbit hReverseOrbit in
theorem hamiltonian_graph :
    (f,secondOutput h hh mass2 quartic vacuum t z) ∈
      (hamiltonian ε hε h hh hb mass2 quartic vacuum t).graph := by
  obtain ⟨hf,he⟩ := (hamiltonian_domain_characterization ε hε h hh hb mass2 quartic vacuum t
    (lift ε h hε hh hb mass2 quartic vacuum t f g hc hForwardOrbit)
    (secondOutput h hh mass2 quartic vacuum t z)).mpr
      (averaged_pairing ε h hε hh hb mass2 quartic vacuum t f g z hc hd hForwardOrbit hReverseOrbit)
  exact (LinearPMap.mem_graph_iff _).mpr ⟨⟨f,hf⟩,rfl,he⟩

include hc hd hForwardOrbit hReverseOrbit in
theorem hamiltonian_domain : f ∈ (hamiltonian ε hε h hh hb mass2 quartic vacuum t).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (hamiltonian_graph ε h hε hh hb mass2 quartic vacuum t f g z hc hd hForwardOrbit hReverseOrbit)

#print axioms orbitSecond_continuous
#print axioms averaged_pairing
#print axioms hamiltonian_graph
#print axioms hamiltonian_domain
end
end UnifiedTheory.Audit.KFCausalAveragedSecondOrbitGraph
