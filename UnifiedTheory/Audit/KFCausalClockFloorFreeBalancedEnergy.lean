/- The balanced full-operator graph for zero mass, quartic and vacuum
couplings. The inactive outputs vanish on the completed form, as a
consequence of the original weighted factor graphs. Four kinetic outputs
remain; their oscillator spectral interpretation is not assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorBalancedHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorFreeBalancedEnergy
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorAveragedFormTransport
open KFCausalClockFloorAveragedSqueezeEnergy (OutputSpace coordinate coordinateLp)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorBalancedSqueeze (balancedPairing balancedPairing_explicit)
open KFCausalClockFloorBalancedHamiltonian (BalancedGraph)
open KFCausalClockFloorAveragedHamiltonian (graphFormVector_surjective)
open KFCausalPhysicalEnergyFactors (modelDirections energyWeight)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalUnitIntervalOrbit (angleMeasure)

private theorem free_weight_zero (t : ℝ) (i : Fin 8) (hi : 5 ≤ i.val) :
    energyWeight 0 0 0 t i = 0 := by
  fin_cases i <;> simp_all [energyWeight]

private theorem pairing_inactive (t : ℝ) (x y : OutputSpace)
    (h5 : coordinateLp 5 x = 0) (h6 : coordinateLp 6 x = 0) (h7 : coordinateLp 7 x = 0) :
    balancedPairing t x y = inner ℂ (coordinateLp 0 x) (coordinateLp 0 y)+
      (Real.exp t:ℂ)*(inner ℂ (coordinateLp 1 x) (coordinateLp 1 y)+
        inner ℂ (coordinateLp 2 x) (coordinateLp 2 y)+
        inner ℂ (coordinateLp 3 x) (coordinateLp 3 y)+
        inner ℂ (coordinateLp 4 x) (coordinateLp 4 y)) := by
  simpa only [h5,h6,h7,inner_zero_left,add_zero,mul_zero] using
    balancedPairing_explicit t x y

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "B" => KFCausalClockFloorFormHamiltonian.formData ε hε h
  (hamiltonian_bound ε h hb) 0 0 0
local notation "V" => FormSpace ε hε h hne hb 0 0 0
local notation "J" => embedding ε hε h hne hb 0 0 0
local notation "A" => energyOutput ε hε h hne hb 0 0 0

private theorem base_inactive (t : ℝ) (u : KFCausalClosedGraphForm.FormSpace (B t))
    (i : Fin 8) (hi : 5 ≤ i.val) : KFCausalClosedGraphForm.energyOutput (B t) u i = 0 := by
  have hg := KFCausalClockFloorJointEnergy.closedEnergy_component_graph ε hε h
    modelDirections pointField 0 0 0 t (hamiltonian_bound ε h hb)
    (KFCausalClosedGraphForm.embedding (B t) u)
    (KFCausalClosedGraphForm.energyOutput (B t) u) u.property i
  rw [free_weight_zero t i hi,zero_smul] at hg
  exact (KFCausalClockFloorCommonDomain.energyFactor ε hε h modelDirections pointField i).closure.mem_graph_snd_inj'
    hg (Submodule.zero_mem _) rfl

theorem inactive_output (t : ℝ) (u : V t) (i : Fin 8) (hi : 5 ≤ i.val) :
    coordinateLp i (A t u) = 0 := by
  obtain ⟨v,rfl⟩ := graphFormVector_surjective ε hε h hne hb 0 0 0 t u
  let E := KFCausalClosedGraphForm.energyOutput (B t)
  let L := KFCausalClockFloorAveragedEnergy.sectionMap ε hε h
    (hamiltonian_bound ε h hb) hne 0 0 0 t v
  change coordinateLp i (E.compLp L) = 0
  apply Lp.ext
  filter_upwards [(coordinate i).coeFn_compLp (E.compLp L),E.coeFn_compLp L,
    Lp.coeFn_zero (E := Hilbert) (p := 2) (μ := angleMeasure)] with θ hc he hz
  change (coordinate i).compLp (E.compLp L) θ = _
  rw [hc,he,hz]
  exact base_inactive ε hε h hb t (L θ) i hi

/-- Only the clock and the four actual kinetic outputs survive at zero couplings. -/
def freePairing (t : ℝ) (u v : V 0) : ℂ :=
  inner ℂ (coordinateLp 0 (A 0 u)) (coordinateLp 0 (A 0 v))+
    (Real.exp t:ℂ)*(inner ℂ (coordinateLp 1 (A 0 u)) (coordinateLp 1 (A 0 v))+
      inner ℂ (coordinateLp 2 (A 0 u)) (coordinateLp 2 (A 0 v))+
      inner ℂ (coordinateLp 3 (A 0 u)) (coordinateLp 3 (A 0 v))+
      inner ℂ (coordinateLp 4 (A 0 u)) (coordinateLp 4 (A 0 v)))

theorem balancedPairing_free (t : ℝ) (u v : V 0) :
    balancedPairing t (A 0 u) (A 0 v) = freePairing ε hε h hne hb t u v :=
  pairing_inactive t (A 0 u) (A 0 v)
    (inactive_output ε hε h hne hb 0 u 5 (by decide))
    (inactive_output ε hε h hne hb 0 u 6 (by decide))
    (inactive_output ε hε h hne hb 0 u 7 (by decide))

theorem free_hamiltonian_graph_iff (t : ℝ) (f g : Hilbert) :
    (KFCausalPairedSqueezeTransport.transport ((-1/2)*t) f,
      KFCausalPairedSqueezeTransport.transport ((-1/2)*t) g) ∈
        (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hne hb 0 0 0 t).graph ↔
      ∃ u : V 0, J 0 u = f ∧ ∀ v : V 0,
        freePairing ε hε h hne hb t u v = inner ℂ g (J 0 v) := by
  apply (KFCausalClockFloorBalancedHamiltonian.hamiltonian_graph_iff
    ε hε h hne hb 0 0 0 t f g).trans
  constructor
  · rintro ⟨u,hu,hpair⟩
    exact ⟨u,hu,fun v => (balancedPairing_free ε hε h hne hb t u v).symm.trans (hpair v)⟩
  · rintro ⟨u,hu,hpair⟩
    exact ⟨u,hu,fun v => (balancedPairing_free ε hε h hne hb t u v).trans (hpair v)⟩

#print axioms inactive_output
#print axioms balancedPairing_free
#print axioms free_hamiltonian_graph_iff
end
end UnifiedTheory.Audit.KFCausalClockFloorFreeBalancedEnergy
