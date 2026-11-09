/- Attach the actual interaction operator to the proved circular free spectrum.
The potential-domain condition is retained; no interacting eigenvalues or
unproved equality of the full Hamiltonian and potential domains is assumed. -/
import UnifiedTheory.Audit.KFCausalFreeCircularSpectralDomain
import UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumThreeOperatorDomain
import UnifiedTheory.Audit.KFCausalClockFloorUnconditionalFormDomainSynthesis

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCircularInteractingBridge
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalFreeCircularSpectral (transform fiberEnergy)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hpos : 0 < h)
  (hb : |h| ≤ Real.pi*ε/3) (m g k : ℝ) (hk : 0 < k) (t : ℝ)
local notation "hw" => KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hpos.ne' hw m g k t
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hpos.ne' hw m g k
local notation "F" => KFCausalFreeCircularSpectral.hamiltonian ε hε h hpos hb t
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "S" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "E" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (hamiltonian_bound ε h hw) hpos.ne' m g k t
local notation "Efree" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (hamiltonian_bound ε h hw) hpos.ne' 0 0 0 t
local notation "Epot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hpos.ne' hw m g k

include hk in
/-- The full interacting form domain is the free form domain intersected with
the actual potential form domain. This does not assume operator-domain regularity. -/
theorem form_domain_iff (f : Hilbert) :
    f ∈ (E).domain ↔ f ∈ (Efree).domain ∧ f ∈ (Epot).domain := by
  rw [KFCausalClockFloorUnconditionalFormDomainSynthesis.averaged_domain_time_eq
    ε hε h hpos.ne' hb m g k t 0 f,
    KFCausalClockFloorPositiveVacuumFormReconstruction.root_growing_domain_iff
      ε hε h hpos.ne' hw m g k hk f,
    KFCausalClockFloorGrowingFormReconstruction.growing_domain_iff
      ε hε h hpos.ne' hb m g k f,
    KFCausalClockFloorFreeFormSum.free_form_domain ε hε h hpos.ne' t hb f]
  tauto

include hk in
theorem common_domain_eq : (H).domain ⊓ (P).domain = (F).domain ⊓ (P).domain := by
  rw [KFCausalClockFloorPositiveVacuumThreeOperatorDomain.hamiltonian_potential_domain_eq
    ε hε h hpos.ne' hb m g k t hk]
  ext f
  have he := KFCausalClockFloorFreeOperatorSum.domain_iff ε hε h hpos.ne' hb t f
  change ((f ∈ (S).domain ∧ f ∈ (K).domain) ∧ f ∈ (P).domain) ↔
    (f ∈ (F).domain ∧ f ∈ (P).domain)
  change f ∈ (F).domain ↔ f ∈ (K).domain ∧ f ∈ (S).domain at he
  tauto

include hk in
theorem graph_free_add (f y z : Hilbert) (hf : (f,y) ∈ (F).graph) (hp : (f,z) ∈ (P).graph) :
    (f,y+(Real.exp (2*t):ℂ) • z) ∈ (H).graph := by
  have hd := (KFCausalClockFloorFreeOperatorSum.domain_iff ε hε h hpos.ne' hb t f).mp
    (LinearPMap.mem_domain_of_mem_graph hf)
  let r := K ⟨f,hd.1⟩
  let s := S ⟨f,hd.2⟩
  have hr : (f,r) ∈ (K).graph := (K).mem_graph ⟨f,hd.1⟩
  have hs : (f,s) ∈ (S).graph := (S).mem_graph ⟨f,hd.2⟩
  have he : y=(Real.exp (2*t):ℂ) • r+s := (F).mem_graph_snd_inj' hf
    (KFCausalClockFloorFreeOperatorSum.graph_from_components ε hε h hpos.ne' hb t f r s hr hs) rfl
  have hH := KFCausalClockFloorPositiveVacuumThreeOperatorDomain.three_operator_hamiltonian_graph
    ε hε h hpos.ne' hb m g k t hk f s r z hs hr hp
  have hout : s+(Real.exp (2*t):ℂ) • (r+z) = y+(Real.exp (2*t):ℂ) • z := by
    rw [he,smul_add]
    abel
  rwa [hout] at hH

include hk in
theorem graph_iff_free (f y z : Hilbert) (hp : (f,z) ∈ (P).graph) :
    (f,y) ∈ (H).graph ↔ (f,y-(Real.exp (2*t):ℂ) • z) ∈ (F).graph := by
  constructor
  · intro hy
    have hd : f ∈ (F).domain := by
      have he := Set.ext_iff.mp (congrArg SetLike.coe (common_domain_eq ε hε h hpos hb m g k hk t)) f
      exact (he.mp ⟨LinearPMap.mem_domain_of_mem_graph hy,
        LinearPMap.mem_domain_of_mem_graph hp⟩).1
    let a := F ⟨f,hd⟩
    have ha : (f,a) ∈ (F).graph := (F).mem_graph ⟨f,hd⟩
    have hi := graph_free_add ε hε h hpos hb m g k hk t f a z ha hp
    have he := (H).mem_graph_snd_inj' hy hi rfl
    change y = a+(Real.exp (2*t):ℂ) • z at he
    have he' : y-(Real.exp (2*t):ℂ) • z = a := by rw [he]; abel
    rwa [he']
  · intro hy
    have he := graph_free_add ε hε h hpos hb m g k hk t f _ z hy hp
    simpa only [sub_add_cancel] using he

include hk in
/-- An exact equation with the actual potential output, on its proved domain. -/
theorem coefficient_graph_iff (f y z : Hilbert) (hp : (f,z) ∈ (P).graph) :
    (f,y) ∈ (H).graph ↔ ∀ i,
      transform h hpos t y i-(Real.exp (2*t):ℂ) • transform h hpos t z i =ᵐ[volume]
        fun x => (fiberEnergy ε h t i x:ℂ)*(transform h hpos t f i) x := by
  rw [graph_iff_free ε hε h hpos hb m g k hk t f y z hp,
    KFCausalFreeCircularSpectral.graph_iff ε hε h hpos hb t f _]
  simp only [map_sub,map_smul,lp.coeFn_sub,lp.coeFn_smul,Pi.sub_apply,Pi.smul_apply]

#print axioms common_domain_eq
#print axioms form_domain_iff
#print axioms graph_free_add
#print axioms graph_iff_free
#print axioms coefficient_graph_iff
end
end UnifiedTheory.Audit.KFCausalCircularInteractingBridge
