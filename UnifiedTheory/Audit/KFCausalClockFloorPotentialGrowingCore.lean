/- Unconditional operator-graph core theorems for the potential Hamiltonian `P`
on the quarter-strip `|h| ≤ π * ε / 4` (including `|h| ≤ π * ε / 6`):
- `Dom(G) = Dom(K_rad) ∩ Dom(P)` is an operator-graph core for `P`.
- `Dom(G) ∩ Dom(clockHalf ε) = Dom(K_rad) ∩ Dom(P) ∩ Dom(clockHalf ε)` is an
  operator-graph core for `P` and is dense in `Hilbert`. -/
import UnifiedTheory.Audit.KFCausalClockFloorPotentialResolventRadialRegularity
import UnifiedTheory.Audit.KFCausalClockFloorPotentialClockCore
import UnifiedTheory.Audit.KFCausalHamiltonianCoreFromSources

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorPotentialGrowingCore
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf clockHalf_selfAdjoint)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorPureClockClockResponse (half_graph)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialYosidaOrderedTransport (inverse_commute)
open KFCausalClockFloorRadialResolventRegularizer (action radial_domain sequence_tendsto)
open KFCausalClockFloorRadialYosidaDomain (operator operator_selfAdjoint)
open KFCausalClockFloorRadialYosidaQuarterStripSector (sixth_le_quarter)
open KFCausalClockFloorPotentialClockResolvent (resolvent resolves resolvent_half_domain)
open KFCausalClockFloorPotentialClockApproximation
  (left_inverse cutoff cutoff_pos approximation approximation_strong)
open KFCausalClockFloorPotentialResolventRadialRegularity
  (resolvent_radial_domain resolvent_growing_domain)
open KFCausalHamiltonianCoreFromSources (graphMap sectorGraph source_graph_closure)

theorem regularizer_inverseL_commute (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (f : Hilbert) :
    inverseL ε hε (action ε hε h N hN f) =
      action ε hε h N hN (inverseL ε hε f) := by
  simp only [action, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, map_sub, map_smul, inverse_commute ε hε h N hN f]

theorem regularizer_clockHalf_domain (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (f : Hilbert) (hf : f ∈ (clockHalf ε).domain) :
    action ε hε h N hN f ∈ (clockHalf ε).domain := by
  let z : Hilbert := clockHalf ε ⟨f, hf⟩
  have hg : (f, z) ∈ (clockHalf ε).graph :=
    (clockHalf ε).mem_graph ⟨f, hf⟩
  have hg' : (action ε hε h N hN f,
      action ε hε h N hN z) ∈ (clockHalf ε).graph := by
    rw [half_graph ε hε] at hg ⊢
    exact (congrArg (action ε hε h N hN) hg).trans
      (regularizer_inverseL_commute ε hε h N hN z).symm
  exact LinearPMap.mem_domain_of_mem_graph hg'

def radialClockDomain (ε : ℝ) (hε : 0 < ε) (h : ℝ) : Submodule ℂ Hilbert :=
  (operator ε hε h).domain ⊓ (clockHalf ε).domain

theorem radialClockDomain_dense (ε : ℝ) (hε : 0 < ε) (h : ℝ) :
    Dense (radialClockDomain ε hε h : Set Hilbert) := by
  have hs : ((clockHalf ε).domain : Set Hilbert) ⊆
      closure (radialClockDomain ε hε h : Set Hilbert) := by
    intro f hf
    exact mem_closure_of_tendsto (sequence_tendsto ε hε h f)
      (Eventually.of_forall fun n =>
        ⟨radial_domain ε hε h ((n : ℝ) + 1) (by positivity) f,
          regularizer_clockHalf_domain ε hε h ((n : ℝ) + 1) (by positivity) f hf⟩)
  intro f
  exact closure_minimal hs isClosed_closure ((clockHalf_selfAdjoint ε).dense_domain f)

theorem radialClockDomain_topologicalClosure (ε : ℝ) (hε : 0 < ε) (h : ℝ) :
    (radialClockDomain ε hε h).topologicalClosure = ⊤ :=
  Submodule.dense_iff_topologicalClosure_eq_top.mp (radialClockDomain_dense ε hε h)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hb : |h| ≤ Real.pi * ε / 3)
  (hh : h ≠ 0) (m g k : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "Kr" => operator ε hε h
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "R" => resolvent ε hε h hh hw m g k

def potentialRadialGraph : Submodule ℂ (Hilbert × Hilbert) :=
  (P).graph ⊓ (Kr).domain.comap (LinearMap.fst ℂ Hilbert Hilbert)

def potentialGrowingGraph : Submodule ℂ (Hilbert × Hilbert) :=
  (P).graph ⊓ (G).domain.comap (LinearMap.fst ℂ Hilbert Hilbert)

def growingClockDomain : Submodule ℂ Hilbert :=
  (G).domain ⊓ (clockHalf ε).domain

def potentialGrowingClockGraph : Submodule ℂ (Hilbert × Hilbert) :=
  (P).graph ⊓ (growingClockDomain ε hε h hb hh m g k).comap (LinearMap.fst ℂ Hilbert Hilbert)

theorem potential_growing_graph_core (hq : |h| ≤ Real.pi * ε / 4) :
    (potentialGrowingGraph ε hε h hb hh m g k).topologicalClosure = (P).graph := by
  have hd : (Kr).domain.topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp (operator_selfAdjoint ε hε h).dense_domain
  have he := source_graph_closure P (R 1) 1
    (resolves ε hε h hh hw m g k 1 zero_lt_one)
    (left_inverse ε hε h hh hw m g k 1 zero_lt_one)
    (KFCausalClosedGraphForm.hamiltonian_closed PD)
    ⊤ (Kr).domain isClosed_univ hd (fun _ _ => trivial) (fun _ _ => trivial)
  have hm : (Kr).domain.map (graphMap (R 1) 1).toLinearMap ≤
      potentialGrowingGraph ε hε h hb hh m g k := by
    rintro p ⟨f, hf, rfl⟩
    obtain ⟨hx, hv⟩ := resolves ε hε h hh hw m g k 1 zero_lt_one f
    exact ⟨(P).mem_graph_iff.mpr ⟨⟨R 1 f, hx⟩, rfl, hv⟩,
      resolvent_growing_domain ε hε h hb hh m g k hq 1 zero_lt_one f hf⟩
  have hc := Submodule.topologicalClosure_mono hm
  rw [he] at hc
  have hs : sectorGraph P ⊤ = (P).graph := by simp [sectorGraph]
  rw [hs] at hc
  exact le_antisymm (Submodule.topologicalClosure_minimal _ (fun _ hp => hp.1)
    (KFCausalClosedGraphForm.hamiltonian_closed PD)) hc

theorem potential_radial_graph_core (hq : |h| ≤ Real.pi * ε / 4) :
    (potentialRadialGraph ε hε h hb hh m g k).topologicalClosure = (P).graph := by
  have hd : (Kr).domain.topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp (operator_selfAdjoint ε hε h).dense_domain
  have he := source_graph_closure P (R 1) 1
    (resolves ε hε h hh hw m g k 1 zero_lt_one)
    (left_inverse ε hε h hh hw m g k 1 zero_lt_one)
    (KFCausalClosedGraphForm.hamiltonian_closed PD)
    ⊤ (Kr).domain isClosed_univ hd (fun _ _ => trivial) (fun _ _ => trivial)
  have hm : (Kr).domain.map (graphMap (R 1) 1).toLinearMap ≤
      potentialRadialGraph ε hε h hb hh m g k := by
    rintro p ⟨f, hf, rfl⟩
    obtain ⟨hx, hv⟩ := resolves ε hε h hh hw m g k 1 zero_lt_one f
    exact ⟨(P).mem_graph_iff.mpr ⟨⟨R 1 f, hx⟩, rfl, hv⟩,
      resolvent_radial_domain ε hε h hb hh m g k hq 1 zero_lt_one f hf⟩
  have hc := Submodule.topologicalClosure_mono hm
  rw [he] at hc
  have hs : sectorGraph P ⊤ = (P).graph := by simp [sectorGraph]
  rw [hs] at hc
  exact le_antisymm (Submodule.topologicalClosure_minimal _ (fun _ hp => hp.1)
    (KFCausalClosedGraphForm.hamiltonian_closed PD)) hc

theorem potential_growing_clockHalf_graph_core (hq : |h| ≤ Real.pi * ε / 4) :
    (potentialGrowingClockGraph ε hε h hb hh m g k).topologicalClosure = (P).graph := by
  have hd := radialClockDomain_topologicalClosure ε hε h
  have he := source_graph_closure P (R 1) 1
    (resolves ε hε h hh hw m g k 1 zero_lt_one)
    (left_inverse ε hε h hh hw m g k 1 zero_lt_one)
    (KFCausalClosedGraphForm.hamiltonian_closed PD)
    ⊤ (radialClockDomain ε hε h) isClosed_univ hd
    (fun _ _ => trivial) (fun _ _ => trivial)
  have hm : (radialClockDomain ε hε h).map (graphMap (R 1) 1).toLinearMap ≤
      potentialGrowingClockGraph ε hε h hb hh m g k := by
    rintro p ⟨f, hf, rfl⟩
    obtain ⟨hx, hv⟩ := resolves ε hε h hh hw m g k 1 zero_lt_one f
    exact ⟨(P).mem_graph_iff.mpr ⟨⟨R 1 f, hx⟩, rfl, hv⟩,
      ⟨resolvent_growing_domain ε hε h hb hh m g k hq 1 zero_lt_one f hf.1,
        resolvent_half_domain ε hε h hh hw m g k 1 zero_lt_one f hf.2⟩⟩
  have hc := Submodule.topologicalClosure_mono hm
  rw [he] at hc
  have hs : sectorGraph P ⊤ = (P).graph := by simp [sectorGraph]
  rw [hs] at hc
  exact le_antisymm (Submodule.topologicalClosure_minimal _ (fun _ hp => hp.1)
    (KFCausalClosedGraphForm.hamiltonian_closed PD)) hc

theorem approximation_growing_domain (hq : |h| ≤ Real.pi * ε / 4)
    (n : ℕ) (f : Hilbert) (hf : f ∈ (Kr).domain) :
    approximation ε hε h hh hw m g k n f ∈ (G).domain :=
  ((G).domain.restrictScalars ℝ).smul_mem (cutoff n)
    (resolvent_growing_domain ε hε h hb hh m g k hq (cutoff n) (cutoff_pos n) f hf)

theorem approximation_growingClockDomain (hq : |h| ≤ Real.pi * ε / 4)
    (n : ℕ) (f : Hilbert) (hf : f ∈ radialClockDomain ε hε h) :
    approximation ε hε h hh hw m g k n f ∈ growingClockDomain ε hε h hb hh m g k :=
  ⟨approximation_growing_domain ε hε h hb hh m g k hq n f hf.1,
    ((clockHalf ε).domain.restrictScalars ℝ).smul_mem (cutoff n)
      (resolvent_half_domain ε hε h hh hw m g k (cutoff n) (cutoff_pos n) f hf.2)⟩

theorem growing_domain_dense (hq : |h| ≤ Real.pi * ε / 4) :
    Dense ((G).domain : Set Hilbert) := by
  have hs : ((Kr).domain : Set Hilbert) ⊆ closure ((G).domain : Set Hilbert) := by
    intro f hf
    exact mem_closure_of_tendsto (approximation_strong ε hε h hh hw m g k f)
      (Eventually.of_forall fun n =>
        approximation_growing_domain ε hε h hb hh m g k hq n f hf)
  intro f
  exact closure_minimal hs isClosed_closure ((operator_selfAdjoint ε hε h).dense_domain f)

theorem growing_clockHalf_domain_dense (hq : |h| ≤ Real.pi * ε / 4) :
    Dense (growingClockDomain ε hε h hb hh m g k : Set Hilbert) := by
  have hs : (radialClockDomain ε hε h : Set Hilbert) ⊆
      closure (growingClockDomain ε hε h hb hh m g k : Set Hilbert) := by
    intro f hf
    exact mem_closure_of_tendsto (approximation_strong ε hε h hh hw m g k f)
      (Eventually.of_forall fun n =>
        approximation_growingClockDomain ε hε h hb hh m g k hq n f hf)
  intro f
  exact closure_minimal hs isClosed_closure (radialClockDomain_dense ε hε h f)

theorem potential_growing_graph_core_sixth (hs : |h| ≤ Real.pi * ε / 6) :
    (potentialGrowingGraph ε hε h hb hh m g k).topologicalClosure = (P).graph :=
  potential_growing_graph_core ε hε h hb hh m g k (sixth_le_quarter ε hε h hs)

theorem potential_growing_clockHalf_graph_core_sixth (hs : |h| ≤ Real.pi * ε / 6) :
    (potentialGrowingClockGraph ε hε h hb hh m g k).topologicalClosure = (P).graph :=
  potential_growing_clockHalf_graph_core ε hε h hb hh m g k (sixth_le_quarter ε hε h hs)

#print axioms regularizer_inverseL_commute
#print axioms regularizer_clockHalf_domain
#print axioms radialClockDomain_dense
#print axioms radialClockDomain_topologicalClosure
#print axioms potential_growing_graph_core
#print axioms potential_radial_graph_core
#print axioms potential_growing_clockHalf_graph_core
#print axioms approximation_growing_domain
#print axioms approximation_growingClockDomain
#print axioms growing_domain_dense
#print axioms growing_clockHalf_domain_dense
#print axioms potential_growing_graph_core_sixth
#print axioms potential_growing_clockHalf_graph_core_sixth
end
end UnifiedTheory.Audit.KFCausalClockFloorPotentialGrowingCore
