/- Unconditional Gaussian clock-core regularization and simultaneous
operator-graph cores for the growing Hamiltonian G and the ordered-potential
Hamiltonian P for all real couplings m, g, k ∈ ℝ:
1. Under |h| ≤ π * ε / 3, the smooth Gaussian growing clock core
   growingClockCore := Dom(G) ∩ Dom(clockOperator ε) ∩ Dom(clockHalf ε)
   equals (Dom(K) ∩ Dom(P)) ∩ Dom(clockOperator ε) ∩ Dom(clockHalf ε),
   embeds into all eight growing, radial, potential, form, and clock domains,
   is invariant under nonnegative clock-Gaussian multipliers, and contains
   action ε a ha.le 0 x for every x ∈ Dom(G) and a > 0.
2. Along a_n = ((n : ℝ) + 1)⁻¹, action ε a_n _ 0 x ∈ growingClockCore converges
   simultaneously in Dom(G), Dom(K), and Dom(P) graphs to (x, G x), (x, K x),
   and (x, P x), making growingClockCore an unconditional operator-graph core
   for G for all real m, g, k.
3. Under |h| ≤ π * ε / 4 (and |h| ≤ π * ε / 6), combining Gaussian graph
   approximation on Dom(G) with potential_growing_graph_core establishes that
   growingClockCore is simultaneously an unconditional operator-graph core for
   both G and P and is dense in Hilbert for all real m, g, k. -/
import UnifiedTheory.Audit.KFCausalClockFloorPotentialGrowingCore
import UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumHamiltonianGaussianCore
import UnifiedTheory.Audit.KFCausalClockFloorGaussianClockCommutation

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGrowingPotentialGaussianClockCore

noncomputable section

open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorClockOperator (clockOperator)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialYosidaQuarterStripSector (sixth_le_quarter)
open KFCausalClockFloorGaussianGrowingTransport (action)
open KFCausalClockFloorGaussianGrowingApproximation (sequence_tendsto)
open KFCausalClockFloorGaussianGrowingRadialPairing (radial_gaussian_graph)
open KFCausalClockFloorGaussianPotentialDomain (gaussian_graph_of_mem)
open KFCausalClockFloorGaussianMultiOperatorApproximation (growing_sum_graph)
open KFCausalClockFloorGaussianClockCommutation
  (gaussian_clockHalf_graph gaussian_clockHalf_domain
   gaussian_clockOperator_graph gaussian_clockOperator_domain
   gaussian_mem_clockOperator_domain_of_pos gaussian_mem_clockHalf_domain_of_pos)
open KFCausalClockFloorPositiveVacuumTwoTimeOperatorDomain
  (three_operator_domain_le_clockHalf_domain unconditional_two_operator_growing_eval)
open KFCausalClockFloorPositiveVacuumHamiltonianGaussianCore
  (positiveVacuumClockCore unconditionalClockCore)
open KFCausalClockFloorPotentialGrowingCore
  (growingClockDomain potentialGrowingGraph potential_growing_graph_core growing_domain_dense)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "GD" => KFCausalClockFloorGrowingHamiltonian.formData ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "Kroot" => KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Tgrow" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k

/-! ### 1. Definition and Domain Identifications of `growingClockCore` -/

/-- The smooth Gaussian growing clock core: vectors in `Dom(G)` that also lie in
both the full clock domain `Dom(clockOperator ε)` and the half-clock domain `Dom(clockHalf ε)`. -/
def growingClockCore : Submodule ℂ Hilbert :=
  (G).domain ⊓ (clockOperator ε hε).domain ⊓ (clockHalf ε).domain

/-- The graph of `G` restricted to `growingClockCore`. -/
def growingClockCoreGraph : Submodule ℂ (Hilbert × Hilbert) :=
  (G).graph ⊓ (growingClockCore ε hε h hh hb m g k).comap (LinearMap.fst ℂ Hilbert Hilbert)

/-- The graph of `P` restricted to `growingClockCore`. -/
def potentialGrowingClockCoreGraph : Submodule ℂ (Hilbert × Hilbert) :=
  (P).graph ⊓ (growingClockCore ε hε h hh hb m g k).comap (LinearMap.fst ℂ Hilbert Hilbert)

/-- The graph of `K` restricted to `growingClockCore`. -/
def radialGrowingClockCoreGraph : Submodule ℂ (Hilbert × Hilbert) :=
  (K).graph ⊓ (growingClockCore ε hε h hh hb m g k).comap (LinearMap.fst ℂ Hilbert Hilbert)

/-- Unconditional identification `(G).domain = (K).domain ⊓ (P).domain`. -/
theorem growing_domain_eq_radial_inf_potential :
    (G).domain = (K).domain ⊓ (P).domain := by
  ext x
  exact KFCausalClockFloorGrowingPotentialSum.domain_iff ε hε h hh hb m g k x

/-- `growingClockCore` equals `((K).domain ⊓ (P).domain) ⊓ (clockOperator ε hε).domain ⊓ (clockHalf ε).domain`. -/
theorem growingClockCore_eq_radial_inf_potential_clock :
    growingClockCore ε hε h hh hb m g k =
      ((K).domain ⊓ (P).domain) ⊓ (clockOperator ε hε).domain ⊓ (clockHalf ε).domain := by
  unfold growingClockCore
  rw [growing_domain_eq_radial_inf_potential ε hε h hh hb m g k]

/-- `growingClockCore` is the intersection of `growingClockDomain = (G).domain ⊓ (clockHalf ε).domain`
with `(clockOperator ε hε).domain`. -/
theorem growingClockCore_eq_growingClockDomain_inf_clockOperator :
    growingClockCore ε hε h hh hb m g k =
      growingClockDomain ε hε h hb hh m g k ⊓ (clockOperator ε hε).domain := by
  ext x
  simp only [growingClockCore, growingClockDomain, Submodule.mem_inf]
  tauto

/-- `growingClockCore` is contained in `growingClockDomain`. -/
theorem growingClockCore_le_growingClockDomain :
    growingClockCore ε hε h hh hb m g k ≤ growingClockDomain ε hε h hb hh m g k :=
  fun _ hx => ⟨hx.1.1, hx.2⟩

/-- `unconditionalClockCore` is contained in `growingClockCore` for all real couplings. -/
theorem unconditionalClockCore_le_growingClockCore :
    unconditionalClockCore ε hε h hh hb m g k ≤ growingClockCore ε hε h hh hb m g k :=
  fun _ hx =>
    ⟨⟨KFCausalClockFloorUnconditionalTwoTimeEvolution.common_domain_subset_growing
        ε hε h hh hb m g k hx.1.1,
      hx.1.2⟩,
     hx.2⟩

/-- `positiveVacuumClockCore` is contained in `growingClockCore` for all real couplings. -/
theorem positiveVacuumClockCore_le_growingClockCore :
    positiveVacuumClockCore ε hε h hh hb m g k ≤ growingClockCore ε hε h hh hb m g k :=
  fun x hx =>
    ⟨⟨(KFCausalClockFloorGrowingPotentialSum.domain_iff ε hε h hh hb m g k x).mpr
        ⟨hx.1.1.1.2, hx.1.1.2⟩,
      hx.1.2⟩,
     hx.2⟩

/-- Every `x ∈ growingClockCore` lies simultaneously in all eight operator, form, and clock
domains: `(G).domain`, `(K).domain`, `(P).domain`, `(Tgrow).domain`, `(Kroot).domain`,
`(Tpot).domain`, `(clockOperator ε hε).domain`, and `(clockHalf ε).domain`. -/
theorem growingClockCore_mem_all_domains
    {x : Hilbert} (hx : x ∈ growingClockCore ε hε h hh hb m g k) :
    x ∈ (G).domain ∧
    x ∈ (K).domain ∧
    x ∈ (P).domain ∧
    x ∈ (Tgrow).domain ∧
    x ∈ (Kroot).domain ∧
    x ∈ (Tpot).domain ∧
    x ∈ (clockOperator ε hε).domain ∧
    x ∈ (clockHalf ε).domain := by
  have hxG : x ∈ (G).domain := hx.1.1
  have hxKP := (KFCausalClockFloorGrowingPotentialSum.domain_iff ε hε h hh hb m g k x).mp hxG
  exact ⟨hxG, hxKP.1, hxKP.2,
    KFCausalClockFloorUnconditionalOperatorFormEnergy.growing_mem_growingForm_domain
      ε hε h hh hb m g k ⟨x, hxG⟩,
    KFCausalClockFloorUnconditionalOperatorFormEnergy.growing_mem_radialRoot_domain
      ε hε h hh hb m g k ⟨x, hxG⟩,
    KFCausalClockFloorUnconditionalOperatorFormEnergy.growing_mem_potentialForm_domain
      ε hε h hh hb m g k ⟨x, hxG⟩,
    hx.1.2, hx.2⟩

/-- For every `x ∈ (G).domain`, `G ⟨x, hx⟩ = K ⟨x, hxK⟩ + P ⟨x, hxP⟩`. -/
theorem growing_apply_eq_radial_add_potential
    {x : Hilbert} (hx : x ∈ (G).domain) :
    let hxKP := (KFCausalClockFloorGrowingPotentialSum.domain_iff ε hε h hh hb m g k x).mp hx
    G ⟨x, hx⟩ = K ⟨x, hxKP.1⟩ + P ⟨x, hxKP.2⟩ := by
  intro hxKP
  exact (unconditional_two_operator_growing_eval
    ε hε h hh hb m g k hxKP.1 hxKP.2).choose_spec

/-! ### 2. Clock-Gaussian Regularization into `growingClockCore` -/

/-- For any `x ∈ (G).domain` and `a ≥ 0`, centered clock-Gaussian multiplication preserves
`(K).graph`, `(P).graph`, and `(G).graph`. -/
theorem gaussian_growing_graphs_of_nonneg
    (a : ℝ) (ha : 0 ≤ a) {x : Hilbert} (hx : x ∈ (G).domain) :
    let hxKP := (KFCausalClockFloorGrowingPotentialSum.domain_iff ε hε h hh hb m g k x).mp hx
    (action ε a ha 0 x, action ε a ha 0 (K ⟨x, hxKP.1⟩)) ∈ (K).graph ∧
    (action ε a ha 0 x, action ε a ha (-h) (P ⟨x, hxKP.2⟩)) ∈ (P).graph ∧
    (action ε a ha 0 x,
      action ε a ha 0 (K ⟨x, hxKP.1⟩) + action ε a ha (-h) (P ⟨x, hxKP.2⟩)) ∈ (G).graph := by
  intro hxKP
  have hr : (x, K ⟨x, hxKP.1⟩) ∈ (K).graph := (K).mem_graph ⟨x, hxKP.1⟩
  have hp : (x, P ⟨x, hxKP.2⟩) ∈ (P).graph := (P).mem_graph ⟨x, hxKP.2⟩
  exact ⟨radial_gaussian_graph ε hε a ha h 0 x (K ⟨x, hxKP.1⟩) hr,
    gaussian_graph_of_mem ε hε h hh hw m g k a ha x (P ⟨x, hxKP.2⟩) hp,
    growing_sum_graph ε hε h hh hb m g k a ha x (K ⟨x, hxKP.1⟩) (P ⟨x, hxKP.2⟩) hr hp⟩

/-- For any `x ∈ (G).domain` and `a ≥ 0`, `action ε a ha 0 x` lies in `(G).domain`,
`(K).domain`, and `(P).domain`. -/
theorem gaussian_mem_growing_domain_of_nonneg
    (a : ℝ) (ha : 0 ≤ a) {x : Hilbert} (hx : x ∈ (G).domain) :
    action ε a ha 0 x ∈ (G).domain ∧
    action ε a ha 0 x ∈ (K).domain ∧
    action ε a ha 0 x ∈ (P).domain := by
  have hg := gaussian_growing_graphs_of_nonneg ε hε h hh hb m g k a ha hx
  exact ⟨LinearPMap.mem_domain_of_mem_graph hg.2.2,
    LinearPMap.mem_domain_of_mem_graph hg.1,
    LinearPMap.mem_domain_of_mem_graph hg.2.1⟩

/-- `growingClockCore` is invariant under centered clock-Gaussian multipliers for all `a ≥ 0`. -/
theorem gaussian_growingClockCore_of_nonneg
    (a : ℝ) (ha : 0 ≤ a) {x : Hilbert} (hx : x ∈ growingClockCore ε hε h hh hb m g k) :
    action ε a ha 0 x ∈ growingClockCore ε hε h hh hb m g k :=
  ⟨⟨(gaussian_mem_growing_domain_of_nonneg ε hε h hh hb m g k a ha hx.1.1).1,
    gaussian_clockOperator_domain ε hε a ha 0 x hx.1.2⟩,
   gaussian_clockHalf_domain ε hε a ha 0 x hx.2⟩

/-- For every `x ∈ (G).domain` and strictly positive width `a > 0`, the centered clock-Gaussian
state `action ε a ha.le 0 x` lies in `growingClockCore`. -/
theorem gaussian_mem_growingClockCore_of_pos
    (a : ℝ) (ha : 0 < a) {x : Hilbert} (hx : x ∈ (G).domain) :
    action ε a ha.le 0 x ∈ growingClockCore ε hε h hh hb m g k :=
  ⟨⟨(gaussian_mem_growing_domain_of_nonneg ε hε h hh hb m g k a ha.le hx).1,
    gaussian_mem_clockOperator_domain_of_pos ε hε a ha 0 x⟩,
   gaussian_mem_clockHalf_domain_of_pos ε hε a ha 0 x⟩

/-- For every `x ∈ (K).domain ⊓ (P).domain` and `a > 0`, `action ε a ha.le 0 x` lies in
`growingClockCore`. -/
theorem gaussian_mem_growingClockCore_of_radial_potential_pos
    (a : ℝ) (ha : 0 < a) {x : Hilbert}
    (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    action ε a ha.le 0 x ∈ growingClockCore ε hε h hh hb m g k :=
  gaussian_mem_growingClockCore_of_pos ε hε h hh hb m g k a ha
    ((KFCausalClockFloorGrowingPotentialSum.domain_iff ε hε h hh hb m g k x).mpr ⟨hxK, hxP⟩)

/-- For every `x ∈ (G).domain` and `a > 0`, `action ε a ha.le 0 x` lies in `growingClockCore`
with simultaneous graph memberships in `(G).graph`, `(K).graph`, and `(P).graph` (hence in
`growingClockCoreGraph`, `radialGrowingClockCoreGraph`, and `potentialGrowingClockCoreGraph`). -/
theorem gaussian_growingClockCore_graphs_of_pos
    (a : ℝ) (ha : 0 < a) {x : Hilbert} (hx : x ∈ (G).domain) :
    let hxKP := (KFCausalClockFloorGrowingPotentialSum.domain_iff ε hε h hh hb m g k x).mp hx
    action ε a ha.le 0 x ∈ growingClockCore ε hε h hh hb m g k ∧
    (action ε a ha.le 0 x,
      action ε a ha.le 0 (K ⟨x, hxKP.1⟩) + action ε a ha.le (-h) (P ⟨x, hxKP.2⟩)) ∈
      growingClockCoreGraph ε hε h hh hb m g k ∧
    (action ε a ha.le 0 x, action ε a ha.le 0 (K ⟨x, hxKP.1⟩)) ∈
      radialGrowingClockCoreGraph ε hε h hh hb m g k ∧
    (action ε a ha.le 0 x, action ε a ha.le (-h) (P ⟨x, hxKP.2⟩)) ∈
      potentialGrowingClockCoreGraph ε hε h hh hb m g k := by
  intro hxKP
  have hcore := gaussian_mem_growingClockCore_of_pos ε hε h hh hb m g k a ha hx
  have hgr := gaussian_growing_graphs_of_nonneg ε hε h hh hb m g k a ha.le hx
  exact ⟨hcore, ⟨hgr.2.2, hcore⟩, ⟨hgr.1, hcore⟩, ⟨hgr.2.1, hcore⟩⟩

/-- When `x ∈ (G).domain` and `x ∈ (clockHalf ε).domain`, for every `a > 0` the smoothed vector
`action ε a ha.le 0 x` lies in `growingClockCore` and satisfies simultaneous graph memberships
in `(G).graph`, `(K).graph`, `(P).graph`, and `(clockHalf ε).graph`. -/
theorem gaussian_growingClockCore_clockHalf_graph_of_pos
    (a : ℝ) (ha : 0 < a) {x : Hilbert}
    (hx : x ∈ (G).domain) (hxh : x ∈ (clockHalf ε).domain) :
    let hxKP := (KFCausalClockFloorGrowingPotentialSum.domain_iff ε hε h hh hb m g k x).mp hx
    action ε a ha.le 0 x ∈ growingClockCore ε hε h hh hb m g k ∧
    (action ε a ha.le 0 x,
      action ε a ha.le 0 (K ⟨x, hxKP.1⟩) + action ε a ha.le (-h) (P ⟨x, hxKP.2⟩)) ∈ (G).graph ∧
    (action ε a ha.le 0 x, action ε a ha.le 0 (K ⟨x, hxKP.1⟩)) ∈ (K).graph ∧
    (action ε a ha.le 0 x, action ε a ha.le (-h) (P ⟨x, hxKP.2⟩)) ∈ (P).graph ∧
    (action ε a ha.le 0 x, action ε a ha.le 0 (clockHalf ε ⟨x, hxh⟩)) ∈ (clockHalf ε).graph := by
  intro hxKP
  have hg := gaussian_growingClockCore_graphs_of_pos ε hε h hh hb m g k a ha hx
  have hc := gaussian_clockHalf_graph ε hε a ha.le 0 x (clockHalf ε ⟨x, hxh⟩)
    ((clockHalf ε).mem_graph ⟨x, hxh⟩)
  exact ⟨hg.1, hg.2.1.1, hg.2.2.1.1, hg.2.2.2.1, hc⟩

/-- When `x ∈ (G).domain` and `x ∈ (clockOperator ε hε).domain`, for every `a > 0` the smoothed
vector `action ε a ha.le 0 x` lies in `growingClockCore` and satisfies `(action ε a ha.le 0 x,
action ε a ha.le 0 (clockOperator ε hε ⟨x, hxc⟩)) ∈ (clockOperator ε hε).graph`. -/
theorem gaussian_growingClockCore_clockOperator_graph_of_pos
    (a : ℝ) (ha : 0 < a) {x : Hilbert}
    (hx : x ∈ (G).domain) (hxc : x ∈ (clockOperator ε hε).domain) :
    action ε a ha.le 0 x ∈ growingClockCore ε hε h hh hb m g k ∧
    (action ε a ha.le 0 x, action ε a ha.le 0 (clockOperator ε hε ⟨x, hxc⟩)) ∈
      (clockOperator ε hε).graph :=
  ⟨gaussian_mem_growingClockCore_of_pos ε hε h hh hb m g k a ha hx,
   gaussian_clockOperator_graph ε hε a ha.le 0 x (clockOperator ε hε ⟨x, hxc⟩)
     ((clockOperator ε hε).mem_graph ⟨x, hxc⟩)⟩

/-! ### 3. Sequence Approximation and Simultaneous Graph Cores for `G` and `P` -/

/-- For every `x ∈ (G).domain`, along `a_n = ((n : ℝ) + 1)⁻¹`, the sequence
`action ε a_n _ 0 x` lies in `growingClockCore` for all `n : ℕ` and converges simultaneously
in `(G).graph`, `(K).graph`, and `(P).graph` to `(x, G ⟨x, hx⟩)`, `(x, K ⟨x, hxK⟩)`, and
`(x, P ⟨x, hxP⟩)`. -/
theorem growing_clock_core_sequence_approximation
    {x : Hilbert} (hx : x ∈ (G).domain) :
    let hxKP := (KFCausalClockFloorGrowingPotentialSum.domain_iff ε hε h hh hb m g k x).mp hx
    let r := K ⟨x, hxKP.1⟩
    let z := P ⟨x, hxKP.2⟩
    (∀ n : ℕ,
      action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 x ∈
        growingClockCore ε hε h hh hb m g k ∧
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 x,
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r +
          action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z) ∈
        growingClockCoreGraph ε hε h hh hb m g k ∧
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 x,
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r) ∈
        radialGrowingClockCoreGraph ε hε h hh hb m g k ∧
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 x,
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z) ∈
        potentialGrowingClockCoreGraph ε hε h hh hb m g k) ∧
    Tendsto (fun n : ℕ =>
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 x,
        (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r +
          action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z,
          (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r,
            action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z))))
      atTop (𝓝 (x, (G ⟨x, hx⟩, (r, z)))) := by
  intro hxKP r z
  refine ⟨fun n =>
    gaussian_growingClockCore_graphs_of_pos ε hε h hh hb m g k
      (((n : ℝ) + 1)⁻¹) (by positivity) hx, ?_⟩
  have hx_lim := sequence_tendsto ε 0 x
  have hr_lim := sequence_tendsto ε 0 r
  have hz_lim := sequence_tendsto ε (-h) z
  have hG_eq : r + z = G ⟨x, hx⟩ :=
    (growing_apply_eq_radial_add_potential ε hε h hh hb m g k hx).symm
  have hg_lim :
      Tendsto (fun n : ℕ =>
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r +
          action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z)
        atTop (𝓝 (G ⟨x, hx⟩)) :=
    hG_eq ▸ hr_lim.add hz_lim
  exact hx_lim.prodMk_nhds (hg_lim.prodMk_nhds (hr_lim.prodMk_nhds hz_lim))

/-- For every `x : (G).domain`, the canonical clock-Gaussian sequence lies in
`growingClockCoreGraph` and converges in `Hilbert × Hilbert` to `((x : Hilbert), G x)`. -/
theorem growing_clock_core_sequence_tendsto_growing_graph (x : (G).domain) :
    let hxKP := (KFCausalClockFloorGrowingPotentialSum.domain_iff
      ε hε h hh hb m g k (x : Hilbert)).mp x.property
    let r := K ⟨(x : Hilbert), hxKP.1⟩
    let z := P ⟨(x : Hilbert), hxKP.2⟩
    (∀ n : ℕ,
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 (x : Hilbert),
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r +
          action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z) ∈
        growingClockCoreGraph ε hε h hh hb m g k) ∧
    Tendsto (fun n : ℕ =>
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 (x : Hilbert),
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r +
          action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z))
      atTop (𝓝 ((x : Hilbert), G x)) := by
  intro hxKP r z
  have happ := growing_clock_core_sequence_approximation ε hε h hh hb m g k x.property
  refine ⟨fun n => (happ.1 n).2.1, ?_⟩
  have hproj : Continuous (fun p : Hilbert × (Hilbert × (Hilbert × Hilbert)) => (p.1, p.2.1)) :=
    continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  exact (hproj.tendsto ((x : Hilbert), (G x, (r, z)))).comp happ.2

/-- For every `x : (G).domain`, the canonical clock-Gaussian sequence lies in
`potentialGrowingClockCoreGraph` and converges in `Hilbert × Hilbert` to
`((x : Hilbert), P ⟨x, hxP⟩)`. -/
theorem growing_clock_core_sequence_tendsto_potential_graph (x : (G).domain) :
    let hxKP := (KFCausalClockFloorGrowingPotentialSum.domain_iff
      ε hε h hh hb m g k (x : Hilbert)).mp x.property
    let z := P ⟨(x : Hilbert), hxKP.2⟩
    (∀ n : ℕ,
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 (x : Hilbert),
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z) ∈
        potentialGrowingClockCoreGraph ε hε h hh hb m g k) ∧
    Tendsto (fun n : ℕ =>
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 (x : Hilbert),
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z))
      atTop (𝓝 ((x : Hilbert), z)) := by
  intro hxKP z
  have happ := growing_clock_core_sequence_approximation ε hε h hh hb m g k x.property
  exact ⟨fun n => (happ.1 n).2.2.2,
    (sequence_tendsto ε 0 (x : Hilbert)).prodMk_nhds (sequence_tendsto ε (-h) z)⟩

/-- Unconditional operator-graph core theorem for `G`: for all real couplings `m, g, k ∈ ℝ`
and `|h| ≤ π * ε / 3`, `growingClockCore` is an operator-graph core for `G`. -/
theorem growing_clock_core_graph_core :
    ((G).graph ⊓ (growingClockCore ε hε h hh hb m g k).comap
      (LinearMap.fst ℂ Hilbert Hilbert)).topologicalClosure = (G).graph := by
  change (growingClockCoreGraph ε hε h hh hb m g k).topologicalClosure = (G).graph
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _ inf_le_left
      (KFCausalClosedGraphForm.hamiltonian_closed GD)
  · rintro ⟨f, y⟩ hfy
    let x : (G).domain := ⟨f, LinearPMap.mem_domain_of_mem_graph hfy⟩
    have hy : G x = y := (G).mem_graph_snd_inj' ((G).mem_graph x) hfy rfl
    have hseq := growing_clock_core_sequence_tendsto_growing_graph ε hε h hh hb m g k x
    have hlim :
        Tendsto (fun n : ℕ =>
          (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
            action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0
              (K ⟨f, ((KFCausalClockFloorGrowingPotentialSum.domain_iff
                ε hε h hh hb m g k f).mp x.property).1⟩) +
              action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h)
                (P ⟨f, ((KFCausalClockFloorGrowingPotentialSum.domain_iff
                  ε hε h hh hb m g k f).mp x.property).2⟩)))
          atTop (𝓝 (f, y)) := by
      simpa only [x, hy] using hseq.2
    exact mem_closure_iff_seq_limit.mpr ⟨_, hseq.1, hlim⟩

/-- Every pair in `potentialGrowingGraph = (P).graph ⊓ (G).domain.comap fst` lies in the
topological closure of `potentialGrowingClockCoreGraph`. -/
theorem potentialGrowingGraph_le_potentialGrowingClockCoreGraph_closure :
    potentialGrowingGraph ε hε h hb hh m g k ≤
      (potentialGrowingClockCoreGraph ε hε h hh hb m g k).topologicalClosure := by
  rintro ⟨f, z⟩ ⟨hfz, hfG⟩
  change f ∈ (G).domain at hfG
  let x : (G).domain := ⟨f, hfG⟩
  have hxP : f ∈ (P).domain :=
    ((KFCausalClockFloorGrowingPotentialSum.domain_iff ε hε h hh hb m g k f).mp hfG).2
  have hz : P ⟨f, hxP⟩ = z := (P).mem_graph_snd_inj' ((P).mem_graph ⟨f, hxP⟩) hfz rfl
  have hseq := growing_clock_core_sequence_tendsto_potential_graph ε hε h hh hb m g k x
  have hlim :
      Tendsto (fun n : ℕ =>
        (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
          action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) (P ⟨f, hxP⟩)))
        atTop (𝓝 (f, z)) := by
    simpa only [x, hz] using hseq.2
  exact mem_closure_iff_seq_limit.mpr ⟨_, hseq.1, hlim⟩

/-- Unconditional operator-graph core theorem for `P` on the quarter-strip `|h| ≤ π * ε / 4`:
for all real couplings `m, g, k ∈ ℝ`, `growingClockCore` is an operator-graph core for `P`. -/
theorem potential_growing_clock_core_graph_core (hq : |h| ≤ Real.pi * ε / 4) :
    ((P).graph ⊓ (growingClockCore ε hε h hh hb m g k).comap
      (LinearMap.fst ℂ Hilbert Hilbert)).topologicalClosure = (P).graph := by
  change (potentialGrowingClockCoreGraph ε hε h hh hb m g k).topologicalClosure = (P).graph
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _ inf_le_left
      (KFCausalClosedGraphForm.hamiltonian_closed PD)
  · have hcl := Submodule.topologicalClosure_minimal _
      (potentialGrowingGraph_le_potentialGrowingClockCoreGraph_closure ε hε h hh hb m g k)
      (potentialGrowingClockCoreGraph ε hε h hh hb m g k).isClosed_topologicalClosure
    rwa [potential_growing_graph_core ε hε h hb hh m g k hq] at hcl

/-- Unconditional operator-graph core theorem for `P` on the sixth-strip `|h| ≤ π * ε / 6`. -/
theorem potential_growing_clock_core_graph_core_sixth (hs : |h| ≤ Real.pi * ε / 6) :
    ((P).graph ⊓ (growingClockCore ε hε h hh hb m g k).comap
      (LinearMap.fst ℂ Hilbert Hilbert)).topologicalClosure = (P).graph :=
  potential_growing_clock_core_graph_core ε hε h hh hb m g k (sixth_le_quarter ε hε h hs)

/-- Under `|h| ≤ π * ε / 4`, `growingClockCore` is simultaneously an unconditional
operator-graph core for both `G` and `P` for all real couplings `m, g, k ∈ ℝ`. -/
theorem growing_and_potential_simultaneous_clock_core (hq : |h| ≤ Real.pi * ε / 4) :
    ((G).graph ⊓ (growingClockCore ε hε h hh hb m g k).comap
      (LinearMap.fst ℂ Hilbert Hilbert)).topologicalClosure = (G).graph ∧
    ((P).graph ⊓ (growingClockCore ε hε h hh hb m g k).comap
      (LinearMap.fst ℂ Hilbert Hilbert)).topologicalClosure = (P).graph :=
  ⟨growing_clock_core_graph_core ε hε h hh hb m g k,
   potential_growing_clock_core_graph_core ε hε h hh hb m g k hq⟩

/-- Under `|h| ≤ π * ε / 6`, `growingClockCore` is simultaneously an unconditional
operator-graph core for both `G` and `P` for all real couplings `m, g, k ∈ ℝ`. -/
theorem growing_and_potential_simultaneous_clock_core_sixth (hs : |h| ≤ Real.pi * ε / 6) :
    ((G).graph ⊓ (growingClockCore ε hε h hh hb m g k).comap
      (LinearMap.fst ℂ Hilbert Hilbert)).topologicalClosure = (G).graph ∧
    ((P).graph ⊓ (growingClockCore ε hε h hh hb m g k).comap
      (LinearMap.fst ℂ Hilbert Hilbert)).topologicalClosure = (P).graph :=
  growing_and_potential_simultaneous_clock_core ε hε h hh hb m g k (sixth_le_quarter ε hε h hs)

/-- Under `|h| ≤ π * ε / 4`, `growingClockCore` is dense in `Hilbert` for all real couplings
`m, g, k ∈ ℝ`. -/
theorem growingClockCore_dense (hq : |h| ≤ Real.pi * ε / 4) :
    Dense (growingClockCore ε hε h hh hb m g k : Set Hilbert) := by
  have hs : ((G).domain : Set Hilbert) ⊆
      closure (growingClockCore ε hε h hh hb m g k : Set Hilbert) := by
    intro f hf
    exact mem_closure_of_tendsto (sequence_tendsto ε 0 f)
      (Eventually.of_forall fun n =>
        gaussian_mem_growingClockCore_of_pos ε hε h hh hb m g k
          (((n : ℝ) + 1)⁻¹) (by positivity) hf)
  intro f
  exact closure_minimal hs isClosed_closure (growing_domain_dense ε hε h hb hh m g k hq f)

/-- Under `|h| ≤ π * ε / 4`, the topological closure of `growingClockCore` in `Hilbert` is `⊤`. -/
theorem growingClockCore_topologicalClosure (hq : |h| ≤ Real.pi * ε / 4) :
    (growingClockCore ε hε h hh hb m g k).topologicalClosure = ⊤ :=
  Submodule.dense_iff_topologicalClosure_eq_top.mp
    (growingClockCore_dense ε hε h hh hb m g k hq)

#print axioms growing_domain_eq_radial_inf_potential
#print axioms growingClockCore_eq_radial_inf_potential_clock
#print axioms growingClockCore_eq_growingClockDomain_inf_clockOperator
#print axioms growingClockCore_le_growingClockDomain
#print axioms unconditionalClockCore_le_growingClockCore
#print axioms positiveVacuumClockCore_le_growingClockCore
#print axioms growingClockCore_mem_all_domains
#print axioms growing_apply_eq_radial_add_potential
#print axioms gaussian_growing_graphs_of_nonneg
#print axioms gaussian_mem_growing_domain_of_nonneg
#print axioms gaussian_growingClockCore_of_nonneg
#print axioms gaussian_mem_growingClockCore_of_pos
#print axioms gaussian_mem_growingClockCore_of_radial_potential_pos
#print axioms gaussian_growingClockCore_graphs_of_pos
#print axioms gaussian_growingClockCore_clockHalf_graph_of_pos
#print axioms gaussian_growingClockCore_clockOperator_graph_of_pos
#print axioms growing_clock_core_sequence_approximation
#print axioms growing_clock_core_sequence_tendsto_growing_graph
#print axioms growing_clock_core_sequence_tendsto_potential_graph
#print axioms growing_clock_core_graph_core
#print axioms potentialGrowingGraph_le_potentialGrowingClockCoreGraph_closure
#print axioms potential_growing_clock_core_graph_core
#print axioms potential_growing_clock_core_graph_core_sixth
#print axioms growing_and_potential_simultaneous_clock_core
#print axioms growing_and_potential_simultaneous_clock_core_sixth
#print axioms growingClockCore_dense
#print axioms growingClockCore_topologicalClosure

end

end UnifiedTheory.Audit.KFCausalClockFloorGrowingPotentialGaussianClockCore
