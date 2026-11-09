/- Unconditional second-power operator-graph cores, resolvent-commutation
identities, Yosida-scaled graph convergence, and 10-domain simultaneous
regularity for the five fundamental Hamiltonians T, P, G, S(t), and H(t) for
all real couplings m, g, k, t ∈ ℝ:
1. For any positive self-adjoint operator A with positive shifted resolvents
   R(a) (a > 0), if x ∈ Dom(A) then R(a) x ∈ Dom(A) and A(R(a) x) = R(a)(A x) ∈ Dom(A),
   so (R(a) x, R(a)(A x)) lies in the second-power graph
   secondPowerGraph A := A.graph ⊓ (A.domain).comap snd.
2. Along a_n = (n : ℝ) + 1, the Yosida-scaled approximants
   x_n := ((n : ℝ) + 1 : ℂ) • R(a_n) x satisfy (x_n, A x_n) ∈ secondPowerGraph A,
   ‖x_n - x‖ = ‖R(a_n)(A x)‖ ≤ a_n⁻¹ ‖A x‖, and (x_n, A x_n) → (x, A x) in A.graph
   for every x ∈ Dom(A), making secondPowerGraph A an operator-graph core for A
   and secondPowerDomain A dense in Hilbert.
3. Instantiating A ∈ {T, P, G, S(t), H(t)} establishes unconditional second-power
   operator-graph cores for all five Hamiltonians and proves that for every
   (x, y) ∈ secondPowerGraph (H t), both x and y = H(t) x lie simultaneously in
   all 10 operator, form, and clock domains. -/
import UnifiedTheory.Audit.KFCausalClockFloorStaticResolventRadialCommutator
import UnifiedTheory.Audit.KFCausalClockFloorEvolvedResolventRegularity

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorSecondPowerOperatorCores

noncomputable section

open Filter
open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalPositiveResolventBounds
  (Resolves point point_value resolvent_apply_norm_bound)
open KFCausalYosidaApproximation (scaled_resolvent_strong_limit)
open KFCausalClockFloorPotentialClockApproximation (cutoff cutoff_pos cutoff_tendsto)
open KFCausalClockFloorStaticResolventRadialCommutator
  (staticOperator_positive staticResolvent staticResolvent_resolves staticResolvent_left_inverse)
open KFCausalClockFloorPositiveVacuumTwoTimeOperatorDomain
  (hamiltonian_domain_le_clockHalf_domain residual_form_domain_time_iff)

/-! ### 1. Abstract Second-Power Operator Graph and Resolvent Core Theory -/

section AbstractSecondPowerCore

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The second-power graph of an unbounded linear operator `A : H →ₗ.[ℂ] H`, consisting of pairs
`(x, y) ∈ A.graph` such that `y = A x ∈ A.domain` (i.e. `x ∈ Dom(A²)`). -/
def secondPowerGraph (A : H →ₗ.[ℂ] H) : Submodule ℂ (H × H) :=
  A.graph ⊓ A.domain.comap (LinearMap.snd ℂ H H)

/-- The second-power domain `Dom(A²)` as the first-coordinate projection of `secondPowerGraph A`. -/
def secondPowerDomain (A : H →ₗ.[ℂ] H) : Submodule ℂ H :=
  (secondPowerGraph A).map (LinearMap.fst ℂ H H)

theorem mem_secondPowerGraph_iff (A : H →ₗ.[ℂ] H) (x y : H) :
    (x, y) ∈ secondPowerGraph A ↔ (x, y) ∈ A.graph ∧ y ∈ A.domain :=
  Iff.rfl

theorem secondPowerDomain_le_domain (A : H →ₗ.[ℂ] H) :
    secondPowerDomain A ≤ A.domain := by
  rintro x ⟨⟨f, y⟩, ⟨hfy, _⟩, rfl⟩
  exact LinearPMap.mem_domain_of_mem_graph hfy

theorem mem_secondPowerDomain_iff (A : H →ₗ.[ℂ] H) (x : H) :
    x ∈ secondPowerDomain A ↔ ∃ hx : x ∈ A.domain, A ⟨x, hx⟩ ∈ A.domain := by
  constructor
  · rintro ⟨⟨f, y⟩, ⟨hfy, hy⟩, rfl⟩
    let hx : f ∈ A.domain := LinearPMap.mem_domain_of_mem_graph hfy
    have heq : A ⟨f, hx⟩ = y := A.mem_graph_snd_inj' (A.mem_graph ⟨f, hx⟩) hfy rfl
    exact ⟨hx, heq.symm ▸ hy⟩
  · rintro ⟨hx, hAx⟩
    exact ⟨(x, A ⟨x, hx⟩), ⟨A.mem_graph ⟨x, hx⟩, hAx⟩, rfl⟩

/-- On `A.domain`, the operator `A` commutes with its positive shifted resolvent `R`:
`A ⟨R x, ...⟩ = R (A x)`. -/
theorem resolvent_commutes_on_domain (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves A R a) (hl : ∀ x : A.domain, R (A x + a • (x : H)) = (x : H))
    (x : A.domain) :
    A (point A R a hr (x : H)) = R (A x) := by
  have hv := point_value A R a hr (x : H)
  have hlin : R (A x) + a • R (x : H) = (x : H) := by
    simpa only [map_add, ContinuousLinearMap.map_smul_of_tower] using hl x
  have hsub : (x : H) - a • R (x : H) = R (A x) :=
    sub_eq_iff_eq_add.mpr hlin.symm
  exact hv.trans hsub

/-- For every `x : A.domain` and `a > 0`, the resolvent pair `(R x, R (A x))` lies in
`secondPowerGraph A = A.graph ⊓ A.domain.comap snd`. -/
theorem resolvent_mem_secondPowerGraph (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves A R a) (hl : ∀ x : A.domain, R (A x + a • (x : H)) = (x : H))
    (x : A.domain) :
    (R (x : H), R (A x)) ∈ secondPowerGraph A := by
  have h1 : (R (x : H), A (point A R a hr (x : H))) ∈ A.graph :=
    A.mem_graph (point A R a hr (x : H))
  rw [resolvent_commutes_on_domain A R a hr hl x] at h1
  exact ⟨h1, (point A R a hr (A x)).property⟩

/-- For every `x : A.domain`, `R x ∈ secondPowerDomain A`. -/
theorem resolvent_mem_secondPowerDomain (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves A R a) (hl : ∀ x : A.domain, R (A x + a • (x : H)) = (x : H))
    (x : A.domain) :
    R (x : H) ∈ secondPowerDomain A :=
  ⟨(R (x : H), R (A x)), resolvent_mem_secondPowerGraph A R a hr hl x, rfl⟩

/-- For every `x : A.domain`, the Yosida-scaled resolvent pair `((a : ℂ) • R x, (a : ℂ) • R (A x))`
lies in `secondPowerGraph A`. -/
theorem scaled_resolvent_mem_secondPowerGraph (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves A R a) (hl : ∀ x : A.domain, R (A x + a • (x : H)) = (x : H))
    (x : A.domain) :
    ((a : ℂ) • R (x : H), (a : ℂ) • R (A x)) ∈ secondPowerGraph A :=
  (secondPowerGraph A).smul_mem (a : ℂ)
    (resolvent_mem_secondPowerGraph A R a hr hl x)

/-- Exact identity `(a : ℂ) • R x - x = - R (A x)` for `x : A.domain`. -/
theorem scaled_resolvent_sub_eq_neg_resolvent (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hl : ∀ x : A.domain, R (A x + a • (x : H)) = (x : H)) (x : A.domain) :
    (a : ℂ) • R (x : H) - (x : H) = -R (A x) := by
  have hlin : R (A x) + (a : ℂ) • R (x : H) = (x : H) := by
    rw [Complex.coe_smul]
    simpa only [map_add, ContinuousLinearMap.map_smul_of_tower] using hl x
  exact (congrArg ((a : ℂ) • R (x : H) - ·) hlin.symm).trans (by abel)

/-- Norm identity `‖(a : ℂ) • R x - x‖ = ‖R (A x)‖` and bound `≤ a⁻¹ * ‖A x‖` on `A.domain`. -/
theorem scaled_resolvent_error_on_domain (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves A R a) (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ z : A.domain, R (A z + a • (z : H)) = (z : H)) (x : A.domain) :
    ‖(a : ℂ) • R (x : H) - (x : H)‖ = ‖R (A x)‖ ∧
    ‖(a : ℂ) • R (x : H) - (x : H)‖ ≤ a⁻¹ * ‖A x‖ := by
  have heq : ‖(a : ℂ) • R (x : H) - (x : H)‖ = ‖R (A x)‖ := by
    rw [scaled_resolvent_sub_eq_neg_resolvent A R a hl x, norm_neg]
  exact ⟨heq, heq.trans_le (resolvent_apply_norm_bound A R a ha hr hp (A x))⟩

/-- If `x ∈ Dom(A²)`, then `‖(a : ℂ) • R (A x) - A x‖ = ‖R (A (A x))‖ ≤ a⁻¹ * ‖A (A x)‖`. -/
theorem scaled_resolvent_output_error_on_secondPowerDomain
    (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves A R a) (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ z : A.domain, R (A z + a • (z : H)) = (z : H))
    (x : A.domain) (hAx : A x ∈ A.domain) :
    ‖(a : ℂ) • R (A x) - A x‖ = ‖R (A ⟨A x, hAx⟩)‖ ∧
    ‖(a : ℂ) • R (A x) - A x‖ ≤ a⁻¹ * ‖A ⟨A x, hAx⟩‖ :=
  scaled_resolvent_error_on_domain A R a ha hr hp hl ⟨A x, hAx⟩

/-- Along `cutoff n = (n : ℝ) + 1`, for every `x : A.domain`, the Yosida-scaled sequence
`(((cutoff n : ℂ) • R (cutoff n) x, (cutoff n : ℂ) • R (cutoff n) (A x)))` lies in
`secondPowerGraph A` and converges to `((x : H), A x)` with explicit `O((n + 1)⁻¹)` error
on the first coordinate. -/
theorem secondPowerGraph_sequence_approximation (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H)
    (hd : Dense (A.domain : Set H))
    (hr : ∀ a, 0 < a → Resolves A (R a) a)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ a, 0 < a → ∀ z : A.domain, R a (A z + a • (z : H)) = (z : H))
    (x : A.domain) :
    (∀ n : ℕ,
      ((cutoff n : ℂ) • R (cutoff n) (x : H),
        (cutoff n : ℂ) • R (cutoff n) (A x)) ∈ secondPowerGraph A ∧
      ‖(cutoff n : ℂ) • R (cutoff n) (x : H) - (x : H)‖ = ‖R (cutoff n) (A x)‖ ∧
      ‖(cutoff n : ℂ) • R (cutoff n) (x : H) - (x : H)‖ ≤ (cutoff n)⁻¹ * ‖A x‖) ∧
    Tendsto (fun n : ℕ =>
      ((cutoff n : ℂ) • R (cutoff n) (x : H),
        (cutoff n : ℂ) • R (cutoff n) (A x)))
      atTop (𝓝 ((x : H), A x)) := by
  refine ⟨fun n => ?_, ?_⟩
  · have hpos := cutoff_pos n
    have herr :=
      scaled_resolvent_error_on_domain A (R (cutoff n)) (cutoff n) hpos
        (hr (cutoff n) hpos) hp (hl (cutoff n) hpos) x
    exact ⟨scaled_resolvent_mem_secondPowerGraph A (R (cutoff n)) (cutoff n)
      (hr (cutoff n) hpos) (hl (cutoff n) hpos) x, herr.1, herr.2⟩
  · have h1 :
        Tendsto (fun n : ℕ => (cutoff n : ℂ) • R (cutoff n) (x : H))
          atTop (𝓝 (x : H)) := by
      simpa only [Complex.coe_smul] using
        (scaled_resolvent_strong_limit A R hd hr hp hl (x : H)).comp cutoff_tendsto
    have h2 :
        Tendsto (fun n : ℕ => (cutoff n : ℂ) • R (cutoff n) (A x))
          atTop (𝓝 (A x)) := by
      simpa only [Complex.coe_smul] using
        (scaled_resolvent_strong_limit A R hd hr hp hl (A x)).comp cutoff_tendsto
    exact h1.prodMk_nhds h2

/-- Abstract second-power operator-graph core theorem: for any closed densely defined
positive operator `A` with positive shifted resolvents `R`, `secondPowerGraph A` is dense
in `A.graph`. -/
theorem secondPowerGraph_topologicalClosure_eq (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H)
    (hc : IsClosed (A.graph : Set (H × H)))
    (hd : Dense (A.domain : Set H))
    (hr : ∀ a, 0 < a → Resolves A (R a) a)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ a, 0 < a → ∀ z : A.domain, R a (A z + a • (z : H)) = (z : H)) :
    (secondPowerGraph A).topologicalClosure = A.graph := by
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _ inf_le_left hc
  · rintro ⟨f, y⟩ hfy
    let x : A.domain := ⟨f, LinearPMap.mem_domain_of_mem_graph hfy⟩
    have hy : A x = y := A.mem_graph_snd_inj' (A.mem_graph x) hfy rfl
    have hseq := secondPowerGraph_sequence_approximation A R hd hr hp hl x
    have hlim :
        Tendsto (fun n : ℕ =>
          ((cutoff n : ℂ) • R (cutoff n) f,
            (cutoff n : ℂ) • R (cutoff n) (A x)))
          atTop (𝓝 (f, y)) := by
      simpa only [x, hy] using hseq.2
    exact mem_closure_iff_seq_limit.mpr ⟨_, fun n => (hseq.1 n).1, hlim⟩

/-- Abstract second-power domain density theorem: `secondPowerDomain A` is dense in `H`. -/
theorem secondPowerDomain_dense (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H)
    (hd : Dense (A.domain : Set H))
    (hr : ∀ a, 0 < a → Resolves A (R a) a)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ a, 0 < a → ∀ z : A.domain, R a (A z + a • (z : H)) = (z : H)) :
    Dense (secondPowerDomain A : Set H) := by
  have hs : (A.domain : Set H) ⊆ closure (secondPowerDomain A : Set H) := by
    intro f hf
    let x : A.domain := ⟨f, hf⟩
    have hseq := secondPowerGraph_sequence_approximation A R hd hr hp hl x
    have hlim :
        Tendsto (fun n : ℕ => (cutoff n : ℂ) • R (cutoff n) f) atTop (𝓝 f) :=
      (continuous_fst.tendsto (f, A x)).comp hseq.2
    exact mem_closure_of_tendsto hlim
      (Eventually.of_forall fun n => ⟨_, (hseq.1 n).1, rfl⟩)
  intro f
  exact closure_minimal hs isClosed_closure (hd f)

end AbstractSecondPowerCore

/-! ### 2. Concrete Instantiations for `T`, `P`, `G`, `S t`, and `H t` -/

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "GD" => KFCausalClockFloorGrowingHamiltonian.formData ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "SD" => KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "AD" => KFCausalClockFloorAveragedHamiltonian.formData ε hε h hh hw m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RT" => staticResolvent ε hε h hb hh
local notation "RP" => KFCausalClockFloorPotentialClockResolvent.resolvent ε hε h hh hw m g k
local notation "RG" => KFCausalClockFloorGrowingYosida.resolvent ε hε h hh hw m g k
local notation "RS" => KFCausalClockFloorResidualClockCore.resolvent ε hε h hh hw m g k
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "Kroot" => KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Tgrow" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (hamiltonian_bound ε h hw) hh m g k

private theorem static_selfAdjoint : IsSelfAdjoint T :=
  KFCausalRealMultiplierSelfAdjoint.realPullback_selfAdjoint
    KFCausalChargeTransverseSplit.dualPhysical
    (KFCausalClockFloorStaticMultiplierForm.symbol ε h)
    (KFCausalClockFloorStaticMultiplierForm.symbol_continuous ε hε h).measurable

/-- Resolvent commutation and second-power graph membership for the static operator `T`. -/
theorem static_resolvent_secondPowerGraph (a : ℝ) (ha : 0 < a) (x : (T).domain) :
    T (point T (RT a) a (staticResolvent_resolves ε hε h hb hh a ha) (x : Hilbert)) =
      RT a (T x) ∧
    (RT a (x : Hilbert), RT a (T x)) ∈ secondPowerGraph T ∧
    ((a : ℂ) • RT a (x : Hilbert), (a : ℂ) • RT a (T x)) ∈ secondPowerGraph T :=
  ⟨resolvent_commutes_on_domain T (RT a) a
      (staticResolvent_resolves ε hε h hb hh a ha)
      (staticResolvent_left_inverse ε hε h hb hh a ha) x,
   resolvent_mem_secondPowerGraph T (RT a) a
      (staticResolvent_resolves ε hε h hb hh a ha)
      (staticResolvent_left_inverse ε hε h hb hh a ha) x,
   scaled_resolvent_mem_secondPowerGraph T (RT a) a
      (staticResolvent_resolves ε hε h hb hh a ha)
      (staticResolvent_left_inverse ε hε h hb hh a ha) x⟩

/-- Yosida-scaled sequence approximation in `secondPowerGraph T` for any `x : (T).domain`. -/
theorem static_secondPowerGraph_sequence_approximation (x : (T).domain) :
    (∀ n : ℕ,
      ((cutoff n : ℂ) • RT (cutoff n) (x : Hilbert),
        (cutoff n : ℂ) • RT (cutoff n) (T x)) ∈ secondPowerGraph T ∧
      ‖(cutoff n : ℂ) • RT (cutoff n) (x : Hilbert) - (x : Hilbert)‖ =
        ‖RT (cutoff n) (T x)‖ ∧
      ‖(cutoff n : ℂ) • RT (cutoff n) (x : Hilbert) - (x : Hilbert)‖ ≤
        (cutoff n)⁻¹ * ‖T x‖) ∧
    Tendsto (fun n : ℕ =>
      ((cutoff n : ℂ) • RT (cutoff n) (x : Hilbert),
        (cutoff n : ℂ) • RT (cutoff n) (T x)))
      atTop (𝓝 ((x : Hilbert), T x)) :=
  secondPowerGraph_sequence_approximation T RT
    (static_selfAdjoint ε hε h).dense_domain
    (staticResolvent_resolves ε hε h hb hh)
    (staticOperator_positive ε hε h)
    (staticResolvent_left_inverse ε hε h hb hh) x

include hh hb in
/-- Unconditional second-power operator-graph core theorem for `T`. -/
theorem static_secondPowerGraph_core :
    ((T).graph ⊓ (T).domain.comap (LinearMap.snd ℂ Hilbert Hilbert)).topologicalClosure =
      (T).graph :=
  secondPowerGraph_topologicalClosure_eq T RT
    (static_selfAdjoint ε hε h).isClosed
    (static_selfAdjoint ε hε h).dense_domain
    (staticResolvent_resolves ε hε h hb hh)
    (staticOperator_positive ε hε h)
    (staticResolvent_left_inverse ε hε h hb hh)

/-- Resolvent commutation and second-power graph membership for the potential Hamiltonian `P`. -/
theorem potential_resolvent_secondPowerGraph (a : ℝ) (ha : 0 < a) (x : (P).domain) :
    P (point P (RP a) a
        (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha)
        (x : Hilbert)) = RP a (P x) ∧
    (RP a (x : Hilbert), RP a (P x)) ∈ secondPowerGraph P ∧
    ((a : ℂ) • RP a (x : Hilbert), (a : ℂ) • RP a (P x)) ∈ secondPowerGraph P :=
  ⟨resolvent_commutes_on_domain P (RP a) a
      (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha)
      (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k a ha) x,
   resolvent_mem_secondPowerGraph P (RP a) a
      (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha)
      (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k a ha) x,
   scaled_resolvent_mem_secondPowerGraph P (RP a) a
      (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha)
      (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k a ha) x⟩

/-- Yosida-scaled sequence approximation in `secondPowerGraph P` for any `x : (P).domain`. -/
theorem potential_secondPowerGraph_sequence_approximation (x : (P).domain) :
    (∀ n : ℕ,
      ((cutoff n : ℂ) • RP (cutoff n) (x : Hilbert),
        (cutoff n : ℂ) • RP (cutoff n) (P x)) ∈ secondPowerGraph P ∧
      ‖(cutoff n : ℂ) • RP (cutoff n) (x : Hilbert) - (x : Hilbert)‖ =
        ‖RP (cutoff n) (P x)‖ ∧
      ‖(cutoff n : ℂ) • RP (cutoff n) (x : Hilbert) - (x : Hilbert)‖ ≤
        (cutoff n)⁻¹ * ‖P x‖) ∧
    Tendsto (fun n : ℕ =>
      ((cutoff n : ℂ) • RP (cutoff n) (x : Hilbert),
        (cutoff n : ℂ) • RP (cutoff n) (P x)))
      atTop (𝓝 ((x : Hilbert), P x)) :=
  secondPowerGraph_sequence_approximation P RP
    (KFCausalClosedGraphForm.hamiltonian_dense PD)
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k)
    (KFCausalClosedGraphForm.hamiltonian_positive PD)
    (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k) x

/-- Unconditional second-power operator-graph core theorem for `P`. -/
theorem potential_secondPowerGraph_core :
    ((P).graph ⊓ (P).domain.comap (LinearMap.snd ℂ Hilbert Hilbert)).topologicalClosure =
      (P).graph :=
  secondPowerGraph_topologicalClosure_eq P RP
    (KFCausalClosedGraphForm.hamiltonian_closed PD)
    (KFCausalClosedGraphForm.hamiltonian_dense PD)
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k)
    (KFCausalClosedGraphForm.hamiltonian_positive PD)
    (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k)

/-- Resolvent commutation and second-power graph membership for the growing Hamiltonian `G`. -/
theorem growing_resolvent_secondPowerGraph (a : ℝ) (ha : 0 < a) (x : (G).domain) :
    G (point G (RG a) a
        (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha)
        (x : Hilbert)) = RG a (G x) ∧
    (RG a (x : Hilbert), RG a (G x)) ∈ secondPowerGraph G ∧
    ((a : ℂ) • RG a (x : Hilbert), (a : ℂ) • RG a (G x)) ∈ secondPowerGraph G :=
  ⟨resolvent_commutes_on_domain G (RG a) a
      (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha)
      (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k a ha) x,
   resolvent_mem_secondPowerGraph G (RG a) a
      (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha)
      (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k a ha) x,
   scaled_resolvent_mem_secondPowerGraph G (RG a) a
      (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha)
      (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k a ha) x⟩

/-- Yosida-scaled sequence approximation in `secondPowerGraph G` for any `x : (G).domain`. -/
theorem growing_secondPowerGraph_sequence_approximation (x : (G).domain) :
    (∀ n : ℕ,
      ((cutoff n : ℂ) • RG (cutoff n) (x : Hilbert),
        (cutoff n : ℂ) • RG (cutoff n) (G x)) ∈ secondPowerGraph G ∧
      ‖(cutoff n : ℂ) • RG (cutoff n) (x : Hilbert) - (x : Hilbert)‖ =
        ‖RG (cutoff n) (G x)‖ ∧
      ‖(cutoff n : ℂ) • RG (cutoff n) (x : Hilbert) - (x : Hilbert)‖ ≤
        (cutoff n)⁻¹ * ‖G x‖) ∧
    Tendsto (fun n : ℕ =>
      ((cutoff n : ℂ) • RG (cutoff n) (x : Hilbert),
        (cutoff n : ℂ) • RG (cutoff n) (G x)))
      atTop (𝓝 ((x : Hilbert), G x)) :=
  secondPowerGraph_sequence_approximation G RG
    (KFCausalClockFloorGrowingHamiltonian.hamiltonian_dense ε hε h hh hw m g k)
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k)
    (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k)
    (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k) x

/-- Unconditional second-power operator-graph core theorem for `G`. -/
theorem growing_secondPowerGraph_core :
    ((G).graph ⊓ (G).domain.comap (LinearMap.snd ℂ Hilbert Hilbert)).topologicalClosure =
      (G).graph :=
  secondPowerGraph_topologicalClosure_eq G RG
    (KFCausalClockFloorGrowingHamiltonian.hamiltonian_closed ε hε h hh hw m g k)
    (KFCausalClockFloorGrowingHamiltonian.hamiltonian_dense ε hε h hh hw m g k)
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k)
    (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k)
    (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k)

/-- Resolvent commutation and second-power graph membership for the residual Hamiltonian `S t`. -/
theorem residual_resolvent_secondPowerGraph (t a : ℝ) (ha : 0 < a) (x : (S t).domain) :
    S t (point (S t) (RS t a) a
        (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha)
        (x : Hilbert)) = RS t a (S t x) ∧
    (RS t a (x : Hilbert), RS t a (S t x)) ∈ secondPowerGraph (S t) ∧
    ((a : ℂ) • RS t a (x : Hilbert), (a : ℂ) • RS t a (S t x)) ∈ secondPowerGraph (S t) :=
  ⟨resolvent_commutes_on_domain (S t) (RS t a) a
      (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha)
      (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t a ha) x,
   resolvent_mem_secondPowerGraph (S t) (RS t a) a
      (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha)
      (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t a ha) x,
   scaled_resolvent_mem_secondPowerGraph (S t) (RS t a) a
      (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha)
      (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t a ha) x⟩

/-- Yosida-scaled sequence approximation in `secondPowerGraph (S t)` for any `x : (S t).domain`. -/
theorem residual_secondPowerGraph_sequence_approximation (t : ℝ) (x : (S t).domain) :
    (∀ n : ℕ,
      ((cutoff n : ℂ) • RS t (cutoff n) (x : Hilbert),
        (cutoff n : ℂ) • RS t (cutoff n) (S t x)) ∈ secondPowerGraph (S t) ∧
      ‖(cutoff n : ℂ) • RS t (cutoff n) (x : Hilbert) - (x : Hilbert)‖ =
        ‖RS t (cutoff n) (S t x)‖ ∧
      ‖(cutoff n : ℂ) • RS t (cutoff n) (x : Hilbert) - (x : Hilbert)‖ ≤
        (cutoff n)⁻¹ * ‖S t x‖) ∧
    Tendsto (fun n : ℕ =>
      ((cutoff n : ℂ) • RS t (cutoff n) (x : Hilbert),
        (cutoff n : ℂ) • RS t (cutoff n) (S t x)))
      atTop (𝓝 ((x : Hilbert), S t x)) :=
  secondPowerGraph_sequence_approximation (S t) (RS t)
    (KFCausalClosedGraphForm.hamiltonian_dense (SD t))
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t)
    (KFCausalClosedGraphForm.hamiltonian_positive (SD t))
    (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t) x

/-- Unconditional second-power operator-graph core theorem for `S t`. -/
theorem residual_secondPowerGraph_core (t : ℝ) :
    ((S t).graph ⊓ (S t).domain.comap (LinearMap.snd ℂ Hilbert Hilbert)).topologicalClosure =
      (S t).graph :=
  secondPowerGraph_topologicalClosure_eq (S t) (RS t)
    (KFCausalClosedGraphForm.hamiltonian_closed (SD t))
    (KFCausalClosedGraphForm.hamiltonian_dense (SD t))
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t)
    (KFCausalClosedGraphForm.hamiltonian_positive (SD t))
    (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t)

/-- Resolvent commutation and second-power graph membership for the full Hamiltonian `H t`. -/
theorem hamiltonian_resolvent_secondPowerGraph (t a : ℝ) (ha : 0 < a) (x : (H t).domain) :
    H t (point (H t) (RH t a) a
        (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
        (x : Hilbert)) = RH t a (H t x) ∧
    (RH t a (x : Hilbert), RH t a (H t x)) ∈ secondPowerGraph (H t) ∧
    ((a : ℂ) • RH t a (x : Hilbert), (a : ℂ) • RH t a (H t x)) ∈ secondPowerGraph (H t) :=
  ⟨resolvent_commutes_on_domain (H t) (RH t a) a
      (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
      (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t a ha) x,
   resolvent_mem_secondPowerGraph (H t) (RH t a) a
      (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
      (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t a ha) x,
   scaled_resolvent_mem_secondPowerGraph (H t) (RH t a) a
      (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
      (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t a ha) x⟩

/-- Yosida-scaled sequence approximation in `secondPowerGraph (H t)` for any `x : (H t).domain`. -/
theorem hamiltonian_secondPowerGraph_sequence_approximation (t : ℝ) (x : (H t).domain) :
    (∀ n : ℕ,
      ((cutoff n : ℂ) • RH t (cutoff n) (x : Hilbert),
        (cutoff n : ℂ) • RH t (cutoff n) (H t x)) ∈ secondPowerGraph (H t) ∧
      ‖(cutoff n : ℂ) • RH t (cutoff n) (x : Hilbert) - (x : Hilbert)‖ =
        ‖RH t (cutoff n) (H t x)‖ ∧
      ‖(cutoff n : ℂ) • RH t (cutoff n) (x : Hilbert) - (x : Hilbert)‖ ≤
        (cutoff n)⁻¹ * ‖H t x‖) ∧
    Tendsto (fun n : ℕ =>
      ((cutoff n : ℂ) • RH t (cutoff n) (x : Hilbert),
        (cutoff n : ℂ) • RH t (cutoff n) (H t x)))
      atTop (𝓝 ((x : Hilbert), H t x)) :=
  secondPowerGraph_sequence_approximation (H t) (RH t)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_dense ε hε h hh hw m g k t)
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
    (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t) x

/-- Unconditional second-power operator-graph core theorem for `H t`. -/
theorem hamiltonian_secondPowerGraph_core (t : ℝ) :
    ((H t).graph ⊓ (H t).domain.comap (LinearMap.snd ℂ Hilbert Hilbert)).topologicalClosure =
      (H t).graph :=
  secondPowerGraph_topologicalClosure_eq (H t) (RH t)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_closed ε hε h hh hw m g k t)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_dense ε hε h hh hw m g k t)
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
    (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t)

/-- Simultaneous second-power operator-graph core synthesis for all five Hamiltonians
`T`, `P`, `G`, `S t`, and `H t`. -/
theorem five_hamiltonians_secondPowerGraph_cores (t : ℝ) :
    ((T).graph ⊓ (T).domain.comap (LinearMap.snd ℂ Hilbert Hilbert)).topologicalClosure =
      (T).graph ∧
    ((P).graph ⊓ (P).domain.comap (LinearMap.snd ℂ Hilbert Hilbert)).topologicalClosure =
      (P).graph ∧
    ((G).graph ⊓ (G).domain.comap (LinearMap.snd ℂ Hilbert Hilbert)).topologicalClosure =
      (G).graph ∧
    ((S t).graph ⊓ (S t).domain.comap (LinearMap.snd ℂ Hilbert Hilbert)).topologicalClosure =
      (S t).graph ∧
    ((H t).graph ⊓ (H t).domain.comap (LinearMap.snd ℂ Hilbert Hilbert)).topologicalClosure =
      (H t).graph :=
  ⟨static_secondPowerGraph_core ε hε h hh hb,
   potential_secondPowerGraph_core ε hε h hh hb m g k,
   growing_secondPowerGraph_core ε hε h hh hb m g k,
   residual_secondPowerGraph_core ε hε h hh hb m g k t,
   hamiltonian_secondPowerGraph_core ε hε h hh hb m g k t⟩

/-- Simultaneous density of `secondPowerDomain` in `Hilbert` for all five Hamiltonians
`T`, `P`, `G`, `S t`, and `H t`. -/
theorem five_hamiltonians_secondPowerDomain_dense (t : ℝ) :
    Dense (secondPowerDomain T : Set Hilbert) ∧
    Dense (secondPowerDomain P : Set Hilbert) ∧
    Dense (secondPowerDomain G : Set Hilbert) ∧
    Dense (secondPowerDomain (S t) : Set Hilbert) ∧
    Dense (secondPowerDomain (H t) : Set Hilbert) :=
  ⟨secondPowerDomain_dense T RT
      (static_selfAdjoint ε hε h).dense_domain
      (staticResolvent_resolves ε hε h hb hh)
      (staticOperator_positive ε hε h)
      (staticResolvent_left_inverse ε hε h hb hh),
   secondPowerDomain_dense P RP
      (KFCausalClosedGraphForm.hamiltonian_dense PD)
      (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k)
      (KFCausalClosedGraphForm.hamiltonian_positive PD)
      (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k),
   secondPowerDomain_dense G RG
      (KFCausalClockFloorGrowingHamiltonian.hamiltonian_dense ε hε h hh hw m g k)
      (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k)
      (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k)
      (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k),
   secondPowerDomain_dense (S t) (RS t)
      (KFCausalClosedGraphForm.hamiltonian_dense (SD t))
      (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t)
      (KFCausalClosedGraphForm.hamiltonian_positive (SD t))
      (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t),
   secondPowerDomain_dense (H t) (RH t)
      (KFCausalClockFloorAveragedHamiltonian.hamiltonian_dense ε hε h hh hw m g k t)
      (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
      (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
      (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t)⟩

/-! ### 3. Ten-Domain Regularity on the Second-Power Hamiltonian Graph -/

/-- Any vector `z ∈ (H t).domain` lies simultaneously in all 10 operator, form, and clock
domains at every observation time `s : ℝ`: `(H t).domain`, `(K).domain`, `(S t).domain`,
`(Eavg s).domain`, `(Tstat).domain`, `(Kroot).domain`, `(Tpot).domain`, `(Tgrow).domain`,
`(Tres s).domain`, and `(clockHalf ε).domain`. -/
theorem hamiltonian_domain_mem_ten_domains (t s : ℝ) {z : Hilbert}
    (hz : z ∈ (H t).domain) :
    z ∈ (H t).domain ∧
    z ∈ (K).domain ∧
    z ∈ (S t).domain ∧
    z ∈ (Eavg s).domain ∧
    z ∈ (Tstat).domain ∧
    z ∈ (Kroot).domain ∧
    z ∈ (Tpot).domain ∧
    z ∈ (Tgrow).domain ∧
    z ∈ (Tres s).domain ∧
    z ∈ (clockHalf ε).domain :=
  ⟨hz,
   KFCausalClockFloorHamiltonianRadialDomination.radial_domain
     ε hε h hh hb m g k t ⟨z, hz⟩,
   KFCausalClockFloorHamiltonianRadialSum.residual_domain
     ε hε h hh hb m g k t ⟨z, hz⟩,
   (KFCausalClockFloorUnconditionalFormDomainSynthesis.averaged_domain_time_eq
     ε hε h hh hb m g k t s z).mp
     (KFCausalClockFloorUnconditionalOperatorFormEnergy.hamiltonian_mem_averaged_domain
       ε hε h hh hb m g k t ⟨z, hz⟩),
   KFCausalClockFloorUnconditionalOperatorFormEnergy.hamiltonian_mem_staticRoot_domain
     ε hε h hh hb m g k t ⟨z, hz⟩,
   KFCausalClockFloorUnconditionalOperatorFormEnergy.hamiltonian_mem_radialRoot_domain
     ε hε h hh hb m g k t ⟨z, hz⟩,
   KFCausalClockFloorUnconditionalOperatorFormEnergy.hamiltonian_mem_potentialForm_domain
     ε hε h hh hb m g k t ⟨z, hz⟩,
   KFCausalClockFloorUnconditionalOperatorFormEnergy.hamiltonian_mem_growingForm_domain
     ε hε h hh hb m g k t ⟨z, hz⟩,
   (residual_form_domain_time_iff ε hε h hh hb m g k t s z).mp
     (KFCausalClockFloorUnconditionalOperatorFormEnergy.hamiltonian_mem_residualForm_domain
       ε hε h hh hb m g k t ⟨z, hz⟩),
   hamiltonian_domain_le_clockHalf_domain ε hε h hh hb m g k t hz⟩

/-- For every `(x, y) ∈ (H t).graph ⊓ (H t).domain.comap snd`, both `x` and `y = H t x`
lie simultaneously in all 10 operator, form, and clock domains at every observation time `s : ℝ`. -/
theorem hamiltonian_secondPowerGraph_both_mem_ten_domains (t s : ℝ) {x y : Hilbert}
    (hxy : (x, y) ∈ (H t).graph ⊓ (H t).domain.comap (LinearMap.snd ℂ Hilbert Hilbert)) :
    let hx : x ∈ (H t).domain := LinearPMap.mem_domain_of_mem_graph hxy.1
    H t ⟨x, hx⟩ = y ∧
    (x ∈ (H t).domain ∧
     x ∈ (K).domain ∧
     x ∈ (S t).domain ∧
     x ∈ (Eavg s).domain ∧
     x ∈ (Tstat).domain ∧
     x ∈ (Kroot).domain ∧
     x ∈ (Tpot).domain ∧
     x ∈ (Tgrow).domain ∧
     x ∈ (Tres s).domain ∧
     x ∈ (clockHalf ε).domain) ∧
    (y ∈ (H t).domain ∧
     y ∈ (K).domain ∧
     y ∈ (S t).domain ∧
     y ∈ (Eavg s).domain ∧
     y ∈ (Tstat).domain ∧
     y ∈ (Kroot).domain ∧
     y ∈ (Tpot).domain ∧
     y ∈ (Tgrow).domain ∧
     y ∈ (Tres s).domain ∧
     y ∈ (clockHalf ε).domain) := by
  intro hx
  exact ⟨(H t).mem_graph_snd_inj' ((H t).mem_graph ⟨x, hx⟩) hxy.1 rfl,
    hamiltonian_domain_mem_ten_domains ε hε h hh hb m g k t s hx,
    hamiltonian_domain_mem_ten_domains ε hε h hh hb m g k t s hxy.2⟩

#print axioms mem_secondPowerGraph_iff
#print axioms secondPowerDomain_le_domain
#print axioms mem_secondPowerDomain_iff
#print axioms resolvent_commutes_on_domain
#print axioms resolvent_mem_secondPowerGraph
#print axioms resolvent_mem_secondPowerDomain
#print axioms scaled_resolvent_mem_secondPowerGraph
#print axioms scaled_resolvent_sub_eq_neg_resolvent
#print axioms scaled_resolvent_error_on_domain
#print axioms scaled_resolvent_output_error_on_secondPowerDomain
#print axioms secondPowerGraph_sequence_approximation
#print axioms secondPowerGraph_topologicalClosure_eq
#print axioms secondPowerDomain_dense
#print axioms static_resolvent_secondPowerGraph
#print axioms static_secondPowerGraph_sequence_approximation
#print axioms static_secondPowerGraph_core
#print axioms potential_resolvent_secondPowerGraph
#print axioms potential_secondPowerGraph_sequence_approximation
#print axioms potential_secondPowerGraph_core
#print axioms growing_resolvent_secondPowerGraph
#print axioms growing_secondPowerGraph_sequence_approximation
#print axioms growing_secondPowerGraph_core
#print axioms residual_resolvent_secondPowerGraph
#print axioms residual_secondPowerGraph_sequence_approximation
#print axioms residual_secondPowerGraph_core
#print axioms hamiltonian_resolvent_secondPowerGraph
#print axioms hamiltonian_secondPowerGraph_sequence_approximation
#print axioms hamiltonian_secondPowerGraph_core
#print axioms five_hamiltonians_secondPowerGraph_cores
#print axioms five_hamiltonians_secondPowerDomain_dense
#print axioms hamiltonian_domain_mem_ten_domains
#print axioms hamiltonian_secondPowerGraph_both_mem_ten_domains

end

end UnifiedTheory.Audit.KFCausalClockFloorSecondPowerOperatorCores
