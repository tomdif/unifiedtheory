/- Unconditional iterated-resolvent second-power operator cores, exact second-power
operator identities, three-tier norm bounds, and ten-domain regularity for the five
fundamental clock-floor Hamiltonians T, P, G, S(t), and H(t):
1. For any unbounded linear operator A with positive shifted resolvents R(a) (a > 0),
   if f ∈ Dom(A) then R(a) f ∈ secondPowerDomain A with A(R(a) f) = f - (a : ℂ) • R(a) f ∈ Dom(A).
2. Unconditionally for EVERY f : H and ANY a > 0, b > 0, the iterated resolvent
   R(a)(R(b) f) lies in secondPowerDomain A with exact second-power identity
   A(A(R(a)(R(b) f))) = f - ((a + b : ℝ) : ℂ) • R(b) f + ((a ^ 2 : ℝ) : ℂ) • R(a)(R(b) f)
   (and at a = b, f - ((a + a : ℝ) : ℂ) • R(a) f + ((a * a : ℝ) : ℂ) • R(a)(R(a) f)),
   together with unconditional three-tier norm bounds:
   ‖R(a)(R(b) f)‖ ≤ a⁻¹ * (b⁻¹ * ‖f‖),
   ‖A(R(a)(R(b) f))‖ ≤ 2 * (b⁻¹ * ‖f‖),
   ‖A(A(R(a)(R(b) f)))‖ ≤ 4 * ‖f‖.
3. Instantiating A ∈ {T, P, G, S(t), H(t)} establishes unconditional iterated-resolvent
   membership in staticSecondPowerDomain, potentialSecondPowerDomain, growingSecondPowerDomain,
   residualSecondPowerDomain t, and hamiltonianSecondPowerDomain t for all f : Hilbert,
   and proves that R_{H(t)}(a)(R_{H(t)}(b) f) and its first-power Hamiltonian output
   automatically belong to all 10 operator, form, and clock domains unconditionally. -/
import UnifiedTheory.Audit.KFCausalClockFloorSecondPowerOperatorCores
import UnifiedTheory.Audit.KFCausalClockFloorEvolvedFormCoreInvariance

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorIteratedResolventSecondPowerCore

noncomputable section

open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalPositiveResolventBounds
  (Resolves point point_value resolvent_apply_norm_bound)
open KFCausalClockFloorStaticResolventRadialCommutator
  (staticOperator_positive staticResolvent staticResolvent_resolves staticResolvent_left_inverse)
open KFCausalClockFloorAveragedEvolution (evolution evolution_norm)
open KFCausalClockFloorSecondPowerOperatorCores
  (secondPowerGraph secondPowerDomain mem_secondPowerGraph_iff mem_secondPowerDomain_iff
   resolvent_commutes_on_domain hamiltonian_domain_mem_ten_domains
   hamiltonian_secondPowerGraph_both_mem_ten_domains)

/-! ### 1. Abstract Iterated Resolvent Second-Power Core and Three-Tier Norm Bounds -/

section AbstractIteratedResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Exact resolvent output identity `A (point A R a hr f) = f - (a : ℂ) • R f` on all of `H`. -/
theorem resolvent_output_eq_sub (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves A R a) (f : H) :
    A (point A R a hr f) = f - (a : ℂ) • R f := by
  rw [point_value A R a hr f, Complex.coe_smul]

/-- If `f ∈ A.domain`, then `(R f, f - (a : ℂ) • R f) ∈ secondPowerGraph A` using only
the resolvent equation `Resolves A R a`. -/
theorem resolvent_mem_secondPowerGraph_of_mem_domain (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves A R a) {f : H} (hf : f ∈ A.domain) :
    (R f, f - (a : ℂ) • R f) ∈ secondPowerGraph A := by
  have h1 : (R f, A (point A R a hr f)) ∈ A.graph :=
    A.mem_graph (point A R a hr f)
  rw [resolvent_output_eq_sub A R a hr f] at h1
  exact ⟨h1, A.domain.sub_mem hf (A.domain.smul_mem (a : ℂ) (point A R a hr f).property)⟩

/-- If `f ∈ A.domain`, then `R f ∈ secondPowerDomain A` using only `Resolves A R a`. -/
theorem resolvent_mem_secondPowerDomain_of_mem_domain (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves A R a) {f : H} (hf : f ∈ A.domain) :
    R f ∈ secondPowerDomain A :=
  ⟨(R f, f - (a : ℂ) • R f),
    resolvent_mem_secondPowerGraph_of_mem_domain A R a hr hf, rfl⟩

/-- Unconditional scaled resolvent norm bound `‖(a : ℂ) • R f‖ ≤ ‖f‖` for `0 < a` and `f : H`. -/
theorem scaled_resolvent_norm_bound (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves A R a) (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re) (f : H) :
    ‖(a : ℂ) • R f‖ ≤ ‖f‖ := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  have hb := mul_le_mul_of_nonneg_left (resolvent_apply_norm_bound A R a ha hr hp f) ha.le
  rwa [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] at hb

/-- Unconditional first-order operator norm bound `‖A (point A R a hr f)‖ ≤ 2 * ‖f‖`
for any `0 < a` and `f : H`. -/
theorem resolvent_first_order_norm_bound (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves A R a) (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re) (f : H) :
    ‖A (point A R a hr f)‖ ≤ 2 * ‖f‖ := by
  rw [resolvent_output_eq_sub A R a hr f]
  have htri : ‖f - (a : ℂ) • R f‖ ≤ ‖f‖ + ‖(a : ℂ) • R f‖ := norm_sub_le f ((a : ℂ) • R f)
  have hsc := scaled_resolvent_norm_bound A R a ha hr hp f
  linarith

/-- Unconditionally for ANY `f : H` and ANY `a, b : ℝ`, the iterated resolvent pair
`(R a (R b f), R b f - (a : ℂ) • R a (R b f))` lies in `secondPowerGraph A`. -/
theorem iterated_resolvent_mem_secondPowerGraph (A : H →ₗ.[ℂ] H) (Ra Rb : H →L[ℂ] H) (a b : ℝ)
    (hra : Resolves A Ra a) (hrb : Resolves A Rb b) (f : H) :
    (Ra (Rb f), Rb f - (a : ℂ) • Ra (Rb f)) ∈ secondPowerGraph A :=
  resolvent_mem_secondPowerGraph_of_mem_domain A Ra a hra (point A Rb b hrb f).property

/-- Unconditionally for ANY `f : H` and ANY `a, b : ℝ`, the iterated resolvent
`Ra (Rb f)` lies in `secondPowerDomain A`. -/
theorem iterated_resolvent_mem_secondPowerDomain (A : H →ₗ.[ℂ] H) (Ra Rb : H →L[ℂ] H) (a b : ℝ)
    (hra : Resolves A Ra a) (hrb : Resolves A Rb b) (f : H) :
    Ra (Rb f) ∈ secondPowerDomain A :=
  resolvent_mem_secondPowerDomain_of_mem_domain A Ra a hra (point A Rb b hrb f).property

/-- First-power operator identity on the iterated resolvent:
`A (point A Ra a hra (Rb f)) = Rb f - (a : ℂ) • Ra (Rb f)`. -/
theorem iterated_resolvent_first_power_eq (A : H →ₗ.[ℂ] H) (Ra Rb : H →L[ℂ] H) (a : ℝ)
    (hra : Resolves A Ra a) (f : H) :
    A (point A Ra a hra (Rb f)) = Rb f - (a : ℂ) • Ra (Rb f) :=
  resolvent_output_eq_sub A Ra a hra (Rb f)

/-- Exact second-power operator identity on the iterated resolvent for any `f : H`:
for `u := point A Rb b hrb f` and `v := point A Ra a hra (Rb f)`, the domain element
`u - (a : ℂ) • v : A.domain` has underlying vector `A v = Rb f - (a : ℂ) • Ra (Rb f)` and
satisfies `A (u - (a : ℂ) • v) = f - ((a + b : ℝ) : ℂ) • Rb f + ((a ^ 2 : ℝ) : ℂ) • Ra (Rb f)`. -/
theorem iterated_resolvent_second_power_eq (A : H →ₗ.[ℂ] H) (Ra Rb : H →L[ℂ] H) (a b : ℝ)
    (hra : Resolves A Ra a) (hrb : Resolves A Rb b) (f : H) :
    let u : A.domain := point A Rb b hrb f
    let v : A.domain := point A Ra a hra (Rb f)
    ((u - (a : ℂ) • v : A.domain) : H) = A v ∧
    A (u - (a : ℂ) • v) =
      f - ((a + b : ℝ) : ℂ) • Rb f + ((a ^ 2 : ℝ) : ℂ) • Ra (Rb f) := by
  intro u v
  have hcoe : ((u - (a : ℂ) • v : A.domain) : H) = A v :=
    (resolvent_output_eq_sub A Ra a hra (Rb f)).symm
  refine ⟨hcoe, ?_⟩
  rw [A.map_sub, A.map_smul]
  have hu : A u = f - (b : ℂ) • Rb f := resolvent_output_eq_sub A Rb b hrb f
  have hv : A v = Rb f - (a : ℂ) • Ra (Rb f) := resolvent_output_eq_sub A Ra a hra (Rb f)
  rw [hu, hv]
  push_cast
  module

/-- Diagonal (`a = b`) second-power operator identity on the iterated resolvent:
`A (u - (a : ℂ) • v) = f - ((a + a : ℝ) : ℂ) • Ra f + ((a * a : ℝ) : ℂ) • Ra (Ra f)`. -/
theorem iterated_resolvent_diagonal_second_power_eq (A : H →ₗ.[ℂ] H) (Ra : H →L[ℂ] H) (a : ℝ)
    (hra : Resolves A Ra a) (f : H) :
    let u : A.domain := point A Ra a hra f
    let v : A.domain := point A Ra a hra (Ra f)
    ((u - (a : ℂ) • v : A.domain) : H) = A v ∧
    A (u - (a : ℂ) • v) =
      f - ((a + a : ℝ) : ℂ) • Ra f + ((a * a : ℝ) : ℂ) • Ra (Ra f) := by
  intro u v
  have h := iterated_resolvent_second_power_eq A Ra Ra a a hra hra f
  refine ⟨h.1, h.2.trans ?_⟩
  rw [sq]

/-- Commuted second-power operator identity on the iterated resolvent: when `Ra` is a left
inverse of `A + a I` on `A.domain`, `A (u - (a : ℂ) • v) = A u - (a : ℂ) • Ra (A u)`. -/
theorem iterated_resolvent_commuted_second_power_eq (A : H →ₗ.[ℂ] H) (Ra Rb : H →L[ℂ] H) (a b : ℝ)
    (hra : Resolves A Ra a) (hrb : Resolves A Rb b)
    (hla : ∀ z : A.domain, Ra (A z + a • (z : H)) = (z : H)) (f : H) :
    let u : A.domain := point A Rb b hrb f
    let v : A.domain := point A Ra a hra (Rb f)
    A (u - (a : ℂ) • v) = A u - (a : ℂ) • Ra (A u) := by
  intro u v
  have hcomm : A v = Ra (A u) := resolvent_commutes_on_domain A Ra a hra hla u
  rw [A.map_sub, A.map_smul, hcomm]

/-- Unconditional zeroth-order norm bound for the iterated resolvent:
`‖Ra (Rb f)‖ ≤ a⁻¹ * (b⁻¹ * ‖f‖)` for all `0 < a`, `0 < b`, and `f : H`. -/
theorem iterated_resolvent_norm_bound (A : H →ₗ.[ℂ] H) (Ra Rb : H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hra : Resolves A Ra a) (hrb : Resolves A Rb b)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re) (f : H) :
    ‖Ra (Rb f)‖ ≤ a⁻¹ * (b⁻¹ * ‖f‖) :=
  (resolvent_apply_norm_bound A Ra a ha hra hp (Rb f)).trans
    (mul_le_mul_of_nonneg_left (resolvent_apply_norm_bound A Rb b hb hrb hp f)
      (inv_pos.mpr ha).le)

/-- Unconditional first-power norm bound for the iterated resolvent:
`‖A (point A Ra a hra (Rb f))‖ ≤ 2 * (b⁻¹ * ‖f‖)` for all `0 < a`, `0 < b`, and `f : H`. -/
theorem iterated_resolvent_first_power_norm_bound (A : H →ₗ.[ℂ] H) (Ra Rb : H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hra : Resolves A Ra a) (hrb : Resolves A Rb b)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re) (f : H) :
    ‖A (point A Ra a hra (Rb f))‖ ≤ 2 * (b⁻¹ * ‖f‖) :=
  (resolvent_first_order_norm_bound A Ra a ha hra hp (Rb f)).trans
    (mul_le_mul_of_nonneg_left (resolvent_apply_norm_bound A Rb b hb hrb hp f) (by norm_num))

/-- Unconditional second-power norm bound for the iterated resolvent:
`‖A (u - (a : ℂ) • v)‖ ≤ 4 * ‖f‖` for all `0 < a`, `0 < b`, and `f : H`. -/
theorem iterated_resolvent_second_power_norm_bound (A : H →ₗ.[ℂ] H) (Ra Rb : H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hra : Resolves A Ra a) (hrb : Resolves A Rb b)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hla : ∀ z : A.domain, Ra (A z + a • (z : H)) = (z : H)) (f : H) :
    let u : A.domain := point A Rb b hrb f
    let v : A.domain := point A Ra a hra (Rb f)
    ‖A (u - (a : ℂ) • v)‖ ≤ 4 * ‖f‖ := by
  intro u v
  rw [iterated_resolvent_commuted_second_power_eq A Ra Rb a b hra hrb hla f]
  have htri : ‖A u - (a : ℂ) • Ra (A u)‖ ≤ ‖A u‖ + ‖(a : ℂ) • Ra (A u)‖ :=
    norm_sub_le (A u) ((a : ℂ) • Ra (A u))
  have hsc : ‖(a : ℂ) • Ra (A u)‖ ≤ ‖A u‖ :=
    scaled_resolvent_norm_bound A Ra a ha hra hp (A u)
  have hu : ‖A u‖ ≤ 2 * ‖f‖ :=
    resolvent_first_order_norm_bound A Rb b hb hrb hp f
  linarith

/-- Complete abstract package of iterated-resolvent second-power membership, exact second-power
identity, and three-tier norm bounds (`a⁻¹ * (b⁻¹ * ‖f‖)`, `2 * (b⁻¹ * ‖f‖)`, `4 * ‖f‖`). -/
theorem iterated_resolvent_three_tier_bounds (A : H →ₗ.[ℂ] H) (Ra Rb : H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hra : Resolves A Ra a) (hrb : Resolves A Rb b)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hla : ∀ z : A.domain, Ra (A z + a • (z : H)) = (z : H)) (f : H) :
    let u : A.domain := point A Rb b hrb f
    let v : A.domain := point A Ra a hra (Rb f)
    Ra (Rb f) ∈ secondPowerDomain A ∧
    (Ra (Rb f), Rb f - (a : ℂ) • Ra (Rb f)) ∈ secondPowerGraph A ∧
    ((u - (a : ℂ) • v : A.domain) : H) = A v ∧
    A (u - (a : ℂ) • v) =
      f - ((a + b : ℝ) : ℂ) • Rb f + ((a ^ 2 : ℝ) : ℂ) • Ra (Rb f) ∧
    ‖Ra (Rb f)‖ ≤ a⁻¹ * (b⁻¹ * ‖f‖) ∧
    ‖A v‖ ≤ 2 * (b⁻¹ * ‖f‖) ∧
    ‖A (u - (a : ℂ) • v)‖ ≤ 4 * ‖f‖ := by
  intro u v
  have hid := iterated_resolvent_second_power_eq A Ra Rb a b hra hrb f
  exact ⟨iterated_resolvent_mem_secondPowerDomain A Ra Rb a b hra hrb f,
    iterated_resolvent_mem_secondPowerGraph A Ra Rb a b hra hrb f,
    hid.1, hid.2,
    iterated_resolvent_norm_bound A Ra Rb a b ha hb hra hrb hp f,
    iterated_resolvent_first_power_norm_bound A Ra Rb a b ha hb hra hrb hp f,
    iterated_resolvent_second_power_norm_bound A Ra Rb a b ha hb hra hrb hp hla f⟩

end AbstractIteratedResolvent

/-! ### 2. Concrete Iterated-Resolvent Second-Power Regularity for `T`, `P`, `G`, `S t`, and `H t` -/

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
local notation "U" => evolution ε hε h hh hw m g k
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "Kroot" => KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Tgrow" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (hamiltonian_bound ε h hw) hh m g k

/-- The second-power domain `Dom(T²)` of the static clock-floor operator `T`. -/
abbrev staticSecondPowerDomain : Submodule ℂ Hilbert :=
  secondPowerDomain T

/-- The second-power domain `Dom(P²)` of the potential clock-floor Hamiltonian `P`. -/
abbrev potentialSecondPowerDomain : Submodule ℂ Hilbert :=
  secondPowerDomain P

/-- The second-power domain `Dom(G²)` of the growing clock-floor Hamiltonian `G`. -/
abbrev growingSecondPowerDomain : Submodule ℂ Hilbert :=
  secondPowerDomain G

/-- The second-power domain `Dom(S(t)²)` of the residual clock-floor Hamiltonian `S t`. -/
abbrev residualSecondPowerDomain (t : ℝ) : Submodule ℂ Hilbert :=
  secondPowerDomain (S t)

/-- The second-power domain `Dom(H(t)²)` of the full clock-floor Hamiltonian `H t`. -/
abbrev hamiltonianSecondPowerDomain (t : ℝ) : Submodule ℂ Hilbert :=
  secondPowerDomain (H t)

/-- If `f ∈ (T).domain` and `0 < a`, then `RT a f ∈ staticSecondPowerDomain`. -/
theorem static_resolvent_mem_secondPowerDomain (a : ℝ) (ha : 0 < a)
    {f : Hilbert} (hf : f ∈ (T).domain) :
    RT a f ∈ staticSecondPowerDomain ε hε h :=
  resolvent_mem_secondPowerDomain_of_mem_domain T (RT a) a
    (staticResolvent_resolves ε hε h hb hh a ha) hf

/-- Unconditional iterated-resolvent second-power membership, exact second-power identity,
and three-tier norm bounds for the static operator `T`. -/
theorem static_iterated_resolvent_secondPower (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b)
    (f : Hilbert) :
    let u : (T).domain :=
      point T (RT b) b (staticResolvent_resolves ε hε h hb hh b hb_pos) f
    let v : (T).domain :=
      point T (RT a) a (staticResolvent_resolves ε hε h hb hh a ha) (RT b f)
    RT a (RT b f) ∈ staticSecondPowerDomain ε hε h ∧
    (RT a (RT b f), RT b f - (a : ℂ) • RT a (RT b f)) ∈ secondPowerGraph T ∧
    ((u - (a : ℂ) • v : (T).domain) : Hilbert) = T v ∧
    T (u - (a : ℂ) • v) =
      f - ((a + b : ℝ) : ℂ) • RT b f + ((a ^ 2 : ℝ) : ℂ) • RT a (RT b f) ∧
    ‖RT a (RT b f)‖ ≤ a⁻¹ * (b⁻¹ * ‖f‖) ∧
    ‖T v‖ ≤ 2 * (b⁻¹ * ‖f‖) ∧
    ‖T (u - (a : ℂ) • v)‖ ≤ 4 * ‖f‖ :=
  iterated_resolvent_three_tier_bounds T (RT a) (RT b) a b ha hb_pos
    (staticResolvent_resolves ε hε h hb hh a ha)
    (staticResolvent_resolves ε hε h hb hh b hb_pos)
    (staticOperator_positive ε hε h)
    (staticResolvent_left_inverse ε hε h hb hh a ha) f

/-- If `f ∈ (P).domain` and `0 < a`, then `RP a f ∈ potentialSecondPowerDomain`. -/
theorem potential_resolvent_mem_secondPowerDomain (a : ℝ) (ha : 0 < a)
    {f : Hilbert} (hf : f ∈ (P).domain) :
    RP a f ∈ potentialSecondPowerDomain ε hε h hh hb m g k :=
  resolvent_mem_secondPowerDomain_of_mem_domain P (RP a) a
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha) hf

/-- Unconditional iterated-resolvent second-power membership, exact second-power identity,
and three-tier norm bounds for the potential Hamiltonian `P`. -/
theorem potential_iterated_resolvent_secondPower (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b)
    (f : Hilbert) :
    let u : (P).domain :=
      point P (RP b) b
        (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k b hb_pos) f
    let v : (P).domain :=
      point P (RP a) a
        (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha) (RP b f)
    RP a (RP b f) ∈ potentialSecondPowerDomain ε hε h hh hb m g k ∧
    (RP a (RP b f), RP b f - (a : ℂ) • RP a (RP b f)) ∈ secondPowerGraph P ∧
    ((u - (a : ℂ) • v : (P).domain) : Hilbert) = P v ∧
    P (u - (a : ℂ) • v) =
      f - ((a + b : ℝ) : ℂ) • RP b f + ((a ^ 2 : ℝ) : ℂ) • RP a (RP b f) ∧
    ‖RP a (RP b f)‖ ≤ a⁻¹ * (b⁻¹ * ‖f‖) ∧
    ‖P v‖ ≤ 2 * (b⁻¹ * ‖f‖) ∧
    ‖P (u - (a : ℂ) • v)‖ ≤ 4 * ‖f‖ :=
  iterated_resolvent_three_tier_bounds P (RP a) (RP b) a b ha hb_pos
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha)
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k b hb_pos)
    (KFCausalClosedGraphForm.hamiltonian_positive PD)
    (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k a ha) f

/-- If `f ∈ (G).domain` and `0 < a`, then `RG a f ∈ growingSecondPowerDomain`. -/
theorem growing_resolvent_mem_secondPowerDomain (a : ℝ) (ha : 0 < a)
    {f : Hilbert} (hf : f ∈ (G).domain) :
    RG a f ∈ growingSecondPowerDomain ε hε h hh hb m g k :=
  resolvent_mem_secondPowerDomain_of_mem_domain G (RG a) a
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha) hf

/-- Unconditional iterated-resolvent second-power membership, exact second-power identity,
and three-tier norm bounds for the growing Hamiltonian `G`. -/
theorem growing_iterated_resolvent_secondPower (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b)
    (f : Hilbert) :
    let u : (G).domain :=
      point G (RG b) b
        (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k b hb_pos) f
    let v : (G).domain :=
      point G (RG a) a
        (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha) (RG b f)
    RG a (RG b f) ∈ growingSecondPowerDomain ε hε h hh hb m g k ∧
    (RG a (RG b f), RG b f - (a : ℂ) • RG a (RG b f)) ∈ secondPowerGraph G ∧
    ((u - (a : ℂ) • v : (G).domain) : Hilbert) = G v ∧
    G (u - (a : ℂ) • v) =
      f - ((a + b : ℝ) : ℂ) • RG b f + ((a ^ 2 : ℝ) : ℂ) • RG a (RG b f) ∧
    ‖RG a (RG b f)‖ ≤ a⁻¹ * (b⁻¹ * ‖f‖) ∧
    ‖G v‖ ≤ 2 * (b⁻¹ * ‖f‖) ∧
    ‖G (u - (a : ℂ) • v)‖ ≤ 4 * ‖f‖ :=
  iterated_resolvent_three_tier_bounds G (RG a) (RG b) a b ha hb_pos
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha)
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k b hb_pos)
    (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k)
    (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k a ha) f

/-- If `f ∈ (S t).domain` and `0 < a`, then `RS t a f ∈ residualSecondPowerDomain t`. -/
theorem residual_resolvent_mem_secondPowerDomain (t a : ℝ) (ha : 0 < a)
    {f : Hilbert} (hf : f ∈ (S t).domain) :
    RS t a f ∈ residualSecondPowerDomain ε hε h hh hb m g k t :=
  resolvent_mem_secondPowerDomain_of_mem_domain (S t) (RS t a) a
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha) hf

/-- Unconditional iterated-resolvent second-power membership, exact second-power identity,
and three-tier norm bounds for the residual Hamiltonian `S t`. -/
theorem residual_iterated_resolvent_secondPower (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b)
    (f : Hilbert) :
    let u : (S t).domain :=
      point (S t) (RS t b) b
        (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t b hb_pos) f
    let v : (S t).domain :=
      point (S t) (RS t a) a
        (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha) (RS t b f)
    RS t a (RS t b f) ∈ residualSecondPowerDomain ε hε h hh hb m g k t ∧
    (RS t a (RS t b f), RS t b f - (a : ℂ) • RS t a (RS t b f)) ∈ secondPowerGraph (S t) ∧
    ((u - (a : ℂ) • v : (S t).domain) : Hilbert) = S t v ∧
    S t (u - (a : ℂ) • v) =
      f - ((a + b : ℝ) : ℂ) • RS t b f + ((a ^ 2 : ℝ) : ℂ) • RS t a (RS t b f) ∧
    ‖RS t a (RS t b f)‖ ≤ a⁻¹ * (b⁻¹ * ‖f‖) ∧
    ‖S t v‖ ≤ 2 * (b⁻¹ * ‖f‖) ∧
    ‖S t (u - (a : ℂ) • v)‖ ≤ 4 * ‖f‖ :=
  iterated_resolvent_three_tier_bounds (S t) (RS t a) (RS t b) a b ha hb_pos
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha)
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t b hb_pos)
    (KFCausalClosedGraphForm.hamiltonian_positive (SD t))
    (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t a ha) f

/-- If `f ∈ (H t).domain` and `0 < a`, then `RH t a f ∈ hamiltonianSecondPowerDomain t`. -/
theorem hamiltonian_resolvent_mem_secondPowerDomain (t a : ℝ) (ha : 0 < a)
    {f : Hilbert} (hf : f ∈ (H t).domain) :
    RH t a f ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t :=
  resolvent_mem_secondPowerDomain_of_mem_domain (H t) (RH t a) a
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha) hf

/-- Unconditional iterated-resolvent second-power membership, exact second-power identity,
and three-tier norm bounds for the full Hamiltonian `H t`. -/
theorem hamiltonian_iterated_resolvent_secondPower (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b)
    (f : Hilbert) :
    let u : (H t).domain :=
      point (H t) (RH t b) b
        (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t b hb_pos) f
    let v : (H t).domain :=
      point (H t) (RH t a) a
        (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha) (RH t b f)
    RH t a (RH t b f) ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t ∧
    (RH t a (RH t b f), RH t b f - (a : ℂ) • RH t a (RH t b f)) ∈ secondPowerGraph (H t) ∧
    ((u - (a : ℂ) • v : (H t).domain) : Hilbert) = H t v ∧
    H t (u - (a : ℂ) • v) =
      f - ((a + b : ℝ) : ℂ) • RH t b f + ((a ^ 2 : ℝ) : ℂ) • RH t a (RH t b f) ∧
    ‖RH t a (RH t b f)‖ ≤ a⁻¹ * (b⁻¹ * ‖f‖) ∧
    ‖H t v‖ ≤ 2 * (b⁻¹ * ‖f‖) ∧
    ‖H t (u - (a : ℂ) • v)‖ ≤ 4 * ‖f‖ :=
  iterated_resolvent_three_tier_bounds (H t) (RH t a) (RH t b) a b ha hb_pos
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t b hb_pos)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
    (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t a ha) f

/-- Unconditional simultaneous membership of all five iterated resolvents in their
second-power domains for EVERY `f : Hilbert` and ANY `0 < a`, `0 < b`. -/
theorem five_hamiltonians_iterated_resolvent_mem_secondPowerDomain
    (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    RT a (RT b f) ∈ staticSecondPowerDomain ε hε h ∧
    RP a (RP b f) ∈ potentialSecondPowerDomain ε hε h hh hb m g k ∧
    RG a (RG b f) ∈ growingSecondPowerDomain ε hε h hh hb m g k ∧
    RS t a (RS t b f) ∈ residualSecondPowerDomain ε hε h hh hb m g k t ∧
    RH t a (RH t b f) ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t :=
  ⟨(static_iterated_resolvent_secondPower ε hε h hh hb a b ha hb_pos f).1,
   (potential_iterated_resolvent_secondPower ε hε h hh hb m g k a b ha hb_pos f).1,
   (growing_iterated_resolvent_secondPower ε hε h hh hb m g k a b ha hb_pos f).1,
   (residual_iterated_resolvent_secondPower ε hε h hh hb m g k t a b ha hb_pos f).1,
   (hamiltonian_iterated_resolvent_secondPower ε hε h hh hb m g k t a b ha hb_pos f).1⟩

/-- Unconditional simultaneous three-tier norm bounds across all five Hamiltonians
for EVERY `f : Hilbert` and ANY `0 < a`, `0 < b`. -/
theorem five_hamiltonians_iterated_resolvent_norm_bounds
    (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    (‖RT a (RT b f)‖ ≤ a⁻¹ * (b⁻¹ * ‖f‖) ∧
     ‖RP a (RP b f)‖ ≤ a⁻¹ * (b⁻¹ * ‖f‖) ∧
     ‖RG a (RG b f)‖ ≤ a⁻¹ * (b⁻¹ * ‖f‖) ∧
     ‖RS t a (RS t b f)‖ ≤ a⁻¹ * (b⁻¹ * ‖f‖) ∧
     ‖RH t a (RH t b f)‖ ≤ a⁻¹ * (b⁻¹ * ‖f‖)) ∧
    (‖T (point T (RT a) a (staticResolvent_resolves ε hε h hb hh a ha) (RT b f))‖ ≤
       2 * (b⁻¹ * ‖f‖) ∧
     ‖P (point P (RP a) a
       (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha) (RP b f))‖ ≤
       2 * (b⁻¹ * ‖f‖) ∧
     ‖G (point G (RG a) a
       (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha) (RG b f))‖ ≤
       2 * (b⁻¹ * ‖f‖) ∧
     ‖S t (point (S t) (RS t a) a
       (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha) (RS t b f))‖ ≤
       2 * (b⁻¹ * ‖f‖) ∧
     ‖H t (point (H t) (RH t a) a
       (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha) (RH t b f))‖ ≤
       2 * (b⁻¹ * ‖f‖)) := by
  have hT := static_iterated_resolvent_secondPower ε hε h hh hb a b ha hb_pos f
  have hP := potential_iterated_resolvent_secondPower ε hε h hh hb m g k a b ha hb_pos f
  have hG := growing_iterated_resolvent_secondPower ε hε h hh hb m g k a b ha hb_pos f
  have hS := residual_iterated_resolvent_secondPower ε hε h hh hb m g k t a b ha hb_pos f
  have hH := hamiltonian_iterated_resolvent_secondPower ε hε h hh hb m g k t a b ha hb_pos f
  exact ⟨⟨hT.2.2.2.2.1, hP.2.2.2.2.1, hG.2.2.2.2.1, hS.2.2.2.2.1, hH.2.2.2.2.1⟩,
    ⟨hT.2.2.2.2.2.1, hP.2.2.2.2.2.1, hG.2.2.2.2.2.1, hS.2.2.2.2.2.1, hH.2.2.2.2.2.1⟩⟩

/-! ### 3. Unconditional 10-Domain Regularity of Iterated Hamiltonian Resolvents -/

/-- Unconditionally for EVERY `f : Hilbert`, ANY `0 < a`, `0 < b`, and ANY times `t, s : ℝ`,
the iterated resolvent `RH t a (RH t b f)` lies in `hamiltonianSecondPowerDomain t` and
simultaneously belongs to all 10 domains from `KFCausalClockFloorSecondPowerOperatorCores`. -/
theorem hamiltonian_iterated_resolvent_mem_ten_domains
    (t s a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    RH t a (RH t b f) ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t ∧
    RH t a (RH t b f) ∈ (H t).domain ∧
    RH t a (RH t b f) ∈ (K).domain ∧
    RH t a (RH t b f) ∈ (S t).domain ∧
    RH t a (RH t b f) ∈ (Eavg s).domain ∧
    RH t a (RH t b f) ∈ (Tstat).domain ∧
    RH t a (RH t b f) ∈ (Kroot).domain ∧
    RH t a (RH t b f) ∈ (Tpot).domain ∧
    RH t a (RH t b f) ∈ (Tgrow).domain ∧
    RH t a (RH t b f) ∈ (Tres s).domain ∧
    RH t a (RH t b f) ∈ (clockHalf ε).domain := by
  have h2 := (hamiltonian_iterated_resolvent_secondPower ε hε h hh hb m g k t a b ha hb_pos f).1
  have hdom : RH t a (RH t b f) ∈ (H t).domain :=
    KFCausalClockFloorSecondPowerOperatorCores.secondPowerDomain_le_domain (H t) h2
  exact ⟨h2, hamiltonian_domain_mem_ten_domains ε hε h hh hb m g k t s hdom⟩

/-- Unconditionally for EVERY `f : Hilbert`, ANY `0 < a`, `0 < b`, and ANY times `t, s : ℝ`,
both `RH t a (RH t b f)` and its first-power Hamiltonian output
`RH t b f - (a : ℂ) • RH t a (RH t b f)` belong simultaneously to all 10 domains from
`KFCausalClockFloorSecondPowerOperatorCores`. -/
theorem hamiltonian_iterated_resolvent_both_mem_ten_domains
    (t s a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let x : Hilbert := RH t a (RH t b f)
    let y : Hilbert := RH t b f - (a : ℂ) • RH t a (RH t b f)
    (x, y) ∈ secondPowerGraph (H t) ∧
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
  intro x y
  have hxy : (x, y) ∈ secondPowerGraph (H t) :=
    (hamiltonian_iterated_resolvent_secondPower ε hε h hh hb m g k t a b ha hb_pos f).2.1
  have h10 := hamiltonian_secondPowerGraph_both_mem_ten_domains ε hε h hh hb m g k t s hxy
  exact ⟨hxy, h10.2.1, h10.2.2⟩

/-- Applying the iterated Hamiltonian resolvent `RH t a (RH t b ·)` to any unitarily evolved
state `U s₁ s₂ f` (`f : Hilbert`) places `RH t a (RH t b (U s₁ s₂ f))` in
`hamiltonianSecondPowerDomain t` and in all 10 domains with `(s₁, s₂)`-independent
three-tier norm bounds (`a⁻¹ * (b⁻¹ * ‖f‖)`, `2 * (b⁻¹ * ‖f‖)`, `4 * ‖f‖`). -/
theorem evolved_hamiltonian_iterated_resolvent_regularity
    (s₁ s₂ t s a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let w : Hilbert := U s₁ s₂ f
    let u : (H t).domain :=
      point (H t) (RH t b) b
        (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t b hb_pos) w
    let v : (H t).domain :=
      point (H t) (RH t a) a
        (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha) (RH t b w)
    (RH t a (RH t b w) ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t ∧
     RH t a (RH t b w) ∈ (H t).domain ∧
     RH t a (RH t b w) ∈ (K).domain ∧
     RH t a (RH t b w) ∈ (S t).domain ∧
     RH t a (RH t b w) ∈ (Eavg s).domain ∧
     RH t a (RH t b w) ∈ (Tstat).domain ∧
     RH t a (RH t b w) ∈ (Kroot).domain ∧
     RH t a (RH t b w) ∈ (Tpot).domain ∧
     RH t a (RH t b w) ∈ (Tgrow).domain ∧
     RH t a (RH t b w) ∈ (Tres s).domain ∧
     RH t a (RH t b w) ∈ (clockHalf ε).domain) ∧
    ‖RH t a (RH t b w)‖ ≤ a⁻¹ * (b⁻¹ * ‖f‖) ∧
    ‖H t v‖ ≤ 2 * (b⁻¹ * ‖f‖) ∧
    ‖H t (u - (a : ℂ) • v)‖ ≤ 4 * ‖f‖ := by
  intro w u v
  have h10 := hamiltonian_iterated_resolvent_mem_ten_domains ε hε h hh hb m g k t s a b ha hb_pos w
  have hH := hamiltonian_iterated_resolvent_secondPower ε hε h hh hb m g k t a b ha hb_pos w
  have hnorm : ‖w‖ = ‖f‖ := evolution_norm ε hε h hh hw m g k s₁ s₂ f
  refine ⟨h10, ?_, ?_, ?_⟩
  · exact hH.2.2.2.2.1.trans_eq (by rw [hnorm])
  · exact hH.2.2.2.2.2.1.trans_eq (by rw [hnorm])
  · exact hH.2.2.2.2.2.2.trans_eq (by rw [hnorm])

#print axioms resolvent_output_eq_sub
#print axioms resolvent_mem_secondPowerGraph_of_mem_domain
#print axioms resolvent_mem_secondPowerDomain_of_mem_domain
#print axioms scaled_resolvent_norm_bound
#print axioms resolvent_first_order_norm_bound
#print axioms iterated_resolvent_mem_secondPowerGraph
#print axioms iterated_resolvent_mem_secondPowerDomain
#print axioms iterated_resolvent_first_power_eq
#print axioms iterated_resolvent_second_power_eq
#print axioms iterated_resolvent_diagonal_second_power_eq
#print axioms iterated_resolvent_commuted_second_power_eq
#print axioms iterated_resolvent_norm_bound
#print axioms iterated_resolvent_first_power_norm_bound
#print axioms iterated_resolvent_second_power_norm_bound
#print axioms iterated_resolvent_three_tier_bounds
#print axioms static_resolvent_mem_secondPowerDomain
#print axioms static_iterated_resolvent_secondPower
#print axioms potential_resolvent_mem_secondPowerDomain
#print axioms potential_iterated_resolvent_secondPower
#print axioms growing_resolvent_mem_secondPowerDomain
#print axioms growing_iterated_resolvent_secondPower
#print axioms residual_resolvent_mem_secondPowerDomain
#print axioms residual_iterated_resolvent_secondPower
#print axioms hamiltonian_resolvent_mem_secondPowerDomain
#print axioms hamiltonian_iterated_resolvent_secondPower
#print axioms five_hamiltonians_iterated_resolvent_mem_secondPowerDomain
#print axioms five_hamiltonians_iterated_resolvent_norm_bounds
#print axioms hamiltonian_iterated_resolvent_mem_ten_domains
#print axioms hamiltonian_iterated_resolvent_both_mem_ten_domains
#print axioms evolved_hamiltonian_iterated_resolvent_regularity

end

end UnifiedTheory.Audit.KFCausalClockFloorIteratedResolventSecondPowerCore
