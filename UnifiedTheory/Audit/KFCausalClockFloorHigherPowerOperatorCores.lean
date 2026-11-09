/- Inductive higher-power operator domains, iterated-resolvent power towers, and
ten-domain regularity for all five clock-floor Hamiltonians T, P, G, S(t), and H(t):
1. For any unbounded linear operator A : H →ₗ.[ℂ] H, defines the inductive r-th power
   domain `operatorPowerDomain A r : Submodule ℂ H` for all r : ℕ, proving exact
   identifications `operatorPowerDomain A 0 = ⊤`, `operatorPowerDomain A 1 = A.domain`,
   and `operatorPowerDomain A 2 = secondPowerDomain A`, together with the step
   monotonicity `operatorPowerDomain A (r + 1) ≤ operatorPowerDomain A r` and
   antitonicity `k ≤ r → operatorPowerDomain A r ≤ operatorPowerDomain A k`.
2. Proves the inductive resolvent regularity shift: if R resolves A at a, then
   `f ∈ operatorPowerDomain A r → R f ∈ operatorPowerDomain A (r + 1)` for all r : ℕ.
   Defines the r-fold iterated resolvent `iteratedResolventPower R r : H →L[ℂ] H` and
   proves unconditionally for every f : H and r : ℕ that
   `iteratedResolventPower R r f ∈ operatorPowerDomain A r`, together with exact
   first- and second-order recurrence identities and geometric norm bounds
   `‖iteratedResolventPower R r f‖ ≤ (a⁻¹) ^ r * ‖f‖`,
   `‖A (point A R a hr (iteratedResolventPower R r f))‖ ≤ 2 * ((a⁻¹) ^ r * ‖f‖)`, and
   `‖A (u - (a : ℂ) • v)‖ ≤ 4 * ((a⁻¹) ^ r * ‖f‖)`.
3. Instantiates the higher-power domain hierarchy for all five clock-floor Hamiltonians
   `T`, `P`, `G`, `S t`, and `H t`, proving unconditional r-th power domain membership,
   geometric norm decay, and simultaneous 10-domain regularity for all `r : ℕ`. -/
import UnifiedTheory.Audit.KFCausalClockFloorIteratedResolventSecondPowerCore

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorHigherPowerOperatorCores

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
  (secondPowerGraph secondPowerDomain mem_secondPowerDomain_iff
   hamiltonian_domain_mem_ten_domains)
open KFCausalClockFloorIteratedResolventSecondPowerCore
  (resolvent_output_eq_sub resolvent_first_order_norm_bound
   iterated_resolvent_diagonal_second_power_eq iterated_resolvent_second_power_norm_bound
   staticSecondPowerDomain potentialSecondPowerDomain growingSecondPowerDomain
   residualSecondPowerDomain hamiltonianSecondPowerDomain)

/-! ### 1. Inductive Higher-Power Operator Domains and Iterated Resolvent Towers -/

section AbstractHigherPower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The inductive `r`-th power domain `Dom(A^r)` of a linear map `A : H →ₗ.[ℂ] H`:
`operatorPowerDomain A 0 = ⊤`, and `operatorPowerDomain A (r + 1)` is the first-coordinate
image of `A.graph ⊓ (operatorPowerDomain A r).comap snd`. -/
def operatorPowerDomain (A : H →ₗ.[ℂ] H) : ℕ → Submodule ℂ H
  | 0 => ⊤
  | r + 1 =>
    (A.graph ⊓ (operatorPowerDomain A r).comap (LinearMap.snd ℂ H H)).map
      (LinearMap.fst ℂ H H)

/-- At `r = 0`, `operatorPowerDomain A 0 = ⊤`. -/
theorem operatorPowerDomain_zero (A : H →ₗ.[ℂ] H) :
    operatorPowerDomain A 0 = ⊤ :=
  rfl

/-- Explicit membership characterization for `operatorPowerDomain A (r + 1)`:
`x ∈ operatorPowerDomain A (r + 1) ↔ ∃ hx : x ∈ A.domain, A ⟨x, hx⟩ ∈ operatorPowerDomain A r`. -/
theorem mem_operatorPowerDomain_succ_iff (A : H →ₗ.[ℂ] H) (r : ℕ) (x : H) :
    x ∈ operatorPowerDomain A (r + 1) ↔
      ∃ hx : x ∈ A.domain, A ⟨x, hx⟩ ∈ operatorPowerDomain A r := by
  change (∃ p : H × H,
      (p ∈ A.graph ∧ p.2 ∈ operatorPowerDomain A r) ∧ p.1 = x) ↔
    ∃ hx : x ∈ A.domain, A ⟨x, hx⟩ ∈ operatorPowerDomain A r
  constructor
  · rintro ⟨⟨f, y⟩, ⟨hfy, hy⟩, rfl⟩
    let hx : f ∈ A.domain := LinearPMap.mem_domain_of_mem_graph hfy
    have heq : A ⟨f, hx⟩ = y := A.mem_graph_snd_inj' (A.mem_graph ⟨f, hx⟩) hfy rfl
    exact ⟨hx, heq.symm ▸ hy⟩
  · rintro ⟨hx, hAx⟩
    exact ⟨(x, A ⟨x, hx⟩), ⟨A.mem_graph ⟨x, hx⟩, hAx⟩, rfl⟩

/-- At `r = 1`, `operatorPowerDomain A 1` is identically `A.domain`. -/
theorem operatorPowerDomain_one_eq_domain (A : H →ₗ.[ℂ] H) :
    operatorPowerDomain A 1 = A.domain := by
  ext x
  rw [mem_operatorPowerDomain_succ_iff]
  exact ⟨fun ⟨hx, _⟩ => hx, fun hx => ⟨hx, Submodule.mem_top⟩⟩

/-- At `r = 2`, `operatorPowerDomain A 2` is identically `secondPowerDomain A`. -/
theorem operatorPowerDomain_two_eq_secondPowerDomain (A : H →ₗ.[ℂ] H) :
    operatorPowerDomain A 2 = secondPowerDomain A := by
  ext x
  rw [mem_operatorPowerDomain_succ_iff, operatorPowerDomain_one_eq_domain,
    mem_secondPowerDomain_iff]

/-- Step inclusion of higher-power domains:
`operatorPowerDomain A (r + 1) ≤ operatorPowerDomain A r` for all `r : ℕ`. -/
theorem operatorPowerDomain_succ_le (A : H →ₗ.[ℂ] H) :
    ∀ r : ℕ, operatorPowerDomain A (r + 1) ≤ operatorPowerDomain A r
  | 0 => le_top
  | r + 1 => by
    intro x hx
    rw [mem_operatorPowerDomain_succ_iff] at hx ⊢
    rcases hx with ⟨hx_dom, hAx⟩
    exact ⟨hx_dom, operatorPowerDomain_succ_le A r hAx⟩

/-- Antitonicity of `operatorPowerDomain A`: if `k ≤ r`, then
`operatorPowerDomain A r ≤ operatorPowerDomain A k`. -/
theorem operatorPowerDomain_le_of_le (A : H →ₗ.[ℂ] H) {k r : ℕ} (hkr : k ≤ r) :
    operatorPowerDomain A r ≤ operatorPowerDomain A k :=
  antitone_nat_of_succ_le (operatorPowerDomain_succ_le A) hkr

/-- Every higher-power domain `operatorPowerDomain A (r + 1)` (`r : ℕ`) is contained in `A.domain`. -/
theorem operatorPowerDomain_succ_le_domain (A : H →ₗ.[ℂ] H) (r : ℕ) :
    operatorPowerDomain A (r + 1) ≤ A.domain := by
  rw [← operatorPowerDomain_one_eq_domain]
  exact operatorPowerDomain_le_of_le A (Nat.succ_le_succ (Nat.zero_le r))

/-- Every higher-power domain `operatorPowerDomain A (r + 2)` (`r : ℕ`) is contained in
`secondPowerDomain A`. -/
theorem operatorPowerDomain_add_two_le_secondPowerDomain (A : H →ₗ.[ℂ] H) (r : ℕ) :
    operatorPowerDomain A (r + 2) ≤ secondPowerDomain A := by
  rw [← operatorPowerDomain_two_eq_secondPowerDomain]
  exact operatorPowerDomain_le_of_le A (Nat.add_le_add_right (Nat.zero_le r) 2)

/-- Inductive resolvent shift across all higher-power domains: if `Resolves A R a`, then
`f ∈ operatorPowerDomain A r → R f ∈ operatorPowerDomain A (r + 1)` for every `r : ℕ`. -/
theorem resolvent_mem_operatorPowerDomain_succ (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves A R a) :
    ∀ r : ℕ, ∀ {f : H}, f ∈ operatorPowerDomain A r → R f ∈ operatorPowerDomain A (r + 1)
  | 0, f, _ => by
    rw [operatorPowerDomain_one_eq_domain]
    exact (point A R a hr f).property
  | r + 1, f, hf => by
    rw [mem_operatorPowerDomain_succ_iff]
    refine ⟨(point A R a hr f).property, ?_⟩
    have hpt : (⟨R f, (point A R a hr f).property⟩ : A.domain) = point A R a hr f := rfl
    rw [hpt, resolvent_output_eq_sub A R a hr f]
    have hf_r : f ∈ operatorPowerDomain A r := operatorPowerDomain_succ_le A r hf
    have hRf : R f ∈ operatorPowerDomain A (r + 1) :=
      resolvent_mem_operatorPowerDomain_succ A R a hr r hf_r
    exact (operatorPowerDomain A (r + 1)).sub_mem hf
      ((operatorPowerDomain A (r + 1)).smul_mem (a : ℂ) hRf)

/-- Every higher-power domain `operatorPowerDomain A r` is invariant under the resolvent `R`. -/
theorem resolvent_maps_operatorPowerDomain_to_self (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves A R a) (r : ℕ) {f : H} (hf : f ∈ operatorPowerDomain A r) :
    R f ∈ operatorPowerDomain A r :=
  operatorPowerDomain_succ_le A r (resolvent_mem_operatorPowerDomain_succ A R a hr r hf)

/-- The `r`-fold iterated resolvent operator `R^r : H →L[ℂ] H`. -/
def iteratedResolventPower (R : H →L[ℂ] H) : ℕ → H →L[ℂ] H
  | 0 => ContinuousLinearMap.id ℂ H
  | r + 1 => R.comp (iteratedResolventPower R r)

/-- Evaluation of `iteratedResolventPower R 0` at `f : H`. -/
theorem iteratedResolventPower_zero_apply (R : H →L[ℂ] H) (f : H) :
    iteratedResolventPower R 0 f = f :=
  rfl

/-- Evaluation of `iteratedResolventPower R (r + 1)` at `f : H`. -/
theorem iteratedResolventPower_succ_apply (R : H →L[ℂ] H) (r : ℕ) (f : H) :
    iteratedResolventPower R (r + 1) f = R (iteratedResolventPower R r f) :=
  rfl

/-- Unconditionally for EVERY `f : H` and EVERY `r : ℕ`, the `r`-fold iterated resolvent
`iteratedResolventPower R r f` belongs to `operatorPowerDomain A r`. -/
theorem iteratedResolventPower_mem_operatorPowerDomain (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves A R a) :
    ∀ r : ℕ, ∀ f : H, iteratedResolventPower R r f ∈ operatorPowerDomain A r
  | 0, _ => Submodule.mem_top
  | r + 1, f =>
    resolvent_mem_operatorPowerDomain_succ A R a hr r
      (iteratedResolventPower_mem_operatorPowerDomain A R a hr r f)

/-- Unconditional geometric norm bound for the `r`-fold iterated resolvent:
`‖iteratedResolventPower R r f‖ ≤ (a⁻¹) ^ r * ‖f‖` for all `0 < a`, `r : ℕ`, and `f : H`. -/
theorem iteratedResolventPower_norm_bound (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves A R a) (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re) :
    ∀ r : ℕ, ∀ f : H, ‖iteratedResolventPower R r f‖ ≤ (a⁻¹) ^ r * ‖f‖
  | 0, f => by simp [iteratedResolventPower_zero_apply]
  | r + 1, f => by
    rw [iteratedResolventPower_succ_apply, pow_succ', mul_assoc]
    exact (resolvent_apply_norm_bound A R a ha hr hp (iteratedResolventPower R r f)).trans
      (mul_le_mul_of_nonneg_left (iteratedResolventPower_norm_bound A R a ha hr hp r f)
        (inv_pos.mpr ha).le)

/-- First-order operator recurrence and norm bound on the `(r + 1)`-fold iterated resolvent:
`A (point A R a hr (iteratedResolventPower R r f)) = iteratedResolventPower R r f - (a : ℂ) • iteratedResolventPower R (r + 1) f`
with norm bounded by `2 * ((a⁻¹) ^ r * ‖f‖)`. -/
theorem iteratedResolventPower_first_order_package (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (ha : 0 < a) (hr : Resolves A R a)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re) (r : ℕ) (f : H) :
    let u : A.domain := point A R a hr (iteratedResolventPower R r f)
    (u : H) = iteratedResolventPower R (r + 1) f ∧
    A u = iteratedResolventPower R r f - (a : ℂ) • iteratedResolventPower R (r + 1) f ∧
    A u ∈ operatorPowerDomain A r ∧
    ‖A u‖ ≤ 2 * ((a⁻¹) ^ r * ‖f‖) := by
  intro u
  have hmem_succ : iteratedResolventPower R (r + 1) f ∈ operatorPowerDomain A (r + 1) :=
    iteratedResolventPower_mem_operatorPowerDomain A R a hr (r + 1) f
  rw [mem_operatorPowerDomain_succ_iff] at hmem_succ
  rcases hmem_succ with ⟨_, hAu_mem⟩
  refine ⟨rfl, resolvent_output_eq_sub A R a hr (iteratedResolventPower R r f), hAu_mem, ?_⟩
  exact (resolvent_first_order_norm_bound A R a ha hr hp (iteratedResolventPower R r f)).trans
    (mul_le_mul_of_nonneg_left (iteratedResolventPower_norm_bound A R a ha hr hp r f)
      (by norm_num))

/-- Second-order operator recurrence and norm bound on the `(r + 2)`-fold iterated resolvent:
`A (u - (a : ℂ) • v) = iteratedResolventPower R r f - ((a + a : ℝ) : ℂ) • iteratedResolventPower R (r + 1) f + ((a * a : ℝ) : ℂ) • iteratedResolventPower R (r + 2) f`
with norm bounded by `4 * ((a⁻¹) ^ r * ‖f‖)`. -/
theorem iteratedResolventPower_second_order_package (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (ha : 0 < a) (hr : Resolves A R a)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hla : ∀ z : A.domain, R (A z + a • (z : H)) = (z : H)) (r : ℕ) (f : H) :
    let g : H := iteratedResolventPower R r f
    let u : A.domain := point A R a hr g
    let v : A.domain := point A R a hr (R g)
    ((u - (a : ℂ) • v : A.domain) : H) = A v ∧
    A (u - (a : ℂ) • v) =
      iteratedResolventPower R r f -
        ((a + a : ℝ) : ℂ) • iteratedResolventPower R (r + 1) f +
        ((a * a : ℝ) : ℂ) • iteratedResolventPower R (r + 2) f ∧
    ‖A (u - (a : ℂ) • v)‖ ≤ 4 * ((a⁻¹) ^ r * ‖f‖) := by
  intro g u v
  have hdiag := iterated_resolvent_diagonal_second_power_eq A R a hr g
  have hnorm2 := iterated_resolvent_second_power_norm_bound A R R a a ha ha hr hr hp hla g
  refine ⟨hdiag.1, hdiag.2, hnorm2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (iteratedResolventPower_norm_bound A R a ha hr hp r f)
    (by norm_num)

end AbstractHigherPower

/-! ### 2. Concrete Higher-Power Operator Domains for `T`, `P`, `G`, `S t`, and `H t` -/

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

/-- The `r`-th power domain `Dom(T^r)` of the static clock-floor operator `T`. -/
abbrev staticPowerDomain (r : ℕ) : Submodule ℂ Hilbert :=
  operatorPowerDomain T r

/-- The `r`-th power domain `Dom(P^r)` of the potential clock-floor Hamiltonian `P`. -/
abbrev potentialPowerDomain (r : ℕ) : Submodule ℂ Hilbert :=
  operatorPowerDomain P r

/-- The `r`-th power domain `Dom(G^r)` of the growing clock-floor Hamiltonian `G`. -/
abbrev growingPowerDomain (r : ℕ) : Submodule ℂ Hilbert :=
  operatorPowerDomain G r

/-- The `r`-th power domain `Dom(S(t)^r)` of the residual clock-floor Hamiltonian `S t`. -/
abbrev residualPowerDomain (t : ℝ) (r : ℕ) : Submodule ℂ Hilbert :=
  operatorPowerDomain (S t) r

/-- The `r`-th power domain `Dom(H(t)^r)` of the full clock-floor Hamiltonian `H t`. -/
abbrev hamiltonianPowerDomain (t : ℝ) (r : ℕ) : Submodule ℂ Hilbert :=
  operatorPowerDomain (H t) r

/-- Base-case identifications (`r = 1` and `r = 2`) for `staticPowerDomain`. -/
theorem staticPowerDomain_one_and_two :
    staticPowerDomain ε hε h 1 = (T).domain ∧
    staticPowerDomain ε hε h 2 = staticSecondPowerDomain ε hε h :=
  ⟨operatorPowerDomain_one_eq_domain T, operatorPowerDomain_two_eq_secondPowerDomain T⟩

/-- Base-case identifications (`r = 1` and `r = 2`) for `potentialPowerDomain`. -/
theorem potentialPowerDomain_one_and_two :
    potentialPowerDomain ε hε h hh hb m g k 1 = (P).domain ∧
    potentialPowerDomain ε hε h hh hb m g k 2 = potentialSecondPowerDomain ε hε h hh hb m g k :=
  ⟨operatorPowerDomain_one_eq_domain P, operatorPowerDomain_two_eq_secondPowerDomain P⟩

/-- Base-case identifications (`r = 1` and `r = 2`) for `growingPowerDomain`. -/
theorem growingPowerDomain_one_and_two :
    growingPowerDomain ε hε h hh hb m g k 1 = (G).domain ∧
    growingPowerDomain ε hε h hh hb m g k 2 = growingSecondPowerDomain ε hε h hh hb m g k :=
  ⟨operatorPowerDomain_one_eq_domain G, operatorPowerDomain_two_eq_secondPowerDomain G⟩

/-- Base-case identifications (`r = 1` and `r = 2`) for `residualPowerDomain t`. -/
theorem residualPowerDomain_one_and_two (t : ℝ) :
    residualPowerDomain ε hε h hh hb m g k t 1 = (S t).domain ∧
    residualPowerDomain ε hε h hh hb m g k t 2 = residualSecondPowerDomain ε hε h hh hb m g k t :=
  ⟨operatorPowerDomain_one_eq_domain (S t), operatorPowerDomain_two_eq_secondPowerDomain (S t)⟩

/-- Base-case identifications (`r = 1` and `r = 2`) for `hamiltonianPowerDomain t`. -/
theorem hamiltonianPowerDomain_one_and_two (t : ℝ) :
    hamiltonianPowerDomain ε hε h hh hb m g k t 1 = (H t).domain ∧
    hamiltonianPowerDomain ε hε h hh hb m g k t 2 =
      hamiltonianSecondPowerDomain ε hε h hh hb m g k t :=
  ⟨operatorPowerDomain_one_eq_domain (H t), operatorPowerDomain_two_eq_secondPowerDomain (H t)⟩

/-- Unconditional `r`-th power domain membership and geometric norm decay for the
iterated static resolvent `iteratedResolventPower (RT a) r`. -/
theorem static_iteratedResolventPower_regularity (a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert) :
    iteratedResolventPower (RT a) r f ∈ staticPowerDomain ε hε h r ∧
    ‖iteratedResolventPower (RT a) r f‖ ≤ (a⁻¹) ^ r * ‖f‖ :=
  ⟨iteratedResolventPower_mem_operatorPowerDomain T (RT a) a
     (staticResolvent_resolves ε hε h hb hh a ha) r f,
   iteratedResolventPower_norm_bound T (RT a) a ha
     (staticResolvent_resolves ε hε h hb hh a ha)
     (staticOperator_positive ε hε h) r f⟩

/-- Unconditional `r`-th power domain membership and geometric norm decay for the
iterated potential resolvent `iteratedResolventPower (RP a) r`. -/
theorem potential_iteratedResolventPower_regularity (a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert) :
    iteratedResolventPower (RP a) r f ∈ potentialPowerDomain ε hε h hh hb m g k r ∧
    ‖iteratedResolventPower (RP a) r f‖ ≤ (a⁻¹) ^ r * ‖f‖ :=
  ⟨iteratedResolventPower_mem_operatorPowerDomain P (RP a) a
     (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha) r f,
   iteratedResolventPower_norm_bound P (RP a) a ha
     (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha)
     (KFCausalClosedGraphForm.hamiltonian_positive PD) r f⟩

/-- Unconditional `r`-th power domain membership and geometric norm decay for the
iterated growing resolvent `iteratedResolventPower (RG a) r`. -/
theorem growing_iteratedResolventPower_regularity (a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert) :
    iteratedResolventPower (RG a) r f ∈ growingPowerDomain ε hε h hh hb m g k r ∧
    ‖iteratedResolventPower (RG a) r f‖ ≤ (a⁻¹) ^ r * ‖f‖ :=
  ⟨iteratedResolventPower_mem_operatorPowerDomain G (RG a) a
     (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha) r f,
   iteratedResolventPower_norm_bound G (RG a) a ha
     (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha)
     (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k) r f⟩

/-- Unconditional `r`-th power domain membership and geometric norm decay for the
iterated residual resolvent `iteratedResolventPower (RS t a) r`. -/
theorem residual_iteratedResolventPower_regularity (t a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert) :
    iteratedResolventPower (RS t a) r f ∈ residualPowerDomain ε hε h hh hb m g k t r ∧
    ‖iteratedResolventPower (RS t a) r f‖ ≤ (a⁻¹) ^ r * ‖f‖ :=
  ⟨iteratedResolventPower_mem_operatorPowerDomain (S t) (RS t a) a
     (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha) r f,
   iteratedResolventPower_norm_bound (S t) (RS t a) a ha
     (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha)
     (KFCausalClosedGraphForm.hamiltonian_positive (SD t)) r f⟩

/-- Unconditional `r`-th power domain membership and geometric norm decay for the
iterated full Hamiltonian resolvent `iteratedResolventPower (RH t a) r`. -/
theorem hamiltonian_iteratedResolventPower_regularity (t a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert) :
    iteratedResolventPower (RH t a) r f ∈ hamiltonianPowerDomain ε hε h hh hb m g k t r ∧
    ‖iteratedResolventPower (RH t a) r f‖ ≤ (a⁻¹) ^ r * ‖f‖ :=
  ⟨iteratedResolventPower_mem_operatorPowerDomain (H t) (RH t a) a
     (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha) r f,
   iteratedResolventPower_norm_bound (H t) (RH t a) a ha
     (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
     (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t) r f⟩

/-- Simultaneous `r`-th power domain membership and geometric norm bounds across all five
clock-floor Hamiltonians for EVERY `r : ℕ`, `0 < a`, `t : ℝ`, and `f : Hilbert`. -/
theorem five_hamiltonians_iteratedResolventPower_package
    (t a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert) :
    (iteratedResolventPower (RT a) r f ∈ staticPowerDomain ε hε h r ∧
     iteratedResolventPower (RP a) r f ∈ potentialPowerDomain ε hε h hh hb m g k r ∧
     iteratedResolventPower (RG a) r f ∈ growingPowerDomain ε hε h hh hb m g k r ∧
     iteratedResolventPower (RS t a) r f ∈ residualPowerDomain ε hε h hh hb m g k t r ∧
     iteratedResolventPower (RH t a) r f ∈ hamiltonianPowerDomain ε hε h hh hb m g k t r) ∧
    (‖iteratedResolventPower (RT a) r f‖ ≤ (a⁻¹) ^ r * ‖f‖ ∧
     ‖iteratedResolventPower (RP a) r f‖ ≤ (a⁻¹) ^ r * ‖f‖ ∧
     ‖iteratedResolventPower (RG a) r f‖ ≤ (a⁻¹) ^ r * ‖f‖ ∧
     ‖iteratedResolventPower (RS t a) r f‖ ≤ (a⁻¹) ^ r * ‖f‖ ∧
     ‖iteratedResolventPower (RH t a) r f‖ ≤ (a⁻¹) ^ r * ‖f‖) := by
  have hT := static_iteratedResolventPower_regularity ε hε h hh hb a ha r f
  have hP := potential_iteratedResolventPower_regularity ε hε h hh hb m g k a ha r f
  have hG := growing_iteratedResolventPower_regularity ε hε h hh hb m g k a ha r f
  have hS := residual_iteratedResolventPower_regularity ε hε h hh hb m g k t a ha r f
  have hH := hamiltonian_iteratedResolventPower_regularity ε hε h hh hb m g k t a ha r f
  exact ⟨⟨hT.1, hP.1, hG.1, hS.1, hH.1⟩, ⟨hT.2, hP.2, hG.2, hS.2, hH.2⟩⟩

/-! ### 3. 10-Domain Regularity for All Higher-Power Hamiltonian Domains and Resolvent Towers -/

/-- Every vector `x ∈ hamiltonianPowerDomain t (r + 1)` (`r : ℕ`) belongs simultaneously
to all 10 operator, form, and clock domains across all observation times `s : ℝ`. -/
theorem hamiltonianPowerDomain_succ_mem_ten_domains (t s : ℝ) (r : ℕ)
    {x : Hilbert} (hx : x ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 1)) :
    x ∈ (H t).domain ∧
    x ∈ (K).domain ∧
    x ∈ (S t).domain ∧
    x ∈ (Eavg s).domain ∧
    x ∈ (Tstat).domain ∧
    x ∈ (Kroot).domain ∧
    x ∈ (Tpot).domain ∧
    x ∈ (Tgrow).domain ∧
    x ∈ (Tres s).domain ∧
    x ∈ (clockHalf ε).domain :=
  hamiltonian_domain_mem_ten_domains ε hε h hh hb m g k t s
    (operatorPowerDomain_succ_le_domain (H t) r hx)

/-- Unconditionally for EVERY `f : Hilbert`, `r : ℕ`, `0 < a`, and `t, s : ℝ`, the
`(r + 1)`-fold iterated Hamiltonian resolvent `iteratedResolventPower (RH t a) (r + 1) f`
lies in `hamiltonianPowerDomain t (r + 1)` and in all 10 domains, with geometric norm bound
`‖iteratedResolventPower (RH t a) (r + 1) f‖ ≤ (a⁻¹) ^ (r + 1) * ‖f‖`. -/
theorem hamiltonian_iteratedResolventPower_succ_mem_ten_domains
    (t s a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert) :
    let x : Hilbert := iteratedResolventPower (RH t a) (r + 1) f
    x ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 1) ∧
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
    ‖x‖ ≤ (a⁻¹) ^ (r + 1) * ‖f‖ := by
  intro x
  have hH := hamiltonian_iteratedResolventPower_regularity ε hε h hh hb m g k t a ha (r + 1) f
  exact ⟨hH.1, hamiltonianPowerDomain_succ_mem_ten_domains ε hε h hh hb m g k t s r hH.1, hH.2⟩

/-- Unconditionally for EVERY `f : Hilbert`, `r : ℕ`, `0 < a`, and `s₁, s₂, t, s : ℝ`,
applying `iteratedResolventPower (RH t a) (r + 1)` to the unitarily evolved state `U s₁ s₂ f`
places the output in `hamiltonianPowerDomain t (r + 1)` and in all 10 domains with
`(s₁, s₂)`-independent geometric norm bound `(a⁻¹) ^ (r + 1) * ‖f‖`. -/
theorem evolved_hamiltonian_iteratedResolventPower_succ_regularity
    (s₁ s₂ t s a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert) :
    let w : Hilbert := U s₁ s₂ f
    let x : Hilbert := iteratedResolventPower (RH t a) (r + 1) w
    x ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 1) ∧
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
    ‖x‖ ≤ (a⁻¹) ^ (r + 1) * ‖f‖ := by
  intro w x
  have hpkg :=
    hamiltonian_iteratedResolventPower_succ_mem_ten_domains ε hε h hh hb m g k t s a ha r w
  have hnorm : ‖w‖ = ‖f‖ := evolution_norm ε hε h hh hw m g k s₁ s₂ f
  refine ⟨hpkg.1, hpkg.2.1, hpkg.2.2.trans_eq (by rw [hnorm])⟩

/-- First-order Hamiltonian recurrence and geometric norm bound on the `(r + 1)`-fold
iterated resolvent `iteratedResolventPower (RH t a) (r + 1) f` for any `r : ℕ` and `f : Hilbert`. -/
theorem hamiltonian_iteratedResolventPower_first_order_package
    (t a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert) :
    let u : (H t).domain :=
      point (H t) (RH t a) a
        (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
        (iteratedResolventPower (RH t a) r f)
    (u : Hilbert) = iteratedResolventPower (RH t a) (r + 1) f ∧
    H t u =
      iteratedResolventPower (RH t a) r f -
        (a : ℂ) • iteratedResolventPower (RH t a) (r + 1) f ∧
    H t u ∈ hamiltonianPowerDomain ε hε h hh hb m g k t r ∧
    ‖H t u‖ ≤ 2 * ((a⁻¹) ^ r * ‖f‖) :=
  iteratedResolventPower_first_order_package (H t) (RH t a) a ha
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t) r f

/-- Second-order Hamiltonian recurrence and geometric norm bound on the `(r + 2)`-fold
iterated resolvent `iteratedResolventPower (RH t a) (r + 2) f` for any `r : ℕ` and `f : Hilbert`. -/
theorem hamiltonian_iteratedResolventPower_second_order_package
    (t a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert) :
    let g_vec : Hilbert := iteratedResolventPower (RH t a) r f
    let u : (H t).domain :=
      point (H t) (RH t a) a
        (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha) g_vec
    let v : (H t).domain :=
      point (H t) (RH t a) a
        (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha) (RH t a g_vec)
    ((u - (a : ℂ) • v : (H t).domain) : Hilbert) = H t v ∧
    H t (u - (a : ℂ) • v) =
      iteratedResolventPower (RH t a) r f -
        ((a + a : ℝ) : ℂ) • iteratedResolventPower (RH t a) (r + 1) f +
        ((a * a : ℝ) : ℂ) • iteratedResolventPower (RH t a) (r + 2) f ∧
    ‖H t (u - (a : ℂ) • v)‖ ≤ 4 * ((a⁻¹) ^ r * ‖f‖) :=
  iteratedResolventPower_second_order_package (H t) (RH t a) a ha
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
    (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t a ha) r f

#print axioms operatorPowerDomain_zero
#print axioms mem_operatorPowerDomain_succ_iff
#print axioms operatorPowerDomain_one_eq_domain
#print axioms operatorPowerDomain_two_eq_secondPowerDomain
#print axioms operatorPowerDomain_succ_le
#print axioms operatorPowerDomain_le_of_le
#print axioms operatorPowerDomain_succ_le_domain
#print axioms operatorPowerDomain_add_two_le_secondPowerDomain
#print axioms resolvent_mem_operatorPowerDomain_succ
#print axioms resolvent_maps_operatorPowerDomain_to_self
#print axioms iteratedResolventPower_zero_apply
#print axioms iteratedResolventPower_succ_apply
#print axioms iteratedResolventPower_mem_operatorPowerDomain
#print axioms iteratedResolventPower_norm_bound
#print axioms iteratedResolventPower_first_order_package
#print axioms iteratedResolventPower_second_order_package
#print axioms staticPowerDomain_one_and_two
#print axioms potentialPowerDomain_one_and_two
#print axioms growingPowerDomain_one_and_two
#print axioms residualPowerDomain_one_and_two
#print axioms hamiltonianPowerDomain_one_and_two
#print axioms static_iteratedResolventPower_regularity
#print axioms potential_iteratedResolventPower_regularity
#print axioms growing_iteratedResolventPower_regularity
#print axioms residual_iteratedResolventPower_regularity
#print axioms hamiltonian_iteratedResolventPower_regularity
#print axioms five_hamiltonians_iteratedResolventPower_package
#print axioms hamiltonianPowerDomain_succ_mem_ten_domains
#print axioms hamiltonian_iteratedResolventPower_succ_mem_ten_domains
#print axioms evolved_hamiltonian_iteratedResolventPower_succ_regularity
#print axioms hamiltonian_iteratedResolventPower_first_order_package
#print axioms hamiltonian_iteratedResolventPower_second_order_package

end

end UnifiedTheory.Audit.KFCausalClockFloorHigherPowerOperatorCores
