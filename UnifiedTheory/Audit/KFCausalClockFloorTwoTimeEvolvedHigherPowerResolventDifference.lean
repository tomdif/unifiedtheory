/- Two-Time Evolved Higher-Power Iterated Resolvent and Yosida Identity Difference
Trajectories, Spectral-Shift Cocycle Algebra, 7-Domain Form-Energy Decompositions and
Two-Sided Exponential Trajectory Bounds, `hamiltonianPowerDomain` Cauchy Rate Bounds on
Evolved States, First-Order Hamiltonian Difference Recurrences, and Two-Time Weak
Continuity of Evolved Higher-Power Resolvent Differences:
1. Extends `KFCausalClockFloorTwoTimeEvolvedHigherPowerResolventRegularity` by introducing
   two-time evolved higher-power Yosida identity difference trajectories
   `evolvedHigherPowerIdentitySub s t a b r f := U(s, t)((a R_{H(s)}(a))^{r+2} f - (b R_{H(s)}(b))^{r+2} f)`
   and `higherPowerIdentitySubOfEvolvedState s t a b r f := (a R_{H(t)}(a))^{r+2}(U(s, t) f) - (b R_{H(t)}(b))^{r+2}(U(s, t) f)`
   alongside `evolvedHigherPowerResolventSub` and `higherPowerResolventSubOfEvolvedState`.
2. Proves exact linear difference decompositions, spectral-shift skew-symmetry (`a ↔ b`),
   diagonal vanishing (`a = b`), three-shift cocycle telescoping (`(a, b) + (b, c) = (a, c)`),
   unitary norm and inner-product preservation, and time-reversal recovery across all
   two-time evolved higher-power resolvent and Yosida identity difference trajectories.
3. Establishes exact five-channel form-energy decompositions (`Eavg q`, `Tstat`, `Kroot`,
   `Tpot`, `Tgrow`, `Tres q`) and two-sided exponential trajectory energy bounds for both
   `evolvedHigherPowerResolventSub` and `evolvedHigherPowerIdentitySub`, together with
   unconditional 7-domain form/clock membership and `2 * ‖f‖` contraction stability for
   `evolvedHigherPowerIdentitySub`.
4. Proves unconditional membership of `higherPowerIdentitySubOfEvolvedState` in
   `hamiltonianPowerDomain t (r + 2)`, `hamiltonianSecondPowerDomain t`, and all 10
   operator, form, and clock domains, an explicit mutual Cauchy rate bound on evolved
   power-domain states `higherPowerResolventOfEvolvedState s t c p f` with rate
   `((r + 2 : ℕ) : ℝ) * (a⁻¹ + b⁻¹) * (2 * ((c⁻¹) ^ (p + 1) * ‖f‖))`, first-order
   Hamiltonian difference recurrence and `hamiltonianPowerDomain t (r + 2)` regularity
   for `H(t)(higherPowerResolventSubOfEvolvedState s t a b r f)`, two-time weak Lipschitz
   continuity of evolved higher-power resolvent differences, and a master synthesis theorem. -/
import UnifiedTheory.Audit.KFCausalClockFloorTwoTimeEvolvedHigherPowerResolventRegularity

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorTwoTimeEvolvedHigherPowerResolventDifference

noncomputable section

open Filter
open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalPositiveResolventBounds (point)
open KFCausalClockFloorAveragedEvolution
  (evolution evolution_norm evolution_inner evolution_reverse)
open KFCausalClockFloorTwoTimeFormEvolutionIsomorphism
  (mem_averaged_domain_of_evolved mem_all_form_domains_of_evolved
   evolved_operator_form_energy_decompositions
   evolved_operator_form_energy_bounds)
open KFCausalClockFloorEvolvedResolventRegularity
  (evolved_two_time_resolvent_weak_diff_bound
   evolved_two_time_resolvent_weak_continuous)
open KFCausalClockFloorIteratedResolventSecondPowerCore
  (hamiltonianSecondPowerDomain)
open KFCausalClockFloorHigherPowerOperatorCores
  (operatorPowerDomain_add_two_le_secondPowerDomain
   iteratedResolventPower
   hamiltonianPowerDomain
   hamiltonian_iteratedResolventPower_regularity
   hamiltonianPowerDomain_succ_mem_ten_domains)
open KFCausalClockFloorHigherPowerYosidaGraphConvergence
  (iteratedIdentityPower)
open KFCausalClockFloorFiveOperatorHigherPowerResolventDifference
  (iteratedIdentityPower_sub_mem_operatorPowerDomain
   iteratedIdentityPower_sub_norm_le_two
   hamiltonianResolvent_iteratedIdentityPower_sub_domain_rate_bound
   hamiltonianResolvent_iteratedResolventPower_sub_succ_mem_ten_domains)
open KFCausalClockFloorTwoTimeEvolvedHigherPowerResolventRegularity
  (evolvedHigherPowerHamiltonianResolvent
   higherPowerResolventOfEvolvedState
   evolvedHigherPowerIdentity
   higherPowerIdentityOfEvolvedState
   evolvedHigherPowerResolventSub
   higherPowerResolventSubOfEvolvedState
   higherPowerResolventOfEvolvedState_first_order_recurrence_and_bound
   evolvedHigherPowerResolventSub_mem_all_form_domains_and_norm_le
   higherPowerResolventSubOfEvolvedState_mem_succ_power_and_ten_domains
   five_operator_higherPowerResolventSub_of_evolved_state_mem_powerDomains
   evolvedHigherPowerHamiltonianResolvent_two_time_outer_weak_diff_bound
   evolvedHigherPowerHamiltonianResolvent_two_time_outer_weak_continuous)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "U" => evolution ε hε h hh hw m g k
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "Kroot" => KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Tgrow" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (hamiltonian_bound ε h hw) hh m g k

/-- The two-time evolved `(r + 2)`-th order Yosida identity difference trajectory
`U(s, t)((a R_{H(s)}(a))^{r+2} f - (b R_{H(s)}(b))^{r+2} f)`. -/
def evolvedHigherPowerIdentitySub (s t a b : ℝ) (r : ℕ) (f : Hilbert) : Hilbert :=
  U s t (iteratedIdentityPower (RH s a) a (r + 2) f -
         iteratedIdentityPower (RH s b) b (r + 2) f)

/-- The `(r + 2)`-th order Yosida identity difference applied at time `t` to an evolved
state `U(s, t) f`: `(a R_{H(t)}(a))^{r+2}(U(s, t) f) - (b R_{H(t)}(b))^{r+2}(U(s, t) f)`. -/
def higherPowerIdentitySubOfEvolvedState (s t a b : ℝ) (r : ℕ) (f : Hilbert) : Hilbert :=
  iteratedIdentityPower (RH t a) a (r + 2) (U s t f) -
  iteratedIdentityPower (RH t b) b (r + 2) (U s t f)

/-! ### 1. Linear Decompositions, Spectral-Shift Cocycle Algebra, and Unitary Trajectory Invariants -/

/-- Exact linear difference decompositions expressing `evolvedHigherPowerResolventSub`,
`higherPowerResolventSubOfEvolvedState`, `evolvedHigherPowerIdentitySub`, and
`higherPowerIdentitySubOfEvolvedState` as differences of single-parameter evolved
higher-power trajectories. -/
theorem evolvedHigherPowerSub_linear_decompositions
    (s t a b : ℝ) (r : ℕ) (f : Hilbert) :
    evolvedHigherPowerResolventSub ε hε h hh hb m g k s t a b r f =
      evolvedHigherPowerHamiltonianResolvent ε hε h hh hb m g k s t a r f -
        evolvedHigherPowerHamiltonianResolvent ε hε h hh hb m g k s t b r f ∧
    higherPowerResolventSubOfEvolvedState ε hε h hh hb m g k s t a b r f =
      higherPowerResolventOfEvolvedState ε hε h hh hb m g k s t a r f -
        higherPowerResolventOfEvolvedState ε hε h hh hb m g k s t b r f ∧
    evolvedHigherPowerIdentitySub ε hε h hh hb m g k s t a b r f =
      evolvedHigherPowerIdentity ε hε h hh hb m g k s t a r f -
        evolvedHigherPowerIdentity ε hε h hh hb m g k s t b r f ∧
    higherPowerIdentitySubOfEvolvedState ε hε h hh hb m g k s t a b r f =
      higherPowerIdentityOfEvolvedState ε hε h hh hb m g k s t a r f -
        higherPowerIdentityOfEvolvedState ε hε h hh hb m g k s t b r f :=
  ⟨(U s t).map_sub
     (iteratedResolventPower (RH s a) (r + 2) f)
     (iteratedResolventPower (RH s b) (r + 2) f),
   rfl,
   (U s t).map_sub
     (iteratedIdentityPower (RH s a) a (r + 2) f)
     (iteratedIdentityPower (RH s b) b (r + 2) f),
   rfl⟩

/-- Diagonal vanishing (`a = b`), skew-symmetry (`a ↔ b`), and three-parameter cocycle
telescoping (`(a, b) + (b, c) = (a, c)`) for `evolvedHigherPowerResolventSub` and
`higherPowerResolventSubOfEvolvedState`. -/
theorem evolvedHigherPowerResolventSub_cocycle_identities
    (s t a b c : ℝ) (r : ℕ) (f : Hilbert) :
    evolvedHigherPowerResolventSub ε hε h hh hb m g k s t a a r f = 0 ∧
    higherPowerResolventSubOfEvolvedState ε hε h hh hb m g k s t a a r f = 0 ∧
    evolvedHigherPowerResolventSub ε hε h hh hb m g k s t b a r f =
      -evolvedHigherPowerResolventSub ε hε h hh hb m g k s t a b r f ∧
    higherPowerResolventSubOfEvolvedState ε hε h hh hb m g k s t b a r f =
      -higherPowerResolventSubOfEvolvedState ε hε h hh hb m g k s t a b r f ∧
    evolvedHigherPowerResolventSub ε hε h hh hb m g k s t a b r f +
        evolvedHigherPowerResolventSub ε hε h hh hb m g k s t b c r f =
      evolvedHigherPowerResolventSub ε hε h hh hb m g k s t a c r f ∧
    higherPowerResolventSubOfEvolvedState ε hε h hh hb m g k s t a b r f +
        higherPowerResolventSubOfEvolvedState ε hε h hh hb m g k s t b c r f =
      higherPowerResolventSubOfEvolvedState ε hε h hh hb m g k s t a c r f := by
  have h1 := (evolvedHigherPowerSub_linear_decompositions ε hε h hh hb m g k s t a a r f).1
  have h2 := (evolvedHigherPowerSub_linear_decompositions ε hε h hh hb m g k s t a b r f).1
  have h3 := (evolvedHigherPowerSub_linear_decompositions ε hε h hh hb m g k s t b a r f).1
  have h4 := (evolvedHigherPowerSub_linear_decompositions ε hε h hh hb m g k s t b c r f).1
  have h5 := (evolvedHigherPowerSub_linear_decompositions ε hε h hh hb m g k s t a c r f).1
  refine ⟨by rw [h1, sub_self], sub_self _, by rw [h2, h3]; abel, ?_, by rw [h2, h4, h5]; abel, ?_⟩
  · unfold higherPowerResolventSubOfEvolvedState; abel
  · unfold higherPowerResolventSubOfEvolvedState; abel

/-- Diagonal vanishing (`a = b`), skew-symmetry (`a ↔ b`), and three-parameter cocycle
telescoping (`(a, b) + (b, c) = (a, c)`) for `evolvedHigherPowerIdentitySub` and
`higherPowerIdentitySubOfEvolvedState`. -/
theorem evolvedHigherPowerIdentitySub_cocycle_identities
    (s t a b c : ℝ) (r : ℕ) (f : Hilbert) :
    evolvedHigherPowerIdentitySub ε hε h hh hb m g k s t a a r f = 0 ∧
    higherPowerIdentitySubOfEvolvedState ε hε h hh hb m g k s t a a r f = 0 ∧
    evolvedHigherPowerIdentitySub ε hε h hh hb m g k s t b a r f =
      -evolvedHigherPowerIdentitySub ε hε h hh hb m g k s t a b r f ∧
    higherPowerIdentitySubOfEvolvedState ε hε h hh hb m g k s t b a r f =
      -higherPowerIdentitySubOfEvolvedState ε hε h hh hb m g k s t a b r f ∧
    evolvedHigherPowerIdentitySub ε hε h hh hb m g k s t a b r f +
        evolvedHigherPowerIdentitySub ε hε h hh hb m g k s t b c r f =
      evolvedHigherPowerIdentitySub ε hε h hh hb m g k s t a c r f ∧
    higherPowerIdentitySubOfEvolvedState ε hε h hh hb m g k s t a b r f +
        higherPowerIdentitySubOfEvolvedState ε hε h hh hb m g k s t b c r f =
      higherPowerIdentitySubOfEvolvedState ε hε h hh hb m g k s t a c r f := by
  have h1 := (evolvedHigherPowerSub_linear_decompositions ε hε h hh hb m g k s t a a r f).2.2.1
  have h2 := (evolvedHigherPowerSub_linear_decompositions ε hε h hh hb m g k s t a b r f).2.2.1
  have h3 := (evolvedHigherPowerSub_linear_decompositions ε hε h hh hb m g k s t b a r f).2.2.1
  have h4 := (evolvedHigherPowerSub_linear_decompositions ε hε h hh hb m g k s t b c r f).2.2.1
  have h5 := (evolvedHigherPowerSub_linear_decompositions ε hε h hh hb m g k s t a c r f).2.2.1
  refine ⟨by rw [h1, sub_self], sub_self _, by rw [h2, h3]; abel, ?_, by rw [h2, h4, h5]; abel, ?_⟩
  · unfold higherPowerIdentitySubOfEvolvedState; abel
  · unfold higherPowerIdentitySubOfEvolvedState; abel

/-- Unitary norm preservation, exact time-reversal recovery, and inner-product invariance
along `evolvedHigherPowerResolventSub`. -/
theorem evolvedHigherPowerResolventSub_unitary_invariants
    (s t a b c d : ℝ) (r p : ℕ) (f f₁ f₂ : Hilbert) :
    ‖evolvedHigherPowerResolventSub ε hε h hh hb m g k s t a b r f‖ =
      ‖iteratedResolventPower (RH s a) (r + 2) f -
        iteratedResolventPower (RH s b) (r + 2) f‖ ∧
    U t s (evolvedHigherPowerResolventSub ε hε h hh hb m g k s t a b r f) =
      iteratedResolventPower (RH s a) (r + 2) f -
        iteratedResolventPower (RH s b) (r + 2) f ∧
    inner ℂ (evolvedHigherPowerResolventSub ε hε h hh hb m g k s t a b r f₁)
        (evolvedHigherPowerResolventSub ε hε h hh hb m g k s t c d p f₂) =
      inner ℂ
        (iteratedResolventPower (RH s a) (r + 2) f₁ -
          iteratedResolventPower (RH s b) (r + 2) f₁)
        (iteratedResolventPower (RH s c) (p + 2) f₂ -
          iteratedResolventPower (RH s d) (p + 2) f₂) :=
  ⟨evolution_norm ε hε h hh hw m g k s t _,
   congrArg (fun A : Hilbert →L[ℂ] Hilbert =>
     A (iteratedResolventPower (RH s a) (r + 2) f -
        iteratedResolventPower (RH s b) (r + 2) f))
     (evolution_reverse ε hε h hh hw m g k s t),
   evolution_inner ε hε h hh hw m g k s t _ _⟩

/-- Unitary norm preservation, exact time-reversal recovery, and inner-product invariance
along `evolvedHigherPowerIdentitySub`. -/
theorem evolvedHigherPowerIdentitySub_unitary_invariants
    (s t a b c d : ℝ) (r p : ℕ) (f f₁ f₂ : Hilbert) :
    ‖evolvedHigherPowerIdentitySub ε hε h hh hb m g k s t a b r f‖ =
      ‖iteratedIdentityPower (RH s a) a (r + 2) f -
        iteratedIdentityPower (RH s b) b (r + 2) f‖ ∧
    U t s (evolvedHigherPowerIdentitySub ε hε h hh hb m g k s t a b r f) =
      iteratedIdentityPower (RH s a) a (r + 2) f -
        iteratedIdentityPower (RH s b) b (r + 2) f ∧
    inner ℂ (evolvedHigherPowerIdentitySub ε hε h hh hb m g k s t a b r f₁)
        (evolvedHigherPowerIdentitySub ε hε h hh hb m g k s t c d p f₂) =
      inner ℂ
        (iteratedIdentityPower (RH s a) a (r + 2) f₁ -
          iteratedIdentityPower (RH s b) b (r + 2) f₁)
        (iteratedIdentityPower (RH s c) c (p + 2) f₂ -
          iteratedIdentityPower (RH s d) d (p + 2) f₂) :=
  ⟨evolution_norm ε hε h hh hw m g k s t _,
   congrArg (fun A : Hilbert →L[ℂ] Hilbert =>
     A (iteratedIdentityPower (RH s a) a (r + 2) f -
        iteratedIdentityPower (RH s b) b (r + 2) f))
     (evolution_reverse ε hε h hh hw m g k s t),
   evolution_inner ε hε h hh hw m g k s t _ _⟩

/-! ### 2. 7-Domain Form-Energy Decompositions and Two-Sided Trajectory Bounds on Evolved Differences -/

/-- Exact five-channel form-energy decompositions of
`‖Eavg q ⟨evolvedHigherPowerResolventSub s t a b r f, ...⟩‖ ^ 2` along the evolved trajectory
for all `s, t, q ∈ ℝ`, `0 < a, 0 < b`, and `r : ℕ`. -/
theorem evolvedHigherPowerResolventSub_operator_form_energy_decompositions
    (s t q a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f : Hilbert) :
    let hEs := (hamiltonianResolvent_iteratedResolventPower_sub_succ_mem_ten_domains
      ε hε h hh hb m g k s s a b ha hb_pos (r + 1) f).2.2.2.2.1
    let u := evolvedHigherPowerResolventSub ε hε h hh hb m g k s t a b r f
    let hdom := mem_all_form_domains_of_evolved ε hε h hh hb m g k s t q hEs
    ‖Eavg q ⟨u, hdom.1⟩‖ ^ 2 =
      ‖Tstat ⟨u, hdom.2.1⟩‖ ^ 2 +
        Real.exp (2 * q) * ‖Tgrow ⟨u, hdom.2.2.2.2.1⟩‖ ^ 2 ∧
    ‖Eavg q ⟨u, hdom.1⟩‖ ^ 2 =
      ‖Tstat ⟨u, hdom.2.1⟩‖ ^ 2 +
        Real.exp (2 * q) * ‖Kroot ⟨u, hdom.2.2.1⟩‖ ^ 2 +
        Real.exp (2 * q) * ‖Tpot ⟨u, hdom.2.2.2.1⟩‖ ^ 2 ∧
    ‖Eavg q ⟨u, hdom.1⟩‖ ^ 2 =
      Real.exp (2 * q) * ‖Kroot ⟨u, hdom.2.2.1⟩‖ ^ 2 +
        ‖Tres q ⟨u, hdom.2.2.2.2.2.1⟩‖ ^ 2 ∧
    ‖Tgrow ⟨u, hdom.2.2.2.2.1⟩‖ ^ 2 =
      ‖Kroot ⟨u, hdom.2.2.1⟩‖ ^ 2 + ‖Tpot ⟨u, hdom.2.2.2.1⟩‖ ^ 2 ∧
    ‖Tres q ⟨u, hdom.2.2.2.2.2.1⟩‖ ^ 2 =
      ‖Tstat ⟨u, hdom.2.1⟩‖ ^ 2 +
        Real.exp (2 * q) * ‖Tpot ⟨u, hdom.2.2.2.1⟩‖ ^ 2 :=
  evolved_operator_form_energy_decompositions ε hε h hh hb m g k s t q
    (hamiltonianResolvent_iteratedResolventPower_sub_succ_mem_ten_domains
      ε hε h hh hb m g k s s a b ha hb_pos (r + 1) f).2.2.2.2.1

/-- Two-sided exponential trajectory bounds comparing the evolved averaged form energy
`‖Eavg t ⟨evolvedHigherPowerResolventSub s t a b r f, ...⟩‖ ^ 2` with the initial difference
form energy at time `s`. -/
theorem evolvedHigherPowerResolventSub_two_sided_trajectory_energy_bounds
    (s t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f : Hilbert) :
    let d₀ := iteratedResolventPower (RH s a) (r + 2) f -
      iteratedResolventPower (RH s b) (r + 2) f
    let hEs : d₀ ∈ (Eavg s).domain :=
      (hamiltonianResolvent_iteratedResolventPower_sub_succ_mem_ten_domains
        ε hε h hh hb m g k s s a b ha hb_pos (r + 1) f).2.2.2.2.1
    let u := evolvedHigherPowerResolventSub ε hε h hh hb m g k s t a b r f
    let hEt : u ∈ (Eavg t).domain :=
      mem_averaged_domain_of_evolved ε hε h hh hb m g k s t t hEs
    Real.exp (-2 * |t - s|) * ‖Eavg s ⟨d₀, hEs⟩‖ ^ 2 ≤ ‖Eavg t ⟨u, hEt⟩‖ ^ 2 ∧
    ‖Eavg t ⟨u, hEt⟩‖ ^ 2 ≤ Real.exp (2 * |t - s|) * ‖Eavg s ⟨d₀, hEs⟩‖ ^ 2 := by
  intro d₀ hEs u hEt
  have hEb := evolved_operator_form_energy_bounds ε hε h hh hb m g k s t t hEs
  exact ⟨hEb.1, hEb.2.1⟩

/-- Unconditional `(r + 2)`-th power domain and 10-domain membership for the `(r + 2)`-th
order Yosida identity difference `iteratedIdentityPower (RH t a) a (r + 2) f - iteratedIdentityPower (RH t b) b (r + 2) f`
along with uniform stability bound `2 * ‖f‖`. -/
theorem hamiltonian_iteratedIdentityPower_sub_succ_mem_ten_domains
    (t q a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f : Hilbert) :
    let y : Hilbert :=
      iteratedIdentityPower (RH t a) a (r + 2) f -
        iteratedIdentityPower (RH t b) b (r + 2) f
    y ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    (y ∈ (H t).domain ∧
     y ∈ (K).domain ∧
     y ∈ (S t).domain ∧
     y ∈ (Eavg q).domain ∧
     y ∈ (Tstat).domain ∧
     y ∈ (Kroot).domain ∧
     y ∈ (Tpot).domain ∧
     y ∈ (Tgrow).domain ∧
     y ∈ (Tres q).domain ∧
     y ∈ (clockHalf ε).domain) ∧
    ‖y‖ ≤ 2 * ‖f‖ := by
  intro y
  have hmem : y ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) :=
    iteratedIdentityPower_sub_mem_operatorPowerDomain (H t) (RH t) a b ha hb_pos
      (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t) (r + 2) f
  have h10 := hamiltonianPowerDomain_succ_mem_ten_domains ε hε h hh hb m g k t q (r + 1) hmem
  have hnorm : ‖y‖ ≤ 2 * ‖f‖ :=
    iteratedIdentityPower_sub_norm_le_two (H t) (RH t) a b ha hb_pos
      (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
      (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
      (r + 2) f
  exact ⟨hmem, h10, hnorm⟩

/-- Unconditionally for all `s, t, q ∈ ℝ`, `0 < a, 0 < b`, and `r : ℕ`,
`evolvedHigherPowerIdentitySub s t a b r f` belongs simultaneously to all 7 form and clock
domains with uniform parameter-free stability `‖evolvedHigherPowerIdentitySub s t a b r f‖ ≤ 2 * ‖f‖`. -/
theorem evolvedHigherPowerIdentitySub_mem_all_form_domains_and_norm_le
    (s t q a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f : Hilbert) :
    let u := evolvedHigherPowerIdentitySub ε hε h hh hb m g k s t a b r f
    (u ∈ (Eavg q).domain ∧
     u ∈ (Tstat).domain ∧
     u ∈ (Kroot).domain ∧
     u ∈ (Tpot).domain ∧
     u ∈ (Tgrow).domain ∧
     u ∈ (Tres q).domain ∧
     u ∈ (clockHalf ε).domain) ∧
    ‖u‖ ≤ 2 * ‖f‖ := by
  intro u
  have hpkg := hamiltonian_iteratedIdentityPower_sub_succ_mem_ten_domains
    ε hε h hh hb m g k s s a b ha hb_pos r f
  have hdom := mem_all_form_domains_of_evolved ε hε h hh hb m g k s t q hpkg.2.1.2.2.2.1
  have hnorm : ‖u‖ ≤ 2 * ‖f‖ :=
    (evolution_norm ε hε h hh hw m g k s t
      (iteratedIdentityPower (RH s a) a (r + 2) f -
       iteratedIdentityPower (RH s b) b (r + 2) f)).trans_le hpkg.2.2
  exact ⟨hdom, hnorm⟩

/-- Exact five-channel form-energy decompositions of
`‖Eavg q ⟨evolvedHigherPowerIdentitySub s t a b r f, ...⟩‖ ^ 2` along the evolved trajectory. -/
theorem evolvedHigherPowerIdentitySub_operator_form_energy_decompositions
    (s t q a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f : Hilbert) :
    let hEs := (hamiltonian_iteratedIdentityPower_sub_succ_mem_ten_domains
      ε hε h hh hb m g k s s a b ha hb_pos r f).2.1.2.2.2.1
    let u := evolvedHigherPowerIdentitySub ε hε h hh hb m g k s t a b r f
    let hdom := mem_all_form_domains_of_evolved ε hε h hh hb m g k s t q hEs
    ‖Eavg q ⟨u, hdom.1⟩‖ ^ 2 =
      ‖Tstat ⟨u, hdom.2.1⟩‖ ^ 2 +
        Real.exp (2 * q) * ‖Tgrow ⟨u, hdom.2.2.2.2.1⟩‖ ^ 2 ∧
    ‖Eavg q ⟨u, hdom.1⟩‖ ^ 2 =
      ‖Tstat ⟨u, hdom.2.1⟩‖ ^ 2 +
        Real.exp (2 * q) * ‖Kroot ⟨u, hdom.2.2.1⟩‖ ^ 2 +
        Real.exp (2 * q) * ‖Tpot ⟨u, hdom.2.2.2.1⟩‖ ^ 2 ∧
    ‖Eavg q ⟨u, hdom.1⟩‖ ^ 2 =
      Real.exp (2 * q) * ‖Kroot ⟨u, hdom.2.2.1⟩‖ ^ 2 +
        ‖Tres q ⟨u, hdom.2.2.2.2.2.1⟩‖ ^ 2 ∧
    ‖Tgrow ⟨u, hdom.2.2.2.2.1⟩‖ ^ 2 =
      ‖Kroot ⟨u, hdom.2.2.1⟩‖ ^ 2 + ‖Tpot ⟨u, hdom.2.2.2.1⟩‖ ^ 2 ∧
    ‖Tres q ⟨u, hdom.2.2.2.2.2.1⟩‖ ^ 2 =
      ‖Tstat ⟨u, hdom.2.1⟩‖ ^ 2 +
        Real.exp (2 * q) * ‖Tpot ⟨u, hdom.2.2.2.1⟩‖ ^ 2 :=
  evolved_operator_form_energy_decompositions ε hε h hh hb m g k s t q
    (hamiltonian_iteratedIdentityPower_sub_succ_mem_ten_domains
      ε hε h hh hb m g k s s a b ha hb_pos r f).2.1.2.2.2.1

/-- Two-sided exponential trajectory bounds comparing the evolved averaged form energy of
`evolvedHigherPowerIdentitySub s t a b r f` at time `t` with its initial form energy at time `s`. -/
theorem evolvedHigherPowerIdentitySub_two_sided_trajectory_energy_bounds
    (s t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f : Hilbert) :
    let y₀ := iteratedIdentityPower (RH s a) a (r + 2) f -
      iteratedIdentityPower (RH s b) b (r + 2) f
    let hEs : y₀ ∈ (Eavg s).domain :=
      (hamiltonian_iteratedIdentityPower_sub_succ_mem_ten_domains
        ε hε h hh hb m g k s s a b ha hb_pos r f).2.1.2.2.2.1
    let u := evolvedHigherPowerIdentitySub ε hε h hh hb m g k s t a b r f
    let hEt : u ∈ (Eavg t).domain :=
      mem_averaged_domain_of_evolved ε hε h hh hb m g k s t t hEs
    Real.exp (-2 * |t - s|) * ‖Eavg s ⟨y₀, hEs⟩‖ ^ 2 ≤ ‖Eavg t ⟨u, hEt⟩‖ ^ 2 ∧
    ‖Eavg t ⟨u, hEt⟩‖ ^ 2 ≤ Real.exp (2 * |t - s|) * ‖Eavg s ⟨y₀, hEs⟩‖ ^ 2 := by
  intro y₀ hEs u hEt
  have hEb := evolved_operator_form_energy_bounds ε hε h hh hb m g k s t t hEs
  exact ⟨hEb.1, hEb.2.1⟩

/-! ### 3. Power-Domain Regularity of `higherPowerIdentitySubOfEvolvedState`, Evolved Cauchy Rate Bounds, and First-Order Hamiltonian Difference Recurrence -/

/-- Unconditionally for all `s, t, q ∈ ℝ`, `0 < a, 0 < b`, and `r : ℕ`,
`higherPowerIdentitySubOfEvolvedState s t a b r f` belongs simultaneously to
`hamiltonianPowerDomain t (r + 2)`, `hamiltonianSecondPowerDomain t`, and all 10 operator,
form, and clock domains, with `(s, t)`-independent stability bound `2 * ‖f‖`. -/
theorem higherPowerIdentitySubOfEvolvedState_mem_power_and_ten_domains
    (s t q a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f : Hilbert) :
    let y := higherPowerIdentitySubOfEvolvedState ε hε h hh hb m g k s t a b r f
    y ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    y ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t ∧
    (y ∈ (H t).domain ∧
     y ∈ (K).domain ∧
     y ∈ (S t).domain ∧
     y ∈ (Eavg q).domain ∧
     y ∈ (Tstat).domain ∧
     y ∈ (Kroot).domain ∧
     y ∈ (Tpot).domain ∧
     y ∈ (Tgrow).domain ∧
     y ∈ (Tres q).domain ∧
     y ∈ (clockHalf ε).domain) ∧
    ‖y‖ ≤ 2 * ‖f‖ := by
  intro y
  have hpkg := hamiltonian_iteratedIdentityPower_sub_succ_mem_ten_domains
    ε hε h hh hb m g k t q a b ha hb_pos r (U s t f)
  have h2 : y ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t :=
    operatorPowerDomain_add_two_le_secondPowerDomain (H t) r hpkg.1
  have hnorm : ‖y‖ ≤ 2 * ‖f‖ :=
    hpkg.2.2.trans_eq (congrArg (2 * ·) (evolution_norm ε hε h hh hw m g k s t f))
  exact ⟨hpkg.1, h2, hpkg.2.1, hnorm⟩

/-- Mutual `(a, b)` Cauchy rate bound on the `(r + 2)`-th order Yosida identity difference
applied at time `t` to any evolved higher-power resolvent state
`higherPowerResolventOfEvolvedState s t c p f`:
`‖(a R_{H(t)}(a))^{r+2} x - (b R_{H(t)}(b))^{r+2} x‖ ≤ ((r + 2 : ℕ) : ℝ) * (a⁻¹ + b⁻¹) * (2 * ((c⁻¹) ^ (p + 1) * ‖f‖))`. -/
theorem higherPowerIdentitySub_on_higherPowerResolventOfEvolvedState_rate_bound
    (s t a b c : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c)
    (r p : ℕ) (f : Hilbert) :
    let x := higherPowerResolventOfEvolvedState ε hε h hh hb m g k s t c p f
    ‖iteratedIdentityPower (RH t a) a (r + 2) x -
      iteratedIdentityPower (RH t b) b (r + 2) x‖ ≤
      ((r + 2 : ℕ) : ℝ) * (a⁻¹ + b⁻¹) * (2 * ((c⁻¹) ^ (p + 1) * ‖f‖)) := by
  intro x
  let w := U s t f
  let u : (H t).domain :=
    point (H t) (RH t c) c
      (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t c hc)
      (iteratedResolventPower (RH t c) (p + 1) w)
  have hrec := higherPowerResolventOfEvolvedState_first_order_recurrence_and_bound
    ε hε h hh hb m g k s t c hc p f
  have hcauchy := hamiltonianResolvent_iteratedIdentityPower_sub_domain_rate_bound
    ε hε h hh hb m g k t a b ha hb_pos (r + 2) u
  have hcoeff : 0 ≤ ((r + 2 : ℕ) : ℝ) * (a⁻¹ + b⁻¹) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hrec.2.2.2 hcoeff
  exact hcauchy.trans hmul

/-- First-order Hamiltonian difference recurrence, `(r + 1)`-th power domain membership,
and `(s, t)`-independent `2 * (((a⁻¹) ^ (r + 1) + (b⁻¹) ^ (r + 1)) * ‖f‖)` norm bound for
`higherPowerResolventSubOfEvolvedState s t a b r f`. -/
theorem higherPowerResolventSubOfEvolvedState_first_order_recurrence_and_bound
    (s t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f : Hilbert) :
    let w := U s t f
    let ua : (H t).domain :=
      point (H t) (RH t a) a
        (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
        (iteratedResolventPower (RH t a) (r + 1) w)
    let ub : (H t).domain :=
      point (H t) (RH t b) b
        (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t b hb_pos)
        (iteratedResolventPower (RH t b) (r + 1) w)
    (((ua - ub : (H t).domain) : Hilbert) =
      higherPowerResolventSubOfEvolvedState ε hε h hh hb m g k s t a b r f) ∧
    H t (ua - ub) =
      (iteratedResolventPower (RH t a) (r + 1) w -
        (a : ℂ) • higherPowerResolventOfEvolvedState ε hε h hh hb m g k s t a r f) -
      (iteratedResolventPower (RH t b) (r + 1) w -
        (b : ℂ) • higherPowerResolventOfEvolvedState ε hε h hh hb m g k s t b r f) ∧
    H t (ua - ub) ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 1) ∧
    ‖H t (ua - ub)‖ ≤ 2 * (((a⁻¹) ^ (r + 1) + (b⁻¹) ^ (r + 1)) * ‖f‖) := by
  intro w ua ub
  have ha_rec := higherPowerResolventOfEvolvedState_first_order_recurrence_and_bound
    ε hε h hh hb m g k s t a ha r f
  have hb_rec := higherPowerResolventOfEvolvedState_first_order_recurrence_and_bound
    ε hε h hh hb m g k s t b hb_pos r f
  have hval : ((ua - ub : (H t).domain) : Hilbert) =
      higherPowerResolventSubOfEvolvedState ε hε h hh hb m g k s t a b r f := by
    rfl
  have hH : H t (ua - ub) =
      (iteratedResolventPower (RH t a) (r + 1) w -
        (a : ℂ) • higherPowerResolventOfEvolvedState ε hε h hh hb m g k s t a r f) -
      (iteratedResolventPower (RH t b) (r + 1) w -
        (b : ℂ) • higherPowerResolventOfEvolvedState ε hε h hh hb m g k s t b r f) := by
    rw [(H t).map_sub, ha_rec.2.1, hb_rec.2.1]
  have hmem : H t (ua - ub) ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 1) := by
    rw [(H t).map_sub]
    exact (hamiltonianPowerDomain ε hε h hh hb m g k t (r + 1)).sub_mem ha_rec.2.2.1 hb_rec.2.2.1
  have hnorm : ‖H t (ua - ub)‖ ≤ 2 * (((a⁻¹) ^ (r + 1) + (b⁻¹) ^ (r + 1)) * ‖f‖) := by
    rw [(H t).map_sub]
    have htri := norm_sub_le (H t ua) (H t ub)
    have h1 := ha_rec.2.2.2
    have h2 := hb_rec.2.2.2
    linarith [add_mul ((a⁻¹) ^ (r + 1)) ((b⁻¹) ^ (r + 1)) ‖f‖]
  exact ⟨hval, hH, hmem, hnorm⟩

/-! ### 4. Two-Time Weak Lipschitz Bound and Weak Continuity for Evolved Higher-Power Resolvent Differences -/

/-- Exact algebraic decomposition of the two-time outer resolvent difference of
higher-power resolvent differences under `U t₁ t₂`. -/
theorem evolvedHigherPowerResolventSub_two_time_outer_split
    (t₁ t₂ s t q a b : ℝ) (r : ℕ) (f₂ : Hilbert) :
    (U t₁ t₂
      (RH s a (iteratedResolventPower (RH q a) (r + 1) f₂) -
       RH s b (iteratedResolventPower (RH q b) (r + 1) f₂)) -
     U t₁ t₂
      (RH t a (iteratedResolventPower (RH q a) (r + 1) f₂) -
       RH t b (iteratedResolventPower (RH q b) (r + 1) f₂))) =
    (U t₁ t₂ (RH s a (iteratedResolventPower (RH q a) (r + 1) f₂)) -
     U t₁ t₂ (RH t a (iteratedResolventPower (RH q a) (r + 1) f₂))) -
    (U t₁ t₂ (RH s b (iteratedResolventPower (RH q b) (r + 1) f₂)) -
     U t₁ t₂ (RH t b (iteratedResolventPower (RH q b) (r + 1) f₂))) := by
  rw [(U t₁ t₂).map_sub, (U t₁ t₂).map_sub]
  abel

/-- Unconditional two-time weak Lipschitz bound for the evolved `(r + 2)`-fold iterated
resolvent difference with outer resolvents evaluated at times `s` and `t`:
`‖inner ℂ f₁ (U t₁ t₂ (RH s a (RH q a)^{r+1} f₂ - RH s b (RH q b)^{r+1} f₂) - U t₁ t₂ (RH t a (RH q a)^{r+1} f₂ - RH t b (RH q b)^{r+1} f₂))‖ ≤ |Real.exp (2 * t) - Real.exp (2 * s)| * (2 * Real.exp (-(t + s)) * ‖f₁‖ * ((a⁻¹) ^ (r + 2) + (b⁻¹) ^ (r + 2)) * ‖f₂‖)`. -/
theorem evolvedHigherPowerResolventSub_two_time_outer_weak_diff_bound
    (t₁ t₂ s t q a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f₁ f₂ : Hilbert) :
    ‖inner ℂ f₁
      (U t₁ t₂
        (RH s a (iteratedResolventPower (RH q a) (r + 1) f₂) -
         RH s b (iteratedResolventPower (RH q b) (r + 1) f₂)) -
       U t₁ t₂
        (RH t a (iteratedResolventPower (RH q a) (r + 1) f₂) -
         RH t b (iteratedResolventPower (RH q b) (r + 1) f₂)))‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| *
        (2 * Real.exp (-(t + s)) * a⁻¹ * ‖f₁‖ * ((a⁻¹) ^ (r + 1) * ‖f₂‖)) +
      |Real.exp (2 * t) - Real.exp (2 * s)| *
        (2 * Real.exp (-(t + s)) * b⁻¹ * ‖f₁‖ * ((b⁻¹) ^ (r + 1) * ‖f₂‖)) := by
  rw [evolvedHigherPowerResolventSub_two_time_outer_split ε hε h hh hb m g k t₁ t₂ s t q a b r f₂,
    inner_sub_right]
  have htri := norm_sub_le
    (inner ℂ f₁
      (U t₁ t₂ (RH s a (iteratedResolventPower (RH q a) (r + 1) f₂)) -
       U t₁ t₂ (RH t a (iteratedResolventPower (RH q a) (r + 1) f₂))))
    (inner ℂ f₁
      (U t₁ t₂ (RH s b (iteratedResolventPower (RH q b) (r + 1) f₂)) -
       U t₁ t₂ (RH t b (iteratedResolventPower (RH q b) (r + 1) f₂))))
  have ha_bd := evolvedHigherPowerHamiltonianResolvent_two_time_outer_weak_diff_bound
    ε hε h hh hb m g k t₁ t₂ s t q a ha r f₁ f₂
  have hb_bd := evolvedHigherPowerHamiltonianResolvent_two_time_outer_weak_diff_bound
    ε hε h hh hb m g k t₁ t₂ s t q b hb_pos r f₁ f₂
  exact htri.trans (add_le_add ha_bd hb_bd)

/-- Unconditional weak continuity
`⟪f₁, U t₁ t₂ (RH s a (RH q a)^{r+1} f₂ - RH s b (RH q b)^{r+1} f₂)⟫ → ⟪f₁, U t₁ t₂ (RH t a (RH q a)^{r+1} f₂ - RH t b (RH q b)^{r+1} f₂)⟫`
as `s → t` for all `f₁, f₂ : Hilbert`, `0 < a, 0 < b`, and `r : ℕ`. -/
theorem evolvedHigherPowerResolventSub_two_time_outer_weak_continuous
    (t₁ t₂ t q a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f₁ f₂ : Hilbert) :
    Tendsto
      (fun s : ℝ => inner ℂ f₁
        (U t₁ t₂
          (RH s a (iteratedResolventPower (RH q a) (r + 1) f₂) -
           RH s b (iteratedResolventPower (RH q b) (r + 1) f₂))))
      (𝓝 t)
      (𝓝 (inner ℂ f₁
        (U t₁ t₂
          (RH t a (iteratedResolventPower (RH q a) (r + 1) f₂) -
           RH t b (iteratedResolventPower (RH q b) (r + 1) f₂))))) := by
  have heq :
      (fun s : ℝ => inner ℂ f₁
        (U t₁ t₂
          (RH s a (iteratedResolventPower (RH q a) (r + 1) f₂) -
           RH s b (iteratedResolventPower (RH q b) (r + 1) f₂)))) =
      (fun s : ℝ =>
        inner ℂ f₁ (U t₁ t₂ (RH s a (iteratedResolventPower (RH q a) (r + 1) f₂))) -
        inner ℂ f₁ (U t₁ t₂ (RH s b (iteratedResolventPower (RH q b) (r + 1) f₂)))) := by
    ext s
    rw [(U t₁ t₂).map_sub, inner_sub_right]
  have hlim_eq :
      inner ℂ f₁
        (U t₁ t₂
          (RH t a (iteratedResolventPower (RH q a) (r + 1) f₂) -
           RH t b (iteratedResolventPower (RH q b) (r + 1) f₂))) =
      inner ℂ f₁ (U t₁ t₂ (RH t a (iteratedResolventPower (RH q a) (r + 1) f₂))) -
      inner ℂ f₁ (U t₁ t₂ (RH t b (iteratedResolventPower (RH q b) (r + 1) f₂))) := by
    rw [(U t₁ t₂).map_sub, inner_sub_right]
  rw [heq, hlim_eq]
  exact (evolvedHigherPowerHamiltonianResolvent_two_time_outer_weak_continuous
    ε hε h hh hb m g k t₁ t₂ t q a ha r f₁ f₂).sub
    (evolvedHigherPowerHamiltonianResolvent_two_time_outer_weak_continuous
      ε hε h hh hb m g k t₁ t₂ t q b hb_pos r f₁ f₂)

/-- Master Two-Time Evolved Higher-Power Resolvent and Yosida Identity Difference Synthesis uniting:
(1) Spectral-shift cocycle identities for `evolvedHigherPowerResolventSub` and `evolvedHigherPowerIdentitySub`,
(2) 7-domain form/clock regularity and two-sided exponential trajectory energy bounds for both
    `evolvedHigherPowerResolventSub` and `evolvedHigherPowerIdentitySub`,
(3) `(r + 3)`-th power domain lift of `higherPowerResolventSubOfEvolvedState` and `(r + 2)`-th
    power domain regularity of `higherPowerIdentitySubOfEvolvedState` across all 10 domains,
(4) Mutual `(a, b)` Cauchy rate bound on `higherPowerResolventOfEvolvedState s t c p f`, and
(5) Unconditional two-time weak continuity of evolved higher-power resolvent differences. -/
theorem two_time_evolved_higher_power_resolvent_difference_master_synthesis
    (t₁ t₂ s t q a b c : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c)
    (r p : ℕ) (f f₁ f₂ : Hilbert) :
    let u_res := evolvedHigherPowerResolventSub ε hε h hh hb m g k s t a b r f
    let u_id := evolvedHigherPowerIdentitySub ε hε h hh hb m g k s t a b r f
    let d_res := higherPowerResolventSubOfEvolvedState ε hε h hh hb m g k s t a b r f
    let d_id := higherPowerIdentitySubOfEvolvedState ε hε h hh hb m g k s t a b r f
    let x_ev := higherPowerResolventOfEvolvedState ε hε h hh hb m g k s t c p f
    (u_res + evolvedHigherPowerResolventSub ε hε h hh hb m g k s t b c r f =
       evolvedHigherPowerResolventSub ε hε h hh hb m g k s t a c r f ∧
     u_id + evolvedHigherPowerIdentitySub ε hε h hh hb m g k s t b c r f =
       evolvedHigherPowerIdentitySub ε hε h hh hb m g k s t a c r f) ∧
    ((u_res ∈ (Eavg q).domain ∧
      u_res ∈ (Tstat).domain ∧
      u_res ∈ (Kroot).domain ∧
      u_res ∈ (Tpot).domain ∧
      u_res ∈ (Tgrow).domain ∧
      u_res ∈ (Tres q).domain ∧
      u_res ∈ (clockHalf ε).domain) ∧
     ‖u_res‖ ≤ ((a⁻¹) ^ (r + 2) + (b⁻¹) ^ (r + 2)) * ‖f‖) ∧
    ((u_id ∈ (Eavg q).domain ∧
      u_id ∈ (Tstat).domain ∧
      u_id ∈ (Kroot).domain ∧
      u_id ∈ (Tpot).domain ∧
      u_id ∈ (Tgrow).domain ∧
      u_id ∈ (Tres q).domain ∧
      u_id ∈ (clockHalf ε).domain) ∧
     ‖u_id‖ ≤ 2 * ‖f‖) ∧
    (d_res ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 3) ∧
     d_res ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t ∧
     d_id ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
     d_id ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t) ∧
    ‖iteratedIdentityPower (RH t a) a (r + 2) x_ev -
      iteratedIdentityPower (RH t b) b (r + 2) x_ev‖ ≤
      ((r + 2 : ℕ) : ℝ) * (a⁻¹ + b⁻¹) * (2 * ((c⁻¹) ^ (p + 1) * ‖f‖)) ∧
    Tendsto
      (fun s' : ℝ => inner ℂ f₁
        (U t₁ t₂
          (RH s' a (iteratedResolventPower (RH q a) (r + 1) f₂) -
           RH s' b (iteratedResolventPower (RH q b) (r + 1) f₂))))
      (𝓝 t)
      (𝓝 (inner ℂ f₁
        (U t₁ t₂
          (RH t a (iteratedResolventPower (RH q a) (r + 1) f₂) -
           RH t b (iteratedResolventPower (RH q b) (r + 1) f₂))))) := by
  intro u_res u_id d_res d_id x_ev
  have hcoc_res := evolvedHigherPowerResolventSub_cocycle_identities
    ε hε h hh hb m g k s t a b c r f
  have hcoc_id := evolvedHigherPowerIdentitySub_cocycle_identities
    ε hε h hh hb m g k s t a b c r f
  have hd_res := higherPowerResolventSubOfEvolvedState_mem_succ_power_and_ten_domains
    ε hε h hh hb m g k s t q a b ha hb_pos r f
  have hd_id := higherPowerIdentitySubOfEvolvedState_mem_power_and_ten_domains
    ε hε h hh hb m g k s t q a b ha hb_pos r f
  exact ⟨⟨hcoc_res.2.2.2.2.1, hcoc_id.2.2.2.2.1⟩,
    evolvedHigherPowerResolventSub_mem_all_form_domains_and_norm_le
      ε hε h hh hb m g k s t q a b ha hb_pos r f,
    evolvedHigherPowerIdentitySub_mem_all_form_domains_and_norm_le
      ε hε h hh hb m g k s t q a b ha hb_pos r f,
    ⟨hd_res.1, hd_res.2.1, hd_id.1, hd_id.2.1⟩,
    higherPowerIdentitySub_on_higherPowerResolventOfEvolvedState_rate_bound
      ε hε h hh hb m g k s t a b c ha hb_pos hc r p f,
    evolvedHigherPowerResolventSub_two_time_outer_weak_continuous
      ε hε h hh hb m g k t₁ t₂ t q a b ha hb_pos r f₁ f₂⟩

#print axioms evolvedHigherPowerSub_linear_decompositions
#print axioms evolvedHigherPowerResolventSub_cocycle_identities
#print axioms evolvedHigherPowerIdentitySub_cocycle_identities
#print axioms evolvedHigherPowerResolventSub_unitary_invariants
#print axioms evolvedHigherPowerIdentitySub_unitary_invariants
#print axioms evolvedHigherPowerResolventSub_operator_form_energy_decompositions
#print axioms evolvedHigherPowerResolventSub_two_sided_trajectory_energy_bounds
#print axioms hamiltonian_iteratedIdentityPower_sub_succ_mem_ten_domains
#print axioms evolvedHigherPowerIdentitySub_mem_all_form_domains_and_norm_le
#print axioms evolvedHigherPowerIdentitySub_operator_form_energy_decompositions
#print axioms evolvedHigherPowerIdentitySub_two_sided_trajectory_energy_bounds
#print axioms higherPowerIdentitySubOfEvolvedState_mem_power_and_ten_domains
#print axioms higherPowerIdentitySub_on_higherPowerResolventOfEvolvedState_rate_bound
#print axioms higherPowerResolventSubOfEvolvedState_first_order_recurrence_and_bound
#print axioms evolvedHigherPowerResolventSub_two_time_outer_split
#print axioms evolvedHigherPowerResolventSub_two_time_outer_weak_diff_bound
#print axioms evolvedHigherPowerResolventSub_two_time_outer_weak_continuous
#print axioms two_time_evolved_higher_power_resolvent_difference_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorTwoTimeEvolvedHigherPowerResolventDifference
