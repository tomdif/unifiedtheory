/- Two-Time Evolved Higher-Power Iterated Resolvent Trajectory Regularity,
`(r + 2)`-th Power Domain Hierarchy, Scaled Yosida Identity Trajectory Contraction,
`(r + 3)`-th Power Resolvent Difference Lift, and Two-Time Weak Continuity:
1. Extends two-time evolved iterated-resolvent trajectory regularity from 2-fold
   (`evolvedIteratedHamiltonianResolvent`, `iteratedResolventOfEvolvedState`) to
   arbitrary `(r + 2)`-fold iterated resolvent powers
   `evolvedHigherPowerHamiltonianResolvent s t a r f := U(s, t)(R_{H(s)}(a)^{r+2} f)` and
   `higherPowerResolventOfEvolvedState s t a r f := R_{H(t)}(a)^{r+2}(U(s, t) f)`,
   as well as scaled Yosida identity powers
   `evolvedHigherPowerIdentity s t a r f := U(s, t)((a R_{H(s)}(a))^{r+2} f)` and
   `higherPowerIdentityOfEvolvedState s t a r f := (a R_{H(t)}(a))^{r+2}(U(s, t) f)`.
2. Proves unconditional membership of `evolvedHigherPowerHamiltonianResolvent` in all
   7 form and clock domains (`Eavg q`, `Tstat`, `Kroot`, `Tpot`, `Tgrow`, `Tres q`,
   `clockHalf ε`), exact five-channel form-energy decompositions, two-sided exponential
   trajectory energy bounds, geometric `(a⁻¹)^{r+2} ‖f‖` norm decay, and explicit
   source-norm energy bounds across all form channels.
3. Establishes unconditional membership of `higherPowerResolventOfEvolvedState` and
   `higherPowerIdentityOfEvolvedState` in `hamiltonianPowerDomain t (r + 2)`,
   `hamiltonianSecondPowerDomain t`, and all 10 operator, form, and clock domains,
   together with first- and second-order Hamiltonian recurrences, `(r + 3)`-th power
   domain regularity lift for higher-power resolvent differences on evolved states
   across all five clock-floor Hamiltonians, two-time weak Lipschitz continuity,
   and a master evolved higher-power resolvent synthesis theorem. -/
import UnifiedTheory.Audit.KFCausalClockFloorEvolvedIteratedResolventTrajectoryRegularity
import UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorHigherPowerResolventDifference

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorTwoTimeEvolvedHigherPowerResolventRegularity

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
  (hamiltonian_resolvent_averaged_energy_le
   evolved_resolvent_multi_domain_energy_bounds
   evolved_two_time_resolvent_weak_diff_bound
   evolved_two_time_resolvent_weak_continuous)
open KFCausalClockFloorIteratedResolventSecondPowerCore
  (hamiltonianSecondPowerDomain)
open KFCausalClockFloorHigherPowerOperatorCores
  (operatorPowerDomain_add_two_le_secondPowerDomain
   iteratedResolventPower iteratedResolventPower_zero_apply iteratedResolventPower_succ_apply
   staticPowerDomain potentialPowerDomain growingPowerDomain
   residualPowerDomain hamiltonianPowerDomain
   hamiltonian_iteratedResolventPower_regularity
   hamiltonianPowerDomain_succ_mem_ten_domains
   hamiltonian_iteratedResolventPower_succ_mem_ten_domains
   evolved_hamiltonian_iteratedResolventPower_succ_regularity
   hamiltonian_iteratedResolventPower_first_order_package
   hamiltonian_iteratedResolventPower_second_order_package)
open KFCausalClockFloorHigherPowerYosidaGraphConvergence
  (iteratedIdentityPower
   hamiltonian_iteratedIdentityPower_succ_mem_ten_domains
   evolved_hamiltonian_iteratedIdentityPower_succ_regularity)
open KFCausalClockFloorFiveOperatorHigherPowerResolventDifference
  (iteratedResolventPower_sub_norm_bound
   staticResolvent_iteratedResolventPower_sub_succ_mem_powerDomain
   potentialResolvent_iteratedResolventPower_sub_succ_mem_powerDomain
   growingResolvent_iteratedResolventPower_sub_succ_mem_powerDomain
   residualResolvent_iteratedResolventPower_sub_succ_mem_powerDomain
   hamiltonianResolvent_iteratedResolventPower_sub_succ_eq
   hamiltonianResolvent_iteratedResolventPower_sub_succ_mem_powerDomain
   hamiltonianResolvent_iteratedIdentityPower_comm
   hamiltonianResolvent_iteratedResolventPower_sub_succ_mem_ten_domains)
open KFCausalClockFloorEvolvedIteratedResolventTrajectoryRegularity
  (evolvedIteratedHamiltonianResolvent iteratedResolventOfEvolvedState)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "U" => evolution ε hε h hh hw m g k
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RT" => KFCausalClockFloorStaticClockCore.resolvent ε hε h hh hw m g k 0
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

/-- The two-time evolved `(r + 2)`-fold iterated Hamiltonian resolvent trajectory
`U(s, t)(R_{H(s)}(a)^{r+2} f)`. -/
def evolvedHigherPowerHamiltonianResolvent (s t a : ℝ) (r : ℕ) (f : Hilbert) : Hilbert :=
  U s t (iteratedResolventPower (RH s a) (r + 2) f)

/-- The `(r + 2)`-fold iterated Hamiltonian resolvent applied at time `t` to an evolved state
`U(s, t) f`: `R_{H(t)}(a)^{r+2}(U(s, t) f)`. -/
def higherPowerResolventOfEvolvedState (s t a : ℝ) (r : ℕ) (f : Hilbert) : Hilbert :=
  iteratedResolventPower (RH t a) (r + 2) (U s t f)

/-- The two-time evolved `(r + 2)`-th order Yosida identity approximant trajectory
`U(s, t)((a R_{H(s)}(a))^{r+2} f)`. -/
def evolvedHigherPowerIdentity (s t a : ℝ) (r : ℕ) (f : Hilbert) : Hilbert :=
  U s t (iteratedIdentityPower (RH s a) a (r + 2) f)

/-- The `(r + 2)`-th order Yosida identity approximant applied at time `t` to an evolved state
`U(s, t) f`: `(a R_{H(t)}(a))^{r+2}(U(s, t) f)`. -/
def higherPowerIdentityOfEvolvedState (s t a : ℝ) (r : ℕ) (f : Hilbert) : Hilbert :=
  iteratedIdentityPower (RH t a) a (r + 2) (U s t f)

/-- The two-time evolved `(r + 2)`-fold iterated Hamiltonian resolvent difference trajectory
`U(s, t)(R_{H(s)}(a)^{r+2} f - R_{H(s)}(b)^{r+2} f)`. -/
def evolvedHigherPowerResolventSub (s t a b : ℝ) (r : ℕ) (f : Hilbert) : Hilbert :=
  U s t (iteratedResolventPower (RH s a) (r + 2) f -
         iteratedResolventPower (RH s b) (r + 2) f)

/-- The `(r + 2)`-fold iterated Hamiltonian resolvent difference applied at time `t` to an
evolved state `U(s, t) f`: `R_{H(t)}(a)^{r+2}(U(s, t) f) - R_{H(t)}(b)^{r+2}(U(s, t) f)`. -/
def higherPowerResolventSubOfEvolvedState (s t a b : ℝ) (r : ℕ) (f : Hilbert) : Hilbert :=
  iteratedResolventPower (RH t a) (r + 2) (U s t f) -
  iteratedResolventPower (RH t b) (r + 2) (U s t f)

/-! ### 1. Definitional Unfoldings, Base-Case Coincidences, and Unitary Trajectory Invariants -/

/-- Definitional unfolding of `evolvedHigherPowerHamiltonianResolvent`. -/
theorem evolvedHigherPowerHamiltonianResolvent_eq (s t a : ℝ) (r : ℕ) (f : Hilbert) :
    evolvedHigherPowerHamiltonianResolvent ε hε h hh hb m g k s t a r f =
      U s t (RH s a (iteratedResolventPower (RH s a) (r + 1) f)) :=
  rfl

/-- Definitional unfolding of `higherPowerResolventOfEvolvedState`. -/
theorem higherPowerResolventOfEvolvedState_eq (s t a : ℝ) (r : ℕ) (f : Hilbert) :
    higherPowerResolventOfEvolvedState ε hε h hh hb m g k s t a r f =
      RH t a (iteratedResolventPower (RH t a) (r + 1) (U s t f)) :=
  rfl

/-- Definitional unfolding of `evolvedHigherPowerIdentity`. -/
theorem evolvedHigherPowerIdentity_eq (s t a : ℝ) (r : ℕ) (f : Hilbert) :
    evolvedHigherPowerIdentity ε hε h hh hb m g k s t a r f =
      U s t (iteratedIdentityPower (RH s a) a (r + 2) f) :=
  rfl

/-- Definitional unfolding of `higherPowerIdentityOfEvolvedState`. -/
theorem higherPowerIdentityOfEvolvedState_eq (s t a : ℝ) (r : ℕ) (f : Hilbert) :
    higherPowerIdentityOfEvolvedState ε hε h hh hb m g k s t a r f =
      iteratedIdentityPower (RH t a) a (r + 2) (U s t f) :=
  rfl

/-- At `r = 0`, `evolvedHigherPowerHamiltonianResolvent s t a 0 f` coincides with the diagonal
2-fold evolved resolvent `evolvedIteratedHamiltonianResolvent s t a a f`. -/
theorem evolvedHigherPowerHamiltonianResolvent_zero_eq (s t a : ℝ) (f : Hilbert) :
    evolvedHigherPowerHamiltonianResolvent ε hε h hh hb m g k s t a 0 f =
      evolvedIteratedHamiltonianResolvent ε hε h hh hb m g k s t a a f :=
  rfl

/-- At `r = 0`, `higherPowerResolventOfEvolvedState s t a 0 f` coincides with the diagonal
2-fold resolvent `iteratedResolventOfEvolvedState s t t a a f`. -/
theorem higherPowerResolventOfEvolvedState_zero_eq (s t a : ℝ) (f : Hilbert) :
    higherPowerResolventOfEvolvedState ε hε h hh hb m g k s t a 0 f =
      iteratedResolventOfEvolvedState ε hε h hh hb m g k s t t a a f :=
  rfl

/-- Unitary norm preservation along the `(r + 2)`-fold evolved resolvent trajectory:
`‖evolvedHigherPowerHamiltonianResolvent s t a r f‖ = ‖iteratedResolventPower (RH s a) (r + 2) f‖`. -/
theorem evolvedHigherPowerHamiltonianResolvent_norm_eq
    (s t a : ℝ) (r : ℕ) (f : Hilbert) :
    ‖evolvedHigherPowerHamiltonianResolvent ε hε h hh hb m g k s t a r f‖ =
      ‖iteratedResolventPower (RH s a) (r + 2) f‖ :=
  evolution_norm ε hε h hh hw m g k s t (iteratedResolventPower (RH s a) (r + 2) f)

/-- Unconditional geometric norm decay along the `(r + 2)`-fold evolved resolvent trajectory:
`‖evolvedHigherPowerHamiltonianResolvent s t a r f‖ ≤ (a⁻¹) ^ (r + 2) * ‖f‖`. -/
theorem evolvedHigherPowerHamiltonianResolvent_norm_le
    (s t a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert) :
    ‖evolvedHigherPowerHamiltonianResolvent ε hε h hh hb m g k s t a r f‖ ≤
      (a⁻¹) ^ (r + 2) * ‖f‖ :=
  (evolvedHigherPowerHamiltonianResolvent_norm_eq ε hε h hh hb m g k s t a r f).trans_le
    (hamiltonian_iteratedResolventPower_regularity ε hε h hh hb m g k s a ha (r + 2) f).2

/-- Exact time-reversal recovery of `iteratedResolventPower (RH s a) (r + 2) f` from
`evolvedHigherPowerHamiltonianResolvent s t a r f`. -/
theorem evolvedHigherPowerHamiltonianResolvent_reverse_eq
    (s t a : ℝ) (r : ℕ) (f : Hilbert) :
    U t s (evolvedHigherPowerHamiltonianResolvent ε hε h hh hb m g k s t a r f) =
      iteratedResolventPower (RH s a) (r + 2) f :=
  congrArg (fun A : Hilbert →L[ℂ] Hilbert => A (iteratedResolventPower (RH s a) (r + 2) f))
    (evolution_reverse ε hε h hh hw m g k s t)

/-- Unitary inner-product invariance for two-time evolved higher-power Hamiltonian resolvents. -/
theorem evolvedHigherPowerHamiltonianResolvent_inner_eq
    (s t a b : ℝ) (r p : ℕ) (f₁ f₂ : Hilbert) :
    inner ℂ (evolvedHigherPowerHamiltonianResolvent ε hε h hh hb m g k s t a r f₁)
      (evolvedHigherPowerHamiltonianResolvent ε hε h hh hb m g k s t b p f₂) =
    inner ℂ (iteratedResolventPower (RH s a) (r + 2) f₁)
      (iteratedResolventPower (RH s b) (p + 2) f₂) :=
  evolution_inner ε hε h hh hw m g k s t
    (iteratedResolventPower (RH s a) (r + 2) f₁)
    (iteratedResolventPower (RH s b) (p + 2) f₂)

/-! ### 2. 7-Domain Form Regularity, Exact Energy Decompositions, and Two-Sided Trajectory Bounds -/

/-- Unconditional averaged form-energy bound on `iteratedResolventPower (RH s a) (r + 2) f`:
`‖Eavg s ⟨x, ...⟩‖ ^ 2 + a * ‖x‖ ^ 2 ≤ a⁻¹ * (((a⁻¹) ^ (r + 1)) ^ 2 * ‖f‖ ^ 2)` and
`‖Eavg s ⟨x, ...⟩‖ ^ 2 ≤ a⁻¹ * (((a⁻¹) ^ (r + 1)) ^ 2 * ‖f‖ ^ 2)`. -/
theorem higherPowerHamiltonianResolvent_averaged_energy_le
    (s a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert) :
    let x := iteratedResolventPower (RH s a) (r + 2) f
    let hEs : x ∈ (Eavg s).domain :=
      (hamiltonian_iteratedResolventPower_succ_mem_ten_domains
        ε hε h hh hb m g k s s a ha (r + 1) f).2.1.2.2.2.1
    ‖Eavg s ⟨x, hEs⟩‖ ^ 2 + a * ‖x‖ ^ 2 ≤
      a⁻¹ * (((a⁻¹) ^ (r + 1)) ^ 2 * ‖f‖ ^ 2) ∧
    ‖Eavg s ⟨x, hEs⟩‖ ^ 2 ≤
      a⁻¹ * (((a⁻¹) ^ (r + 1)) ^ 2 * ‖f‖ ^ 2) := by
  intro x hEs
  have h1 := hamiltonian_resolvent_averaged_energy_le ε hε h hh hb m g k s a ha
    (iteratedResolventPower (RH s a) (r + 1) f)
  have h2 : ‖iteratedResolventPower (RH s a) (r + 1) f‖ ^ 2 ≤
      ((a⁻¹) ^ (r + 1)) ^ 2 * ‖f‖ ^ 2 := by
    have hbnd := (hamiltonian_iteratedResolventPower_regularity
      ε hε h hh hb m g k s a ha (r + 1) f).2
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hbnd
    simpa only [mul_pow] using hsq
  have hmul := mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr ha.le)
  exact ⟨h1.1.trans hmul, h1.2.trans hmul⟩

/-- Unconditionally for all `s, t, q ∈ ℝ`, `0 < a`, and `r : ℕ`,
`evolvedHigherPowerHamiltonianResolvent s t a r f` belongs simultaneously to all 7 form and
clock domains `(Eavg q).domain`, `(Tstat).domain`, `(Kroot).domain`, `(Tpot).domain`,
`(Tgrow).domain`, `(Tres q).domain`, and `(clockHalf ε).domain`. -/
theorem evolvedHigherPowerHamiltonianResolvent_mem_all_form_domains
    (s t q a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert) :
    let u := evolvedHigherPowerHamiltonianResolvent ε hε h hh hb m g k s t a r f
    u ∈ (Eavg q).domain ∧
    u ∈ (Tstat).domain ∧
    u ∈ (Kroot).domain ∧
    u ∈ (Tpot).domain ∧
    u ∈ (Tgrow).domain ∧
    u ∈ (Tres q).domain ∧
    u ∈ (clockHalf ε).domain :=
  mem_all_form_domains_of_evolved ε hε h hh hb m g k s t q
    (hamiltonian_iteratedResolventPower_succ_mem_ten_domains
      ε hε h hh hb m g k s s a ha (r + 1) f).2.1.2.2.2.1

/-- Exact five-channel form-energy decompositions of `‖Eavg q ⟨evolvedHigherPowerHamiltonianResolvent s t a r f, ...⟩‖ ^ 2`
along the evolved trajectory for all `s, t, q ∈ ℝ`, `0 < a`, and `r : ℕ`. -/
theorem evolvedHigherPowerHamiltonianResolvent_operator_form_energy_decompositions
    (s t q a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert) :
    let hEs := (hamiltonian_iteratedResolventPower_succ_mem_ten_domains
      ε hε h hh hb m g k s s a ha (r + 1) f).2.1.2.2.2.1
    let u := evolvedHigherPowerHamiltonianResolvent ε hε h hh hb m g k s t a r f
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
    (hamiltonian_iteratedResolventPower_succ_mem_ten_domains
      ε hε h hh hb m g k s s a ha (r + 1) f).2.1.2.2.2.1

/-- Two-sided exponential trajectory bounds comparing the evolved averaged form energy
`‖Eavg t ⟨evolvedHigherPowerHamiltonianResolvent s t a r f, ...⟩‖ ^ 2` with the initial
averaged form energy `‖Eavg s ⟨iteratedResolventPower (RH s a) (r + 2) f, ...⟩‖ ^ 2`. -/
theorem evolvedHigherPowerHamiltonianResolvent_two_sided_trajectory_energy_bounds
    (s t a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert) :
    let x := iteratedResolventPower (RH s a) (r + 2) f
    let hEs : x ∈ (Eavg s).domain :=
      (hamiltonian_iteratedResolventPower_succ_mem_ten_domains
        ε hε h hh hb m g k s s a ha (r + 1) f).2.1.2.2.2.1
    let u := evolvedHigherPowerHamiltonianResolvent ε hε h hh hb m g k s t a r f
    let hEt : u ∈ (Eavg t).domain :=
      mem_averaged_domain_of_evolved ε hε h hh hb m g k s t t hEs
    Real.exp (-2 * |t - s|) * ‖Eavg s ⟨x, hEs⟩‖ ^ 2 ≤ ‖Eavg t ⟨u, hEt⟩‖ ^ 2 ∧
    ‖Eavg t ⟨u, hEt⟩‖ ^ 2 ≤ Real.exp (2 * |t - s|) * ‖Eavg s ⟨x, hEs⟩‖ ^ 2 := by
  intro x hEs u hEt
  have hEb := evolved_operator_form_energy_bounds ε hε h hh hb m g k s t t hEs
  exact ⟨hEb.1, hEb.2.1⟩

/-- Unconditional source-norm bounds on the evolved averaged form energy of
`evolvedHigherPowerHamiltonianResolvent s t a r f` at target time `t` and at arbitrary
observation time `q`. -/
theorem evolvedHigherPowerHamiltonianResolvent_averaged_energy_le_source
    (s t q a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert) :
    let hEs := (hamiltonian_iteratedResolventPower_succ_mem_ten_domains
      ε hε h hh hb m g k s s a ha (r + 1) f).2.1.2.2.2.1
    let u := evolvedHigherPowerHamiltonianResolvent ε hε h hh hb m g k s t a r f
    let hEt := mem_averaged_domain_of_evolved ε hε h hh hb m g k s t t hEs
    let hEq := (evolvedHigherPowerHamiltonianResolvent_mem_all_form_domains
      ε hε h hh hb m g k s t q a ha r f).1
    ‖Eavg t ⟨u, hEt⟩‖ ^ 2 ≤
      Real.exp (2 * |t - s|) * (a⁻¹ * (((a⁻¹) ^ (r + 1)) ^ 2 * ‖f‖ ^ 2)) ∧
    ‖Eavg q ⟨u, hEq⟩‖ ^ 2 ≤
      max 1 (Real.exp (2 * (q - t))) * Real.exp (2 * |t - s|) *
        (a⁻¹ * (((a⁻¹) ^ (r + 1)) ^ 2 * ‖f‖ ^ 2)) := by
  intro hEs u hEt hEq
  have hb_u := evolved_resolvent_multi_domain_energy_bounds ε hε h hh hb m g k s t q a ha
    (iteratedResolventPower (RH s a) (r + 1) f)
  have h2 : ‖iteratedResolventPower (RH s a) (r + 1) f‖ ^ 2 ≤
      ((a⁻¹) ^ (r + 1)) ^ 2 * ‖f‖ ^ 2 := by
    have hbnd := (hamiltonian_iteratedResolventPower_regularity
      ε hε h hh hb m g k s a ha (r + 1) f).2
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hbnd
    simpa only [mul_pow] using hsq
  have hE0 := mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr ha.le)
  have hexp_pos : 0 ≤ Real.exp (2 * |t - s|) := (Real.exp_pos _).le
  have hmax_pos : 0 ≤ max 1 (Real.exp (2 * (q - t))) * Real.exp (2 * |t - s|) :=
    mul_nonneg (le_trans zero_le_one (le_max_left 1 _)) hexp_pos
  exact ⟨hb_u.2.2.1.trans (mul_le_mul_of_nonneg_left hE0 hexp_pos),
    hb_u.2.2.2.1.trans (mul_le_mul_of_nonneg_left hE0 hmax_pos)⟩

/-- Unconditional static-root (`Tstat`) and half-clock (`clockHalf ε`) trajectory energy
bounds on `evolvedHigherPowerHamiltonianResolvent s t a r f` in terms of `‖f‖ ^ 2`. -/
theorem evolvedHigherPowerHamiltonianResolvent_static_and_clock_energy_le_source
    (s t q a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert) :
    let u := evolvedHigherPowerHamiltonianResolvent ε hε h hh hb m g k s t a r f
    let hdom := evolvedHigherPowerHamiltonianResolvent_mem_all_form_domains
      ε hε h hh hb m g k s t q a ha r f
    ‖Tstat ⟨u, hdom.2.1⟩‖ ^ 2 ≤
      Real.exp (2 * |t - s|) * (a⁻¹ * (((a⁻¹) ^ (r + 1)) ^ 2 * ‖f‖ ^ 2)) ∧
    ‖clockHalf ε ⟨u, hdom.2.2.2.2.2.2⟩‖ ^ 2 ≤
      2 * (Real.exp (2 * |t - s|) * (a⁻¹ * (((a⁻¹) ^ (r + 1)) ^ 2 * ‖f‖ ^ 2))) := by
  intro u hdom
  have hb_u := evolved_resolvent_multi_domain_energy_bounds ε hε h hh hb m g k s t q a ha
    (iteratedResolventPower (RH s a) (r + 1) f)
  have h2 : ‖iteratedResolventPower (RH s a) (r + 1) f‖ ^ 2 ≤
      ((a⁻¹) ^ (r + 1)) ^ 2 * ‖f‖ ^ 2 := by
    have hbnd := (hamiltonian_iteratedResolventPower_regularity
      ε hε h hh hb m g k s a ha (r + 1) f).2
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hbnd
    simpa only [mul_pow] using hsq
  have hE0 := mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr ha.le)
  have hexp_pos : 0 ≤ Real.exp (2 * |t - s|) := (Real.exp_pos _).le
  have hmul := mul_le_mul_of_nonneg_left hE0 hexp_pos
  exact ⟨hb_u.2.2.2.2.1.trans hmul,
    hb_u.2.2.2.2.2.1.trans (mul_le_mul_of_nonneg_left hmul (by norm_num))⟩

/-- Unconditional growing (`Tgrow`), radial-root (`Kroot`), and potential-form (`Tpot`)
trajectory energy bounds on `evolvedHigherPowerHamiltonianResolvent s t a r f`. -/
theorem evolvedHigherPowerHamiltonianResolvent_growing_radial_potential_energy_le_source
    (s t q a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert) :
    let u := evolvedHigherPowerHamiltonianResolvent ε hε h hh hb m g k s t a r f
    let hdom := evolvedHigherPowerHamiltonianResolvent_mem_all_form_domains
      ε hε h hh hb m g k s t q a ha r f
    ‖Tgrow ⟨u, hdom.2.2.2.2.1⟩‖ ^ 2 ≤
      Real.exp (2 * (|t - s| - t)) * (a⁻¹ * (((a⁻¹) ^ (r + 1)) ^ 2 * ‖f‖ ^ 2)) ∧
    ‖Kroot ⟨u, hdom.2.2.1⟩‖ ^ 2 ≤
      Real.exp (2 * (|t - s| - t)) * (a⁻¹ * (((a⁻¹) ^ (r + 1)) ^ 2 * ‖f‖ ^ 2)) ∧
    ‖Tpot ⟨u, hdom.2.2.2.1⟩‖ ^ 2 ≤
      Real.exp (2 * (|t - s| - t)) * (a⁻¹ * (((a⁻¹) ^ (r + 1)) ^ 2 * ‖f‖ ^ 2)) := by
  intro u hdom
  have hb_u := evolved_resolvent_multi_domain_energy_bounds ε hε h hh hb m g k s t q a ha
    (iteratedResolventPower (RH s a) (r + 1) f)
  have h2 : ‖iteratedResolventPower (RH s a) (r + 1) f‖ ^ 2 ≤
      ((a⁻¹) ^ (r + 1)) ^ 2 * ‖f‖ ^ 2 := by
    have hbnd := (hamiltonian_iteratedResolventPower_regularity
      ε hε h hh hb m g k s a ha (r + 1) f).2
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hbnd
    simpa only [mul_pow] using hsq
  have hE0 := mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr ha.le)
  have hexp_sub_pos : 0 ≤ Real.exp (2 * (|t - s| - t)) := (Real.exp_pos _).le
  have hmul := mul_le_mul_of_nonneg_left hE0 hexp_sub_pos
  exact ⟨hb_u.2.2.2.2.2.2.2.1.trans hmul,
    hb_u.2.2.2.2.2.2.2.2.2.1.trans hmul,
    hb_u.2.2.2.2.2.2.2.2.2.2.2.1.trans hmul⟩

/-- Unconditional residual-form (`Tres q`) trajectory energy bound on
`evolvedHigherPowerHamiltonianResolvent s t a r f` in terms of `‖f‖ ^ 2`. -/
theorem evolvedHigherPowerHamiltonianResolvent_residual_energy_le_source
    (s t q a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert) :
    let u := evolvedHigherPowerHamiltonianResolvent ε hε h hh hb m g k s t a r f
    let hdom := evolvedHigherPowerHamiltonianResolvent_mem_all_form_domains
      ε hε h hh hb m g k s t q a ha r f
    ‖Tres q ⟨u, hdom.2.2.2.2.2.1⟩‖ ^ 2 ≤
      max 1 (Real.exp (2 * (q - t))) * Real.exp (2 * |t - s|) *
        (a⁻¹ * (((a⁻¹) ^ (r + 1)) ^ 2 * ‖f‖ ^ 2)) := by
  intro u hdom
  have hb_u := evolved_resolvent_multi_domain_energy_bounds ε hε h hh hb m g k s t q a ha
    (iteratedResolventPower (RH s a) (r + 1) f)
  have h2 : ‖iteratedResolventPower (RH s a) (r + 1) f‖ ^ 2 ≤
      ((a⁻¹) ^ (r + 1)) ^ 2 * ‖f‖ ^ 2 := by
    have hbnd := (hamiltonian_iteratedResolventPower_regularity
      ε hε h hh hb m g k s a ha (r + 1) f).2
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hbnd
    simpa only [mul_pow] using hsq
  have hE0 := mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr ha.le)
  have hmax_pos : 0 ≤ max 1 (Real.exp (2 * (q - t))) * Real.exp (2 * |t - s|) :=
    mul_nonneg (le_trans zero_le_one (le_max_left 1 _)) (Real.exp_pos _).le
  exact hb_u.2.2.2.2.2.2.2.2.2.2.2.2.trans (mul_le_mul_of_nonneg_left hE0 hmax_pos)

/-! ### 3. `(r + 2)`-th Power Domain, Second-Power Domain, and 10-Domain Regularity for `higherPowerResolventOfEvolvedState` and Yosida Identity Powers -/

/-- Unconditionally for all `s, t, q ∈ ℝ`, `0 < a`, and `r : ℕ`,
`higherPowerResolventOfEvolvedState s t a r f` belongs simultaneously to
`hamiltonianPowerDomain t (r + 2)`, `hamiltonianSecondPowerDomain t`, and all 10 operator,
form, and clock domains, with `(s, t)`-independent geometric norm bound `(a⁻¹) ^ (r + 2) * ‖f‖`. -/
theorem higherPowerResolventOfEvolvedState_mem_power_and_ten_domains
    (s t q a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert) :
    let x := higherPowerResolventOfEvolvedState ε hε h hh hb m g k s t a r f
    x ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    x ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t ∧
    (x ∈ (H t).domain ∧
     x ∈ (K).domain ∧
     x ∈ (S t).domain ∧
     x ∈ (Eavg q).domain ∧
     x ∈ (Tstat).domain ∧
     x ∈ (Kroot).domain ∧
     x ∈ (Tpot).domain ∧
     x ∈ (Tgrow).domain ∧
     x ∈ (Tres q).domain ∧
     x ∈ (clockHalf ε).domain) ∧
    ‖x‖ ≤ (a⁻¹) ^ (r + 2) * ‖f‖ := by
  intro x
  have hpkg := evolved_hamiltonian_iteratedResolventPower_succ_regularity
    ε hε h hh hb m g k s t t q a ha (r + 1) f
  have h2 : x ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t :=
    operatorPowerDomain_add_two_le_secondPowerDomain (H t) r hpkg.1
  exact ⟨hpkg.1, h2, hpkg.2.1, hpkg.2.2⟩

/-- First-order Hamiltonian recurrence, `(r + 1)`-th power domain membership, and
`(s, t)`-independent `2 * ((a⁻¹) ^ (r + 1) * ‖f‖)` norm bound on
`higherPowerResolventOfEvolvedState s t a r f`. -/
theorem higherPowerResolventOfEvolvedState_first_order_recurrence_and_bound
    (s t a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert) :
    let w := U s t f
    let u : (H t).domain :=
      point (H t) (RH t a) a
        (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
        (iteratedResolventPower (RH t a) (r + 1) w)
    (u : Hilbert) = higherPowerResolventOfEvolvedState ε hε h hh hb m g k s t a r f ∧
    H t u =
      iteratedResolventPower (RH t a) (r + 1) w -
        (a : ℂ) • higherPowerResolventOfEvolvedState ε hε h hh hb m g k s t a r f ∧
    H t u ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 1) ∧
    ‖H t u‖ ≤ 2 * ((a⁻¹) ^ (r + 1) * ‖f‖) := by
  intro w u
  have hpkg := hamiltonian_iteratedResolventPower_first_order_package
    ε hε h hh hb m g k t a ha (r + 1) w
  have hnorm : ‖w‖ = ‖f‖ := evolution_norm ε hε h hh hw m g k s t f
  exact ⟨hpkg.1, hpkg.2.1, hpkg.2.2.1,
    hpkg.2.2.2.trans_eq (congrArg (fun z : ℝ => 2 * ((a⁻¹) ^ (r + 1) * z)) hnorm)⟩

/-- Second-order Hamiltonian recurrence and `(s, t)`-independent `4 * ((a⁻¹) ^ r * ‖f‖)` norm
bound on `higherPowerResolventOfEvolvedState s t a r f`. -/
theorem higherPowerResolventOfEvolvedState_second_order_recurrence_and_bound
    (s t a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert) :
    let w := U s t f
    let g_vec : Hilbert := iteratedResolventPower (RH t a) r w
    let u : (H t).domain :=
      point (H t) (RH t a) a
        (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha) g_vec
    let v : (H t).domain :=
      point (H t) (RH t a) a
        (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha) (RH t a g_vec)
    ((u - (a : ℂ) • v : (H t).domain) : Hilbert) = H t v ∧
    H t (u - (a : ℂ) • v) =
      iteratedResolventPower (RH t a) r w -
        ((a + a : ℝ) : ℂ) • iteratedResolventPower (RH t a) (r + 1) w +
        ((a * a : ℝ) : ℂ) • higherPowerResolventOfEvolvedState ε hε h hh hb m g k s t a r f ∧
    ‖H t (u - (a : ℂ) • v)‖ ≤ 4 * ((a⁻¹) ^ r * ‖f‖) := by
  intro w g_vec u v
  have hpkg := hamiltonian_iteratedResolventPower_second_order_package
    ε hε h hh hb m g k t a ha r w
  have hnorm : ‖w‖ = ‖f‖ := evolution_norm ε hε h hh hw m g k s t f
  exact ⟨hpkg.1, hpkg.2.1,
    hpkg.2.2.trans_eq (congrArg (fun z : ℝ => 4 * ((a⁻¹) ^ r * z)) hnorm)⟩

/-- Unconditionally for all `s, t, q ∈ ℝ`, `0 < a`, and `r : ℕ`,
`evolvedHigherPowerIdentity s t a r f` belongs simultaneously to all 7 form and clock domains
with parameter-free contraction `‖evolvedHigherPowerIdentity s t a r f‖ ≤ ‖f‖`. -/
theorem evolvedHigherPowerIdentity_mem_all_form_domains_and_contraction
    (s t q a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert) :
    let u := evolvedHigherPowerIdentity ε hε h hh hb m g k s t a r f
    (u ∈ (Eavg q).domain ∧
     u ∈ (Tstat).domain ∧
     u ∈ (Kroot).domain ∧
     u ∈ (Tpot).domain ∧
     u ∈ (Tgrow).domain ∧
     u ∈ (Tres q).domain ∧
     u ∈ (clockHalf ε).domain) ∧
    ‖u‖ ≤ ‖f‖ := by
  intro u
  have hpkg := hamiltonian_iteratedIdentityPower_succ_mem_ten_domains
    ε hε h hh hb m g k s s a ha (r + 1) f
  have hdom := mem_all_form_domains_of_evolved ε hε h hh hb m g k s t q hpkg.2.1.2.2.2.1
  have hnorm : ‖u‖ ≤ ‖f‖ :=
    (evolution_norm ε hε h hh hw m g k s t
      (iteratedIdentityPower (RH s a) a (r + 2) f)).trans_le hpkg.2.2
  exact ⟨hdom, hnorm⟩

/-- Unconditionally for all `s, t, q ∈ ℝ`, `0 < a`, and `r : ℕ`,
`higherPowerIdentityOfEvolvedState s t a r f` belongs simultaneously to
`hamiltonianPowerDomain t (r + 2)`, `hamiltonianSecondPowerDomain t`, and all 10 operator,
form, and clock domains, with parameter-free contraction `‖higherPowerIdentityOfEvolvedState s t a r f‖ ≤ ‖f‖`. -/
theorem higherPowerIdentityOfEvolvedState_mem_power_and_ten_domains
    (s t q a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert) :
    let y := higherPowerIdentityOfEvolvedState ε hε h hh hb m g k s t a r f
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
    ‖y‖ ≤ ‖f‖ := by
  intro y
  have hpkg := evolved_hamiltonian_iteratedIdentityPower_succ_regularity
    ε hε h hh hb m g k s t t q a ha (r + 1) f
  have h2 : y ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t :=
    operatorPowerDomain_add_two_le_secondPowerDomain (H t) r hpkg.1
  exact ⟨hpkg.1, h2, hpkg.2.1, hpkg.2.2⟩

/-- Two-sided exponential trajectory bounds comparing the evolved averaged form energy of
`evolvedHigherPowerIdentity s t a r f` at time `t` with the initial averaged form energy of
`iteratedIdentityPower (RH s a) a (r + 2) f` at time `s`. -/
theorem evolvedHigherPowerIdentity_two_sided_trajectory_energy_bounds
    (s t a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert) :
    let y := iteratedIdentityPower (RH s a) a (r + 2) f
    let hEs : y ∈ (Eavg s).domain :=
      (hamiltonian_iteratedIdentityPower_succ_mem_ten_domains
        ε hε h hh hb m g k s s a ha (r + 1) f).2.1.2.2.2.1
    let u := evolvedHigherPowerIdentity ε hε h hh hb m g k s t a r f
    let hEt : u ∈ (Eavg t).domain :=
      mem_averaged_domain_of_evolved ε hε h hh hb m g k s t t hEs
    Real.exp (-2 * |t - s|) * ‖Eavg s ⟨y, hEs⟩‖ ^ 2 ≤ ‖Eavg t ⟨u, hEt⟩‖ ^ 2 ∧
    ‖Eavg t ⟨u, hEt⟩‖ ^ 2 ≤ Real.exp (2 * |t - s|) * ‖Eavg s ⟨y, hEs⟩‖ ^ 2 := by
  intro y hEs u hEt
  have hEb := evolved_operator_form_energy_bounds ε hε h hh hb m g k s t t hEs
  exact ⟨hEb.1, hEb.2.1⟩

/-- Two-parameter `(a, b)` and two-order `(r + 2, p + 2)` commutativity of
`higherPowerIdentityOfEvolvedState` at target time `t`. -/
theorem higherPowerIdentityOfEvolvedState_two_param_comm
    (s t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r p : ℕ) (f : Hilbert) :
    iteratedIdentityPower (RH t a) a (r + 2)
        (higherPowerIdentityOfEvolvedState ε hε h hh hb m g k s t b p f) =
      iteratedIdentityPower (RH t b) b (p + 2)
        (higherPowerIdentityOfEvolvedState ε hε h hh hb m g k s t a r f) :=
  hamiltonianResolvent_iteratedIdentityPower_comm
    ε hε h hh hb m g k t a b ha hb_pos (r + 2) (p + 2) (U s t f)

/-! ### 4. `(r + 3)`-th Power Domain Lift for Higher-Power Resolvent Differences, Weak Continuity, and Master Synthesis -/

/-- Exact step recurrence for the evolved `(r + 2)`-fold resolvent difference trajectory
`evolvedHigherPowerResolventSub s t a b r f`. -/
theorem evolvedHigherPowerResolventSub_step_eq
    (s t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f : Hilbert) :
    evolvedHigherPowerResolventSub ε hε h hh hb m g k s t a b r f =
      ((b - a : ℝ) : ℂ) •
          U s t (RH s a (RH s b (iteratedResolventPower (RH s a) (r + 1) f))) +
        U s t (RH s b
          (iteratedResolventPower (RH s a) (r + 1) f -
           iteratedResolventPower (RH s b) (r + 1) f)) :=
  (congrArg (U s t)
    (hamiltonianResolvent_iteratedResolventPower_sub_succ_eq
      ε hε h hh hb m g k s a b ha hb_pos (r + 1) f)).trans
    (((U s t).map_add
      (((b - a : ℝ) : ℂ) • RH s a (RH s b (iteratedResolventPower (RH s a) (r + 1) f)))
      (RH s b (iteratedResolventPower (RH s a) (r + 1) f -
        iteratedResolventPower (RH s b) (r + 1) f))).trans
      (congrArg
        (· + U s t (RH s b (iteratedResolventPower (RH s a) (r + 1) f -
          iteratedResolventPower (RH s b) (r + 1) f)))
        ((U s t).map_smul ((b - a : ℝ) : ℂ)
          (RH s a (RH s b (iteratedResolventPower (RH s a) (r + 1) f))))))

/-- Unconditionally for all `s, t, q ∈ ℝ`, `0 < a, 0 < b`, and `r : ℕ`,
`evolvedHigherPowerResolventSub s t a b r f` belongs simultaneously to all 7 form and clock
domains with geometric norm bound `‖evolvedHigherPowerResolventSub s t a b r f‖ ≤ ((a⁻¹) ^ (r + 2) + (b⁻¹) ^ (r + 2)) * ‖f‖`. -/
theorem evolvedHigherPowerResolventSub_mem_all_form_domains_and_norm_le
    (s t q a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f : Hilbert) :
    let u := evolvedHigherPowerResolventSub ε hε h hh hb m g k s t a b r f
    (u ∈ (Eavg q).domain ∧
     u ∈ (Tstat).domain ∧
     u ∈ (Kroot).domain ∧
     u ∈ (Tpot).domain ∧
     u ∈ (Tgrow).domain ∧
     u ∈ (Tres q).domain ∧
     u ∈ (clockHalf ε).domain) ∧
    ‖u‖ ≤ ((a⁻¹) ^ (r + 2) + (b⁻¹) ^ (r + 2)) * ‖f‖ := by
  intro u
  have hEs := (hamiltonianResolvent_iteratedResolventPower_sub_succ_mem_ten_domains
    ε hε h hh hb m g k s s a b ha hb_pos (r + 1) f).2.2.2.2.1
  have hdom := mem_all_form_domains_of_evolved ε hε h hh hb m g k s t q hEs
  have hnorm : ‖u‖ ≤ ((a⁻¹) ^ (r + 2) + (b⁻¹) ^ (r + 2)) * ‖f‖ :=
    (evolution_norm ε hε h hh hw m g k s t
      (iteratedResolventPower (RH s a) (r + 2) f -
       iteratedResolventPower (RH s b) (r + 2) f)).trans_le
      (iteratedResolventPower_sub_norm_bound (H s) (RH s) a b ha hb_pos
        (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k s)
        (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k s)
        (r + 2) f)
  exact ⟨hdom, hnorm⟩

/-- Higher-power domain regularity lift on evolved states: while
`higherPowerResolventOfEvolvedState s t a r f` and `higherPowerResolventOfEvolvedState s t b r f`
individually lie in `hamiltonianPowerDomain t (r + 2)`, their difference
`higherPowerResolventSubOfEvolvedState s t a b r f` lies in `hamiltonianPowerDomain t (r + 3)`,
`hamiltonianSecondPowerDomain t`, and all 10 operator, form, and clock domains, with
`(s, t)`-independent norm bound `((a⁻¹) ^ (r + 2) + (b⁻¹) ^ (r + 2)) * ‖f‖`. -/
theorem higherPowerResolventSubOfEvolvedState_mem_succ_power_and_ten_domains
    (s t q a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f : Hilbert) :
    let d := higherPowerResolventSubOfEvolvedState ε hε h hh hb m g k s t a b r f
    d ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 3) ∧
    d ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t ∧
    (d ∈ (H t).domain ∧
     d ∈ (K).domain ∧
     d ∈ (S t).domain ∧
     d ∈ (Eavg q).domain ∧
     d ∈ (Tstat).domain ∧
     d ∈ (Kroot).domain ∧
     d ∈ (Tpot).domain ∧
     d ∈ (Tgrow).domain ∧
     d ∈ (Tres q).domain ∧
     d ∈ (clockHalf ε).domain) ∧
    ‖d‖ ≤ ((a⁻¹) ^ (r + 2) + (b⁻¹) ^ (r + 2)) * ‖f‖ := by
  intro d
  have h10 := hamiltonianResolvent_iteratedResolventPower_sub_succ_mem_ten_domains
    ε hε h hh hb m g k t q a b ha hb_pos (r + 1) (U s t f)
  have h2 : d ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t :=
    operatorPowerDomain_add_two_le_secondPowerDomain (H t) (r + 1) h10.1
  have hbd := (iteratedResolventPower_sub_norm_bound (H t) (RH t) a b ha hb_pos
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
    (r + 2) (U s t f)).trans_eq
    (congrArg (fun z : ℝ => ((a⁻¹) ^ (r + 2) + (b⁻¹) ^ (r + 2)) * z)
      (evolution_norm ε hε h hh hw m g k s t f))
  exact ⟨h10.1, h2, h10.2, hbd⟩

/-- Simultaneous `(r + 3)`-th power domain lift across all five clock-floor Hamiltonians
`T, P, G, S t, H t` for `(r + 2)`-fold iterated resolvent differences applied to any evolved
state `w := U s t f`. -/
theorem five_operator_higherPowerResolventSub_of_evolved_state_mem_powerDomains
    (s t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f : Hilbert) :
    let w := U s t f
    iteratedResolventPower (RT a) (r + 2) w - iteratedResolventPower (RT b) (r + 2) w ∈
      staticPowerDomain ε hε h (r + 3) ∧
    iteratedResolventPower (RP a) (r + 2) w - iteratedResolventPower (RP b) (r + 2) w ∈
      potentialPowerDomain ε hε h hh hb m g k (r + 3) ∧
    iteratedResolventPower (RG a) (r + 2) w - iteratedResolventPower (RG b) (r + 2) w ∈
      growingPowerDomain ε hε h hh hb m g k (r + 3) ∧
    iteratedResolventPower (RS t a) (r + 2) w - iteratedResolventPower (RS t b) (r + 2) w ∈
      residualPowerDomain ε hε h hh hb m g k t (r + 3) ∧
    iteratedResolventPower (RH t a) (r + 2) w - iteratedResolventPower (RH t b) (r + 2) w ∈
      hamiltonianPowerDomain ε hε h hh hb m g k t (r + 3) :=
  ⟨staticResolvent_iteratedResolventPower_sub_succ_mem_powerDomain
     ε hε h hh hb m g k a b ha hb_pos (r + 1) (U s t f),
   potentialResolvent_iteratedResolventPower_sub_succ_mem_powerDomain
     ε hε h hh hb m g k a b ha hb_pos (r + 1) (U s t f),
   growingResolvent_iteratedResolventPower_sub_succ_mem_powerDomain
     ε hε h hh hb m g k a b ha hb_pos (r + 1) (U s t f),
   residualResolvent_iteratedResolventPower_sub_succ_mem_powerDomain
     ε hε h hh hb m g k t a b ha hb_pos (r + 1) (U s t f),
   hamiltonianResolvent_iteratedResolventPower_sub_succ_mem_powerDomain
     ε hε h hh hb m g k t a b ha hb_pos (r + 1) (U s t f)⟩

/-- Unconditional two-time weak Lipschitz bound for the evolved `(r + 2)`-fold iterated
resolvent with outer resolvent evaluated at times `s` and `t`:
`‖inner ℂ f₁ (U t₁ t₂ (RH s a (iteratedResolventPower (RH q a) (r + 1) f₂)) - U t₁ t₂ (RH t a (iteratedResolventPower (RH q a) (r + 1) f₂)))‖ ≤ |Real.exp (2 * t) - Real.exp (2 * s)| * (2 * Real.exp (-(t + s)) * a⁻¹ * ‖f₁‖ * ((a⁻¹) ^ (r + 1) * ‖f₂‖))`. -/
theorem evolvedHigherPowerHamiltonianResolvent_two_time_outer_weak_diff_bound
    (t₁ t₂ s t q a : ℝ) (ha : 0 < a) (r : ℕ) (f₁ f₂ : Hilbert) :
    ‖inner ℂ f₁
      (U t₁ t₂ (RH s a (iteratedResolventPower (RH q a) (r + 1) f₂)) -
       U t₁ t₂ (RH t a (iteratedResolventPower (RH q a) (r + 1) f₂)))‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| *
        (2 * Real.exp (-(t + s)) * a⁻¹ * ‖f₁‖ * ((a⁻¹) ^ (r + 1) * ‖f₂‖)) := by
  have h1 := evolved_two_time_resolvent_weak_diff_bound
    ε hε h hh hb m g k t₁ t₂ s t a ha f₁ (iteratedResolventPower (RH q a) (r + 1) f₂)
  have h2 := (hamiltonian_iteratedResolventPower_regularity
    ε hε h hh hb m g k q a ha (r + 1) f₂).2
  have hcoeff : 0 ≤ |Real.exp (2 * t) - Real.exp (2 * s)| *
      (2 * Real.exp (-(t + s)) * a⁻¹ * ‖f₁‖) := by positivity
  have hmul := mul_le_mul_of_nonneg_left h2 hcoeff
  exact h1.trans (by linarith)

/-- Unconditional weak continuity `⟪f₁, U t₁ t₂ (RH s a (iteratedResolventPower (RH q a) (r + 1) f₂))⟫ → ⟪f₁, U t₁ t₂ (RH t a (iteratedResolventPower (RH q a) (r + 1) f₂))⟫`
as `s → t` for all `f₁, f₂ : Hilbert`, `0 < a`, and `r : ℕ`. -/
theorem evolvedHigherPowerHamiltonianResolvent_two_time_outer_weak_continuous
    (t₁ t₂ t q a : ℝ) (ha : 0 < a) (r : ℕ) (f₁ f₂ : Hilbert) :
    Tendsto
      (fun s : ℝ => inner ℂ f₁ (U t₁ t₂ (RH s a (iteratedResolventPower (RH q a) (r + 1) f₂))))
      (𝓝 t)
      (𝓝 (inner ℂ f₁ (U t₁ t₂ (RH t a (iteratedResolventPower (RH q a) (r + 1) f₂))))) :=
  evolved_two_time_resolvent_weak_continuous
    ε hε h hh hb m g k t₁ t₂ t a ha f₁ (iteratedResolventPower (RH q a) (r + 1) f₂)

/-- Master Two-Time Evolved Higher-Power Resolvent Trajectory Synthesis uniting:
(1) 7-domain form/clock regularity and `(a⁻¹) ^ (r + 2) * ‖f‖` norm decay of
    `evolvedHigherPowerHamiltonianResolvent`,
(2) `hamiltonianPowerDomain t (r + 2)`, `hamiltonianSecondPowerDomain t`, and 10-domain
    regularity of `higherPowerResolventOfEvolvedState`,
(3) `(r + 3)`-th power domain lift of `higherPowerResolventSubOfEvolvedState`, and
(4) parameter-free contraction `≤ ‖f‖` of both `evolvedHigherPowerIdentity` and
    `higherPowerIdentityOfEvolvedState`. -/
theorem evolved_higher_power_resolvent_trajectory_master_synthesis
    (s t q a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f : Hilbert) :
    let u := evolvedHigherPowerHamiltonianResolvent ε hε h hh hb m g k s t a r f
    let x := higherPowerResolventOfEvolvedState ε hε h hh hb m g k s t a r f
    let d := higherPowerResolventSubOfEvolvedState ε hε h hh hb m g k s t a b r f
    let u_id := evolvedHigherPowerIdentity ε hε h hh hb m g k s t a r f
    let x_id := higherPowerIdentityOfEvolvedState ε hε h hh hb m g k s t a r f
    (u ∈ (Eavg q).domain ∧ u ∈ (clockHalf ε).domain ∧ ‖u‖ ≤ (a⁻¹) ^ (r + 2) * ‖f‖) ∧
    (x ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
     x ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t ∧
     x ∈ (Eavg q).domain ∧
     ‖x‖ ≤ (a⁻¹) ^ (r + 2) * ‖f‖) ∧
    (d ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 3) ∧
     ‖d‖ ≤ ((a⁻¹) ^ (r + 2) + (b⁻¹) ^ (r + 2)) * ‖f‖) ∧
    (u_id ∈ (Eavg q).domain ∧ ‖u_id‖ ≤ ‖f‖ ∧
     x_id ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧ ‖x_id‖ ≤ ‖f‖) := by
  intro u x d u_id x_id
  have hu := evolvedHigherPowerHamiltonianResolvent_mem_all_form_domains
    ε hε h hh hb m g k s t q a ha r f
  have hu_bd := evolvedHigherPowerHamiltonianResolvent_norm_le
    ε hε h hh hb m g k s t a ha r f
  have hx := higherPowerResolventOfEvolvedState_mem_power_and_ten_domains
    ε hε h hh hb m g k s t q a ha r f
  have hd := higherPowerResolventSubOfEvolvedState_mem_succ_power_and_ten_domains
    ε hε h hh hb m g k s t q a b ha hb_pos r f
  have huid := evolvedHigherPowerIdentity_mem_all_form_domains_and_contraction
    ε hε h hh hb m g k s t q a ha r f
  have hxid := higherPowerIdentityOfEvolvedState_mem_power_and_ten_domains
    ε hε h hh hb m g k s t q a ha r f
  exact ⟨⟨hu.1, hu.2.2.2.2.2.2, hu_bd⟩,
    ⟨hx.1, hx.2.1, hx.2.2.1.2.2.2.1, hx.2.2.2⟩,
    ⟨hd.1, hd.2.2.2⟩,
    ⟨huid.1.1, huid.2, hxid.1, hxid.2.2.2⟩⟩

#print axioms evolvedHigherPowerHamiltonianResolvent_eq
#print axioms higherPowerResolventOfEvolvedState_eq
#print axioms evolvedHigherPowerIdentity_eq
#print axioms higherPowerIdentityOfEvolvedState_eq
#print axioms evolvedHigherPowerHamiltonianResolvent_zero_eq
#print axioms higherPowerResolventOfEvolvedState_zero_eq
#print axioms evolvedHigherPowerHamiltonianResolvent_norm_eq
#print axioms evolvedHigherPowerHamiltonianResolvent_norm_le
#print axioms evolvedHigherPowerHamiltonianResolvent_reverse_eq
#print axioms evolvedHigherPowerHamiltonianResolvent_inner_eq
#print axioms higherPowerHamiltonianResolvent_averaged_energy_le
#print axioms evolvedHigherPowerHamiltonianResolvent_mem_all_form_domains
#print axioms evolvedHigherPowerHamiltonianResolvent_operator_form_energy_decompositions
#print axioms evolvedHigherPowerHamiltonianResolvent_two_sided_trajectory_energy_bounds
#print axioms evolvedHigherPowerHamiltonianResolvent_averaged_energy_le_source
#print axioms evolvedHigherPowerHamiltonianResolvent_static_and_clock_energy_le_source
#print axioms evolvedHigherPowerHamiltonianResolvent_growing_radial_potential_energy_le_source
#print axioms evolvedHigherPowerHamiltonianResolvent_residual_energy_le_source
#print axioms higherPowerResolventOfEvolvedState_mem_power_and_ten_domains
#print axioms higherPowerResolventOfEvolvedState_first_order_recurrence_and_bound
#print axioms higherPowerResolventOfEvolvedState_second_order_recurrence_and_bound
#print axioms evolvedHigherPowerIdentity_mem_all_form_domains_and_contraction
#print axioms higherPowerIdentityOfEvolvedState_mem_power_and_ten_domains
#print axioms evolvedHigherPowerIdentity_two_sided_trajectory_energy_bounds
#print axioms higherPowerIdentityOfEvolvedState_two_param_comm
#print axioms evolvedHigherPowerResolventSub_step_eq
#print axioms evolvedHigherPowerResolventSub_mem_all_form_domains_and_norm_le
#print axioms higherPowerResolventSubOfEvolvedState_mem_succ_power_and_ten_domains
#print axioms five_operator_higherPowerResolventSub_of_evolved_state_mem_powerDomains
#print axioms evolvedHigherPowerHamiltonianResolvent_two_time_outer_weak_diff_bound
#print axioms evolvedHigherPowerHamiltonianResolvent_two_time_outer_weak_continuous
#print axioms evolved_higher_power_resolvent_trajectory_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorTwoTimeEvolvedHigherPowerResolventRegularity
