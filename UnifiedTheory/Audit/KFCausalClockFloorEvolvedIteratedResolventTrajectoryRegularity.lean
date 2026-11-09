/- Trajectory Regularity, Two-Sided Form-Energy Bounds, Parameter Commutativity,
First- and Second-Power Radial-Residual Decompositions, Five-Operator Second-Power
Regularity, Quartic Squared-Resolvent Difference Bounds, and Two-Time Weak Continuity
for Compositions of the Nonautonomous Evolution U(s, t) with Iterated Resolvents:
1. Defines the evolved iterated Hamiltonian resolvent trajectory
   `evolvedIteratedHamiltonianResolvent s t a b f := U(s, t)(R_{H(s)}(a)(R_{H(s)}(b) f))`,
   the iterated resolvent of an evolved state
   `iteratedResolventOfEvolvedState s t r a b f := R_{H(r)}(a)(R_{H(r)}(b)(U(s, t) f))`,
   and the evolved squared-resolvent difference
   `evolvedSquaredResolventSub s t a b f := U(s, t)(R_{H(s)}(a)^2 f - R_{H(s)}(b)^2 f)`.
2. Proves parameter commutativity in `(a, b)`, unitary norm and inner-product preservation,
   time-reversal recovery, unconditional 7-domain form/clock trajectory regularity, exact
   five-channel form-energy decompositions, two-sided exponential trajectory energy bounds,
   and explicit source-norm bounds across `Eavg`, `Tstat`, `clockHalf`, `Tgrow`, `Kroot`,
   `Tpot`, and `Tres`.
3. Establishes unconditional 10-domain and second-power domain regularity for
   `iteratedResolventOfEvolvedState`, exact first- and second-power radial-residual
   decompositions, uniform component and form-energy bounds, simultaneous 5-operator
   second-power regularity on evolved states, evolved squared-resolvent difference
   factorization and quartic decay, and two-time weak Lipschitz and continuity estimates. -/
import UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorIteratedResolventCommutativity
import UnifiedTheory.Audit.KFCausalClockFloorEvolvedResolventRegularity
import UnifiedTheory.Audit.KFCausalClockFloorArbitraryCouplingIteratedThreeOperatorSynthesis

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorEvolvedIteratedResolventTrajectoryRegularity

noncomputable section

open Filter
open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorAveragedEvolution
  (evolution evolution_norm evolution_inner evolution_reverse)
open KFCausalClockFloorTwoTimeFormEvolutionIsomorphism
  (mem_averaged_domain_of_evolved mem_all_form_domains_of_evolved
   evolved_operator_form_energy_decompositions
   evolved_operator_form_energy_bounds
   evolved_component_form_energy_bounds)
open KFCausalClockFloorEvolvedResolventRegularity
  (hamiltonian_resolvent_averaged_energy_le
   evolved_resolvent_multi_domain_energy_bounds
   evolved_two_time_resolvent_weak_diff_bound
   evolved_two_time_resolvent_weak_continuous)
open KFCausalClockFloorStaticResolventRadialCommutator (staticResolvent)
open KFCausalClockFloorIteratedResolventSecondPowerCore
  (staticSecondPowerDomain potentialSecondPowerDomain
   growingSecondPowerDomain residualSecondPowerDomain
   hamiltonianSecondPowerDomain
   five_hamiltonians_iterated_resolvent_mem_secondPowerDomain)
open KFCausalClockFloorHigherPowerOperatorCores
  (hamiltonianPowerDomain)
open KFCausalClockFloorFiveOperatorFirstResolventIdentity
  (quarterStripResolvent_comm
   potentialResolvent_comm
   staticGeneratorResolvent_comm
   staticResidualResolvent_comm
   hamiltonianResolvent_comm)
open KFCausalClockFloorIteratedHamiltonianResolventUnconditionalDomination
  (iteratedHamiltonianResolvent squaredHamiltonianResolvent
   iteratedHamiltonianResolvent_mem_ten_domains
   iteratedHamiltonianResolvent_first_power_mem_ten_domains
   iteratedHamiltonianResolvent_mem_radial_residual_domain
   iteratedHamiltonianResolvent_first_power_mem_radial_residual_domain
   iteratedHamiltonianResolvent_hamiltonian_eq_radial_add_residual
   iteratedHamiltonianResolvent_second_power_radial_residual_eq
   iteratedHamiltonianResolvent_component_norm_sq_le_source
   iteratedHamiltonianResolvent_first_power_component_norm_sq_le_source)
open KFCausalClockFloorFiveOperatorIteratedResolventCommutativity
  (hamiltonianResolvent_squared_sub_eq
   hamiltonianResolvent_squared_sub_mem_thirdPowerDomain
   hamiltonianResolvent_squared_sub_norm_le
   hamiltonianResolvent_squared_sub_mem_ten_domains)
open KFCausalClockFloorHamiltonianComponentResolventBounds
  (resolvent_norm_le)
open KFCausalClockFloorHamiltonianResolventFormBounds
  (hamiltonian_resolvent_mem_staticRoot_domain
   hamiltonian_resolvent_mem_radialRoot_domain
   hamiltonian_resolvent_mem_potentialForm_domain
   hamiltonian_resolvent_three_channel_energy_le)

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

/-- The evolved iterated Hamiltonian resolvent trajectory
`U(s, t)(R_{H(s)}(a)(R_{H(s)}(b) f))`. -/
def evolvedIteratedHamiltonianResolvent (s t a b : ℝ) (f : Hilbert) : Hilbert :=
  U s t (iteratedHamiltonianResolvent ε hε h hh hb m g k s a b f)

/-- The iterated Hamiltonian resolvent applied at time `r` to an evolved state `U(s, t) f`:
`R_{H(r)}(a)(R_{H(r)}(b)(U(s, t) f))`. -/
def iteratedResolventOfEvolvedState (s t r a b : ℝ) (f : Hilbert) : Hilbert :=
  iteratedHamiltonianResolvent ε hε h hh hb m g k r a b (U s t f)

/-- The evolved squared-resolvent difference trajectory
`U(s, t)(R_{H(s)}(a)^2 f - R_{H(s)}(b)^2 f)`. -/
def evolvedSquaredResolventSub (s t a b : ℝ) (f : Hilbert) : Hilbert :=
  U s t (squaredHamiltonianResolvent ε hε h hh hb m g k s a f -
         squaredHamiltonianResolvent ε hε h hh hb m g k s b f)

/-! ### 1. Definitional Unfoldings, Parameter Commutativity, and Unitary Trajectory Invariants -/

/-- Definitional unfolding of `evolvedIteratedHamiltonianResolvent`. -/
theorem evolvedIteratedHamiltonianResolvent_eq (s t a b : ℝ) (f : Hilbert) :
    evolvedIteratedHamiltonianResolvent ε hε h hh hb m g k s t a b f =
      U s t (RH s a (RH s b f)) :=
  rfl

/-- Definitional unfolding of `iteratedResolventOfEvolvedState`. -/
theorem iteratedResolventOfEvolvedState_eq (s t r a b : ℝ) (f : Hilbert) :
    iteratedResolventOfEvolvedState ε hε h hh hb m g k s t r a b f =
      RH r a (RH r b (U s t f)) :=
  rfl

/-- Definitional unfolding of `evolvedSquaredResolventSub`. -/
theorem evolvedSquaredResolventSub_eq (s t a b : ℝ) (f : Hilbert) :
    evolvedSquaredResolventSub ε hε h hh hb m g k s t a b f =
      U s t (RH s a (RH s a f) - RH s b (RH s b f)) :=
  rfl

/-- Parameter commutativity of `evolvedIteratedHamiltonianResolvent` in `(a, b)` for `0 < a, 0 < b`. -/
theorem evolvedIteratedHamiltonianResolvent_comm
    (s t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    evolvedIteratedHamiltonianResolvent ε hε h hh hb m g k s t a b f =
      evolvedIteratedHamiltonianResolvent ε hε h hh hb m g k s t b a f :=
  congrArg (U s t)
    (hamiltonianResolvent_comm ε hε h hh hb m g k s a b ha hb_pos f)

/-- Parameter commutativity of `iteratedResolventOfEvolvedState` in `(a, b)` for `0 < a, 0 < b`. -/
theorem iteratedResolventOfEvolvedState_comm
    (s t r a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    iteratedResolventOfEvolvedState ε hε h hh hb m g k s t r a b f =
      iteratedResolventOfEvolvedState ε hε h hh hb m g k s t r b a f :=
  hamiltonianResolvent_comm ε hε h hh hb m g k r a b ha hb_pos (U s t f)

/-- Unitary norm preservation along the evolved iterated-resolvent trajectory:
`‖evolvedIteratedHamiltonianResolvent s t a b f‖ = ‖iteratedHamiltonianResolvent s a b f‖`. -/
theorem evolvedIteratedHamiltonianResolvent_norm_eq
    (s t a b : ℝ) (f : Hilbert) :
    ‖evolvedIteratedHamiltonianResolvent ε hε h hh hb m g k s t a b f‖ =
      ‖iteratedHamiltonianResolvent ε hε h hh hb m g k s a b f‖ :=
  evolution_norm ε hε h hh hw m g k s t
    (iteratedHamiltonianResolvent ε hε h hh hb m g k s a b f)

/-- Unconditional Hilbert-norm contraction of `evolvedIteratedHamiltonianResolvent`:
`‖evolvedIteratedHamiltonianResolvent s t a b f‖ ≤ a⁻¹ * (b⁻¹ * ‖f‖)`. -/
theorem evolvedIteratedHamiltonianResolvent_norm_le
    (s t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    ‖evolvedIteratedHamiltonianResolvent ε hε h hh hb m g k s t a b f‖ ≤
      a⁻¹ * (b⁻¹ * ‖f‖) := by
  rw [evolvedIteratedHamiltonianResolvent_norm_eq]
  have h1 := resolvent_norm_le ε hε h hh hb m g k s a ha (RH s b f)
  have h2 := resolvent_norm_le ε hε h hh hb m g k s b hb_pos f
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr ha.le))

/-- Unconditional Hilbert-norm contraction of `iteratedResolventOfEvolvedState` uniform in `(s, t)`:
`‖iteratedResolventOfEvolvedState s t r a b f‖ ≤ a⁻¹ * (b⁻¹ * ‖f‖)`. -/
theorem iteratedResolventOfEvolvedState_norm_le
    (s t r a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    ‖iteratedResolventOfEvolvedState ε hε h hh hb m g k s t r a b f‖ ≤
      a⁻¹ * (b⁻¹ * ‖f‖) := by
  have h1 := resolvent_norm_le ε hε h hh hb m g k r a ha (RH r b (U s t f))
  have h2 := (resolvent_norm_le ε hε h hh hb m g k r b hb_pos (U s t f)).trans_eq
    (congrArg (b⁻¹ * ·) (evolution_norm ε hε h hh hw m g k s t f))
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr ha.le))

/-- Exact time-reversal recovery of `iteratedHamiltonianResolvent` from its evolved trajectory:
`U t s (evolvedIteratedHamiltonianResolvent s t a b f) = iteratedHamiltonianResolvent s a b f`. -/
theorem evolvedIteratedHamiltonianResolvent_reverse_eq
    (s t a b : ℝ) (f : Hilbert) :
    U t s (evolvedIteratedHamiltonianResolvent ε hε h hh hb m g k s t a b f) =
      iteratedHamiltonianResolvent ε hε h hh hb m g k s a b f :=
  congrArg (fun A : Hilbert →L[ℂ] Hilbert =>
      A (iteratedHamiltonianResolvent ε hε h hh hb m g k s a b f))
    (evolution_reverse ε hε h hh hw m g k s t)

/-- Unitary inner-product invariance for evolved iterated Hamiltonian resolvents:
`inner ℂ (evolvedIteratedHamiltonianResolvent s t a b f₁) (evolvedIteratedHamiltonianResolvent s t c d f₂) = inner ℂ (iteratedHamiltonianResolvent s a b f₁) (iteratedHamiltonianResolvent s c d f₂)`. -/
theorem evolvedIteratedHamiltonianResolvent_inner_eq
    (s t a b c d : ℝ) (f₁ f₂ : Hilbert) :
    inner ℂ (evolvedIteratedHamiltonianResolvent ε hε h hh hb m g k s t a b f₁)
      (evolvedIteratedHamiltonianResolvent ε hε h hh hb m g k s t c d f₂) =
    inner ℂ (iteratedHamiltonianResolvent ε hε h hh hb m g k s a b f₁)
      (iteratedHamiltonianResolvent ε hε h hh hb m g k s c d f₂) :=
  evolution_inner ε hε h hh hw m g k s t
    (iteratedHamiltonianResolvent ε hε h hh hb m g k s a b f₁)
    (iteratedHamiltonianResolvent ε hε h hh hb m g k s c d f₂)

/-! ### 2. Multi-Domain Form Regularity and Two-Sided Trajectory Energy Bounds for `evolvedIteratedHamiltonianResolvent` -/

/-- Unconditional averaged form-energy bound on `iteratedHamiltonianResolvent s a b f`:
`‖Eavg s ⟨iteratedHamiltonianResolvent s a b f, ...⟩‖ ^ 2 + a * ‖iteratedHamiltonianResolvent s a b f‖ ^ 2 ≤ a⁻¹ * ((b⁻¹) ^ 2 * ‖f‖ ^ 2)`
and `‖Eavg s ⟨iteratedHamiltonianResolvent s a b f, ...⟩‖ ^ 2 ≤ a⁻¹ * ((b⁻¹) ^ 2 * ‖f‖ ^ 2)`. -/
theorem iteratedHamiltonianResolvent_averaged_energy_le
    (s a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let x := iteratedHamiltonianResolvent ε hε h hh hb m g k s a b f
    let hEs : x ∈ (Eavg s).domain :=
      (iteratedHamiltonianResolvent_mem_ten_domains ε hε h hh hb m g k s s a b ha hb_pos f).2.2.2.2.1
    ‖Eavg s ⟨x, hEs⟩‖ ^ 2 + a * ‖x‖ ^ 2 ≤ a⁻¹ * ((b⁻¹) ^ 2 * ‖f‖ ^ 2) ∧
    ‖Eavg s ⟨x, hEs⟩‖ ^ 2 ≤ a⁻¹ * ((b⁻¹) ^ 2 * ‖f‖ ^ 2) := by
  intro x hEs
  have h1 := hamiltonian_resolvent_averaged_energy_le ε hε h hh hb m g k s a ha (RH s b f)
  have h2 : ‖RH s b f‖ ^ 2 ≤ (b⁻¹) ^ 2 * ‖f‖ ^ 2 := by
    have hbnd := resolvent_norm_le ε hε h hh hb m g k s b hb_pos f
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hbnd
    simpa only [mul_pow] using hsq
  have hmul := mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr ha.le)
  exact ⟨h1.1.trans hmul, h1.2.trans hmul⟩

/-- Unconditionally for all `s, t, q ∈ ℝ` and `0 < a, 0 < b`,
`evolvedIteratedHamiltonianResolvent s t a b f` belongs simultaneously to all 7 form and clock
domains `(Eavg q).domain`, `(Tstat).domain`, `(Kroot).domain`, `(Tpot).domain`,
`(Tgrow).domain`, `(Tres q).domain`, and `(clockHalf ε).domain`. -/
theorem evolvedIteratedHamiltonianResolvent_mem_all_form_domains
    (s t q a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let u := evolvedIteratedHamiltonianResolvent ε hε h hh hb m g k s t a b f
    u ∈ (Eavg q).domain ∧
    u ∈ (Tstat).domain ∧
    u ∈ (Kroot).domain ∧
    u ∈ (Tpot).domain ∧
    u ∈ (Tgrow).domain ∧
    u ∈ (Tres q).domain ∧
    u ∈ (clockHalf ε).domain :=
  mem_all_form_domains_of_evolved ε hε h hh hb m g k s t q
    (iteratedHamiltonianResolvent_mem_ten_domains ε hε h hh hb m g k s s a b ha hb_pos f).2.2.2.2.1

/-- Exact five-channel form-energy decompositions of `‖Eavg q ⟨evolvedIteratedHamiltonianResolvent s t a b f, ...⟩‖ ^ 2`
along the evolved trajectory for all `s, t, q ∈ ℝ` and `0 < a, 0 < b`. -/
theorem evolvedIteratedHamiltonianResolvent_operator_form_energy_decompositions
    (s t q a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let hEs := (iteratedHamiltonianResolvent_mem_ten_domains
      ε hε h hh hb m g k s s a b ha hb_pos f).2.2.2.2.1
    let u := evolvedIteratedHamiltonianResolvent ε hε h hh hb m g k s t a b f
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
    (iteratedHamiltonianResolvent_mem_ten_domains ε hε h hh hb m g k s s a b ha hb_pos f).2.2.2.2.1

/-- Two-sided exponential trajectory bounds comparing the evolved averaged form energy
`‖Eavg t ⟨evolvedIteratedHamiltonianResolvent s t a b f, ...⟩‖ ^ 2` with the initial
averaged form energy `‖Eavg s ⟨iteratedHamiltonianResolvent s a b f, ...⟩‖ ^ 2`. -/
theorem evolvedIteratedHamiltonianResolvent_two_sided_trajectory_energy_bounds
    (s t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let x := iteratedHamiltonianResolvent ε hε h hh hb m g k s a b f
    let hEs : x ∈ (Eavg s).domain :=
      (iteratedHamiltonianResolvent_mem_ten_domains ε hε h hh hb m g k s s a b ha hb_pos f).2.2.2.2.1
    let u := evolvedIteratedHamiltonianResolvent ε hε h hh hb m g k s t a b f
    let hEt : u ∈ (Eavg t).domain :=
      mem_averaged_domain_of_evolved ε hε h hh hb m g k s t t hEs
    Real.exp (-2 * |t - s|) * ‖Eavg s ⟨x, hEs⟩‖ ^ 2 ≤ ‖Eavg t ⟨u, hEt⟩‖ ^ 2 ∧
    ‖Eavg t ⟨u, hEt⟩‖ ^ 2 ≤ Real.exp (2 * |t - s|) * ‖Eavg s ⟨x, hEs⟩‖ ^ 2 := by
  intro x hEs u hEt
  have hEb := evolved_operator_form_energy_bounds ε hε h hh hb m g k s t t hEs
  exact ⟨hEb.1, hEb.2.1⟩

/-- Unconditional source-norm bounds on the evolved averaged form energy of
`evolvedIteratedHamiltonianResolvent s t a b f` at target time `t` and at arbitrary
observation time `q`. -/
theorem evolvedIteratedHamiltonianResolvent_averaged_energy_le_source
    (s t q a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let hEs :=
      (iteratedHamiltonianResolvent_mem_ten_domains ε hε h hh hb m g k s s a b ha hb_pos f).2.2.2.2.1
    let u := evolvedIteratedHamiltonianResolvent ε hε h hh hb m g k s t a b f
    let hEt := mem_averaged_domain_of_evolved ε hε h hh hb m g k s t t hEs
    let hEq := (evolvedIteratedHamiltonianResolvent_mem_all_form_domains
      ε hε h hh hb m g k s t q a b ha hb_pos f).1
    ‖Eavg t ⟨u, hEt⟩‖ ^ 2 ≤
      Real.exp (2 * |t - s|) * (a⁻¹ * ((b⁻¹) ^ 2 * ‖f‖ ^ 2)) ∧
    ‖Eavg q ⟨u, hEq⟩‖ ^ 2 ≤
      max 1 (Real.exp (2 * (q - t))) * Real.exp (2 * |t - s|) *
        (a⁻¹ * ((b⁻¹) ^ 2 * ‖f‖ ^ 2)) := by
  intro hEs u hEt hEq
  have hb_u := evolved_resolvent_multi_domain_energy_bounds ε hε h hh hb m g k s t q a ha (RH s b f)
  have h2 : ‖RH s b f‖ ^ 2 ≤ (b⁻¹) ^ 2 * ‖f‖ ^ 2 := by
    have hbnd := resolvent_norm_le ε hε h hh hb m g k s b hb_pos f
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hbnd
    simpa only [mul_pow] using hsq
  have hE0 : a⁻¹ * ‖RH s b f‖ ^ 2 ≤ a⁻¹ * ((b⁻¹) ^ 2 * ‖f‖ ^ 2) :=
    mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr ha.le)
  have hexp_pos : 0 ≤ Real.exp (2 * |t - s|) := (Real.exp_pos _).le
  have hmax_pos : 0 ≤ max 1 (Real.exp (2 * (q - t))) * Real.exp (2 * |t - s|) :=
    mul_nonneg (le_trans zero_le_one (le_max_left 1 _)) hexp_pos
  exact ⟨hb_u.2.2.1.trans (mul_le_mul_of_nonneg_left hE0 hexp_pos),
    hb_u.2.2.2.1.trans (mul_le_mul_of_nonneg_left hE0 hmax_pos)⟩

/-- Unconditional static-root (`Tstat`) and half-clock (`clockHalf ε`) trajectory energy
bounds on `evolvedIteratedHamiltonianResolvent s t a b f` in terms of `‖f‖ ^ 2`. -/
theorem evolvedIteratedHamiltonianResolvent_static_and_clock_energy_le_source
    (s t q a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let u := evolvedIteratedHamiltonianResolvent ε hε h hh hb m g k s t a b f
    let hdom := evolvedIteratedHamiltonianResolvent_mem_all_form_domains
      ε hε h hh hb m g k s t q a b ha hb_pos f
    ‖Tstat ⟨u, hdom.2.1⟩‖ ^ 2 ≤
      Real.exp (2 * |t - s|) * (a⁻¹ * ((b⁻¹) ^ 2 * ‖f‖ ^ 2)) ∧
    ‖clockHalf ε ⟨u, hdom.2.2.2.2.2.2⟩‖ ^ 2 ≤
      2 * (Real.exp (2 * |t - s|) * (a⁻¹ * ((b⁻¹) ^ 2 * ‖f‖ ^ 2))) := by
  intro u hdom
  have hb_u := evolved_resolvent_multi_domain_energy_bounds ε hε h hh hb m g k s t q a ha (RH s b f)
  have h2 : ‖RH s b f‖ ^ 2 ≤ (b⁻¹) ^ 2 * ‖f‖ ^ 2 := by
    have hbnd := resolvent_norm_le ε hε h hh hb m g k s b hb_pos f
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hbnd
    simpa only [mul_pow] using hsq
  have hE0 : a⁻¹ * ‖RH s b f‖ ^ 2 ≤ a⁻¹ * ((b⁻¹) ^ 2 * ‖f‖ ^ 2) :=
    mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr ha.le)
  have hexp_pos : 0 ≤ Real.exp (2 * |t - s|) := (Real.exp_pos _).le
  have hmul := mul_le_mul_of_nonneg_left hE0 hexp_pos
  exact ⟨hb_u.2.2.2.2.1.trans hmul,
    hb_u.2.2.2.2.2.1.trans (mul_le_mul_of_nonneg_left hmul (by norm_num))⟩

/-- Unconditional growing (`Tgrow`), radial-root (`Kroot`), and potential-form (`Tpot`)
trajectory energy bounds on `evolvedIteratedHamiltonianResolvent s t a b f` in terms of `‖f‖ ^ 2`. -/
theorem evolvedIteratedHamiltonianResolvent_growing_radial_potential_energy_le_source
    (s t q a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let u := evolvedIteratedHamiltonianResolvent ε hε h hh hb m g k s t a b f
    let hdom := evolvedIteratedHamiltonianResolvent_mem_all_form_domains
      ε hε h hh hb m g k s t q a b ha hb_pos f
    ‖Tgrow ⟨u, hdom.2.2.2.2.1⟩‖ ^ 2 ≤
      Real.exp (2 * (|t - s| - t)) * (a⁻¹ * ((b⁻¹) ^ 2 * ‖f‖ ^ 2)) ∧
    ‖Kroot ⟨u, hdom.2.2.1⟩‖ ^ 2 ≤
      Real.exp (2 * (|t - s| - t)) * (a⁻¹ * ((b⁻¹) ^ 2 * ‖f‖ ^ 2)) ∧
    ‖Tpot ⟨u, hdom.2.2.2.1⟩‖ ^ 2 ≤
      Real.exp (2 * (|t - s| - t)) * (a⁻¹ * ((b⁻¹) ^ 2 * ‖f‖ ^ 2)) := by
  intro u hdom
  have hb_u := evolved_resolvent_multi_domain_energy_bounds ε hε h hh hb m g k s t q a ha (RH s b f)
  have h2 : ‖RH s b f‖ ^ 2 ≤ (b⁻¹) ^ 2 * ‖f‖ ^ 2 := by
    have hbnd := resolvent_norm_le ε hε h hh hb m g k s b hb_pos f
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hbnd
    simpa only [mul_pow] using hsq
  have hE0 : a⁻¹ * ‖RH s b f‖ ^ 2 ≤ a⁻¹ * ((b⁻¹) ^ 2 * ‖f‖ ^ 2) :=
    mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr ha.le)
  have hexp_sub_pos : 0 ≤ Real.exp (2 * (|t - s| - t)) := (Real.exp_pos _).le
  have hmul := mul_le_mul_of_nonneg_left hE0 hexp_sub_pos
  exact ⟨hb_u.2.2.2.2.2.2.2.1.trans hmul,
    hb_u.2.2.2.2.2.2.2.2.2.1.trans hmul,
    hb_u.2.2.2.2.2.2.2.2.2.2.2.1.trans hmul⟩

/-- Unconditional residual-form (`Tres q`) trajectory energy bound on
`evolvedIteratedHamiltonianResolvent s t a b f` in terms of `‖f‖ ^ 2`. -/
theorem evolvedIteratedHamiltonianResolvent_residual_energy_le_source
    (s t q a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let u := evolvedIteratedHamiltonianResolvent ε hε h hh hb m g k s t a b f
    let hdom := evolvedIteratedHamiltonianResolvent_mem_all_form_domains
      ε hε h hh hb m g k s t q a b ha hb_pos f
    ‖Tres q ⟨u, hdom.2.2.2.2.2.1⟩‖ ^ 2 ≤
      max 1 (Real.exp (2 * (q - t))) * Real.exp (2 * |t - s|) *
        (a⁻¹ * ((b⁻¹) ^ 2 * ‖f‖ ^ 2)) := by
  intro u hdom
  have hb_u := evolved_resolvent_multi_domain_energy_bounds ε hε h hh hb m g k s t q a ha (RH s b f)
  have h2 : ‖RH s b f‖ ^ 2 ≤ (b⁻¹) ^ 2 * ‖f‖ ^ 2 := by
    have hbnd := resolvent_norm_le ε hε h hh hb m g k s b hb_pos f
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hbnd
    simpa only [mul_pow] using hsq
  have hE0 : a⁻¹ * ‖RH s b f‖ ^ 2 ≤ a⁻¹ * ((b⁻¹) ^ 2 * ‖f‖ ^ 2) :=
    mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr ha.le)
  have hmax_pos : 0 ≤ max 1 (Real.exp (2 * (q - t))) * Real.exp (2 * |t - s|) :=
    mul_nonneg (le_trans zero_le_one (le_max_left 1 _)) (Real.exp_pos _).le
  exact hb_u.2.2.2.2.2.2.2.2.2.2.2.2.trans (mul_le_mul_of_nonneg_left hE0 hmax_pos)

/-! ### 3. Unconditional 10-Domain Regularity, Second-Power Decompositions, and Uniform Bounds for `iteratedResolventOfEvolvedState` -/

/-- Unconditionally for all `s, t, r, q ∈ ℝ` and `0 < a, 0 < b`,
`iteratedResolventOfEvolvedState s t r a b f` belongs simultaneously to
`hamiltonianSecondPowerDomain r` and all 10 operator, form, and clock domains. -/
theorem iteratedResolventOfEvolvedState_mem_ten_domains
    (s t r q a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let x := iteratedResolventOfEvolvedState ε hε h hh hb m g k s t r a b f
    x ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k r ∧
    x ∈ (H r).domain ∧
    x ∈ (K).domain ∧
    x ∈ (S r).domain ∧
    x ∈ (Eavg q).domain ∧
    x ∈ (Tstat).domain ∧
    x ∈ (Kroot).domain ∧
    x ∈ (Tpot).domain ∧
    x ∈ (Tgrow).domain ∧
    x ∈ (Tres q).domain ∧
    x ∈ (clockHalf ε).domain :=
  iteratedHamiltonianResolvent_mem_ten_domains ε hε h hh hb m g k r q a b ha hb_pos (U s t f)

/-- Unconditionally for all `s, t, r, q ∈ ℝ` and `0 < a, 0 < b`, the first-power Hamiltonian
output `RH r b (U s t f) - (a : ℂ) • iteratedResolventOfEvolvedState s t r a b f` belongs
simultaneously to all 10 operator, form, and clock domains. -/
theorem iteratedResolventOfEvolvedState_first_power_mem_ten_domains
    (s t r q a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let y := RH r b (U s t f) -
      (a : ℂ) • iteratedResolventOfEvolvedState ε hε h hh hb m g k s t r a b f
    y ∈ (H r).domain ∧
    y ∈ (K).domain ∧
    y ∈ (S r).domain ∧
    y ∈ (Eavg q).domain ∧
    y ∈ (Tstat).domain ∧
    y ∈ (Kroot).domain ∧
    y ∈ (Tpot).domain ∧
    y ∈ (Tgrow).domain ∧
    y ∈ (Tres q).domain ∧
    y ∈ (clockHalf ε).domain :=
  iteratedHamiltonianResolvent_first_power_mem_ten_domains
    ε hε h hh hb m g k r q a b ha hb_pos (U s t f)

/-- Exact first-power radial-residual decomposition on `x := iteratedResolventOfEvolvedState s t r a b f`:
`H r x = exp(2r) • K x + S r x = RH r b (U s t f) - (a : ℂ) • x`. -/
theorem iteratedResolventOfEvolvedState_hamiltonian_eq_radial_add_residual
    (s t r a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let x := iteratedResolventOfEvolvedState ε hε h hh hb m g k s t r a b f
    let hdom := iteratedHamiltonianResolvent_mem_radial_residual_domain
      ε hε h hh hb m g k r a b ha hb_pos (U s t f)
    H r ⟨x, hdom.1⟩ =
      (Real.exp (2 * r) : ℂ) • K ⟨x, hdom.2.1⟩ + S r ⟨x, hdom.2.2⟩ ∧
    H r ⟨x, hdom.1⟩ = RH r b (U s t f) - (a : ℂ) • x :=
  iteratedHamiltonianResolvent_hamiltonian_eq_radial_add_residual
    ε hε h hh hb m g k r a b ha hb_pos (U s t f)

/-- Exact second-power radial-residual identity for `x := iteratedResolventOfEvolvedState s t r a b f`
and `y := RH r b (U s t f) - (a : ℂ) • x`:
`exp(2r) • K y + S r y = U s t f - ((a + b : ℝ) : ℂ) • RH r b (U s t f) + ((a ^ 2 : ℝ) : ℂ) • x`. -/
theorem iteratedResolventOfEvolvedState_second_power_radial_residual_eq
    (s t r a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let x := iteratedResolventOfEvolvedState ε hε h hh hb m g k s t r a b f
    let y := RH r b (U s t f) - (a : ℂ) • x
    let hdom := iteratedHamiltonianResolvent_first_power_mem_radial_residual_domain
      ε hε h hh hb m g k r a b ha hb_pos (U s t f)
    (Real.exp (2 * r) : ℂ) • K ⟨y, hdom.2.1⟩ + S r ⟨y, hdom.2.2⟩ =
      U s t f - ((a + b : ℝ) : ℂ) • RH r b (U s t f) + ((a ^ 2 : ℝ) : ℂ) • x :=
  iteratedHamiltonianResolvent_second_power_radial_residual_eq
    ε hε h hh hb m g k r a b ha hb_pos (U s t f)

/-- Unconditional combined radial and residual norm-square bound on
`x := iteratedResolventOfEvolvedState s t r a b f` uniform in the evolution times `(s, t)`:
`exp(4r) ‖K x‖² + ‖S r x‖² ≤ (2 + 2 exp(2r) (h²/ε²) (a⁻¹)²) * (b⁻¹)² * ‖f‖²`. -/
theorem iteratedResolventOfEvolvedState_component_norm_sq_le_source
    (s t r a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let x := iteratedResolventOfEvolvedState ε hε h hh hb m g k s t r a b f
    let hdom := iteratedHamiltonianResolvent_mem_radial_residual_domain
      ε hε h hh hb m g k r a b ha hb_pos (U s t f)
    Real.exp (4 * r) * ‖K ⟨x, hdom.2.1⟩‖ ^ 2 + ‖S r ⟨x, hdom.2.2⟩‖ ^ 2 ≤
      (2 + 2 * Real.exp (2 * r) * (h ^ 2 / ε ^ 2) * (a⁻¹) ^ 2) * (b⁻¹) ^ 2 * ‖f‖ ^ 2 := by
  intro x hdom
  have h1 := iteratedHamiltonianResolvent_component_norm_sq_le_source
    ε hε h hh hb m g k r a b ha hb_pos (U s t f)
  have hnorm : ‖U s t f‖ = ‖f‖ := evolution_norm ε hε h hh hw m g k s t f
  exact h1.trans_eq
    (congrArg
      (fun u : ℝ =>
        (2 + 2 * Real.exp (2 * r) * (h ^ 2 / ε ^ 2) * (a⁻¹) ^ 2) * (b⁻¹) ^ 2 * u ^ 2)
      hnorm)

/-- Unconditional combined radial and residual norm-square bound on the first-power output
`y := RH r b (U s t f) - (a : ℂ) • iteratedResolventOfEvolvedState s t r a b f` uniform in `(s, t)`:
`exp(4r) ‖K y‖² + ‖S r y‖² ≤ 4 * (2 + 2 exp(2r) (h²/ε²) (a⁻¹)²) * ‖f‖²`. -/
theorem iteratedResolventOfEvolvedState_first_power_component_norm_sq_le_source
    (s t r a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let y := RH r b (U s t f) -
      (a : ℂ) • iteratedResolventOfEvolvedState ε hε h hh hb m g k s t r a b f
    let hdom := iteratedHamiltonianResolvent_first_power_mem_radial_residual_domain
      ε hε h hh hb m g k r a b ha hb_pos (U s t f)
    Real.exp (4 * r) * ‖K ⟨y, hdom.2.1⟩‖ ^ 2 + ‖S r ⟨y, hdom.2.2⟩‖ ^ 2 ≤
      4 * (2 + 2 * Real.exp (2 * r) * (h ^ 2 / ε ^ 2) * (a⁻¹) ^ 2) * ‖f‖ ^ 2 := by
  intro y hdom
  have h1 := iteratedHamiltonianResolvent_first_power_component_norm_sq_le_source
    ε hε h hh hb m g k r a b ha hb_pos (U s t f)
  have hnorm : ‖U s t f‖ = ‖f‖ := evolution_norm ε hε h hh hw m g k s t f
  exact h1.trans_eq
    (congrArg
      (fun u : ℝ =>
        4 * (2 + 2 * Real.exp (2 * r) * (h ^ 2 / ε ^ 2) * (a⁻¹) ^ 2) * u ^ 2)
      hnorm)

/-- Unconditional averaged form-energy and three-channel (`Tstat`, `Kroot`, `Tpot`) form-energy
bounds on `x := iteratedResolventOfEvolvedState s t r a b f` uniform in `(s, t)`:
`‖Eavg r ⟨x, ...⟩‖ ^ 2 + a * ‖x‖ ^ 2 ≤ a⁻¹ * ((b⁻¹) ^ 2 * ‖f‖ ^ 2)` and
`‖Tstat x‖ ^ 2 + exp(2r) ‖Kroot x‖ ^ 2 + exp(2r) ‖Tpot x‖ ^ 2 + a ‖x‖ ^ 2 ≤ a⁻¹ * ((b⁻¹) ^ 2 * ‖f‖ ^ 2)`. -/
theorem iteratedResolventOfEvolvedState_averaged_and_three_channel_energy_le
    (s t r a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let x := iteratedResolventOfEvolvedState ε hε h hh hb m g k s t r a b f
    let hEr : x ∈ (Eavg r).domain :=
      (iteratedResolventOfEvolvedState_mem_ten_domains ε hε h hh hb m g k s t r r a b ha hb_pos f).2.2.2.2.1
    ‖Eavg r ⟨x, hEr⟩‖ ^ 2 + a * ‖x‖ ^ 2 ≤ a⁻¹ * ((b⁻¹) ^ 2 * ‖f‖ ^ 2) ∧
    ‖Tstat ⟨x,
      hamiltonian_resolvent_mem_staticRoot_domain ε hε h hh hb m g k r a ha (RH r b (U s t f))⟩‖ ^ 2 +
      Real.exp (2 * r) *
        ‖Kroot ⟨x,
          hamiltonian_resolvent_mem_radialRoot_domain ε hε h hh hb m g k r a ha (RH r b (U s t f))⟩‖ ^ 2 +
      Real.exp (2 * r) *
        ‖Tpot ⟨x,
          hamiltonian_resolvent_mem_potentialForm_domain ε hε h hh hb m g k r a ha (RH r b (U s t f))⟩‖ ^ 2 +
      a * ‖x‖ ^ 2 ≤ a⁻¹ * ((b⁻¹) ^ 2 * ‖f‖ ^ 2) := by
  intro x hEr
  have hnorm : ‖U s t f‖ = ‖f‖ := evolution_norm ε hε h hh hw m g k s t f
  have h1 := (iteratedHamiltonianResolvent_averaged_energy_le
    ε hε h hh hb m g k r a b ha hb_pos (U s t f)).1.trans_eq
    (congrArg (fun u : ℝ => a⁻¹ * ((b⁻¹) ^ 2 * u ^ 2)) hnorm)
  have h3 := hamiltonian_resolvent_three_channel_energy_le
    ε hε h hh hb m g k r a ha (RH r b (U s t f))
  have h2 : ‖RH r b (U s t f)‖ ^ 2 ≤ (b⁻¹) ^ 2 * ‖f‖ ^ 2 := by
    have hbnd := (resolvent_norm_le ε hε h hh hb m g k r b hb_pos (U s t f)).trans_eq
      (congrArg (b⁻¹ * ·) hnorm)
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hbnd
    simpa only [mul_pow] using hsq
  have hmul := mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr ha.le)
  exact ⟨h1, h3.trans hmul⟩

/-! ### 4. Five-Operator Second-Power Regularity, Evolved Squared-Resolvent Differences, and Weak Continuity -/

/-- Applying the 5 iterated resolvents (`staticResolvent`, `RP`, `RG`, `RS r`, `RH r`) with `0 < a, 0 < b`
to any evolved state `U s t f` places the resulting vectors in their respective second-power
domains (`staticSecondPowerDomain`, `potentialSecondPowerDomain`, `growingSecondPowerDomain`,
`residualSecondPowerDomain r`, `hamiltonianSecondPowerDomain r`) with exact `(a, b)` commutativity. -/
theorem five_operator_iterated_resolvents_of_evolved_state_mem_secondPowerDomains
    (s t r a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let w := U s t f
    (staticResolvent ε hε h hb hh a (staticResolvent ε hε h hb hh b w) ∈
       staticSecondPowerDomain ε hε h ∧
     RP a (RP b w) ∈ potentialSecondPowerDomain ε hε h hh hb m g k ∧
     RG a (RG b w) ∈ growingSecondPowerDomain ε hε h hh hb m g k ∧
     RS r a (RS r b w) ∈ residualSecondPowerDomain ε hε h hh hb m g k r ∧
     RH r a (RH r b w) ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k r) ∧
    (RT a (RT b w) = RT b (RT a w) ∧
     RP a (RP b w) = RP b (RP a w) ∧
     RG a (RG b w) = RG b (RG a w) ∧
     RS r a (RS r b w) = RS r b (RS r a w) ∧
     RH r a (RH r b w) = RH r b (RH r a w)) :=
  ⟨five_hamiltonians_iterated_resolvent_mem_secondPowerDomain
     ε hε h hh hb m g k r a b ha hb_pos (U s t f),
   ⟨quarterStripResolvent_comm ε hε h hh hb m g k a b ha hb_pos (U s t f),
    potentialResolvent_comm ε hε h hh hb m g k a b ha hb_pos (U s t f),
    staticGeneratorResolvent_comm ε hε h hh hb m g k a b ha hb_pos (U s t f),
    staticResidualResolvent_comm ε hε h hh hb m g k r a b ha hb_pos (U s t f),
    hamiltonianResolvent_comm ε hε h hh hb m g k r a b ha hb_pos (U s t f)⟩⟩

/-- Exact triple-resolvent factorization of `evolvedSquaredResolventSub`:
`evolvedSquaredResolventSub s t a b f = ((b - a : ℝ) : ℂ) • U s t (RH s a (RH s a (RH s b f)) + RH s a (RH s b (RH s b f)))`. -/
theorem evolvedSquaredResolventSub_eq_triple_resolvent
    (s t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    evolvedSquaredResolventSub ε hε h hh hb m g k s t a b f =
      ((b - a : ℝ) : ℂ) •
        U s t (RH s a (RH s a (RH s b f)) + RH s a (RH s b (RH s b f))) :=
  (congrArg (U s t)
    (hamiltonianResolvent_squared_sub_eq ε hε h hh hb m g k s a b ha hb_pos f)).trans
    (map_smul (U s t) ((b - a : ℝ) : ℂ)
      (RH s a (RH s a (RH s b f)) + RH s a (RH s b (RH s b f))))

/-- Unconditional quartic norm decay along the evolved squared-resolvent difference trajectory:
`‖evolvedSquaredResolventSub s t a b f‖ ≤ |a - b| * ((a⁻¹ + b⁻¹) * a⁻¹ * b⁻¹ * ‖f‖)`. -/
theorem evolvedSquaredResolventSub_norm_le
    (s t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    ‖evolvedSquaredResolventSub ε hε h hh hb m g k s t a b f‖ ≤
      |a - b| * ((a⁻¹ + b⁻¹) * a⁻¹ * b⁻¹ * ‖f‖) :=
  (evolution_norm ε hε h hh hw m g k s t
    (squaredHamiltonianResolvent ε hε h hh hb m g k s a f -
     squaredHamiltonianResolvent ε hε h hh hb m g k s b f)).trans_le
    (hamiltonianResolvent_squared_sub_norm_le ε hε h hh hb m g k s a b ha hb_pos f)

/-- Unconditionally for all `s, t, q ∈ ℝ` and `0 < a, 0 < b`,
`evolvedSquaredResolventSub s t a b f` belongs simultaneously to all 7 form and clock domains
`(Eavg q).domain`, `(Tstat).domain`, `(Kroot).domain`, `(Tpot).domain`, `(Tgrow).domain`,
`(Tres q).domain`, and `(clockHalf ε).domain`. -/
theorem evolvedSquaredResolventSub_mem_all_form_domains
    (s t q a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let u := evolvedSquaredResolventSub ε hε h hh hb m g k s t a b f
    u ∈ (Eavg q).domain ∧
    u ∈ (Tstat).domain ∧
    u ∈ (Kroot).domain ∧
    u ∈ (Tpot).domain ∧
    u ∈ (Tgrow).domain ∧
    u ∈ (Tres q).domain ∧
    u ∈ (clockHalf ε).domain :=
  mem_all_form_domains_of_evolved ε hε h hh hb m g k s t q
    (hamiltonianResolvent_squared_sub_mem_ten_domains ε hε h hh hb m g k s s a b ha hb_pos f).2.2.2.2.1

/-- Applying the squared-resolvent difference at time `r` to an evolved state `U s t f`
places `squaredHamiltonianResolvent r a (U s t f) - squaredHamiltonianResolvent r b (U s t f)`
in `hamiltonianPowerDomain r 3` and all 10 operator, form, and clock domains, with norm
bounded by `|a - b| * ((a⁻¹ + b⁻¹) * a⁻¹ * b⁻¹ * ‖f‖)` uniformly in `(s, t)`. -/
theorem squaredResolventSub_of_evolved_state_mem_thirdPower_and_ten_domains
    (s t r q a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let d := squaredHamiltonianResolvent ε hε h hh hb m g k r a (U s t f) -
             squaredHamiltonianResolvent ε hε h hh hb m g k r b (U s t f)
    (d ∈ hamiltonianPowerDomain ε hε h hh hb m g k r 3 ∧
     d ∈ (H r).domain ∧
     d ∈ (K).domain ∧
     d ∈ (S r).domain ∧
     d ∈ (Eavg q).domain ∧
     d ∈ (Tstat).domain ∧
     d ∈ (Kroot).domain ∧
     d ∈ (Tpot).domain ∧
     d ∈ (Tgrow).domain ∧
     d ∈ (Tres q).domain ∧
     d ∈ (clockHalf ε).domain) ∧
    ‖d‖ ≤ |a - b| * ((a⁻¹ + b⁻¹) * a⁻¹ * b⁻¹ * ‖f‖) :=
  ⟨hamiltonianResolvent_squared_sub_mem_ten_domains
     ε hε h hh hb m g k r q a b ha hb_pos (U s t f),
   (hamiltonianResolvent_squared_sub_norm_le
     ε hε h hh hb m g k r a b ha hb_pos (U s t f)).trans_eq
     (congrArg (fun u : ℝ => |a - b| * ((a⁻¹ + b⁻¹) * a⁻¹ * b⁻¹ * u))
       (evolution_norm ε hε h hh hw m g k s t f))⟩

/-- Unconditional weak Lipschitz bound for the evolved iterated resolvent with two-time
outer resolvent `U t₁ t₂ (RH s a (RH r b f₂)) - U t₁ t₂ (RH t a (RH r b f₂))`:
`‖inner ℂ f₁ (U t₁ t₂ (RH s a (RH r b f₂)) - U t₁ t₂ (RH t a (RH r b f₂)))‖ ≤ |Real.exp (2 * t) - Real.exp (2 * s)| * (2 * Real.exp (-(t + s)) * a⁻¹ * ‖f₁‖ * (b⁻¹ * ‖f₂‖))`. -/
theorem evolvedIteratedHamiltonianResolvent_two_time_outer_weak_diff_bound
    (t₁ t₂ s t r a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f₁ f₂ : Hilbert) :
    ‖inner ℂ f₁ (U t₁ t₂ (RH s a (RH r b f₂)) - U t₁ t₂ (RH t a (RH r b f₂)))‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| *
        (2 * Real.exp (-(t + s)) * a⁻¹ * ‖f₁‖ * (b⁻¹ * ‖f₂‖)) := by
  have h1 := evolved_two_time_resolvent_weak_diff_bound
    ε hε h hh hb m g k t₁ t₂ s t a ha f₁ (RH r b f₂)
  have h2 := resolvent_norm_le ε hε h hh hb m g k r b hb_pos f₂
  have hcoeff : 0 ≤ |Real.exp (2 * t) - Real.exp (2 * s)| *
      (2 * Real.exp (-(t + s)) * a⁻¹ * ‖f₁‖) := by positivity
  have hmul := mul_le_mul_of_nonneg_left h2 hcoeff
  exact h1.trans (by linarith)

/-- Unconditional weak continuity `⟪f₁, U t₁ t₂ (RH s a (RH r b f₂))⟫ → ⟪f₁, U t₁ t₂ (RH t a (RH r b f₂))⟫`
as `s → t` for all `f₁, f₂ : Hilbert` and `0 < a, 0 < b`. -/
theorem evolvedIteratedHamiltonianResolvent_two_time_outer_weak_continuous
    (t₁ t₂ t r a b : ℝ) (ha : 0 < a) (f₁ f₂ : Hilbert) :
    Tendsto (fun s : ℝ => inner ℂ f₁ (U t₁ t₂ (RH s a (RH r b f₂))))
      (𝓝 t) (𝓝 (inner ℂ f₁ (U t₁ t₂ (RH t a (RH r b f₂))))) :=
  evolved_two_time_resolvent_weak_continuous
    ε hε h hh hb m g k t₁ t₂ t a ha f₁ (RH r b f₂)

#print axioms evolvedIteratedHamiltonianResolvent_eq
#print axioms iteratedResolventOfEvolvedState_eq
#print axioms evolvedSquaredResolventSub_eq
#print axioms evolvedIteratedHamiltonianResolvent_comm
#print axioms iteratedResolventOfEvolvedState_comm
#print axioms evolvedIteratedHamiltonianResolvent_norm_eq
#print axioms evolvedIteratedHamiltonianResolvent_norm_le
#print axioms iteratedResolventOfEvolvedState_norm_le
#print axioms evolvedIteratedHamiltonianResolvent_reverse_eq
#print axioms evolvedIteratedHamiltonianResolvent_inner_eq
#print axioms iteratedHamiltonianResolvent_averaged_energy_le
#print axioms evolvedIteratedHamiltonianResolvent_mem_all_form_domains
#print axioms evolvedIteratedHamiltonianResolvent_operator_form_energy_decompositions
#print axioms evolvedIteratedHamiltonianResolvent_two_sided_trajectory_energy_bounds
#print axioms evolvedIteratedHamiltonianResolvent_averaged_energy_le_source
#print axioms evolvedIteratedHamiltonianResolvent_static_and_clock_energy_le_source
#print axioms evolvedIteratedHamiltonianResolvent_growing_radial_potential_energy_le_source
#print axioms evolvedIteratedHamiltonianResolvent_residual_energy_le_source
#print axioms iteratedResolventOfEvolvedState_mem_ten_domains
#print axioms iteratedResolventOfEvolvedState_first_power_mem_ten_domains
#print axioms iteratedResolventOfEvolvedState_hamiltonian_eq_radial_add_residual
#print axioms iteratedResolventOfEvolvedState_second_power_radial_residual_eq
#print axioms iteratedResolventOfEvolvedState_component_norm_sq_le_source
#print axioms iteratedResolventOfEvolvedState_first_power_component_norm_sq_le_source
#print axioms iteratedResolventOfEvolvedState_averaged_and_three_channel_energy_le
#print axioms five_operator_iterated_resolvents_of_evolved_state_mem_secondPowerDomains
#print axioms evolvedSquaredResolventSub_eq_triple_resolvent
#print axioms evolvedSquaredResolventSub_norm_le
#print axioms evolvedSquaredResolventSub_mem_all_form_domains
#print axioms squaredResolventSub_of_evolved_state_mem_thirdPower_and_ten_domains
#print axioms evolvedIteratedHamiltonianResolvent_two_time_outer_weak_diff_bound
#print axioms evolvedIteratedHamiltonianResolvent_two_time_outer_weak_continuous

end

end UnifiedTheory.Audit.KFCausalClockFloorEvolvedIteratedResolventTrajectoryRegularity
