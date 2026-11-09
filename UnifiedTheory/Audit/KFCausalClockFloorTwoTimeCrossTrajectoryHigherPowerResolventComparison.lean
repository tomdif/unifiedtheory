/- Cross-Trajectory (`(s₁, s₂)` and `(t₁, t₂)`) and Cross-Shift (`(a, b)`) Higher-Power
Iterated Resolvent and Yosida Identity Comparisons, Bridge Decompositions, 10-Domain and
8-Domain Regularity, and Multi-Trajectory Cocycle Algebra:
1. Extends `KFCausalClockFloorTwoTimeEvolvedHigherPowerResolventDifference` from single-trajectory
   two-shift differences `(s, t, a, b)` to four-parameter cross-initial comparisons
   `crossInitialHigherPowerResolventDiff s₁ s₂ t a b r f₁ f₂ := R_{H(t)}(a)^{r+2}(U(s₁, t) f₁) - R_{H(t)}(b)^{r+2}(U(s₂, t) f₂)`
   and `crossInitialHigherPowerIdentityDiff s₁ s₂ t a b r f₁ f₂ := (a R_{H(t)}(a))^{r+2}(U(s₁, t) f₁) - (b R_{H(t)}(b))^{r+2}(U(s₂, t) f₂)`,
   as well as cross-final comparisons
   `crossFinalHigherPowerResolventDiff s t₁ t₂ a b r f := R_{H(t₁)}(a)^{r+2}(U(s, t₁) f) - R_{H(t₂)}(b)^{r+2}(U(s, t₂) f)`
   and `crossFinalHigherPowerIdentityDiff s t₁ t₂ a b r f := (a R_{H(t₁)}(a))^{r+2}(U(s, t₁) f) - (b R_{H(t₂)}(b))^{r+2}(U(s, t₂) f)`.
2. Proves:
   - Diagonal vanishing, skew-symmetry, and three-trajectory cocycle cancellation across
     `(s₁, a, f₁; s₂, b, f₂; s₃, c, f₃)` and `(t₁, a; t₂, b; t₃, c)`,
   - Exact bridge decompositions splitting `crossInitialHigherPowerResolventDiff` into the
     single-trajectory shift difference `higherPowerResolventSubOfEvolvedState s₁ t a b r f₁`
     plus the unitary state difference `R_{H(t)}(b)^{r+2}(U(s₁, t) f₁ - U(s₂, t) f₂)`,
   - Unconditional membership of `crossInitialHigherPowerResolventDiff` and
     `crossInitialHigherPowerIdentityDiff` in `hamiltonianPowerDomain t (r + 2)`,
     `hamiltonianSecondPowerDomain t`, and all 10 operator, form, and clock domains, with
     explicit two-source and bridge norm bounds,
   - Unconditional membership of `crossFinalHigherPowerResolventDiff` and
     `crossFinalHigherPowerIdentityDiff` across all 8 time-independent / observation-time `q`
     domains (`K`, `Eavg q`, `Tstat`, `Kroot`, `Tpot`, `Tgrow`, `Tres q`, `clockHalf ε`), with
     geometric `((a⁻¹)^{r+2} + (b⁻¹)^{r+2}) * ‖f‖` and uniform `2 * ‖f‖` bounds. -/
import UnifiedTheory.Audit.KFCausalClockFloorTwoTimeEvolvedHigherPowerResolventDifference

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorTwoTimeCrossTrajectoryHigherPowerResolventComparison

noncomputable section

open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorAveragedEvolution (evolution)
open KFCausalClockFloorIteratedResolventSecondPowerCore
  (hamiltonianSecondPowerDomain)
open KFCausalClockFloorHigherPowerOperatorCores
  (iteratedResolventPower iteratedResolventPower_norm_bound
   hamiltonianPowerDomain)
open KFCausalClockFloorHigherPowerYosidaGraphConvergence
  (iteratedIdentityPower iteratedIdentityPower_sub
   iteratedIdentityPower_norm_le)
open KFCausalClockFloorTwoTimeEvolvedHigherPowerResolventRegularity
  (higherPowerResolventOfEvolvedState
   higherPowerIdentityOfEvolvedState
   higherPowerResolventSubOfEvolvedState
   higherPowerResolventOfEvolvedState_mem_power_and_ten_domains
   higherPowerIdentityOfEvolvedState_mem_power_and_ten_domains
   higherPowerResolventSubOfEvolvedState_mem_succ_power_and_ten_domains)
open KFCausalClockFloorTwoTimeEvolvedHigherPowerResolventDifference
  (higherPowerIdentitySubOfEvolvedState
   higherPowerIdentitySubOfEvolvedState_mem_power_and_ten_domains)

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

/-! ### 1. Cross-Initial and Cross-Final Higher-Power Resolvent & Yosida Differences -/

/-- Cross-initial `(r + 2)`-fold iterated Hamiltonian resolvent difference at target time `t`
comparing `U(s₁, t) f₁` at shift `a` against `U(s₂, t) f₂` at shift `b`:
`R_{H(t)}(a)^{r+2}(U(s₁, t) f₁) - R_{H(t)}(b)^{r+2}(U(s₂, t) f₂)`. -/
def crossInitialHigherPowerResolventDiff
    (s₁ s₂ t a b : ℝ) (r : ℕ) (f₁ f₂ : Hilbert) : Hilbert :=
  higherPowerResolventOfEvolvedState ε hε h hh hb m g k s₁ t a r f₁ -
    higherPowerResolventOfEvolvedState ε hε h hh hb m g k s₂ t b r f₂

/-- Cross-initial `(r + 2)`-th order Yosida identity difference at target time `t`
comparing `U(s₁, t) f₁` at shift `a` against `U(s₂, t) f₂` at shift `b`:
`(a R_{H(t)}(a))^{r+2}(U(s₁, t) f₁) - (b R_{H(t)}(b))^{r+2}(U(s₂, t) f₂)`. -/
def crossInitialHigherPowerIdentityDiff
    (s₁ s₂ t a b : ℝ) (r : ℕ) (f₁ f₂ : Hilbert) : Hilbert :=
  higherPowerIdentityOfEvolvedState ε hε h hh hb m g k s₁ t a r f₁ -
    higherPowerIdentityOfEvolvedState ε hε h hh hb m g k s₂ t b r f₂

/-- Cross-final `(r + 2)`-fold iterated Hamiltonian resolvent difference from initial time `s`
comparing target time `t₁` at shift `a` against target time `t₂` at shift `b`:
`R_{H(t₁)}(a)^{r+2}(U(s, t₁) f) - R_{H(t₂)}(b)^{r+2}(U(s, t₂) f)`. -/
def crossFinalHigherPowerResolventDiff
    (s t₁ t₂ a b : ℝ) (r : ℕ) (f : Hilbert) : Hilbert :=
  higherPowerResolventOfEvolvedState ε hε h hh hb m g k s t₁ a r f -
    higherPowerResolventOfEvolvedState ε hε h hh hb m g k s t₂ b r f

/-- Cross-final `(r + 2)`-th order Yosida identity difference from initial time `s`
comparing target time `t₁` at shift `a` against target time `t₂` at shift `b`:
`(a R_{H(t₁)}(a))^{r+2}(U(s, t₁) f) - (b R_{H(t₂)}(b))^{r+2}(U(s, t₂) f)`. -/
def crossFinalHigherPowerIdentityDiff
    (s t₁ t₂ a b : ℝ) (r : ℕ) (f : Hilbert) : Hilbert :=
  higherPowerIdentityOfEvolvedState ε hε h hh hb m g k s t₁ a r f -
    higherPowerIdentityOfEvolvedState ε hε h hh hb m g k s t₂ b r f

/-- Diagonal vanishing, skew-symmetry, and three-trajectory cocycle cancellation for
`crossInitialHigherPowerResolventDiff` and `crossInitialHigherPowerIdentityDiff`. -/
theorem crossInitialHigherPowerDiff_cocycle_identities
    (s₁ s₂ s₃ t a b c : ℝ) (r : ℕ) (f₁ f₂ f₃ : Hilbert) :
    crossInitialHigherPowerResolventDiff ε hε h hh hb m g k s₁ s₁ t a a r f₁ f₁ = 0 ∧
    crossInitialHigherPowerIdentityDiff ε hε h hh hb m g k s₁ s₁ t a a r f₁ f₁ = 0 ∧
    crossInitialHigherPowerResolventDiff ε hε h hh hb m g k s₂ s₁ t b a r f₂ f₁ =
      -crossInitialHigherPowerResolventDiff ε hε h hh hb m g k s₁ s₂ t a b r f₁ f₂ ∧
    crossInitialHigherPowerIdentityDiff ε hε h hh hb m g k s₂ s₁ t b a r f₂ f₁ =
      -crossInitialHigherPowerIdentityDiff ε hε h hh hb m g k s₁ s₂ t a b r f₁ f₂ ∧
    crossInitialHigherPowerResolventDiff ε hε h hh hb m g k s₁ s₂ t a b r f₁ f₂ +
        crossInitialHigherPowerResolventDiff ε hε h hh hb m g k s₂ s₃ t b c r f₂ f₃ =
      crossInitialHigherPowerResolventDiff ε hε h hh hb m g k s₁ s₃ t a c r f₁ f₃ ∧
    crossInitialHigherPowerIdentityDiff ε hε h hh hb m g k s₁ s₂ t a b r f₁ f₂ +
        crossInitialHigherPowerIdentityDiff ε hε h hh hb m g k s₂ s₃ t b c r f₂ f₃ =
      crossInitialHigherPowerIdentityDiff ε hε h hh hb m g k s₁ s₃ t a c r f₁ f₃ := by
  unfold crossInitialHigherPowerResolventDiff crossInitialHigherPowerIdentityDiff
  refine ⟨sub_self _, sub_self _, by abel, by abel, by abel, by abel⟩

/-- Exact bridge decompositions splitting `crossInitialHigherPowerResolventDiff` and
`crossInitialHigherPowerIdentityDiff` into single-trajectory shift differences at `s₁`
plus unitary state differences at shift `b`. -/
theorem crossInitialHigherPowerDiff_bridge_decompositions
    (s₁ s₂ t a b : ℝ) (r : ℕ) (f₁ f₂ : Hilbert) :
    crossInitialHigherPowerResolventDiff ε hε h hh hb m g k s₁ s₂ t a b r f₁ f₂ =
      higherPowerResolventSubOfEvolvedState ε hε h hh hb m g k s₁ t a b r f₁ +
        iteratedResolventPower (RH t b) (r + 2) (U s₁ t f₁ - U s₂ t f₂) ∧
    crossInitialHigherPowerIdentityDiff ε hε h hh hb m g k s₁ s₂ t a b r f₁ f₂ =
      higherPowerIdentitySubOfEvolvedState ε hε h hh hb m g k s₁ t a b r f₁ +
        iteratedIdentityPower (RH t b) b (r + 2) (U s₁ t f₁ - U s₂ t f₂) := by
  unfold crossInitialHigherPowerResolventDiff crossInitialHigherPowerIdentityDiff
    higherPowerResolventOfEvolvedState higherPowerIdentityOfEvolvedState
    higherPowerResolventSubOfEvolvedState higherPowerIdentitySubOfEvolvedState
  rw [(iteratedResolventPower (RH t b) (r + 2)).map_sub (U s₁ t f₁) (U s₂ t f₂),
    iteratedIdentityPower_sub (RH t b) b (r + 2) (U s₁ t f₁) (U s₂ t f₂)]
  refine ⟨by abel, by abel⟩

/-- At equal initial time `s₁ = s₂ = s` and equal source `f₁ = f₂ = f`,
`crossInitialHigherPowerResolventDiff` reduces to `higherPowerResolventSubOfEvolvedState`
and lies in `hamiltonianPowerDomain t (r + 3)`. -/
theorem crossInitialHigherPowerResolventDiff_same_initial_mem_succ_power
    (s t q a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f : Hilbert) :
    crossInitialHigherPowerResolventDiff ε hε h hh hb m g k s s t a b r f f =
      higherPowerResolventSubOfEvolvedState ε hε h hh hb m g k s t a b r f ∧
    crossInitialHigherPowerResolventDiff ε hε h hh hb m g k s s t a b r f f ∈
      hamiltonianPowerDomain ε hε h hh hb m g k t (r + 3) :=
  ⟨rfl,
   (higherPowerResolventSubOfEvolvedState_mem_succ_power_and_ten_domains
     ε hε h hh hb m g k s t q a b ha hb_pos r f).1⟩

/-! ### 2. 10-Domain Regularity and Norm Bounds for Cross-Initial Higher-Power Differences -/

/-- Unconditionally for all `s₁, s₂, t, q ∈ ℝ`, `0 < a, 0 < b`, and `r : ℕ`,
`crossInitialHigherPowerResolventDiff s₁ s₂ t a b r f₁ f₂` belongs simultaneously to
`hamiltonianPowerDomain t (r + 2)`, `hamiltonianSecondPowerDomain t`, and all 10 operator,
form, and clock domains, with two-source and bridge norm bounds. -/
theorem crossInitialHigherPowerResolventDiff_mem_power_and_ten_domains
    (s₁ s₂ t q a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f₁ f₂ : Hilbert) :
    let d := crossInitialHigherPowerResolventDiff ε hε h hh hb m g k s₁ s₂ t a b r f₁ f₂
    d ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
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
    ‖d‖ ≤ (a⁻¹) ^ (r + 2) * ‖f₁‖ + (b⁻¹) ^ (r + 2) * ‖f₂‖ ∧
    ‖d‖ ≤ ((a⁻¹) ^ (r + 2) + (b⁻¹) ^ (r + 2)) * ‖f₁‖ +
      (b⁻¹) ^ (r + 2) * ‖U s₁ t f₁ - U s₂ t f₂‖ := by
  intro d
  have h1 := higherPowerResolventOfEvolvedState_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ t q a ha r f₁
  have h2 := higherPowerResolventOfEvolvedState_mem_power_and_ten_domains
    ε hε h hh hb m g k s₂ t q b hb_pos r f₂
  have hnorm1 : ‖d‖ ≤ (a⁻¹) ^ (r + 2) * ‖f₁‖ + (b⁻¹) ^ (r + 2) * ‖f₂‖ := by
    dsimp only [d, crossInitialHigherPowerResolventDiff]
    have htri := norm_sub_le
      (higherPowerResolventOfEvolvedState ε hε h hh hb m g k s₁ t a r f₁)
      (higherPowerResolventOfEvolvedState ε hε h hh hb m g k s₂ t b r f₂)
    linarith [h1.2.2.2, h2.2.2.2]
  have hnorm2 :
      ‖d‖ ≤ ((a⁻¹) ^ (r + 2) + (b⁻¹) ^ (r + 2)) * ‖f₁‖ +
        (b⁻¹) ^ (r + 2) * ‖U s₁ t f₁ - U s₂ t f₂‖ := by
    dsimp only [d]
    have hbr := (crossInitialHigherPowerDiff_bridge_decompositions
      ε hε h hh hb m g k s₁ s₂ t a b r f₁ f₂).1
    have hsub := (higherPowerResolventSubOfEvolvedState_mem_succ_power_and_ten_domains
      ε hε h hh hb m g k s₁ t q a b ha hb_pos r f₁).2.2.2
    have hres_b := iteratedResolventPower_norm_bound
      (H t) (RH t b) b hb_pos
      (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t b hb_pos)
      (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
      (r + 2) (U s₁ t f₁ - U s₂ t f₂)
    have htri := norm_add_le
      (higherPowerResolventSubOfEvolvedState ε hε h hh hb m g k s₁ t a b r f₁)
      (iteratedResolventPower (RH t b) (r + 2) (U s₁ t f₁ - U s₂ t f₂))
    rw [hbr]
    linarith
  exact ⟨(hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2)).sub_mem h1.1 h2.1,
    (hamiltonianSecondPowerDomain ε hε h hh hb m g k t).sub_mem h1.2.1 h2.2.1,
    ⟨(H t).domain.sub_mem h1.2.2.1.1 h2.2.2.1.1,
     (K).domain.sub_mem h1.2.2.1.2.1 h2.2.2.1.2.1,
     (S t).domain.sub_mem h1.2.2.1.2.2.1 h2.2.2.1.2.2.1,
     (Eavg q).domain.sub_mem h1.2.2.1.2.2.2.1 h2.2.2.1.2.2.2.1,
     (Tstat).domain.sub_mem h1.2.2.1.2.2.2.2.1 h2.2.2.1.2.2.2.2.1,
     (Kroot).domain.sub_mem h1.2.2.1.2.2.2.2.2.1 h2.2.2.1.2.2.2.2.2.1,
     (Tpot).domain.sub_mem h1.2.2.1.2.2.2.2.2.2.1 h2.2.2.1.2.2.2.2.2.2.1,
     (Tgrow).domain.sub_mem h1.2.2.1.2.2.2.2.2.2.2.1 h2.2.2.1.2.2.2.2.2.2.2.1,
     (Tres q).domain.sub_mem h1.2.2.1.2.2.2.2.2.2.2.2.1 h2.2.2.1.2.2.2.2.2.2.2.2.1,
     (clockHalf ε).domain.sub_mem h1.2.2.1.2.2.2.2.2.2.2.2.2 h2.2.2.1.2.2.2.2.2.2.2.2.2⟩,
    hnorm1, hnorm2⟩

/-- Unconditionally for all `s₁, s₂, t, q ∈ ℝ`, `0 < a, 0 < b`, and `r : ℕ`,
`crossInitialHigherPowerIdentityDiff s₁ s₂ t a b r f₁ f₂` belongs simultaneously to
`hamiltonianPowerDomain t (r + 2)`, `hamiltonianSecondPowerDomain t`, and all 10 operator,
form, and clock domains, with two-source `‖f₁‖ + ‖f₂‖` and bridge `2 * ‖f₁‖ + ‖U s₁ t f₁ - U s₂ t f₂‖`
norm bounds. -/
theorem crossInitialHigherPowerIdentityDiff_mem_power_and_ten_domains
    (s₁ s₂ t q a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f₁ f₂ : Hilbert) :
    let y := crossInitialHigherPowerIdentityDiff ε hε h hh hb m g k s₁ s₂ t a b r f₁ f₂
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
    ‖y‖ ≤ ‖f₁‖ + ‖f₂‖ ∧
    ‖y‖ ≤ 2 * ‖f₁‖ + ‖U s₁ t f₁ - U s₂ t f₂‖ := by
  intro y
  have h1 := higherPowerIdentityOfEvolvedState_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ t q a ha r f₁
  have h2 := higherPowerIdentityOfEvolvedState_mem_power_and_ten_domains
    ε hε h hh hb m g k s₂ t q b hb_pos r f₂
  have hnorm1 : ‖y‖ ≤ ‖f₁‖ + ‖f₂‖ := by
    dsimp only [y, crossInitialHigherPowerIdentityDiff]
    have htri := norm_sub_le
      (higherPowerIdentityOfEvolvedState ε hε h hh hb m g k s₁ t a r f₁)
      (higherPowerIdentityOfEvolvedState ε hε h hh hb m g k s₂ t b r f₂)
    linarith [h1.2.2.2, h2.2.2.2]
  have hnorm2 : ‖y‖ ≤ 2 * ‖f₁‖ + ‖U s₁ t f₁ - U s₂ t f₂‖ := by
    dsimp only [y]
    have hbr := (crossInitialHigherPowerDiff_bridge_decompositions
      ε hε h hh hb m g k s₁ s₂ t a b r f₁ f₂).2
    have hsub := (higherPowerIdentitySubOfEvolvedState_mem_power_and_ten_domains
      ε hε h hh hb m g k s₁ t q a b ha hb_pos r f₁).2.2.2
    have hid_b := iteratedIdentityPower_norm_le
      (H t) (RH t b) b hb_pos
      (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t b hb_pos)
      (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
      (r + 2) (U s₁ t f₁ - U s₂ t f₂)
    have htri := norm_add_le
      (higherPowerIdentitySubOfEvolvedState ε hε h hh hb m g k s₁ t a b r f₁)
      (iteratedIdentityPower (RH t b) b (r + 2) (U s₁ t f₁ - U s₂ t f₂))
    rw [hbr]
    linarith
  exact ⟨(hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2)).sub_mem h1.1 h2.1,
    (hamiltonianSecondPowerDomain ε hε h hh hb m g k t).sub_mem h1.2.1 h2.2.1,
    ⟨(H t).domain.sub_mem h1.2.2.1.1 h2.2.2.1.1,
     (K).domain.sub_mem h1.2.2.1.2.1 h2.2.2.1.2.1,
     (S t).domain.sub_mem h1.2.2.1.2.2.1 h2.2.2.1.2.2.1,
     (Eavg q).domain.sub_mem h1.2.2.1.2.2.2.1 h2.2.2.1.2.2.2.1,
     (Tstat).domain.sub_mem h1.2.2.1.2.2.2.2.1 h2.2.2.1.2.2.2.2.1,
     (Kroot).domain.sub_mem h1.2.2.1.2.2.2.2.2.1 h2.2.2.1.2.2.2.2.2.1,
     (Tpot).domain.sub_mem h1.2.2.1.2.2.2.2.2.2.1 h2.2.2.1.2.2.2.2.2.2.1,
     (Tgrow).domain.sub_mem h1.2.2.1.2.2.2.2.2.2.2.1 h2.2.2.1.2.2.2.2.2.2.2.1,
     (Tres q).domain.sub_mem h1.2.2.1.2.2.2.2.2.2.2.2.1 h2.2.2.1.2.2.2.2.2.2.2.2.1,
     (clockHalf ε).domain.sub_mem h1.2.2.1.2.2.2.2.2.2.2.2.2 h2.2.2.1.2.2.2.2.2.2.2.2.2⟩,
    hnorm1, hnorm2⟩

/-! ### 3. Cross-Final Higher-Power Differences: Cocycles, Bridge Splits, and 8-Domain Regularity -/

/-- Diagonal vanishing, skew-symmetry, three-time cocycle cancellation, and bridge decomposition
through `(t₁, b)` for `crossFinalHigherPowerResolventDiff` and `crossFinalHigherPowerIdentityDiff`. -/
theorem crossFinalHigherPowerDiff_cocycle_and_bridge
    (s t₁ t₂ t₃ a b c : ℝ) (r : ℕ) (f : Hilbert) :
    crossFinalHigherPowerResolventDiff ε hε h hh hb m g k s t₁ t₁ a a r f = 0 ∧
    crossFinalHigherPowerIdentityDiff ε hε h hh hb m g k s t₁ t₁ a a r f = 0 ∧
    crossFinalHigherPowerResolventDiff ε hε h hh hb m g k s t₂ t₁ b a r f =
      -crossFinalHigherPowerResolventDiff ε hε h hh hb m g k s t₁ t₂ a b r f ∧
    crossFinalHigherPowerResolventDiff ε hε h hh hb m g k s t₁ t₂ a b r f +
        crossFinalHigherPowerResolventDiff ε hε h hh hb m g k s t₂ t₃ b c r f =
      crossFinalHigherPowerResolventDiff ε hε h hh hb m g k s t₁ t₃ a c r f ∧
    crossFinalHigherPowerResolventDiff ε hε h hh hb m g k s t₁ t₂ a b r f =
      higherPowerResolventSubOfEvolvedState ε hε h hh hb m g k s t₁ a b r f +
        crossFinalHigherPowerResolventDiff ε hε h hh hb m g k s t₁ t₂ b b r f ∧
    crossFinalHigherPowerIdentityDiff ε hε h hh hb m g k s t₁ t₂ a b r f =
      higherPowerIdentitySubOfEvolvedState ε hε h hh hb m g k s t₁ a b r f +
        crossFinalHigherPowerIdentityDiff ε hε h hh hb m g k s t₁ t₂ b b r f := by
  unfold crossFinalHigherPowerResolventDiff crossFinalHigherPowerIdentityDiff
    higherPowerResolventSubOfEvolvedState higherPowerIdentitySubOfEvolvedState
    higherPowerResolventOfEvolvedState higherPowerIdentityOfEvolvedState
  refine ⟨sub_self _, sub_self _, by abel, by abel, by abel, by abel⟩

/-- Unconditionally for all `s, t₁, t₂, q ∈ ℝ`, `0 < a, 0 < b`, and `r : ℕ`,
`crossFinalHigherPowerResolventDiff s t₁ t₂ a b r f` belongs simultaneously to all 8
time-independent / observation-time `q` domains (`K`, `Eavg q`, `Tstat`, `Kroot`, `Tpot`,
`Tgrow`, `Tres q`, `clockHalf ε`) with geometric norm bound `((a⁻¹)^{r+2} + (b⁻¹)^{r+2}) * ‖f‖`. -/
theorem crossFinalHigherPowerResolventDiff_mem_eight_domains_and_norm_le
    (s t₁ t₂ q a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f : Hilbert) :
    let d := crossFinalHigherPowerResolventDiff ε hε h hh hb m g k s t₁ t₂ a b r f
    (d ∈ (K).domain ∧
     d ∈ (Eavg q).domain ∧
     d ∈ (Tstat).domain ∧
     d ∈ (Kroot).domain ∧
     d ∈ (Tpot).domain ∧
     d ∈ (Tgrow).domain ∧
     d ∈ (Tres q).domain ∧
     d ∈ (clockHalf ε).domain) ∧
    ‖d‖ ≤ ((a⁻¹) ^ (r + 2) + (b⁻¹) ^ (r + 2)) * ‖f‖ := by
  intro d
  have h1 := higherPowerResolventOfEvolvedState_mem_power_and_ten_domains
    ε hε h hh hb m g k s t₁ q a ha r f
  have h2 := higherPowerResolventOfEvolvedState_mem_power_and_ten_domains
    ε hε h hh hb m g k s t₂ q b hb_pos r f
  have hnorm : ‖d‖ ≤ ((a⁻¹) ^ (r + 2) + (b⁻¹) ^ (r + 2)) * ‖f‖ := by
    dsimp only [d, crossFinalHigherPowerResolventDiff]
    have htri := norm_sub_le
      (higherPowerResolventOfEvolvedState ε hε h hh hb m g k s t₁ a r f)
      (higherPowerResolventOfEvolvedState ε hε h hh hb m g k s t₂ b r f)
    linarith [h1.2.2.2, h2.2.2.2, add_mul ((a⁻¹) ^ (r + 2)) ((b⁻¹) ^ (r + 2)) ‖f‖]
  exact ⟨⟨(K).domain.sub_mem h1.2.2.1.2.1 h2.2.2.1.2.1,
    (Eavg q).domain.sub_mem h1.2.2.1.2.2.2.1 h2.2.2.1.2.2.2.1,
    (Tstat).domain.sub_mem h1.2.2.1.2.2.2.2.1 h2.2.2.1.2.2.2.2.1,
    (Kroot).domain.sub_mem h1.2.2.1.2.2.2.2.2.1 h2.2.2.1.2.2.2.2.2.1,
    (Tpot).domain.sub_mem h1.2.2.1.2.2.2.2.2.2.1 h2.2.2.1.2.2.2.2.2.2.1,
    (Tgrow).domain.sub_mem h1.2.2.1.2.2.2.2.2.2.2.1 h2.2.2.1.2.2.2.2.2.2.2.1,
    (Tres q).domain.sub_mem h1.2.2.1.2.2.2.2.2.2.2.2.1 h2.2.2.1.2.2.2.2.2.2.2.2.1,
    (clockHalf ε).domain.sub_mem h1.2.2.1.2.2.2.2.2.2.2.2.2 h2.2.2.1.2.2.2.2.2.2.2.2.2⟩,
    hnorm⟩

/-- Unconditionally for all `s, t₁, t₂, q ∈ ℝ`, `0 < a, 0 < b`, and `r : ℕ`,
`crossFinalHigherPowerIdentityDiff s t₁ t₂ a b r f` belongs simultaneously to all 8
time-independent / observation-time `q` domains with parameter-free stability `‖d‖ ≤ 2 * ‖f‖`. -/
theorem crossFinalHigherPowerIdentityDiff_mem_eight_domains_and_norm_le
    (s t₁ t₂ q a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f : Hilbert) :
    let y := crossFinalHigherPowerIdentityDiff ε hε h hh hb m g k s t₁ t₂ a b r f
    (y ∈ (K).domain ∧
     y ∈ (Eavg q).domain ∧
     y ∈ (Tstat).domain ∧
     y ∈ (Kroot).domain ∧
     y ∈ (Tpot).domain ∧
     y ∈ (Tgrow).domain ∧
     y ∈ (Tres q).domain ∧
     y ∈ (clockHalf ε).domain) ∧
    ‖y‖ ≤ 2 * ‖f‖ := by
  intro y
  have h1 := higherPowerIdentityOfEvolvedState_mem_power_and_ten_domains
    ε hε h hh hb m g k s t₁ q a ha r f
  have h2 := higherPowerIdentityOfEvolvedState_mem_power_and_ten_domains
    ε hε h hh hb m g k s t₂ q b hb_pos r f
  have hnorm : ‖y‖ ≤ 2 * ‖f‖ := by
    dsimp only [y, crossFinalHigherPowerIdentityDiff]
    have htri := norm_sub_le
      (higherPowerIdentityOfEvolvedState ε hε h hh hb m g k s t₁ a r f)
      (higherPowerIdentityOfEvolvedState ε hε h hh hb m g k s t₂ b r f)
    linarith [h1.2.2.2, h2.2.2.2]
  exact ⟨⟨(K).domain.sub_mem h1.2.2.1.2.1 h2.2.2.1.2.1,
    (Eavg q).domain.sub_mem h1.2.2.1.2.2.2.1 h2.2.2.1.2.2.2.1,
    (Tstat).domain.sub_mem h1.2.2.1.2.2.2.2.1 h2.2.2.1.2.2.2.2.1,
    (Kroot).domain.sub_mem h1.2.2.1.2.2.2.2.2.1 h2.2.2.1.2.2.2.2.2.1,
    (Tpot).domain.sub_mem h1.2.2.1.2.2.2.2.2.2.1 h2.2.2.1.2.2.2.2.2.2.1,
    (Tgrow).domain.sub_mem h1.2.2.1.2.2.2.2.2.2.2.1 h2.2.2.1.2.2.2.2.2.2.2.1,
    (Tres q).domain.sub_mem h1.2.2.1.2.2.2.2.2.2.2.2.1 h2.2.2.1.2.2.2.2.2.2.2.2.1,
    (clockHalf ε).domain.sub_mem h1.2.2.1.2.2.2.2.2.2.2.2.2 h2.2.2.1.2.2.2.2.2.2.2.2.2⟩,
    hnorm⟩

/-- Master Cross-Trajectory (`(s₁, s₂)` and `(t₁, t₂)`) and Cross-Shift (`(a, b)`)
Higher-Power Resolvent & Yosida Comparison Synthesis. -/
theorem crossTrajectory_two_time_higher_power_resolvent_comparison_master_synthesis
    (s₁ s₂ t₁ t₂ q a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r : ℕ) (f₁ f₂ : Hilbert) :
    let d_init := crossInitialHigherPowerResolventDiff ε hε h hh hb m g k s₁ s₂ t₁ a b r f₁ f₂
    let y_init := crossInitialHigherPowerIdentityDiff ε hε h hh hb m g k s₁ s₂ t₁ a b r f₁ f₂
    let d_fin := crossFinalHigherPowerResolventDiff ε hε h hh hb m g k s₁ t₁ t₂ a b r f₁
    let y_fin := crossFinalHigherPowerIdentityDiff ε hε h hh hb m g k s₁ t₁ t₂ a b r f₁
    (d_init ∈ hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2) ∧
     d_init ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t₁ ∧
     y_init ∈ hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2) ∧
     y_init ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t₁) ∧
    (‖d_init‖ ≤ ((a⁻¹) ^ (r + 2) + (b⁻¹) ^ (r + 2)) * ‖f₁‖ +
       (b⁻¹) ^ (r + 2) * ‖U s₁ t₁ f₁ - U s₂ t₁ f₂‖ ∧
     ‖y_init‖ ≤ 2 * ‖f₁‖ + ‖U s₁ t₁ f₁ - U s₂ t₁ f₂‖) ∧
    ((d_fin ∈ (K).domain ∧
      d_fin ∈ (Eavg q).domain ∧
      d_fin ∈ (Tstat).domain ∧
      d_fin ∈ (Kroot).domain ∧
      d_fin ∈ (Tpot).domain ∧
      d_fin ∈ (Tgrow).domain ∧
      d_fin ∈ (Tres q).domain ∧
      d_fin ∈ (clockHalf ε).domain) ∧
     ‖d_fin‖ ≤ ((a⁻¹) ^ (r + 2) + (b⁻¹) ^ (r + 2)) * ‖f₁‖) ∧
    ((y_fin ∈ (K).domain ∧
      y_fin ∈ (Eavg q).domain ∧
      y_fin ∈ (Tstat).domain ∧
      y_fin ∈ (Kroot).domain ∧
      y_fin ∈ (Tpot).domain ∧
      y_fin ∈ (Tgrow).domain ∧
      y_fin ∈ (Tres q).domain ∧
      y_fin ∈ (clockHalf ε).domain) ∧
     ‖y_fin‖ ≤ 2 * ‖f₁‖) := by
  intro d_init y_init d_fin y_fin
  have hci_res := crossInitialHigherPowerResolventDiff_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ t₁ q a b ha hb_pos r f₁ f₂
  have hci_id := crossInitialHigherPowerIdentityDiff_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ t₁ q a b ha hb_pos r f₁ f₂
  have hcf_res := crossFinalHigherPowerResolventDiff_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ t₁ t₂ q a b ha hb_pos r f₁
  have hcf_id := crossFinalHigherPowerIdentityDiff_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ t₁ t₂ q a b ha hb_pos r f₁
  exact ⟨⟨hci_res.1, hci_res.2.1, hci_id.1, hci_id.2.1⟩,
    ⟨hci_res.2.2.2.2, hci_id.2.2.2.2⟩,
    hcf_res, hcf_id⟩

#print axioms crossInitialHigherPowerDiff_cocycle_identities
#print axioms crossInitialHigherPowerDiff_bridge_decompositions
#print axioms crossInitialHigherPowerResolventDiff_same_initial_mem_succ_power
#print axioms crossInitialHigherPowerResolventDiff_mem_power_and_ten_domains
#print axioms crossInitialHigherPowerIdentityDiff_mem_power_and_ten_domains
#print axioms crossFinalHigherPowerDiff_cocycle_and_bridge
#print axioms crossFinalHigherPowerResolventDiff_mem_eight_domains_and_norm_le
#print axioms crossFinalHigherPowerIdentityDiff_mem_eight_domains_and_norm_le
#print axioms crossTrajectory_two_time_higher_power_resolvent_comparison_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorTwoTimeCrossTrajectoryHigherPowerResolventComparison
