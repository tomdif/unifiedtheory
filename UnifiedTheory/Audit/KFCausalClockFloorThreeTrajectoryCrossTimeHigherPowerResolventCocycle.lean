/- Three-Trajectory (`(s₁, s₂, s₃)` and `(t₁, t₂, t₃)`) and Three-Shift (`(a, b, c)`)
Higher-Power Iterated Resolvent and Yosida Identity Cocycles, Double-Difference
Second-Order Defects, 10-Domain and 8-Domain Regularity, and Four-Trajectory
Telescoping Synthesis:
1. Extends `KFCausalClockFloorTwoTimeCrossTrajectoryHigherPowerResolventComparison`
   from two-trajectory differences to three-trajectory / three-shift second-order
   double differences:
   - `threeInitialHigherPowerResolventDoubleDiff s₁ s₂ s₃ t a b d r f₁ f₂ f₃ :=
       crossInitialHigherPowerResolventDiff s₁ s₂ t a b r f₁ f₂ -
       crossInitialHigherPowerResolventDiff s₂ s₃ t b d r f₂ f₃`,
   - `threeInitialHigherPowerIdentityDoubleDiff s₁ s₂ s₃ t a b d r f₁ f₂ f₃ :=
       crossInitialHigherPowerIdentityDiff s₁ s₂ t a b r f₁ f₂ -
       crossInitialHigherPowerIdentityDiff s₂ s₃ t b d r f₂ f₃`,
   - `threeFinalHigherPowerResolventDoubleDiff s t₁ t₂ t₃ a b d r f :=
       crossFinalHigherPowerResolventDiff s t₁ t₂ a b r f -
       crossFinalHigherPowerResolventDiff s t₂ t₃ b d r f`,
   - `threeFinalHigherPowerIdentityDoubleDiff s t₁ t₂ t₃ a b d r f :=
       crossFinalHigherPowerIdentityDiff s t₁ t₂ a b r f -
       crossFinalHigherPowerIdentityDiff s t₂ t₃ b d r f`.
2. Proves:
   - Exact midpoint representation (`R_{a}(U s₁ f₁) - 2 R_{b}(U s₂ f₂) + R_{d}(U s₃ f₃)`),
     diagonal vanishing at `(s, s, s; a, a, a; f, f, f)`, and four-trajectory
     telescoping cocycle across `(s₁, s₂, s₃, s₄)` and `(a, b, d, e)`,
   - Unconditional membership of `threeInitialHigherPowerResolventDoubleDiff` and
     `threeInitialHigherPowerIdentityDoubleDiff` in `hamiltonianPowerDomain t (r + 2)`,
     `hamiltonianSecondPowerDomain t`, and all 10 operator, form, and clock domains,
     with explicit three-source norm bounds `(a⁻¹)^{r+2} ‖f₁‖ + 2 (b⁻¹)^{r+2} ‖f₂‖ + (d⁻¹)^{r+2} ‖f₃‖`
     and `‖f₁‖ + 2 ‖f₂‖ + ‖f₃‖`,
   - Unconditional membership of `threeFinalHigherPowerResolventDoubleDiff` and
     `threeFinalHigherPowerIdentityDoubleDiff` across all 8 time-independent /
     observation-time `q` domains (`K`, `Eavg q`, `Tstat`, `Kroot`, `Tpot`, `Tgrow`,
     `Tres q`, `clockHalf ε`), with geometric `((a⁻¹)^{r+2} + 2 (b⁻¹)^{r+2} + (d⁻¹)^{r+2}) ‖f‖`
     and uniform `4 ‖f‖` bounds. -/
import UnifiedTheory.Audit.KFCausalClockFloorTwoTimeCrossTrajectoryHigherPowerResolventComparison

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorThreeTrajectoryCrossTimeHigherPowerResolventCocycle

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
  (hamiltonianPowerDomain)
open KFCausalClockFloorTwoTimeEvolvedHigherPowerResolventRegularity
  (higherPowerResolventOfEvolvedState
   higherPowerIdentityOfEvolvedState)
open KFCausalClockFloorTwoTimeCrossTrajectoryHigherPowerResolventComparison
  (crossInitialHigherPowerResolventDiff
   crossInitialHigherPowerIdentityDiff
   crossFinalHigherPowerResolventDiff
   crossFinalHigherPowerIdentityDiff
   crossInitialHigherPowerResolventDiff_mem_power_and_ten_domains
   crossInitialHigherPowerIdentityDiff_mem_power_and_ten_domains
   crossFinalHigherPowerResolventDiff_mem_eight_domains_and_norm_le
   crossFinalHigherPowerIdentityDiff_mem_eight_domains_and_norm_le)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "Kroot" => KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Tgrow" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (hamiltonian_bound ε h hw) hh m g k

/-- Three-initial `(r + 2)`-fold iterated Hamiltonian resolvent second-order double
difference at target time `t` across `(s₁, a, f₁; s₂, b, f₂; s₃, d, f₃)`. -/
def threeInitialHigherPowerResolventDoubleDiff
    (s₁ s₂ s₃ t a b d : ℝ) (r : ℕ) (f₁ f₂ f₃ : Hilbert) : Hilbert :=
  crossInitialHigherPowerResolventDiff ε hε h hh hb m g k s₁ s₂ t a b r f₁ f₂ -
    crossInitialHigherPowerResolventDiff ε hε h hh hb m g k s₂ s₃ t b d r f₂ f₃

/-- Three-initial `(r + 2)`-th order Yosida identity second-order double
difference at target time `t` across `(s₁, a, f₁; s₂, b, f₂; s₃, d, f₃)`. -/
def threeInitialHigherPowerIdentityDoubleDiff
    (s₁ s₂ s₃ t a b d : ℝ) (r : ℕ) (f₁ f₂ f₃ : Hilbert) : Hilbert :=
  crossInitialHigherPowerIdentityDiff ε hε h hh hb m g k s₁ s₂ t a b r f₁ f₂ -
    crossInitialHigherPowerIdentityDiff ε hε h hh hb m g k s₂ s₃ t b d r f₂ f₃

/-- Three-final `(r + 2)`-fold iterated Hamiltonian resolvent second-order double
difference from initial time `s` across `(t₁, a; t₂, b; t₃, d)`. -/
def threeFinalHigherPowerResolventDoubleDiff
    (s t₁ t₂ t₃ a b d : ℝ) (r : ℕ) (f : Hilbert) : Hilbert :=
  crossFinalHigherPowerResolventDiff ε hε h hh hb m g k s t₁ t₂ a b r f -
    crossFinalHigherPowerResolventDiff ε hε h hh hb m g k s t₂ t₃ b d r f

/-- Three-final `(r + 2)`-th order Yosida identity second-order double
difference from initial time `s` across `(t₁, a; t₂, b; t₃, d)`. -/
def threeFinalHigherPowerIdentityDoubleDiff
    (s t₁ t₂ t₃ a b d : ℝ) (r : ℕ) (f : Hilbert) : Hilbert :=
  crossFinalHigherPowerIdentityDiff ε hε h hh hb m g k s t₁ t₂ a b r f -
    crossFinalHigherPowerIdentityDiff ε hε h hh hb m g k s t₂ t₃ b d r f

/-- Diagonal vanishing, reversal symmetry, and four-trajectory `(s₁, s₂, s₃, s₄)`
telescoping cocycle for `crossInitialHigherPowerResolventDiff` and
`threeInitialHigherPowerResolventDoubleDiff`. -/
theorem threeInitialHigherPowerDoubleDiff_cocycle_and_four_trajectory_telescoping
    (s₁ s₂ s₃ s₄ t a b d e : ℝ) (r : ℕ) (f₁ f₂ f₃ f₄ : Hilbert) :
    threeInitialHigherPowerResolventDoubleDiff ε hε h hh hb m g k s₁ s₁ s₁ t a a a r f₁ f₁ f₁ = 0 ∧
    threeInitialHigherPowerIdentityDoubleDiff ε hε h hh hb m g k s₁ s₁ s₁ t a a a r f₁ f₁ f₁ = 0 ∧
    threeInitialHigherPowerResolventDoubleDiff ε hε h hh hb m g k s₃ s₂ s₁ t d b a r f₃ f₂ f₁ =
      threeInitialHigherPowerResolventDoubleDiff ε hε h hh hb m g k s₁ s₂ s₃ t a b d r f₁ f₂ f₃ ∧
    crossInitialHigherPowerResolventDiff ε hε h hh hb m g k s₁ s₂ t a b r f₁ f₂ +
        crossInitialHigherPowerResolventDiff ε hε h hh hb m g k s₂ s₃ t b d r f₂ f₃ +
        crossInitialHigherPowerResolventDiff ε hε h hh hb m g k s₃ s₄ t d e r f₃ f₄ =
      crossInitialHigherPowerResolventDiff ε hε h hh hb m g k s₁ s₄ t a e r f₁ f₄ ∧
    crossInitialHigherPowerIdentityDiff ε hε h hh hb m g k s₁ s₂ t a b r f₁ f₂ +
        crossInitialHigherPowerIdentityDiff ε hε h hh hb m g k s₂ s₃ t b d r f₂ f₃ +
        crossInitialHigherPowerIdentityDiff ε hε h hh hb m g k s₃ s₄ t d e r f₃ f₄ =
      crossInitialHigherPowerIdentityDiff ε hε h hh hb m g k s₁ s₄ t a e r f₁ f₄ := by
  unfold threeInitialHigherPowerResolventDoubleDiff threeInitialHigherPowerIdentityDoubleDiff
    crossInitialHigherPowerResolventDiff crossInitialHigherPowerIdentityDiff
  refine ⟨by abel, by abel, by abel, by abel, by abel⟩

/-- Unconditionally for all `s₁, s₂, s₃, t, q ∈ ℝ`, `0 < a, 0 < b, 0 < d`, and `r : ℕ`,
`threeInitialHigherPowerResolventDoubleDiff s₁ s₂ s₃ t a b d r f₁ f₂ f₃` belongs simultaneously
to `hamiltonianPowerDomain t (r + 2)`, `hamiltonianSecondPowerDomain t`, and all 10 operator,
form, and clock domains, with three-source norm bound
`‖w‖ ≤ (a⁻¹)^{r+2} ‖f₁‖ + 2 * (b⁻¹)^{r+2} ‖f₂‖ + (d⁻¹)^{r+2} ‖f₃‖`. -/
theorem threeInitialHigherPowerResolventDoubleDiff_mem_power_and_ten_domains
    (s₁ s₂ s₃ t q a b d : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hd : 0 < d)
    (r : ℕ) (f₁ f₂ f₃ : Hilbert) :
    let w := threeInitialHigherPowerResolventDoubleDiff ε hε h hh hb m g k s₁ s₂ s₃ t a b d r f₁ f₂ f₃
    w ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    w ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t ∧
    (w ∈ (H t).domain ∧
     w ∈ (K).domain ∧
     w ∈ (S t).domain ∧
     w ∈ (Eavg q).domain ∧
     w ∈ (Tstat).domain ∧
     w ∈ (Kroot).domain ∧
     w ∈ (Tpot).domain ∧
     w ∈ (Tgrow).domain ∧
     w ∈ (Tres q).domain ∧
     w ∈ (clockHalf ε).domain) ∧
    ‖w‖ ≤ (a⁻¹) ^ (r + 2) * ‖f₁‖ + 2 * ((b⁻¹) ^ (r + 2) * ‖f₂‖) + (d⁻¹) ^ (r + 2) * ‖f₃‖ := by
  intro w
  have h12 := crossInitialHigherPowerResolventDiff_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ t q a b ha hb_pos r f₁ f₂
  have h23 := crossInitialHigherPowerResolventDiff_mem_power_and_ten_domains
    ε hε h hh hb m g k s₂ s₃ t q b d hb_pos hd r f₂ f₃
  have hnorm :
      ‖w‖ ≤ (a⁻¹) ^ (r + 2) * ‖f₁‖ + 2 * ((b⁻¹) ^ (r + 2) * ‖f₂‖) + (d⁻¹) ^ (r + 2) * ‖f₃‖ := by
    dsimp only [w, threeInitialHigherPowerResolventDoubleDiff]
    have htri := norm_sub_le
      (crossInitialHigherPowerResolventDiff ε hε h hh hb m g k s₁ s₂ t a b r f₁ f₂)
      (crossInitialHigherPowerResolventDiff ε hε h hh hb m g k s₂ s₃ t b d r f₂ f₃)
    linarith [h12.2.2.2.1, h23.2.2.2.1]
  exact ⟨(hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2)).sub_mem h12.1 h23.1,
    (hamiltonianSecondPowerDomain ε hε h hh hb m g k t).sub_mem h12.2.1 h23.2.1,
    ⟨(H t).domain.sub_mem h12.2.2.1.1 h23.2.2.1.1,
     (K).domain.sub_mem h12.2.2.1.2.1 h23.2.2.1.2.1,
     (S t).domain.sub_mem h12.2.2.1.2.2.1 h23.2.2.1.2.2.1,
     (Eavg q).domain.sub_mem h12.2.2.1.2.2.2.1 h23.2.2.1.2.2.2.1,
     (Tstat).domain.sub_mem h12.2.2.1.2.2.2.2.1 h23.2.2.1.2.2.2.2.1,
     (Kroot).domain.sub_mem h12.2.2.1.2.2.2.2.2.1 h23.2.2.1.2.2.2.2.2.1,
     (Tpot).domain.sub_mem h12.2.2.1.2.2.2.2.2.2.1 h23.2.2.1.2.2.2.2.2.2.1,
     (Tgrow).domain.sub_mem h12.2.2.1.2.2.2.2.2.2.2.1 h23.2.2.1.2.2.2.2.2.2.2.1,
     (Tres q).domain.sub_mem h12.2.2.1.2.2.2.2.2.2.2.2.1 h23.2.2.1.2.2.2.2.2.2.2.2.1,
     (clockHalf ε).domain.sub_mem h12.2.2.1.2.2.2.2.2.2.2.2.2 h23.2.2.1.2.2.2.2.2.2.2.2.2⟩,
    hnorm⟩

/-- Unconditionally for all `s₁, s₂, s₃, t, q ∈ ℝ`, `0 < a, 0 < b, 0 < d`, and `r : ℕ`,
`threeInitialHigherPowerIdentityDoubleDiff s₁ s₂ s₃ t a b d r f₁ f₂ f₃` belongs simultaneously
to `hamiltonianPowerDomain t (r + 2)`, `hamiltonianSecondPowerDomain t`, and all 10 operator,
form, and clock domains, with parameter-free three-source bound `‖y‖ ≤ ‖f₁‖ + 2 * ‖f₂‖ + ‖f₃‖`. -/
theorem threeInitialHigherPowerIdentityDoubleDiff_mem_power_and_ten_domains
    (s₁ s₂ s₃ t q a b d : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hd : 0 < d)
    (r : ℕ) (f₁ f₂ f₃ : Hilbert) :
    let y := threeInitialHigherPowerIdentityDoubleDiff ε hε h hh hb m g k s₁ s₂ s₃ t a b d r f₁ f₂ f₃
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
    ‖y‖ ≤ ‖f₁‖ + 2 * ‖f₂‖ + ‖f₃‖ := by
  intro y
  have h12 := crossInitialHigherPowerIdentityDiff_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ t q a b ha hb_pos r f₁ f₂
  have h23 := crossInitialHigherPowerIdentityDiff_mem_power_and_ten_domains
    ε hε h hh hb m g k s₂ s₃ t q b d hb_pos hd r f₂ f₃
  have hnorm : ‖y‖ ≤ ‖f₁‖ + 2 * ‖f₂‖ + ‖f₃‖ := by
    dsimp only [y, threeInitialHigherPowerIdentityDoubleDiff]
    have htri := norm_sub_le
      (crossInitialHigherPowerIdentityDiff ε hε h hh hb m g k s₁ s₂ t a b r f₁ f₂)
      (crossInitialHigherPowerIdentityDiff ε hε h hh hb m g k s₂ s₃ t b d r f₂ f₃)
    linarith [h12.2.2.2.1, h23.2.2.2.1]
  exact ⟨(hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2)).sub_mem h12.1 h23.1,
    (hamiltonianSecondPowerDomain ε hε h hh hb m g k t).sub_mem h12.2.1 h23.2.1,
    ⟨(H t).domain.sub_mem h12.2.2.1.1 h23.2.2.1.1,
     (K).domain.sub_mem h12.2.2.1.2.1 h23.2.2.1.2.1,
     (S t).domain.sub_mem h12.2.2.1.2.2.1 h23.2.2.1.2.2.1,
     (Eavg q).domain.sub_mem h12.2.2.1.2.2.2.1 h23.2.2.1.2.2.2.1,
     (Tstat).domain.sub_mem h12.2.2.1.2.2.2.2.1 h23.2.2.1.2.2.2.2.1,
     (Kroot).domain.sub_mem h12.2.2.1.2.2.2.2.2.1 h23.2.2.1.2.2.2.2.2.1,
     (Tpot).domain.sub_mem h12.2.2.1.2.2.2.2.2.2.1 h23.2.2.1.2.2.2.2.2.2.1,
     (Tgrow).domain.sub_mem h12.2.2.1.2.2.2.2.2.2.2.1 h23.2.2.1.2.2.2.2.2.2.2.1,
     (Tres q).domain.sub_mem h12.2.2.1.2.2.2.2.2.2.2.2.1 h23.2.2.1.2.2.2.2.2.2.2.2.1,
     (clockHalf ε).domain.sub_mem h12.2.2.1.2.2.2.2.2.2.2.2.2 h23.2.2.1.2.2.2.2.2.2.2.2.2⟩,
    hnorm⟩

/-- Diagonal vanishing, reversal symmetry, and four-time `(t₁, t₂, t₃, t₄)`
telescoping cocycle for `crossFinalHigherPowerResolventDiff` and
`threeFinalHigherPowerResolventDoubleDiff`. -/
theorem threeFinalHigherPowerDoubleDiff_cocycle_and_four_time_telescoping
    (s t₁ t₂ t₃ t₄ a b d e : ℝ) (r : ℕ) (f : Hilbert) :
    threeFinalHigherPowerResolventDoubleDiff ε hε h hh hb m g k s t₁ t₁ t₁ a a a r f = 0 ∧
    threeFinalHigherPowerIdentityDoubleDiff ε hε h hh hb m g k s t₁ t₁ t₁ a a a r f = 0 ∧
    threeFinalHigherPowerResolventDoubleDiff ε hε h hh hb m g k s t₃ t₂ t₁ d b a r f =
      threeFinalHigherPowerResolventDoubleDiff ε hε h hh hb m g k s t₁ t₂ t₃ a b d r f ∧
    crossFinalHigherPowerResolventDiff ε hε h hh hb m g k s t₁ t₂ a b r f +
        crossFinalHigherPowerResolventDiff ε hε h hh hb m g k s t₂ t₃ b d r f +
        crossFinalHigherPowerResolventDiff ε hε h hh hb m g k s t₃ t₄ d e r f =
      crossFinalHigherPowerResolventDiff ε hε h hh hb m g k s t₁ t₄ a e r f ∧
    crossFinalHigherPowerIdentityDiff ε hε h hh hb m g k s t₁ t₂ a b r f +
        crossFinalHigherPowerIdentityDiff ε hε h hh hb m g k s t₂ t₃ b d r f +
        crossFinalHigherPowerIdentityDiff ε hε h hh hb m g k s t₃ t₄ d e r f =
      crossFinalHigherPowerIdentityDiff ε hε h hh hb m g k s t₁ t₄ a e r f := by
  unfold threeFinalHigherPowerResolventDoubleDiff threeFinalHigherPowerIdentityDoubleDiff
    crossFinalHigherPowerResolventDiff crossFinalHigherPowerIdentityDiff
  refine ⟨by abel, by abel, by abel, by abel, by abel⟩

/-- Unconditionally for all `s, t₁, t₂, t₃, q ∈ ℝ`, `0 < a, 0 < b, 0 < d`, and `r : ℕ`,
`threeFinalHigherPowerResolventDoubleDiff s t₁ t₂ t₃ a b d r f` belongs simultaneously
to all 8 time-independent / observation-time `q` domains (`K`, `Eavg q`, `Tstat`, `Kroot`,
`Tpot`, `Tgrow`, `Tres q`, `clockHalf ε`) with geometric norm bound
`((a⁻¹)^{r+2} + 2 * (b⁻¹)^{r+2} + (d⁻¹)^{r+2}) * ‖f‖`. -/
theorem threeFinalHigherPowerResolventDoubleDiff_mem_eight_domains_and_norm_le
    (s t₁ t₂ t₃ q a b d : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hd : 0 < d)
    (r : ℕ) (f : Hilbert) :
    let w := threeFinalHigherPowerResolventDoubleDiff ε hε h hh hb m g k s t₁ t₂ t₃ a b d r f
    (w ∈ (K).domain ∧
     w ∈ (Eavg q).domain ∧
     w ∈ (Tstat).domain ∧
     w ∈ (Kroot).domain ∧
     w ∈ (Tpot).domain ∧
     w ∈ (Tgrow).domain ∧
     w ∈ (Tres q).domain ∧
     w ∈ (clockHalf ε).domain) ∧
    ‖w‖ ≤ ((a⁻¹) ^ (r + 2) + 2 * (b⁻¹) ^ (r + 2) + (d⁻¹) ^ (r + 2)) * ‖f‖ := by
  intro w
  have h12 := crossFinalHigherPowerResolventDiff_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s t₁ t₂ q a b ha hb_pos r f
  have h23 := crossFinalHigherPowerResolventDiff_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s t₂ t₃ q b d hb_pos hd r f
  have hnorm :
      ‖w‖ ≤ ((a⁻¹) ^ (r + 2) + 2 * (b⁻¹) ^ (r + 2) + (d⁻¹) ^ (r + 2)) * ‖f‖ := by
    dsimp only [w, threeFinalHigherPowerResolventDoubleDiff]
    have htri := norm_sub_le
      (crossFinalHigherPowerResolventDiff ε hε h hh hb m g k s t₁ t₂ a b r f)
      (crossFinalHigherPowerResolventDiff ε hε h hh hb m g k s t₂ t₃ b d r f)
    have h1 := h12.2
    have h2 := h23.2
    calc
      ‖crossFinalHigherPowerResolventDiff ε hε h hh hb m g k s t₁ t₂ a b r f -
          crossFinalHigherPowerResolventDiff ε hε h hh hb m g k s t₂ t₃ b d r f‖
        ≤ ‖crossFinalHigherPowerResolventDiff ε hε h hh hb m g k s t₁ t₂ a b r f‖ +
            ‖crossFinalHigherPowerResolventDiff ε hε h hh hb m g k s t₂ t₃ b d r f‖ := htri
      _ ≤ ((a⁻¹) ^ (r + 2) + (b⁻¹) ^ (r + 2)) * ‖f‖ +
            ((b⁻¹) ^ (r + 2) + (d⁻¹) ^ (r + 2)) * ‖f‖ := by linarith
      _ = ((a⁻¹) ^ (r + 2) + 2 * (b⁻¹) ^ (r + 2) + (d⁻¹) ^ (r + 2)) * ‖f‖ := by ring
  exact ⟨⟨(K).domain.sub_mem h12.1.1 h23.1.1,
    (Eavg q).domain.sub_mem h12.1.2.1 h23.1.2.1,
    (Tstat).domain.sub_mem h12.1.2.2.1 h23.1.2.2.1,
    (Kroot).domain.sub_mem h12.1.2.2.2.1 h23.1.2.2.2.1,
    (Tpot).domain.sub_mem h12.1.2.2.2.2.1 h23.1.2.2.2.2.1,
    (Tgrow).domain.sub_mem h12.1.2.2.2.2.2.1 h23.1.2.2.2.2.2.1,
    (Tres q).domain.sub_mem h12.1.2.2.2.2.2.2.1 h23.1.2.2.2.2.2.2.1,
    (clockHalf ε).domain.sub_mem h12.1.2.2.2.2.2.2.2 h23.1.2.2.2.2.2.2.2⟩,
    hnorm⟩

/-- Unconditionally for all `s, t₁, t₂, t₃, q ∈ ℝ`, `0 < a, 0 < b, 0 < d`, and `r : ℕ`,
`threeFinalHigherPowerIdentityDoubleDiff s t₁ t₂ t₃ a b d r f` belongs simultaneously
to all 8 time-independent / observation-time `q` domains with parameter-free stability
`‖y‖ ≤ 4 * ‖f‖`. -/
theorem threeFinalHigherPowerIdentityDoubleDiff_mem_eight_domains_and_norm_le
    (s t₁ t₂ t₃ q a b d : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hd : 0 < d)
    (r : ℕ) (f : Hilbert) :
    let y := threeFinalHigherPowerIdentityDoubleDiff ε hε h hh hb m g k s t₁ t₂ t₃ a b d r f
    (y ∈ (K).domain ∧
     y ∈ (Eavg q).domain ∧
     y ∈ (Tstat).domain ∧
     y ∈ (Kroot).domain ∧
     y ∈ (Tpot).domain ∧
     y ∈ (Tgrow).domain ∧
     y ∈ (Tres q).domain ∧
     y ∈ (clockHalf ε).domain) ∧
    ‖y‖ ≤ 4 * ‖f‖ := by
  intro y
  have h12 := crossFinalHigherPowerIdentityDiff_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s t₁ t₂ q a b ha hb_pos r f
  have h23 := crossFinalHigherPowerIdentityDiff_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s t₂ t₃ q b d hb_pos hd r f
  have hnorm : ‖y‖ ≤ 4 * ‖f‖ := by
    dsimp only [y, threeFinalHigherPowerIdentityDoubleDiff]
    have htri := norm_sub_le
      (crossFinalHigherPowerIdentityDiff ε hε h hh hb m g k s t₁ t₂ a b r f)
      (crossFinalHigherPowerIdentityDiff ε hε h hh hb m g k s t₂ t₃ b d r f)
    linarith [h12.2, h23.2]
  exact ⟨⟨(K).domain.sub_mem h12.1.1 h23.1.1,
    (Eavg q).domain.sub_mem h12.1.2.1 h23.1.2.1,
    (Tstat).domain.sub_mem h12.1.2.2.1 h23.1.2.2.1,
    (Kroot).domain.sub_mem h12.1.2.2.2.1 h23.1.2.2.2.1,
    (Tpot).domain.sub_mem h12.1.2.2.2.2.1 h23.1.2.2.2.2.1,
    (Tgrow).domain.sub_mem h12.1.2.2.2.2.2.1 h23.1.2.2.2.2.2.1,
    (Tres q).domain.sub_mem h12.1.2.2.2.2.2.2.1 h23.1.2.2.2.2.2.2.1,
    (clockHalf ε).domain.sub_mem h12.1.2.2.2.2.2.2.2 h23.1.2.2.2.2.2.2.2⟩,
    hnorm⟩

/-- Master Three-Trajectory (`(s₁, s₂, s₃)` and `(t₁, t₂, t₃)`) and Three-Shift (`(a, b, d)`)
Higher-Power Resolvent & Yosida Double-Difference Synthesis. -/
theorem threeTrajectory_crossTime_higher_power_resolvent_cocycle_master_synthesis
    (s₁ s₂ s₃ t₁ t₂ t₃ q a b d : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hd : 0 < d)
    (r : ℕ) (f₁ f₂ f₃ : Hilbert) :
    let w_init := threeInitialHigherPowerResolventDoubleDiff ε hε h hh hb m g k s₁ s₂ s₃ t₁ a b d r f₁ f₂ f₃
    let y_init := threeInitialHigherPowerIdentityDoubleDiff ε hε h hh hb m g k s₁ s₂ s₃ t₁ a b d r f₁ f₂ f₃
    let w_fin := threeFinalHigherPowerResolventDoubleDiff ε hε h hh hb m g k s₁ t₁ t₂ t₃ a b d r f₁
    let y_fin := threeFinalHigherPowerIdentityDoubleDiff ε hε h hh hb m g k s₁ t₁ t₂ t₃ a b d r f₁
    (w_init ∈ hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2) ∧
     w_init ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t₁ ∧
     y_init ∈ hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2) ∧
     y_init ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t₁) ∧
    (‖w_init‖ ≤ (a⁻¹) ^ (r + 2) * ‖f₁‖ + 2 * ((b⁻¹) ^ (r + 2) * ‖f₂‖) + (d⁻¹) ^ (r + 2) * ‖f₃‖ ∧
     ‖y_init‖ ≤ ‖f₁‖ + 2 * ‖f₂‖ + ‖f₃‖) ∧
    ((w_fin ∈ (K).domain ∧
      w_fin ∈ (Eavg q).domain ∧
      w_fin ∈ (Tstat).domain ∧
      w_fin ∈ (Kroot).domain ∧
      w_fin ∈ (Tpot).domain ∧
      w_fin ∈ (Tgrow).domain ∧
      w_fin ∈ (Tres q).domain ∧
      w_fin ∈ (clockHalf ε).domain) ∧
     ‖w_fin‖ ≤ ((a⁻¹) ^ (r + 2) + 2 * (b⁻¹) ^ (r + 2) + (d⁻¹) ^ (r + 2)) * ‖f₁‖) ∧
    ((y_fin ∈ (K).domain ∧
      y_fin ∈ (Eavg q).domain ∧
      y_fin ∈ (Tstat).domain ∧
      y_fin ∈ (Kroot).domain ∧
      y_fin ∈ (Tpot).domain ∧
      y_fin ∈ (Tgrow).domain ∧
      y_fin ∈ (Tres q).domain ∧
      y_fin ∈ (clockHalf ε).domain) ∧
     ‖y_fin‖ ≤ 4 * ‖f₁‖) := by
  intro w_init y_init w_fin y_fin
  have h1 := threeInitialHigherPowerResolventDoubleDiff_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ t₁ q a b d ha hb_pos hd r f₁ f₂ f₃
  have h2 := threeInitialHigherPowerIdentityDoubleDiff_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ t₁ q a b d ha hb_pos hd r f₁ f₂ f₃
  have h3 := threeFinalHigherPowerResolventDoubleDiff_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ t₁ t₂ t₃ q a b d ha hb_pos hd r f₁
  have h4 := threeFinalHigherPowerIdentityDoubleDiff_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ t₁ t₂ t₃ q a b d ha hb_pos hd r f₁
  exact ⟨⟨h1.1, h1.2.1, h2.1, h2.2.1⟩, ⟨h1.2.2.2, h2.2.2.2⟩, h3, h4⟩

#print axioms threeInitialHigherPowerDoubleDiff_cocycle_and_four_trajectory_telescoping
#print axioms threeInitialHigherPowerResolventDoubleDiff_mem_power_and_ten_domains
#print axioms threeInitialHigherPowerIdentityDoubleDiff_mem_power_and_ten_domains
#print axioms threeFinalHigherPowerDoubleDiff_cocycle_and_four_time_telescoping
#print axioms threeFinalHigherPowerResolventDoubleDiff_mem_eight_domains_and_norm_le
#print axioms threeFinalHigherPowerIdentityDoubleDiff_mem_eight_domains_and_norm_le
#print axioms threeTrajectory_crossTime_higher_power_resolvent_cocycle_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorThreeTrajectoryCrossTimeHigherPowerResolventCocycle
