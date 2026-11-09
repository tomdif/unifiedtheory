/- Four-by-Four `(s₁, s₂, s₃, s₄) × (t₁, t₂, t₃, t₄)` (`3 × 3 = 9` Elementary Plaquettes)
Mixed Initial-and-Final Higher-Power Iterated Resolvent and Yosida Identity Plaquette Grid,
Exact 2D Stokes / Green Plaquette Boundary Cancellation Across Nine Interior Cells,
Cyclic Four-Step Plaquette Quadrangle Cocycles, and 8-Domain / Equal-Final-Time 10-Domain
Regularity. -/
import UnifiedTheory.Audit.KFCausalClockFloorThreeByThreeMixedInitialFinalHigherPowerResolventPlaquetteGrid

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorFourByFourMixedInitialFinalHigherPowerResolventPlaquetteGrid

noncomputable section

open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorIteratedResolventSecondPowerCore
  (hamiltonianSecondPowerDomain)
open KFCausalClockFloorHigherPowerOperatorCores
  (hamiltonianPowerDomain)
open KFCausalClockFloorTwoTimeCrossTrajectoryHigherPowerResolventComparison
  (crossInitialHigherPowerResolventDiff
   crossInitialHigherPowerIdentityDiff
   crossFinalHigherPowerResolventDiff
   crossFinalHigherPowerIdentityDiff)
open UnifiedTheory.Audit.KFCausalClockFloorTwoTimeMixedInitialFinalHigherPowerResolventPlaquette
  (mixedInitialFinalHigherPowerResolventPlaquette
   mixedInitialFinalHigherPowerIdentityPlaquette
   mixedInitialFinalHigherPowerResolventPlaquette_mem_eight_domains_and_norm_le
   mixedInitialFinalHigherPowerIdentityPlaquette_mem_eight_domains_and_norm_le
   mixedInitialFinalHigherPowerResolventPlaquette_equal_final_time_mem_power_and_ten_domains
   mixedInitialFinalHigherPowerIdentityPlaquette_equal_final_time_mem_power_and_ten_domains)
open UnifiedTheory.Audit.KFCausalClockFloorThreeByThreeMixedInitialFinalHigherPowerResolventPlaquetteGrid
  (twoByTwoResolventPlaquetteGridSum
   twoByTwoIdentityPlaquetteGridSum
   twoByTwoPlaquetteGridSum_stokes_boundary_cancellation)

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

/-- Sum of the nine (`3 × 3`) elementary `(r + 2)`-fold iterated Hamiltonian resolvent plaquettes
in a `4 × 4` initial-final time grid `(s₁, s₂, s₃, s₄) × (t₁, t₂, t₃, t₄)` with spectral parameters
`(a₁, a₂, a₃, a₄)`, `(b₁, b₂, b₃, b₄)`, `(c₁, c₂, c₃, c₄)`, `(e₁, e₂, e₃, e₄)` and source vectors
`(f₁, f₂, f₃, f₄)`. -/
def threeByThreeResolventPlaquetteGridSum
    (s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄
     a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ : Hilbert) : Hilbert :=
  (mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₂ s₃ t₁ t₂ a₂ a₃ b₂ b₃ r f₂ f₃ +
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₃ s₄ t₁ t₂ a₃ a₄ b₃ b₄ r f₃ f₄) +
  (mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₂ t₃ b₁ b₂ c₁ c₂ r f₁ f₂ +
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₂ s₃ t₂ t₃ b₂ b₃ c₂ c₃ r f₂ f₃ +
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₃ s₄ t₂ t₃ b₃ b₄ c₃ c₄ r f₃ f₄) +
  (mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₃ t₄ c₁ c₂ e₁ e₂ r f₁ f₂ +
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₂ s₃ t₃ t₄ c₂ c₃ e₂ e₃ r f₂ f₃ +
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₃ s₄ t₃ t₄ c₃ c₄ e₃ e₄ r f₃ f₄)

/-- Sum of the nine (`3 × 3`) elementary `(r + 2)`-th order Yosida identity plaquettes in a
`4 × 4` initial-final time grid `(s₁, s₂, s₃, s₄) × (t₁, t₂, t₃, t₄)`. -/
def threeByThreeIdentityPlaquetteGridSum
    (s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄
     a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ : Hilbert) : Hilbert :=
  (mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₂ s₃ t₁ t₂ a₂ a₃ b₂ b₃ r f₂ f₃ +
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₃ s₄ t₁ t₂ a₃ a₄ b₃ b₄ r f₃ f₄) +
  (mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₂ t₃ b₁ b₂ c₁ c₂ r f₁ f₂ +
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₂ s₃ t₂ t₃ b₂ b₃ c₂ c₃ r f₂ f₃ +
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₃ s₄ t₂ t₃ b₃ b₄ c₃ c₄ r f₃ f₄) +
  (mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₃ t₄ c₁ c₂ e₁ e₂ r f₁ f₂ +
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₂ s₃ t₃ t₄ c₂ c₃ e₂ e₃ r f₂ f₃ +
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₃ s₄ t₃ t₄ c₃ c₄ e₃ e₄ r f₃ f₄)

/-- Exact 2D Stokes / Green plaquette boundary cancellation on the `4 × 4` (`9`-cell) time-parameter
grid: `threeByThreeResolventPlaquetteGridSum` and `threeByThreeIdentityPlaquetteGridSum` equal the
single outer boundary plaquette between `(s₁, s₄)` and `(t₁, t₄)` at `(a₁, a₄, e₁, e₄)` and
`(f₁, f₄)`, canceling all 4 interior vertices `(s₂, t₂), (s₂, t₃), (s₃, t₂), (s₃, t₃)` and all
12 interior edges. -/
theorem threeByThreePlaquetteGridSum_stokes_boundary_cancellation
    (s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄
     a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ : Hilbert) :
    threeByThreeResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄
        a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ r f₁ f₂ f₃ f₄ =
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₄ t₁ t₄ a₁ a₄ e₁ e₄ r f₁ f₄ ∧
    threeByThreeIdentityPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄
        a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ r f₁ f₂ f₃ f₄ =
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₄ t₁ t₄ a₁ a₄ e₁ e₄ r f₁ f₄ := by
  unfold threeByThreeResolventPlaquetteGridSum threeByThreeIdentityPlaquetteGridSum
    mixedInitialFinalHigherPowerResolventPlaquette
    mixedInitialFinalHigherPowerIdentityPlaquette
    crossInitialHigherPowerResolventDiff crossInitialHigherPowerIdentityDiff
  refine ⟨by abel, by abel⟩

/-- Cyclic 4-step initial-time `(s₁, s₂, s₃, s₄)` and final-time `(t₁, t₂, t₃, t₄)` plaquette
quadrangle cocycles for `mixedInitialFinalHigherPowerResolventPlaquette` and
`mixedInitialFinalHigherPowerIdentityPlaquette`. -/
theorem mixedInitialFinalHigherPowerPlaquette_four_initial_and_final_quadrangle_cocycles
    (s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄ a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ e₁ e₂ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ : Hilbert) :
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₂ s₃ t₁ t₂ a₂ a₃ b₂ b₃ r f₂ f₃ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₃ s₄ t₁ t₂ a₃ a₄ b₃ b₄ r f₃ f₄ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₄ s₁ t₁ t₂ a₄ a₁ b₄ b₁ r f₄ f₁ = 0 ∧
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₂ s₃ t₁ t₂ a₂ a₃ b₂ b₃ r f₂ f₃ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₃ s₄ t₁ t₂ a₃ a₄ b₃ b₄ r f₃ f₄ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₄ s₁ t₁ t₂ a₄ a₁ b₄ b₁ r f₄ f₁ = 0 ∧
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₂ t₃ b₁ b₂ c₁ c₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₃ t₄ c₁ c₂ e₁ e₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₄ t₁ e₁ e₂ a₁ a₂ r f₁ f₂ = 0 ∧
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₂ t₃ b₁ b₂ c₁ c₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₃ t₄ c₁ c₂ e₁ e₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₄ t₁ e₁ e₂ a₁ a₂ r f₁ f₂ = 0 := by
  unfold mixedInitialFinalHigherPowerResolventPlaquette
    mixedInitialFinalHigherPowerIdentityPlaquette
    crossInitialHigherPowerResolventDiff crossInitialHigherPowerIdentityDiff
  refine ⟨by abel, by abel, by abel, by abel⟩

/-- Unconditionally for all `s₁..s₄, t₁..t₄, q ∈ ℝ`, `0 < a₁, a₄, e₁, e₄`, and `r : ℕ`,
`threeByThreeResolventPlaquetteGridSum` belongs simultaneously to all 8 time-independent /
observation-time `q` domains with outer-corner geometric norm bound independent of all interior
times, parameters, and sources. -/
theorem threeByThreeResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
    (s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄ q
     a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ : ℝ)
    (ha₁ : 0 < a₁) (ha₄ : 0 < a₄) (he₁ : 0 < e₁) (he₄ : 0 < e₄)
    (r : ℕ) (f₁ f₂ f₃ f₄ : Hilbert) :
    let w_grid := threeByThreeResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄
      a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ r f₁ f₂ f₃ f₄
    (w_grid ∈ (K).domain ∧
     w_grid ∈ (Eavg q).domain ∧
     w_grid ∈ (Tstat).domain ∧
     w_grid ∈ (Kroot).domain ∧
     w_grid ∈ (Tpot).domain ∧
     w_grid ∈ (Tgrow).domain ∧
     w_grid ∈ (Tres q).domain ∧
     w_grid ∈ (clockHalf ε).domain) ∧
    ‖w_grid‖ ≤ ((a₁⁻¹) ^ (r + 2) + (e₁⁻¹) ^ (r + 2)) * ‖f₁‖ +
      ((a₄⁻¹) ^ (r + 2) + (e₄⁻¹) ^ (r + 2)) * ‖f₄‖ := by
  intro w_grid
  have hstokes := (threeByThreePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄
    a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ r f₁ f₂ f₃ f₄).1
  have houter := mixedInitialFinalHigherPowerResolventPlaquette_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₄ t₁ t₄ q a₁ a₄ e₁ e₄ ha₁ ha₄ he₁ he₄ r f₁ f₄
  dsimp only [w_grid]
  rw [hstokes]
  exact houter

/-- Unconditionally for all `s₁..s₄, t₁..t₄, q ∈ ℝ`, `0 < a₁, a₄, e₁, e₄`, and `r : ℕ`,
`threeByThreeIdentityPlaquetteGridSum` belongs simultaneously to all 8 time-independent /
observation-time `q` domains with outer-corner stability bound `‖y_grid‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₄‖`. -/
theorem threeByThreeIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
    (s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄ q
     a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ : ℝ)
    (ha₁ : 0 < a₁) (ha₄ : 0 < a₄) (he₁ : 0 < e₁) (he₄ : 0 < e₄)
    (r : ℕ) (f₁ f₂ f₃ f₄ : Hilbert) :
    let y_grid := threeByThreeIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄
      a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ r f₁ f₂ f₃ f₄
    (y_grid ∈ (K).domain ∧
     y_grid ∈ (Eavg q).domain ∧
     y_grid ∈ (Tstat).domain ∧
     y_grid ∈ (Kroot).domain ∧
     y_grid ∈ (Tpot).domain ∧
     y_grid ∈ (Tgrow).domain ∧
     y_grid ∈ (Tres q).domain ∧
     y_grid ∈ (clockHalf ε).domain) ∧
    ‖y_grid‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₄‖ := by
  intro y_grid
  have hstokes := (threeByThreePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄
    a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ r f₁ f₂ f₃ f₄).2
  have houter := mixedInitialFinalHigherPowerIdentityPlaquette_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₄ t₁ t₄ q a₁ a₄ e₁ e₄ ha₁ ha₄ he₁ he₄ r f₁ f₄
  dsimp only [y_grid]
  rw [hstokes]
  exact houter

/-- When the outer final times coincide (`t₁ = t₄ = t`), `threeByThreeResolventPlaquetteGridSum`
belongs simultaneously to `hamiltonianPowerDomain t (r + 2)`, `hamiltonianSecondPowerDomain t`,
and all 10 operator, form, and clock domains regardless of the intermediate times `(t₂, t₃)`. -/
theorem threeByThreeResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    (s₁ s₂ s₃ s₄ t t₂ t₃ q
     a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ : ℝ)
    (ha₁ : 0 < a₁) (ha₄ : 0 < a₄) (he₁ : 0 < e₁) (he₄ : 0 < e₄)
    (r : ℕ) (f₁ f₂ f₃ f₄ : Hilbert) :
    let w_grid := threeByThreeResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ t t₂ t₃ t
      a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ r f₁ f₂ f₃ f₄
    w_grid ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    w_grid ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t ∧
    (w_grid ∈ (H t).domain ∧
     w_grid ∈ (K).domain ∧
     w_grid ∈ (S t).domain ∧
     w_grid ∈ (Eavg q).domain ∧
     w_grid ∈ (Tstat).domain ∧
     w_grid ∈ (Kroot).domain ∧
     w_grid ∈ (Tpot).domain ∧
     w_grid ∈ (Tgrow).domain ∧
     w_grid ∈ (Tres q).domain ∧
     w_grid ∈ (clockHalf ε).domain) ∧
    ‖w_grid‖ ≤ ((a₁⁻¹) ^ (r + 2) + (e₁⁻¹) ^ (r + 2)) * ‖f₁‖ +
      ((a₄⁻¹) ^ (r + 2) + (e₄⁻¹) ^ (r + 2)) * ‖f₄‖ := by
  intro w_grid
  have hstokes := (threeByThreePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ t t₂ t₃ t
    a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ r f₁ f₂ f₃ f₄).1
  have houter := mixedInitialFinalHigherPowerResolventPlaquette_equal_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₄ t q a₁ a₄ e₁ e₄ ha₁ ha₄ he₁ he₄ r f₁ f₄
  dsimp only [w_grid]
  rw [hstokes]
  exact houter

/-- When the outer final times coincide (`t₁ = t₄ = t`), `threeByThreeIdentityPlaquetteGridSum`
belongs simultaneously to `hamiltonianPowerDomain t (r + 2)`, `hamiltonianSecondPowerDomain t`,
and all 10 operator, form, and clock domains with `‖y_grid‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₄‖`. -/
theorem threeByThreeIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    (s₁ s₂ s₃ s₄ t t₂ t₃ q
     a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ : ℝ)
    (ha₁ : 0 < a₁) (ha₄ : 0 < a₄) (he₁ : 0 < e₁) (he₄ : 0 < e₄)
    (r : ℕ) (f₁ f₂ f₃ f₄ : Hilbert) :
    let y_grid := threeByThreeIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ t t₂ t₃ t
      a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ r f₁ f₂ f₃ f₄
    y_grid ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    y_grid ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t ∧
    (y_grid ∈ (H t).domain ∧
     y_grid ∈ (K).domain ∧
     y_grid ∈ (S t).domain ∧
     y_grid ∈ (Eavg q).domain ∧
     y_grid ∈ (Tstat).domain ∧
     y_grid ∈ (Kroot).domain ∧
     y_grid ∈ (Tpot).domain ∧
     y_grid ∈ (Tgrow).domain ∧
     y_grid ∈ (Tres q).domain ∧
     y_grid ∈ (clockHalf ε).domain) ∧
    ‖y_grid‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₄‖ := by
  intro y_grid
  have hstokes := (threeByThreePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ t t₂ t₃ t
    a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ r f₁ f₂ f₃ f₄).2
  have houter := mixedInitialFinalHigherPowerIdentityPlaquette_equal_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₄ t q a₁ a₄ e₁ e₄ ha₁ ha₄ he₁ he₄ r f₁ f₄
  dsimp only [y_grid]
  rw [hstokes]
  exact houter

/-- Master Four-by-Four `(s₁, s₂, s₃, s₄) × (t₁, t₂, t₃, t₄)` (`3 × 3 = 9` Cells) Mixed
Initial-and-Final Higher-Power Resolvent Plaquette Grid and 2D Stokes Boundary Cancellation
Synthesis. -/
theorem four_by_four_mixed_initial_final_plaquette_grid_master_synthesis
    (s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄ q
     a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ : ℝ)
    (ha₁ : 0 < a₁) (ha₄ : 0 < a₄) (he₁ : 0 < e₁) (he₄ : 0 < e₄)
    (r : ℕ) (f₁ f₂ f₃ f₄ : Hilbert) :
    let w_grid := threeByThreeResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄
      a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ r f₁ f₂ f₃ f₄
    let y_grid := threeByThreeIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄
      a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ r f₁ f₂ f₃ f₄
    let w_grid_eq := threeByThreeResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₁
      a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ r f₁ f₂ f₃ f₄
    (w_grid = mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₄ t₁ t₄ a₁ a₄ e₁ e₄ r f₁ f₄ ∧
     y_grid = mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₄ t₁ t₄ a₁ a₄ e₁ e₄ r f₁ f₄) ∧
    (w_grid ∈ (K).domain ∧ w_grid ∈ (Eavg q).domain ∧ w_grid ∈ (clockHalf ε).domain ∧
     ‖w_grid‖ ≤ ((a₁⁻¹) ^ (r + 2) + (e₁⁻¹) ^ (r + 2)) * ‖f₁‖ +
       ((a₄⁻¹) ^ (r + 2) + (e₄⁻¹) ^ (r + 2)) * ‖f₄‖) ∧
    (y_grid ∈ (K).domain ∧ y_grid ∈ (Eavg q).domain ∧ y_grid ∈ (clockHalf ε).domain ∧
     ‖y_grid‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₄‖) ∧
    (w_grid_eq ∈ hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2) ∧
     w_grid_eq ∈ (H t₁).domain ∧ w_grid_eq ∈ (S t₁).domain) := by
  intro w_grid y_grid w_grid_eq
  have hstokes := threeByThreePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄
    a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ r f₁ f₂ f₃ f₄
  have hw_pl := threeByThreeResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄ q
    a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ ha₁ ha₄ he₁ he₄ r f₁ f₂ f₃ f₄
  have hy_pl := threeByThreeIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄ q
    a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ ha₁ ha₄ he₁ he₄ r f₁ f₂ f₃ f₄
  have hweq := threeByThreeResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ t₁ t₂ t₃ q
    a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ ha₁ ha₄ he₁ he₄ r f₁ f₂ f₃ f₄
  exact ⟨hstokes,
    ⟨hw_pl.1.1, hw_pl.1.2.1, hw_pl.1.2.2.2.2.2.2.2, hw_pl.2⟩,
    ⟨hy_pl.1.1, hy_pl.1.2.1, hy_pl.1.2.2.2.2.2.2.2, hy_pl.2⟩,
    ⟨hweq.1, hweq.2.2.1.1, hweq.2.2.1.2.2.1⟩⟩

#print axioms threeByThreePlaquetteGridSum_stokes_boundary_cancellation
#print axioms mixedInitialFinalHigherPowerPlaquette_four_initial_and_final_quadrangle_cocycles
#print axioms threeByThreeResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
#print axioms threeByThreeIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
#print axioms threeByThreeResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
#print axioms threeByThreeIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
#print axioms four_by_four_mixed_initial_final_plaquette_grid_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorFourByFourMixedInitialFinalHigherPowerResolventPlaquetteGrid
