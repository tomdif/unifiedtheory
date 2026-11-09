/- Unconditional 10-Domain Regularity, First- and Second-Power Radial-Residual
Decompositions, Second-Resolvent Identities, Radial-Root Smoothing, Quarter-Strip
Growing-Domain Regularity, and 5-Way Three-Operator Synthesis for the Iterated
Hamiltonian Resolvent R_{H(t)}(a)(R_{H(t)}(b) f) across all real couplings m, g, k ∈ ℝ:
1. Establishes that for every f : Hilbert, all real m, g, k, t, s ∈ ℝ, and any a, b > 0,
   both x := R_{H(t)}(a)(R_{H(t)}(b) f) and its first-power Hamiltonian output
   y := R_{H(t)}(b) f - (a : ℂ) • x lie in all 10 operator, form, and clock domains,
   satisfying exact first- and second-power radial-residual decompositions:
   H(t) x = exp(2t) • K x + S(t) x = R_{H(t)}(b) f - (a : ℂ) • x,
   H(t) y = exp(2t) • K y + S(t) y = f - (a + b) • R_{H(t)}(b) f + a² • x,
   together with unconditional radial and residual norm-square bounds on both tiers.
2. Deduces unconditional second-resolvent identities, radial-root (K_root) bounds,
   parabolic growing-resolvent radial smoothing bounds, and quarter-strip (|h| ≤ π * ε / 4)
   potential-resolvent growing-domain regularity on R_{H(t)}(b) f and x.
3. Proves the 5-way common-domain equivalence and exact 3-operator static-radial-potential
   decompositions and static-Hamiltonian second-resolvent identities on x. -/
import UnifiedTheory.Audit.KFCausalClockFloorIteratedResolventSecondPowerCore
import UnifiedTheory.Audit.KFCausalClockFloorFullFiveResolventChainSynthesis
import UnifiedTheory.Audit.KFCausalClockFloorHamiltonianResolventThreeOperatorSynthesis
import UnifiedTheory.Audit.KFCausalClockFloorGrowingResolventRadialRegularity

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorIteratedHamiltonianResolventUnconditionalDomination

noncomputable section

open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalPositiveResolventBounds (point)
open KFCausalClockFloorRadialYosidaQuarterStripSector (quarter_le_third)
open KFCausalClockFloorSecondPowerOperatorCores
  (secondPowerGraph secondPowerDomain)
open KFCausalClockFloorIteratedResolventSecondPowerCore
  (hamiltonianSecondPowerDomain
   hamiltonian_iterated_resolvent_secondPower
   hamiltonian_iterated_resolvent_mem_ten_domains
   hamiltonian_iterated_resolvent_both_mem_ten_domains)
open KFCausalClockFloorHamiltonianComponentResolventBounds
  (resolvent_mem_hamiltonian_domain resolvent_mem_radial_domain
   resolvent_mem_residual_domain resolvent_norm_le
   resolvent_component_norm_sq_le_source)
open KFCausalClockFloorHamiltonianResidualSecondResolventIdentity
  (hamiltonian_resolvent_eq_residual_resolvent_shifted_source
   residual_sub_hamiltonian_resolvent_eq
   residual_sub_hamiltonian_resolvent_norm_le_radial
   residual_sub_hamiltonian_resolvent_norm_sq_le_source
   hamiltonian_resolvent_radial_norm_sq_le_source_sharp)
open KFCausalClockFloorFullFiveResolventChainSynthesis
  (potential_sub_hamiltonian_via_growing_residual_eq
   static_sub_hamiltonian_resolvent_eq
   static_sub_hamiltonian_resolvent_eq_radial_add_potential
   hamiltonian_resolvent_mem_growing_of_potential)
open KFCausalClockFloorHamiltonianResolventThreeOperatorSynthesis
  (hamiltonian_resolvent_radialRoot_norm_le_of_radialRoot
   hamiltonian_resolvent_five_way_domain_iff
   hamiltonian_resolvent_mem_potential_iff_common
   hamiltonian_resolvent_eq_three_operator_of_potential)
open KFCausalClockFloorUnconditionalTwoTimeEvolution
  (commonOperatorDomain common_domain_subset_hamiltonian)
open KFCausalClockFloorGrowingResolventRadialRegularity
  (growing_resolvent_mem_radialRoot_domain
   growing_resolvent_radialRoot_norm_le_of_rootDomain
   growing_resolvent_radial_norm_le_min_of_rootDomain
   growing_resolvent_radial_norm_le_min_of_radialDomain)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
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

/-- The iterated full-Hamiltonian resolvent `R_{H(t)}(a)(R_{H(t)}(b) f)`. -/
def iteratedHamiltonianResolvent (t a b : ℝ) (f : Hilbert) : Hilbert :=
  RH t a (RH t b f)

/-- The diagonal (squared) full-Hamiltonian resolvent `R_{H(t)}(a)(R_{H(t)}(a) f)`. -/
def squaredHamiltonianResolvent (t a : ℝ) (f : Hilbert) : Hilbert :=
  iteratedHamiltonianResolvent ε hε h hh hb m g k t a a f

/-! ### 1. Unconditional 10-Domain Membership & Exact First- and Second-Power Radial-Residual Decompositions -/

/-- Definitional unfolding of `iteratedHamiltonianResolvent`. -/
theorem iteratedHamiltonianResolvent_eq (t a b : ℝ) (f : Hilbert) :
    iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f = RH t a (RH t b f) :=
  rfl

/-- Definitional unfolding of `squaredHamiltonianResolvent`. -/
theorem squaredHamiltonianResolvent_eq (t a : ℝ) (f : Hilbert) :
    squaredHamiltonianResolvent ε hε h hh hb m g k t a f = RH t a (RH t a f) :=
  rfl

/-- Unconditionally for all real `m, g, k, t` and `0 < a, 0 < b`,
`iteratedHamiltonianResolvent t a b f` lies in `hamiltonianSecondPowerDomain t`. -/
theorem iteratedHamiltonianResolvent_mem_secondPowerDomain
    (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f ∈
      hamiltonianSecondPowerDomain ε hε h hh hb m g k t :=
  (hamiltonian_iterated_resolvent_secondPower ε hε h hh hb m g k t a b ha hb_pos f).1

/-- Unconditionally for all real `m, g, k, t` and `0 < a, 0 < b`, the pair
`(iteratedHamiltonianResolvent t a b f, RH t b f - (a : ℂ) • iteratedHamiltonianResolvent t a b f)`
lies in `secondPowerGraph (H t)`. -/
theorem iteratedHamiltonianResolvent_mem_secondPowerGraph
    (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    (iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f,
     RH t b f - (a : ℂ) • iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f) ∈
      secondPowerGraph (H t) :=
  (hamiltonian_iterated_resolvent_secondPower ε hε h hh hb m g k t a b ha hb_pos f).2.1

/-- Unconditionally for all real `m, g, k, t, s` and `0 < a, 0 < b`,
`iteratedHamiltonianResolvent t a b f` belongs simultaneously to all 10 operator,
form, and clock domains. -/
theorem iteratedHamiltonianResolvent_mem_ten_domains
    (t s a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let x := iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f
    x ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t ∧
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
  hamiltonian_iterated_resolvent_mem_ten_domains ε hε h hh hb m g k t s a b ha hb_pos f

/-- Unconditionally for all real `m, g, k, t, s` and `0 < a, 0 < b`, the first-power
Hamiltonian output `RH t b f - (a : ℂ) • iteratedHamiltonianResolvent t a b f` belongs
simultaneously to all 10 operator, form, and clock domains. -/
theorem iteratedHamiltonianResolvent_first_power_mem_ten_domains
    (t s a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let y := RH t b f - (a : ℂ) • iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f
    y ∈ (H t).domain ∧
    y ∈ (K).domain ∧
    y ∈ (S t).domain ∧
    y ∈ (Eavg s).domain ∧
    y ∈ (Tstat).domain ∧
    y ∈ (Kroot).domain ∧
    y ∈ (Tpot).domain ∧
    y ∈ (Tgrow).domain ∧
    y ∈ (Tres s).domain ∧
    y ∈ (clockHalf ε).domain :=
  (hamiltonian_iterated_resolvent_both_mem_ten_domains ε hε h hh hb m g k t s a b ha hb_pos f).2.2

/-- Unconditionally for all real `m, g, k, t` and `0 < a, 0 < b`,
`iteratedHamiltonianResolvent t a b f` belongs to `(H t).domain ⊓ (K).domain ⊓ (S t).domain`. -/
theorem iteratedHamiltonianResolvent_mem_radial_residual_domain
    (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let x := iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f
    x ∈ (H t).domain ∧ x ∈ (K).domain ∧ x ∈ (S t).domain := by
  have h10 := iteratedHamiltonianResolvent_mem_ten_domains ε hε h hh hb m g k t 0 a b ha hb_pos f
  exact ⟨h10.2.1, h10.2.2.1, h10.2.2.2.1⟩

/-- Unconditionally for all real `m, g, k, t` and `0 < a, 0 < b`, the first-power output
`RH t b f - (a : ℂ) • iteratedHamiltonianResolvent t a b f` belongs to
`(H t).domain ⊓ (K).domain ⊓ (S t).domain`. -/
theorem iteratedHamiltonianResolvent_first_power_mem_radial_residual_domain
    (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let y := RH t b f - (a : ℂ) • iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f
    y ∈ (H t).domain ∧ y ∈ (K).domain ∧ y ∈ (S t).domain := by
  have h10 :=
    iteratedHamiltonianResolvent_first_power_mem_ten_domains ε hε h hh hb m g k t 0 a b ha hb_pos f
  exact ⟨h10.1, h10.2.1, h10.2.2.1⟩

/-- Exact first-power radial-residual decomposition on `iteratedHamiltonianResolvent t a b f`:
`H t x = exp(2t) • K x + S t x = RH t b f - (a : ℂ) • x`. -/
theorem iteratedHamiltonianResolvent_hamiltonian_eq_radial_add_residual
    (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let x := iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f
    let hdom := iteratedHamiltonianResolvent_mem_radial_residual_domain ε hε h hh hb m g k t a b ha hb_pos f
    H t ⟨x, hdom.1⟩ =
      (Real.exp (2 * t) : ℂ) • K ⟨x, hdom.2.1⟩ + S t ⟨x, hdom.2.2⟩ ∧
    H t ⟨x, hdom.1⟩ = RH t b f - (a : ℂ) • x := by
  intro x hdom
  refine ⟨?_, ?_⟩
  · rw [KFCausalClockFloorHamiltonianRadialSum.residual_output ε hε h hh hb m g k t ⟨x, hdom.1⟩]
    exact (add_sub_cancel _ _).symm
  · rw [Complex.coe_smul]
    exact KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_equation
      ε hε h hh hb m g k t a ha (RH t b f)

/-- Exact residual evaluation on `iteratedHamiltonianResolvent t a b f`:
`S t x = RH t b f - (a : ℂ) • x - exp(2t) • K x`. -/
theorem iteratedHamiltonianResolvent_residual_eq_shifted_sub_radial
    (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let x := iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f
    let hdom := iteratedHamiltonianResolvent_mem_radial_residual_domain ε hε h hh hb m g k t a b ha hb_pos f
    S t ⟨x, hdom.2.2⟩ =
      RH t b f - (a : ℂ) • x - (Real.exp (2 * t) : ℂ) • K ⟨x, hdom.2.1⟩ := by
  intro x hdom
  have h1 := iteratedHamiltonianResolvent_hamiltonian_eq_radial_add_residual
    ε hε h hh hb m g k t a b ha hb_pos f
  dsimp only at h1
  have h2 : (Real.exp (2 * t) : ℂ) • K ⟨x, hdom.2.1⟩ + S t ⟨x, hdom.2.2⟩ =
      RH t b f - (a : ℂ) • x := h1.1.symm.trans h1.2
  rw [← h2, add_sub_cancel_left]

/-- Exact radial-residual decomposition on the first-power output
`y := RH t b f - (a : ℂ) • iteratedHamiltonianResolvent t a b f`:
`H t y = exp(2t) • K y + S t y`. -/
theorem iteratedHamiltonianResolvent_first_power_hamiltonian_eq_radial_add_residual
    (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let y := RH t b f - (a : ℂ) • iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f
    let hdom :=
      iteratedHamiltonianResolvent_first_power_mem_radial_residual_domain
        ε hε h hh hb m g k t a b ha hb_pos f
    H t ⟨y, hdom.1⟩ =
      (Real.exp (2 * t) : ℂ) • K ⟨y, hdom.2.1⟩ + S t ⟨y, hdom.2.2⟩ := by
  intro y hdom
  rw [KFCausalClockFloorHamiltonianRadialSum.residual_output ε hε h hh hb m g k t ⟨y, hdom.1⟩]
  exact (add_sub_cancel _ _).symm

/-- Exact second-power radial-residual identity for `iteratedHamiltonianResolvent t a b f`:
on `y := RH t b f - (a : ℂ) • x`,
`exp(2t) • K y + S t y = f - (a + b) • RH t b f + a² • x`. -/
theorem iteratedHamiltonianResolvent_second_power_radial_residual_eq
    (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let x := iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f
    let y := RH t b f - (a : ℂ) • x
    let hdom :=
      iteratedHamiltonianResolvent_first_power_mem_radial_residual_domain
        ε hε h hh hb m g k t a b ha hb_pos f
    (Real.exp (2 * t) : ℂ) • K ⟨y, hdom.2.1⟩ + S t ⟨y, hdom.2.2⟩ =
      f - ((a + b : ℝ) : ℂ) • RH t b f + ((a ^ 2 : ℝ) : ℂ) • x := by
  intro x y hdom
  rw [← iteratedHamiltonianResolvent_first_power_hamiltonian_eq_radial_add_residual
    ε hε h hh hb m g k t a b ha hb_pos f]
  have hsec := (hamiltonian_iterated_resolvent_secondPower ε hε h hh hb m g k t a b ha hb_pos f).2.2
  let u : (H t).domain :=
    point (H t) (RH t b) b
      (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t b hb_pos) f
  let v : (H t).domain :=
    point (H t) (RH t a) a
      (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha) (RH t b f)
  have hsub : (⟨y, hdom.1⟩ : (H t).domain) = u - (a : ℂ) • v := Subtype.ext rfl
  rw [hsub]
  exact hsec.2.1

/-- Diagonal (`a = b`) second-power radial-residual identity for `squaredHamiltonianResolvent t a f`. -/
theorem squaredHamiltonianResolvent_second_power_radial_residual_eq
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    let x := squaredHamiltonianResolvent ε hε h hh hb m g k t a f
    let y := RH t a f - (a : ℂ) • x
    let hdom :=
      iteratedHamiltonianResolvent_first_power_mem_radial_residual_domain
        ε hε h hh hb m g k t a a ha ha f
    (Real.exp (2 * t) : ℂ) • K ⟨y, hdom.2.1⟩ + S t ⟨y, hdom.2.2⟩ =
      f - ((a + a : ℝ) : ℂ) • RH t a f + ((a ^ 2 : ℝ) : ℂ) • x :=
  iteratedHamiltonianResolvent_second_power_radial_residual_eq ε hε h hh hb m g k t a a ha ha f

/-- Unconditional combined radial and residual norm-square bound on `iteratedHamiltonianResolvent t a b f`:
`exp(4t) ‖K x‖² + ‖S t x‖² ≤ (2 + 2 exp(2t) (h²/ε²) (a⁻¹)²) * (b⁻¹)² * ‖f‖²`. -/
theorem iteratedHamiltonianResolvent_component_norm_sq_le_source
    (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let x := iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f
    let hdom := iteratedHamiltonianResolvent_mem_radial_residual_domain ε hε h hh hb m g k t a b ha hb_pos f
    Real.exp (4 * t) * ‖K ⟨x, hdom.2.1⟩‖ ^ 2 + ‖S t ⟨x, hdom.2.2⟩‖ ^ 2 ≤
      (2 + 2 * Real.exp (2 * t) * (h ^ 2 / ε ^ 2) * (a⁻¹) ^ 2) * (b⁻¹) ^ 2 * ‖f‖ ^ 2 := by
  intro x hdom
  have h1 := resolvent_component_norm_sq_le_source ε hε h hh hb m g k t a ha (RH t b f)
  have h2 : ‖RH t b f‖ ^ 2 ≤ (b⁻¹) ^ 2 * ‖f‖ ^ 2 := by
    have hbnd := resolvent_norm_le ε hε h hh hb m g k t b hb_pos f
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hbnd
    simpa only [mul_pow] using hsq
  have hmul := mul_le_mul_of_nonneg_left h2
    (show 0 ≤ 2 + 2 * Real.exp (2 * t) * (h ^ 2 / ε ^ 2) * (a⁻¹) ^ 2 by positivity)
  exact (h1.trans hmul).trans_eq (by ring)

/-- Unconditional sharp radial norm-square bound on `iteratedHamiltonianResolvent t a b f`:
`exp(4t) ‖K x‖² ≤ (1 + 2 exp(2t) (h²/ε²) (a⁻¹)²) * (b⁻¹)² * ‖f‖²`. -/
theorem iteratedHamiltonianResolvent_radial_norm_sq_le_source
    (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let x := iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f
    let hdom := iteratedHamiltonianResolvent_mem_radial_residual_domain ε hε h hh hb m g k t a b ha hb_pos f
    Real.exp (4 * t) * ‖K ⟨x, hdom.2.1⟩‖ ^ 2 ≤
      (1 + 2 * Real.exp (2 * t) * (h ^ 2 / ε ^ 2) * (a⁻¹) ^ 2) * (b⁻¹) ^ 2 * ‖f‖ ^ 2 := by
  intro x hdom
  have h1 := hamiltonian_resolvent_radial_norm_sq_le_source_sharp ε hε h hh hb m g k t a ha (RH t b f)
  have h2 : ‖RH t b f‖ ^ 2 ≤ (b⁻¹) ^ 2 * ‖f‖ ^ 2 := by
    have hbnd := resolvent_norm_le ε hε h hh hb m g k t b hb_pos f
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hbnd
    simpa only [mul_pow] using hsq
  have hmul := mul_le_mul_of_nonneg_left h2
    (show 0 ≤ 1 + 2 * Real.exp (2 * t) * (h ^ 2 / ε ^ 2) * (a⁻¹) ^ 2 by positivity)
  exact (h1.trans hmul).trans_eq (by ring)

/-- Unconditional residual norm-square bound on `iteratedHamiltonianResolvent t a b f`:
`‖S t x‖² ≤ (2 + 2 exp(2t) (h²/ε²) (a⁻¹)²) * (b⁻¹)² * ‖f‖²`. -/
theorem iteratedHamiltonianResolvent_residual_norm_sq_le_source
    (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let x := iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f
    let hdom := iteratedHamiltonianResolvent_mem_radial_residual_domain ε hε h hh hb m g k t a b ha hb_pos f
    ‖S t ⟨x, hdom.2.2⟩‖ ^ 2 ≤
      (2 + 2 * Real.exp (2 * t) * (h ^ 2 / ε ^ 2) * (a⁻¹) ^ 2) * (b⁻¹) ^ 2 * ‖f‖ ^ 2 := by
  intro x hdom
  have h1 := iteratedHamiltonianResolvent_component_norm_sq_le_source ε hε h hh hb m g k t a b ha hb_pos f
  have h2 : 0 ≤ Real.exp (4 * t) * ‖K ⟨x, hdom.2.1⟩‖ ^ 2 := by positivity
  dsimp only at h1 ⊢
  linarith

/-- Unconditional combined radial and residual norm-square bound on the first-power output
`y := RH t b f - (a : ℂ) • iteratedHamiltonianResolvent t a b f`:
`exp(4t) ‖K y‖² + ‖S t y‖² ≤ 4 * (2 + 2 exp(2t) (h²/ε²) (a⁻¹)²) * ‖f‖²`. -/
theorem iteratedHamiltonianResolvent_first_power_component_norm_sq_le_source
    (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let y := RH t b f - (a : ℂ) • iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f
    let hdom :=
      iteratedHamiltonianResolvent_first_power_mem_radial_residual_domain
        ε hε h hh hb m g k t a b ha hb_pos f
    Real.exp (4 * t) * ‖K ⟨y, hdom.2.1⟩‖ ^ 2 + ‖S t ⟨y, hdom.2.2⟩‖ ^ 2 ≤
      4 * (2 + 2 * Real.exp (2 * t) * (h ^ 2 / ε ^ 2) * (a⁻¹) ^ 2) * ‖f‖ ^ 2 := by
  intro y hdom
  let uH : (H t).domain :=
    point (H t) (RH t b) b
      (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t b hb_pos) f
  let vH : (H t).domain :=
    point (H t) (RH t a) a
      (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha) (RH t b f)
  have hcomm0 : H t vH = RH t a (H t uH) :=
    KFCausalClockFloorSecondPowerOperatorCores.resolvent_commutes_on_domain
      (H t) (RH t a) a
      (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
      (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t a ha) uH
  have hvH : H t vH = y :=
    KFCausalClockFloorIteratedResolventSecondPowerCore.resolvent_output_eq_sub
      (H t) (RH t a) a
      (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha) (RH t b f)
  have hcomm : y = RH t a (H t uH) := hvH.symm.trans hcomm0
  let wK : (K).domain :=
    ⟨RH t a (H t uH),
      resolvent_mem_radial_domain ε hε h hh hb m g k t a ha (H t uH)⟩
  let wS : (S t).domain :=
    ⟨RH t a (H t uH),
      resolvent_mem_residual_domain ε hε h hh hb m g k t a ha (H t uH)⟩
  have hyK : (⟨y, hdom.2.1⟩ : (K).domain) = wK := Subtype.ext hcomm
  have hyS : (⟨y, hdom.2.2⟩ : (S t).domain) = wS := Subtype.ext hcomm
  have hw_bnd := resolvent_component_norm_sq_le_source ε hε h hh hb m g k t a ha (H t uH)
  have huH_sq : ‖H t uH‖ ^ 2 ≤ 4 * ‖f‖ ^ 2 := by
    have huH :=
      KFCausalClockFloorIteratedResolventSecondPowerCore.resolvent_first_order_norm_bound
        (H t) (RH t b) b hb_pos
        (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t b hb_pos)
        (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t) f
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr huH
    linarith [show (2 * ‖f‖) ^ 2 = 4 * ‖f‖ ^ 2 by ring]
  have hmul := mul_le_mul_of_nonneg_left huH_sq
    (show 0 ≤ 2 + 2 * Real.exp (2 * t) * (h ^ 2 / ε ^ 2) * (a⁻¹) ^ 2 by positivity)
  rw [hyK, hyS]
  linarith

/-! ### 2. Unconditional Second-Resolvent Identities, Radial-Root Regularity, and Quarter-Strip Domination -/

/-- Exact shifted-source residual representation of `iteratedHamiltonianResolvent t a b f`:
`iteratedHamiltonianResolvent t a b f = RS t a (RH t b f - exp(2t) • K (iteratedHamiltonianResolvent t a b f))`. -/
theorem iteratedHamiltonianResolvent_eq_residual_resolvent_shifted_source
    (t a b : ℝ) (ha : 0 < a) (f : Hilbert) :
    iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f =
      RS t a (RH t b f - (Real.exp (2 * t) : ℂ) •
        K ⟨iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f,
          resolvent_mem_radial_domain ε hε h hh hb m g k t a ha (RH t b f)⟩) :=
  hamiltonian_resolvent_eq_residual_resolvent_shifted_source ε hε h hh hb m g k t a ha (RH t b f)

/-- Unconditional residual-Hamiltonian second resolvent identity on `RH t b f`:
`RS t a (RH t b f) - iteratedHamiltonianResolvent t a b f = exp(2t) • RS t a (K (iteratedHamiltonianResolvent t a b f))`. -/
theorem residual_sub_iteratedHamiltonianResolvent_eq
    (t a b : ℝ) (ha : 0 < a) (f : Hilbert) :
    RS t a (RH t b f) - iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f =
      (Real.exp (2 * t) : ℂ) •
        RS t a (K ⟨iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f,
          resolvent_mem_radial_domain ε hε h hh hb m g k t a ha (RH t b f)⟩) :=
  residual_sub_hamiltonian_resolvent_eq ε hε h hh hb m g k t a ha (RH t b f)

/-- Unconditional radial norm bound for `RS t a (RH t b f) - iteratedHamiltonianResolvent t a b f`. -/
theorem residual_sub_iteratedHamiltonianResolvent_norm_le_radial
    (t a b : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖RS t a (RH t b f) - iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f‖ ≤
      a⁻¹ * Real.exp (2 * t) *
        ‖K ⟨iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f,
          resolvent_mem_radial_domain ε hε h hh hb m g k t a ha (RH t b f)⟩‖ :=
  residual_sub_hamiltonian_resolvent_norm_le_radial ε hε h hh hb m g k t a ha (RH t b f)

/-- Unconditional source norm-square bound for `RS t a (RH t b f) - iteratedHamiltonianResolvent t a b f`:
`‖RS t a (RH t b f) - iteratedHamiltonianResolvent t a b f‖² ≤ (a⁻¹)² * (1 + 2 exp(2t) (h²/ε²) (a⁻¹)²) * (b⁻¹)² * ‖f‖²`. -/
theorem residual_sub_iteratedHamiltonianResolvent_norm_sq_le_source
    (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    ‖RS t a (RH t b f) - iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f‖ ^ 2 ≤
      (a⁻¹) ^ 2 * (1 + 2 * Real.exp (2 * t) * (h ^ 2 / ε ^ 2) * (a⁻¹) ^ 2) *
        (b⁻¹) ^ 2 * ‖f‖ ^ 2 := by
  have h1 := residual_sub_hamiltonian_resolvent_norm_sq_le_source ε hε h hh hb m g k t a ha (RH t b f)
  have h2 : ‖RH t b f‖ ^ 2 ≤ (b⁻¹) ^ 2 * ‖f‖ ^ 2 := by
    have hbnd := resolvent_norm_le ε hε h hh hb m g k t b hb_pos f
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hbnd
    simpa only [mul_pow] using hsq
  have hmul := mul_le_mul_of_nonneg_left h2
    (show 0 ≤ (a⁻¹) ^ 2 * (1 + 2 * Real.exp (2 * t) * (h ^ 2 / ε ^ 2) * (a⁻¹) ^ 2) by positivity)
  exact (h1.trans hmul).trans_eq (by ring)

/-- Unconditional 4-resolvent chain identity on `RH t b f` for all real `m, g, k, t`:
`RP a (RH t b f) - iteratedHamiltonianResolvent t a b f = RP a (K (RG a (RH t b f))) + (RG a (RH t b f) - RS t a (RH t b f)) + exp(2t) • RS t a (K (iteratedHamiltonianResolvent t a b f))`. -/
theorem potential_sub_iteratedHamiltonianResolvent_via_growing_residual_eq
    (t a b : ℝ) (ha : 0 < a) (f : Hilbert) :
    RP a (RH t b f) - iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f =
      RP a (K ⟨RG a (RH t b f),
        KFCausalClockFloorGrowingComponentResolventBounds.resolvent_mem_radial_domain
          ε hε h hh hb m g k a ha (RH t b f)⟩) +
        (RG a (RH t b f) - RS t a (RH t b f)) +
        (Real.exp (2 * t) : ℂ) •
          RS t a (K ⟨iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f,
            resolvent_mem_radial_domain ε hε h hh hb m g k t a ha (RH t b f)⟩) :=
  potential_sub_hamiltonian_via_growing_residual_eq ε hε h hh hb m g k t a ha (RH t b f)

/-- Unconditional radial-root (`Kroot`) norm bound on `iteratedHamiltonianResolvent t a b f`:
because `RH t b f ∈ (Kroot).domain` for EVERY `f : Hilbert`, `Kroot (iteratedHamiltonianResolvent t a b f)`
is bounded in terms of `‖Kroot (RH t b f)‖` and `‖iteratedHamiltonianResolvent t a b f‖`. -/
theorem iteratedHamiltonianResolvent_radialRoot_norm_le
    (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    ‖Kroot ⟨iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f,
      KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_mem_radialRoot_domain
        ε hε h hh hb m g k t a ha (RH t b f)⟩‖ ≤
      ‖Kroot ⟨RH t b f,
        KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_mem_radialRoot_domain
          ε hε h hh hb m g k t b hb_pos f⟩‖ / a +
        (|h| / ε * ‖iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f‖) / Real.sqrt a :=
  hamiltonian_resolvent_radialRoot_norm_le_of_radialRoot ε hε h hh hb m g k t a ha (RH t b f)
    (KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_mem_radialRoot_domain
      ε hε h hh hb m g k t b hb_pos f)

/-- Unconditional radial-root contraction of `RG a` on `RH t b f` for every `f : Hilbert`:
`‖Kroot (RG a (RH t b f))‖ ≤ a⁻¹ * ‖Kroot (RH t b f)‖`. -/
theorem growing_resolvent_on_hamiltonian_resolvent_radialRoot_norm_le
    (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    ‖Kroot ⟨RG a (RH t b f),
      growing_resolvent_mem_radialRoot_domain ε hε h hb hh m g k a ha (RH t b f)⟩‖ ≤
      a⁻¹ * ‖Kroot ⟨RH t b f,
        KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_mem_radialRoot_domain
          ε hε h hh hb m g k t b hb_pos f⟩‖ :=
  growing_resolvent_radialRoot_norm_le_of_rootDomain ε hε h hb hh m g k a ha (RH t b f)
    (KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_mem_radialRoot_domain
      ε hε h hh hb m g k t b hb_pos f)

/-- Unconditional full-strip (`|h| ≤ π * ε / 3`) parabolic radial smoothing bound for
`RG a (RH t b f)` for every `f : Hilbert`:
`‖K (RG a (RH t b f))‖ ≤ min ‖RH t b f‖ (Real.sqrt (a⁻¹) * ‖Kroot (RH t b f)‖)`. -/
theorem growing_resolvent_on_hamiltonian_resolvent_radial_norm_le_min
    (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    ‖K ⟨RG a (RH t b f),
      KFCausalClockFloorGrowingComponentResolventBounds.resolvent_mem_radial_domain
        ε hε h hh hb m g k a ha (RH t b f)⟩‖ ≤
      min ‖RH t b f‖
        (Real.sqrt (a⁻¹) * ‖Kroot ⟨RH t b f,
          KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_mem_radialRoot_domain
            ε hε h hh hb m g k t b hb_pos f⟩‖) :=
  growing_resolvent_radial_norm_le_min_of_rootDomain ε hε h hb hh m g k a ha (RH t b f)
    (KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_mem_radialRoot_domain
      ε hε h hh hb m g k t b hb_pos f)

/-- On the quarter-strip `|h| ≤ π * ε / 4`, because `RH t b f ∈ (K).domain` unconditionally
for every `f : Hilbert`, `RP a (RH t b f)` automatically lies in `(G).domain = (K).domain ⊓ (P).domain`. -/
theorem potential_resolvent_on_hamiltonian_resolvent_mem_growing_domain_quarter_strip
    (hq : |h| ≤ Real.pi * ε / 4) (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let hb' := quarter_le_third ε hε h hq
    let hw' := wide_bound ε hε h hb'
    let u := KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw' m g k t b f
    KFCausalClockFloorPotentialClockResolvent.resolvent ε hε h hh hw' m g k a u ∈
      (KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw' m g k).domain := by
  intro hb' hw' u
  have huK : u ∈ (K).domain :=
    resolvent_mem_radial_domain ε hε h hh hb' m g k t b hb_pos f
  exact KFCausalClockFloorPotentialResolventRadialRegularity.resolvent_growing_domain
    ε hε h hb' hh m g k hq a ha u huK

/-- On the quarter-strip `|h| ≤ π * ε / 4`, because `RH t b f ∈ (K).domain` unconditionally
for every `f : Hilbert`, `RG a (RH t b f)` satisfies the maximal radial contraction
`‖K (RG a (RH t b f))‖ ≤ min ‖RH t b f‖ (a⁻¹ * ‖K (RH t b f)‖)`. -/
theorem growing_resolvent_on_hamiltonian_resolvent_radial_norm_le_min_quarter_strip
    (hq : |h| ≤ Real.pi * ε / 4) (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let hb' := quarter_le_third ε hε h hq
    let hw' := wide_bound ε hε h hb'
    let u := KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw' m g k t b f
    let huK : u ∈ (K).domain :=
      resolvent_mem_radial_domain ε hε h hh hb' m g k t b hb_pos f
    ‖K ⟨KFCausalClockFloorGrowingYosida.resolvent ε hε h hh hw' m g k a u,
      KFCausalClockFloorGrowingComponentResolventBounds.resolvent_mem_radial_domain
        ε hε h hh hb' m g k a ha u⟩‖ ≤
      min ‖u‖ (a⁻¹ * ‖K ⟨u, huK⟩‖) := by
  intro hb' hw' u huK
  exact growing_resolvent_radial_norm_le_min_of_radialDomain
    ε hε h hh m g k hq a ha u huK

/-! ### 3. Unconditional 5-Way Common-Domain Equivalence and 3-Operator Synthesis on `iteratedHamiltonianResolvent` -/

/-- Unconditional 5-way operator-domain equivalence for `iteratedHamiltonianResolvent t a b f`:
membership in `(P).domain`, `(T).domain`, `(G).domain`, `commonOperatorDomain`, and
shifted residual resolvent membership in `(P).domain` are all equivalent for all real `m, g, k, t`. -/
theorem iteratedHamiltonianResolvent_five_way_domain_iff
    (t a b : ℝ) (ha : 0 < a) (f : Hilbert) :
    let x := iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f
    (x ∈ (P).domain ↔ x ∈ (T).domain) ∧
    (x ∈ (T).domain ↔ x ∈ (G).domain) ∧
    (x ∈ (G).domain ↔ x ∈ commonOperatorDomain ε hε h hh hb m g k) ∧
    (x ∈ commonOperatorDomain ε hε h hh hb m g k ↔
      RS t a (RH t b f - (Real.exp (2 * t) : ℂ) •
        K ⟨x, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha (RH t b f)⟩) ∈ (P).domain) :=
  hamiltonian_resolvent_five_way_domain_iff ε hε h hh hb m g k t a ha (RH t b f)

/-- Unconditionally for all real `m, g, k, t`, `0 < a`, `0 < b`, and every `z : commonOperatorDomain`,
applying `iteratedHamiltonianResolvent t a b` to the doubly shifted source
`(H t + b I)((H t + a I) z)` recovers `z : Hilbert` and hence lies in `commonOperatorDomain`. -/
theorem iteratedHamiltonianResolvent_on_shifted_common_eq
    (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b)
    (z : commonOperatorDomain ε hε h hh hb m g k)
    (hz2 : H t ⟨(z : Hilbert),
      common_domain_subset_hamiltonian ε hε h hh hb m g k t z.property⟩ +
      a • (z : Hilbert) ∈ (H t).domain) :
    let zH : (H t).domain :=
      ⟨(z : Hilbert), common_domain_subset_hamiltonian ε hε h hh hb m g k t z.property⟩
    let wH : (H t).domain := ⟨H t zH + a • (z : Hilbert), hz2⟩
    iteratedHamiltonianResolvent ε hε h hh hb m g k t a b
      (H t wH + b • (wH : Hilbert)) = (z : Hilbert) ∧
    iteratedHamiltonianResolvent ε hε h hh hb m g k t a b
      (H t wH + b • (wH : Hilbert)) ∈ commonOperatorDomain ε hε h hh hb m g k := by
  intro zH wH
  have h1 : RH t b (H t wH + b • (wH : Hilbert)) = (wH : Hilbert) :=
    KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t b hb_pos wH
  have h2 : RH t a (H t zH + a • (z : Hilbert)) = (z : Hilbert) :=
    KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t a ha zH
  have heq : iteratedHamiltonianResolvent ε hε h hh hb m g k t a b
      (H t wH + b • (wH : Hilbert)) = (z : Hilbert) := by
    change RH t a (RH t b (H t wH + b • (wH : Hilbert))) = (z : Hilbert)
    rw [h1]
    exact h2
  exact ⟨heq, heq.symm ▸ z.property⟩

/-- Exact 3-operator decomposition `H t x = T x + exp(2t) • (K x + P x)` on
`x := iteratedHamiltonianResolvent t a b f` whenever `x ∈ (P).domain` (for all real `m, g, k, t`). -/
theorem iteratedHamiltonianResolvent_eq_three_operator_of_potential
    (t a b : ℝ) (ha : 0 < a) (f : Hilbert)
    (hp : iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f ∈ (P).domain) :
    let x := iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f
    let hc : x ∈ commonOperatorDomain ε hε h hh hb m g k :=
      (hamiltonian_resolvent_mem_potential_iff_common ε hε h hh hb m g k t a ha (RH t b f)).mp hp
    let ht : x ∈ (T).domain := hc.1.1.1
    H t ⟨x, resolvent_mem_hamiltonian_domain ε hε h hh hb m g k t a ha (RH t b f)⟩ =
      T ⟨x, ht⟩ +
        (Real.exp (2 * t) : ℂ) •
          (K ⟨x, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha (RH t b f)⟩ +
            P ⟨x, hp⟩) :=
  hamiltonian_resolvent_eq_three_operator_of_potential ε hε h hh hb m g k t a ha (RH t b f) hp

/-- Exact static-Hamiltonian second resolvent identity on `RH t b f` whenever
`iteratedHamiltonianResolvent t a b f ∈ (P).domain`:
`RT a (RH t b f) - iteratedHamiltonianResolvent t a b f = exp(2t) • RT a (G (iteratedHamiltonianResolvent t a b f))`. -/
theorem static_sub_iteratedHamiltonianResolvent_eq_of_potential
    (t a b : ℝ) (ha : 0 < a) (f : Hilbert)
    (hp : iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f ∈ (P).domain) :
    let x := iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f
    RT a (RH t b f) - x =
      (Real.exp (2 * t) : ℂ) •
        RT a (G ⟨x,
          hamiltonian_resolvent_mem_growing_of_potential ε hε h hh hb m g k t a ha (RH t b f) hp⟩) :=
  static_sub_hamiltonian_resolvent_eq ε hε h hh hb m g k t a ha (RH t b f) hp

/-- Exact 3-operator static-Hamiltonian second resolvent decomposition on `RH t b f` whenever
`iteratedHamiltonianResolvent t a b f ∈ (P).domain`:
`RT a (RH t b f) - iteratedHamiltonianResolvent t a b f = exp(2t) • RT a (K x) + exp(2t) • RT a (P x)`. -/
theorem static_sub_iteratedHamiltonianResolvent_eq_radial_add_potential_of_potential
    (t a b : ℝ) (ha : 0 < a) (f : Hilbert)
    (hp : iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f ∈ (P).domain) :
    let x := iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f
    RT a (RH t b f) - x =
      (Real.exp (2 * t) : ℂ) •
        RT a (K ⟨x, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha (RH t b f)⟩) +
      (Real.exp (2 * t) : ℂ) • RT a (P ⟨x, hp⟩) :=
  static_sub_hamiltonian_resolvent_eq_radial_add_potential ε hε h hh hb m g k t a ha (RH t b f) hp

#print axioms iteratedHamiltonianResolvent_eq
#print axioms squaredHamiltonianResolvent_eq
#print axioms iteratedHamiltonianResolvent_mem_secondPowerDomain
#print axioms iteratedHamiltonianResolvent_mem_secondPowerGraph
#print axioms iteratedHamiltonianResolvent_mem_ten_domains
#print axioms iteratedHamiltonianResolvent_first_power_mem_ten_domains
#print axioms iteratedHamiltonianResolvent_mem_radial_residual_domain
#print axioms iteratedHamiltonianResolvent_first_power_mem_radial_residual_domain
#print axioms iteratedHamiltonianResolvent_hamiltonian_eq_radial_add_residual
#print axioms iteratedHamiltonianResolvent_residual_eq_shifted_sub_radial
#print axioms iteratedHamiltonianResolvent_first_power_hamiltonian_eq_radial_add_residual
#print axioms iteratedHamiltonianResolvent_second_power_radial_residual_eq
#print axioms squaredHamiltonianResolvent_second_power_radial_residual_eq
#print axioms iteratedHamiltonianResolvent_component_norm_sq_le_source
#print axioms iteratedHamiltonianResolvent_radial_norm_sq_le_source
#print axioms iteratedHamiltonianResolvent_residual_norm_sq_le_source
#print axioms iteratedHamiltonianResolvent_first_power_component_norm_sq_le_source
#print axioms iteratedHamiltonianResolvent_eq_residual_resolvent_shifted_source
#print axioms residual_sub_iteratedHamiltonianResolvent_eq
#print axioms residual_sub_iteratedHamiltonianResolvent_norm_le_radial
#print axioms residual_sub_iteratedHamiltonianResolvent_norm_sq_le_source
#print axioms potential_sub_iteratedHamiltonianResolvent_via_growing_residual_eq
#print axioms iteratedHamiltonianResolvent_radialRoot_norm_le
#print axioms growing_resolvent_on_hamiltonian_resolvent_radialRoot_norm_le
#print axioms growing_resolvent_on_hamiltonian_resolvent_radial_norm_le_min
#print axioms potential_resolvent_on_hamiltonian_resolvent_mem_growing_domain_quarter_strip
#print axioms growing_resolvent_on_hamiltonian_resolvent_radial_norm_le_min_quarter_strip
#print axioms iteratedHamiltonianResolvent_five_way_domain_iff
#print axioms iteratedHamiltonianResolvent_on_shifted_common_eq
#print axioms iteratedHamiltonianResolvent_eq_three_operator_of_potential
#print axioms static_sub_iteratedHamiltonianResolvent_eq_of_potential
#print axioms static_sub_iteratedHamiltonianResolvent_eq_radial_add_potential_of_potential

end

end UnifiedTheory.Audit.KFCausalClockFloorIteratedHamiltonianResolventUnconditionalDomination
