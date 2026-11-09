/- Five-Operator Nine-Parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param)` Higher-Power
Nonagon Cocycle, Eight-Term Path Decomposition, and `Dom(A^{r+2})` Regularity Across All Five
Clock-Floor Hamiltonians `T`, `P`, `G`, `S(t)`, and `H(t)`. -/
import UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorEightParameterHigherPowerOctagonCocycleAndYosida
import UnifiedTheory.Audit.KFCausalClockFloorHigherPowerYosidaGraphConvergence

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorNineParameterHigherPowerNonagonCocycleAndYosida

noncomputable section

open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalPositiveResolventBounds (Resolves)
open KFCausalClockFloorStaticResolventRadialCommutator
  (staticOperator_positive staticResolvent staticResolvent_resolves staticResolvent_left_inverse)
open KFCausalClockFloorHigherPowerOperatorCores
  (operatorPowerDomain iteratedResolventPower
   iteratedResolventPower_mem_operatorPowerDomain
   iteratedResolventPower_norm_bound
   staticPowerDomain potentialPowerDomain growingPowerDomain
   residualPowerDomain hamiltonianPowerDomain)
open KFCausalClockFloorHigherPowerYosidaGraphConvergence
  (iteratedIdentityPower iteratedIdentityPower_mem_operatorPowerDomain
   iteratedIdentityPower_norm_le)

section AbstractNineParameterHigherPowerNonagon

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Difference of `(r + 1)`-fold iterated resolvents `R_a^{r+1} f - R_b^{r+1} f`. -/
def higherPowerResolventSub (Ra Rb : H →L[ℂ] H) (r : ℕ) (f : H) : H :=
  iteratedResolventPower Ra (r + 1) f - iteratedResolventPower Rb (r + 1) f

/-- Difference of `(r + 1)`-fold Yosida identity powers `(a • R_a)^{r+1} f - (b • R_b)^{r+1} f`. -/
def higherPowerIdentityPowerSub (Ra Rb : H →L[ℂ] H) (a b : ℝ) (r : ℕ) (f : H) : H :=
  iteratedIdentityPower Ra a (r + 1) f - iteratedIdentityPower Rb b (r + 1) f

/-- Abstract nine-parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param)` higher-power
nonagon path decomposition, cyclic nine-step nonagon cocycle vanishing, `operatorPowerDomain A (r + 2)`
membership, and direct + nonagon triangle norm bounds for `higherPowerResolventSub` and
`higherPowerIdentityPowerSub`. -/
theorem higherPowerResolvent_and_identity_nine_parameter_nonagon_cocycle_and_regularity
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H)
    (a b c d e f_param g_param h_param i_param : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param) (hi_p : 0 < i_param)
    (hr : ∀ u, 0 < u → Resolves A (R u) u)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (_hl : ∀ u, 0 < u → ∀ z : A.domain, R u (A z + u • (z : H)) = (z : H))
    (r : ℕ) (f : H) :
    higherPowerResolventSub (R a) (R i_param) (r + 1) f =
      higherPowerResolventSub (R a) (R b) (r + 1) f +
      higherPowerResolventSub (R b) (R c) (r + 1) f +
      higherPowerResolventSub (R c) (R d) (r + 1) f +
      higherPowerResolventSub (R d) (R e) (r + 1) f +
      higherPowerResolventSub (R e) (R f_param) (r + 1) f +
      higherPowerResolventSub (R f_param) (R g_param) (r + 1) f +
      higherPowerResolventSub (R g_param) (R h_param) (r + 1) f +
      higherPowerResolventSub (R h_param) (R i_param) (r + 1) f ∧
    higherPowerResolventSub (R a) (R b) (r + 1) f +
      higherPowerResolventSub (R b) (R c) (r + 1) f +
      higherPowerResolventSub (R c) (R d) (r + 1) f +
      higherPowerResolventSub (R d) (R e) (r + 1) f +
      higherPowerResolventSub (R e) (R f_param) (r + 1) f +
      higherPowerResolventSub (R f_param) (R g_param) (r + 1) f +
      higherPowerResolventSub (R g_param) (R h_param) (r + 1) f +
      higherPowerResolventSub (R h_param) (R i_param) (r + 1) f +
      higherPowerResolventSub (R i_param) (R a) (r + 1) f = 0 ∧
    higherPowerIdentityPowerSub (R a) (R i_param) a i_param (r + 1) f =
      higherPowerIdentityPowerSub (R a) (R b) a b (r + 1) f +
      higherPowerIdentityPowerSub (R b) (R c) b c (r + 1) f +
      higherPowerIdentityPowerSub (R c) (R d) c d (r + 1) f +
      higherPowerIdentityPowerSub (R d) (R e) d e (r + 1) f +
      higherPowerIdentityPowerSub (R e) (R f_param) e f_param (r + 1) f +
      higherPowerIdentityPowerSub (R f_param) (R g_param) f_param g_param (r + 1) f +
      higherPowerIdentityPowerSub (R g_param) (R h_param) g_param h_param (r + 1) f +
      higherPowerIdentityPowerSub (R h_param) (R i_param) h_param i_param (r + 1) f ∧
    higherPowerIdentityPowerSub (R a) (R b) a b (r + 1) f +
      higherPowerIdentityPowerSub (R b) (R c) b c (r + 1) f +
      higherPowerIdentityPowerSub (R c) (R d) c d (r + 1) f +
      higherPowerIdentityPowerSub (R d) (R e) d e (r + 1) f +
      higherPowerIdentityPowerSub (R e) (R f_param) e f_param (r + 1) f +
      higherPowerIdentityPowerSub (R f_param) (R g_param) f_param g_param (r + 1) f +
      higherPowerIdentityPowerSub (R g_param) (R h_param) g_param h_param (r + 1) f +
      higherPowerIdentityPowerSub (R h_param) (R i_param) h_param i_param (r + 1) f +
      higherPowerIdentityPowerSub (R i_param) (R a) i_param a (r + 1) f = 0 ∧
    higherPowerResolventSub (R a) (R i_param) (r + 1) f ∈ operatorPowerDomain A (r + 2) ∧
    higherPowerIdentityPowerSub (R a) (R i_param) a i_param (r + 1) f ∈
      operatorPowerDomain A (r + 2) ∧
    ‖higherPowerResolventSub (R a) (R i_param) (r + 1) f‖ ≤
      ((a⁻¹) ^ (r + 2) + (i_param⁻¹) ^ (r + 2)) * ‖f‖ ∧
    ‖higherPowerResolventSub (R a) (R i_param) (r + 1) f‖ ≤
      ((a⁻¹) ^ (r + 2) + 2 * (b⁻¹) ^ (r + 2) + 2 * (c⁻¹) ^ (r + 2) +
        2 * (d⁻¹) ^ (r + 2) + 2 * (e⁻¹) ^ (r + 2) + 2 * (f_param⁻¹) ^ (r + 2) +
        2 * (g_param⁻¹) ^ (r + 2) + 2 * (h_param⁻¹) ^ (r + 2) + (i_param⁻¹) ^ (r + 2)) * ‖f‖ ∧
    ‖higherPowerIdentityPowerSub (R a) (R i_param) a i_param (r + 1) f‖ ≤ 2 * ‖f‖ := by
  have h1 :
      higherPowerResolventSub (R a) (R i_param) (r + 1) f =
        higherPowerResolventSub (R a) (R b) (r + 1) f +
        higherPowerResolventSub (R b) (R c) (r + 1) f +
        higherPowerResolventSub (R c) (R d) (r + 1) f +
        higherPowerResolventSub (R d) (R e) (r + 1) f +
        higherPowerResolventSub (R e) (R f_param) (r + 1) f +
        higherPowerResolventSub (R f_param) (R g_param) (r + 1) f +
        higherPowerResolventSub (R g_param) (R h_param) (r + 1) f +
        higherPowerResolventSub (R h_param) (R i_param) (r + 1) f := by
    unfold higherPowerResolventSub
    abel
  have h2 :
      higherPowerResolventSub (R a) (R b) (r + 1) f +
        higherPowerResolventSub (R b) (R c) (r + 1) f +
        higherPowerResolventSub (R c) (R d) (r + 1) f +
        higherPowerResolventSub (R d) (R e) (r + 1) f +
        higherPowerResolventSub (R e) (R f_param) (r + 1) f +
        higherPowerResolventSub (R f_param) (R g_param) (r + 1) f +
        higherPowerResolventSub (R g_param) (R h_param) (r + 1) f +
        higherPowerResolventSub (R h_param) (R i_param) (r + 1) f +
        higherPowerResolventSub (R i_param) (R a) (r + 1) f = 0 := by
    unfold higherPowerResolventSub
    abel
  have h3 :
      higherPowerIdentityPowerSub (R a) (R i_param) a i_param (r + 1) f =
        higherPowerIdentityPowerSub (R a) (R b) a b (r + 1) f +
        higherPowerIdentityPowerSub (R b) (R c) b c (r + 1) f +
        higherPowerIdentityPowerSub (R c) (R d) c d (r + 1) f +
        higherPowerIdentityPowerSub (R d) (R e) d e (r + 1) f +
        higherPowerIdentityPowerSub (R e) (R f_param) e f_param (r + 1) f +
        higherPowerIdentityPowerSub (R f_param) (R g_param) f_param g_param (r + 1) f +
        higherPowerIdentityPowerSub (R g_param) (R h_param) g_param h_param (r + 1) f +
        higherPowerIdentityPowerSub (R h_param) (R i_param) h_param i_param (r + 1) f := by
    unfold higherPowerIdentityPowerSub
    abel
  have h4 :
      higherPowerIdentityPowerSub (R a) (R b) a b (r + 1) f +
        higherPowerIdentityPowerSub (R b) (R c) b c (r + 1) f +
        higherPowerIdentityPowerSub (R c) (R d) c d (r + 1) f +
        higherPowerIdentityPowerSub (R d) (R e) d e (r + 1) f +
        higherPowerIdentityPowerSub (R e) (R f_param) e f_param (r + 1) f +
        higherPowerIdentityPowerSub (R f_param) (R g_param) f_param g_param (r + 1) f +
        higherPowerIdentityPowerSub (R g_param) (R h_param) g_param h_param (r + 1) f +
        higherPowerIdentityPowerSub (R h_param) (R i_param) h_param i_param (r + 1) f +
        higherPowerIdentityPowerSub (R i_param) (R a) i_param a (r + 1) f = 0 := by
    unfold higherPowerIdentityPowerSub
    abel
  have hmem_res :
      higherPowerResolventSub (R a) (R i_param) (r + 1) f ∈ operatorPowerDomain A (r + 2) :=
    (operatorPowerDomain A (r + 2)).sub_mem
      (iteratedResolventPower_mem_operatorPowerDomain A (R a) a (hr a ha) (r + 2) f)
      (iteratedResolventPower_mem_operatorPowerDomain A (R i_param) i_param (hr i_param hi_p) (r + 2) f)
  have hmem_id :
      higherPowerIdentityPowerSub (R a) (R i_param) a i_param (r + 1) f ∈
        operatorPowerDomain A (r + 2) :=
    (operatorPowerDomain A (r + 2)).sub_mem
      (iteratedIdentityPower_mem_operatorPowerDomain A (R a) a (hr a ha) (r + 2) f)
      (iteratedIdentityPower_mem_operatorPowerDomain A (R i_param) i_param (hr i_param hi_p) (r + 2) f)
  have hna := iteratedResolventPower_norm_bound A (R a) a ha (hr a ha) hp (r + 2) f
  have hni := iteratedResolventPower_norm_bound A (R i_param) i_param hi_p (hr i_param hi_p) hp (r + 2) f
  have hbd_ai :
      ‖higherPowerResolventSub (R a) (R i_param) (r + 1) f‖ ≤
        ((a⁻¹) ^ (r + 2) + (i_param⁻¹) ^ (r + 2)) * ‖f‖ := by
    have htri := norm_sub_le
      (iteratedResolventPower (R a) (r + 2) f)
      (iteratedResolventPower (R i_param) (r + 2) f)
    change ‖iteratedResolventPower (R a) (r + 2) f -
      iteratedResolventPower (R i_param) (r + 2) f‖ ≤ _
    linarith
  have hpos_mid :
      0 ≤ (2 * (b⁻¹) ^ (r + 2) + 2 * (c⁻¹) ^ (r + 2) +
        2 * (d⁻¹) ^ (r + 2) + 2 * (e⁻¹) ^ (r + 2) + 2 * (f_param⁻¹) ^ (r + 2) +
        2 * (g_param⁻¹) ^ (r + 2) + 2 * (h_param⁻¹) ^ (r + 2)) * ‖f‖ := by
    positivity
  have hbd_nonagon :
      ‖higherPowerResolventSub (R a) (R i_param) (r + 1) f‖ ≤
        ((a⁻¹) ^ (r + 2) + 2 * (b⁻¹) ^ (r + 2) + 2 * (c⁻¹) ^ (r + 2) +
          2 * (d⁻¹) ^ (r + 2) + 2 * (e⁻¹) ^ (r + 2) + 2 * (f_param⁻¹) ^ (r + 2) +
          2 * (g_param⁻¹) ^ (r + 2) + 2 * (h_param⁻¹) ^ (r + 2) + (i_param⁻¹) ^ (r + 2)) * ‖f‖ := by
    linarith [hbd_ai, hpos_mid]
  have hida := iteratedIdentityPower_norm_le A (R a) a ha (hr a ha) hp (r + 2) f
  have hidi := iteratedIdentityPower_norm_le A (R i_param) i_param hi_p (hr i_param hi_p) hp (r + 2) f
  have hbd_id :
      ‖higherPowerIdentityPowerSub (R a) (R i_param) a i_param (r + 1) f‖ ≤ 2 * ‖f‖ := by
    have htri := norm_sub_le
      (iteratedIdentityPower (R a) a (r + 2) f)
      (iteratedIdentityPower (R i_param) i_param (r + 2) f)
    change ‖iteratedIdentityPower (R a) a (r + 2) f -
      iteratedIdentityPower (R i_param) i_param (r + 2) f‖ ≤ 2 * ‖f‖
    linarith
  exact ⟨h1, h2, h3, h4, hmem_res, hmem_id, hbd_ai, hbd_nonagon, hbd_id⟩

end AbstractNineParameterHigherPowerNonagon

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "SD" => KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RT" => staticResolvent ε hε h hb hh
local notation "RP" => KFCausalClockFloorPotentialClockResolvent.resolvent ε hε h hh hw m g k
local notation "RG" => KFCausalClockFloorGrowingYosida.resolvent ε hε h hh hw m g k
local notation "RS" => KFCausalClockFloorResidualClockCore.resolvent ε hε h hh hw m g k
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k

/-- Nine-parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param)` higher-power nonagon
cocycle and `staticPowerDomain ε hε h (r + 2)` regularity for `T`. -/
theorem static_higherPower_nine_parameter_nonagon_package
    (a b c d e f_param g_param h_param i_param : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param) (hi_p : 0 < i_param)
    (r : ℕ) (f : Hilbert) :
    higherPowerResolventSub (RT a) (RT i_param) (r + 1) f =
      higherPowerResolventSub (RT a) (RT b) (r + 1) f +
      higherPowerResolventSub (RT b) (RT c) (r + 1) f +
      higherPowerResolventSub (RT c) (RT d) (r + 1) f +
      higherPowerResolventSub (RT d) (RT e) (r + 1) f +
      higherPowerResolventSub (RT e) (RT f_param) (r + 1) f +
      higherPowerResolventSub (RT f_param) (RT g_param) (r + 1) f +
      higherPowerResolventSub (RT g_param) (RT h_param) (r + 1) f +
      higherPowerResolventSub (RT h_param) (RT i_param) (r + 1) f ∧
    higherPowerResolventSub (RT a) (RT b) (r + 1) f +
      higherPowerResolventSub (RT b) (RT c) (r + 1) f +
      higherPowerResolventSub (RT c) (RT d) (r + 1) f +
      higherPowerResolventSub (RT d) (RT e) (r + 1) f +
      higherPowerResolventSub (RT e) (RT f_param) (r + 1) f +
      higherPowerResolventSub (RT f_param) (RT g_param) (r + 1) f +
      higherPowerResolventSub (RT g_param) (RT h_param) (r + 1) f +
      higherPowerResolventSub (RT h_param) (RT i_param) (r + 1) f +
      higherPowerResolventSub (RT i_param) (RT a) (r + 1) f = 0 ∧
    higherPowerResolventSub (RT a) (RT i_param) (r + 1) f ∈ staticPowerDomain ε hε h (r + 2) ∧
    higherPowerIdentityPowerSub (RT a) (RT i_param) a i_param (r + 1) f ∈
      staticPowerDomain ε hε h (r + 2) ∧
    ‖higherPowerResolventSub (RT a) (RT i_param) (r + 1) f‖ ≤
      ((a⁻¹) ^ (r + 2) + (i_param⁻¹) ^ (r + 2)) * ‖f‖ ∧
    ‖higherPowerIdentityPowerSub (RT a) (RT i_param) a i_param (r + 1) f‖ ≤ 2 * ‖f‖ := by
  have hpkg := higherPowerResolvent_and_identity_nine_parameter_nonagon_cocycle_and_regularity
    T RT a b c d e f_param g_param h_param i_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p
    (staticResolvent_resolves ε hε h hb hh)
    (staticOperator_positive ε hε h)
    (staticResolvent_left_inverse ε hε h hb hh) r f
  exact ⟨hpkg.1, hpkg.2.1, hpkg.2.2.2.2.1, hpkg.2.2.2.2.2.1,
    hpkg.2.2.2.2.2.2.1, hpkg.2.2.2.2.2.2.2.2⟩

/-- Nine-parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param)` higher-power nonagon
cocycle and `potentialPowerDomain ε hε h hh hb m g k (r + 2)` regularity for `P`. -/
theorem potential_higherPower_nine_parameter_nonagon_package
    (a b c d e f_param g_param h_param i_param : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param) (hi_p : 0 < i_param)
    (r : ℕ) (f : Hilbert) :
    higherPowerResolventSub (RP a) (RP i_param) (r + 1) f =
      higherPowerResolventSub (RP a) (RP b) (r + 1) f +
      higherPowerResolventSub (RP b) (RP c) (r + 1) f +
      higherPowerResolventSub (RP c) (RP d) (r + 1) f +
      higherPowerResolventSub (RP d) (RP e) (r + 1) f +
      higherPowerResolventSub (RP e) (RP f_param) (r + 1) f +
      higherPowerResolventSub (RP f_param) (RP g_param) (r + 1) f +
      higherPowerResolventSub (RP g_param) (RP h_param) (r + 1) f +
      higherPowerResolventSub (RP h_param) (RP i_param) (r + 1) f ∧
    higherPowerResolventSub (RP a) (RP b) (r + 1) f +
      higherPowerResolventSub (RP b) (RP c) (r + 1) f +
      higherPowerResolventSub (RP c) (RP d) (r + 1) f +
      higherPowerResolventSub (RP d) (RP e) (r + 1) f +
      higherPowerResolventSub (RP e) (RP f_param) (r + 1) f +
      higherPowerResolventSub (RP f_param) (RP g_param) (r + 1) f +
      higherPowerResolventSub (RP g_param) (RP h_param) (r + 1) f +
      higherPowerResolventSub (RP h_param) (RP i_param) (r + 1) f +
      higherPowerResolventSub (RP i_param) (RP a) (r + 1) f = 0 ∧
    higherPowerResolventSub (RP a) (RP i_param) (r + 1) f ∈
      potentialPowerDomain ε hε h hh hb m g k (r + 2) ∧
    higherPowerIdentityPowerSub (RP a) (RP i_param) a i_param (r + 1) f ∈
      potentialPowerDomain ε hε h hh hb m g k (r + 2) ∧
    ‖higherPowerResolventSub (RP a) (RP i_param) (r + 1) f‖ ≤
      ((a⁻¹) ^ (r + 2) + (i_param⁻¹) ^ (r + 2)) * ‖f‖ ∧
    ‖higherPowerIdentityPowerSub (RP a) (RP i_param) a i_param (r + 1) f‖ ≤ 2 * ‖f‖ := by
  have hpkg := higherPowerResolvent_and_identity_nine_parameter_nonagon_cocycle_and_regularity
    P RP a b c d e f_param g_param h_param i_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k)
    (KFCausalClosedGraphForm.hamiltonian_positive PD)
    (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k) r f
  exact ⟨hpkg.1, hpkg.2.1, hpkg.2.2.2.2.1, hpkg.2.2.2.2.2.1,
    hpkg.2.2.2.2.2.2.1, hpkg.2.2.2.2.2.2.2.2⟩

/-- Nine-parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param)` higher-power nonagon
cocycle and `growingPowerDomain ε hε h hh hb m g k (r + 2)` regularity for `G`. -/
theorem growing_higherPower_nine_parameter_nonagon_package
    (a b c d e f_param g_param h_param i_param : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param) (hi_p : 0 < i_param)
    (r : ℕ) (f : Hilbert) :
    higherPowerResolventSub (RG a) (RG i_param) (r + 1) f =
      higherPowerResolventSub (RG a) (RG b) (r + 1) f +
      higherPowerResolventSub (RG b) (RG c) (r + 1) f +
      higherPowerResolventSub (RG c) (RG d) (r + 1) f +
      higherPowerResolventSub (RG d) (RG e) (r + 1) f +
      higherPowerResolventSub (RG e) (RG f_param) (r + 1) f +
      higherPowerResolventSub (RG f_param) (RG g_param) (r + 1) f +
      higherPowerResolventSub (RG g_param) (RG h_param) (r + 1) f +
      higherPowerResolventSub (RG h_param) (RG i_param) (r + 1) f ∧
    higherPowerResolventSub (RG a) (RG b) (r + 1) f +
      higherPowerResolventSub (RG b) (RG c) (r + 1) f +
      higherPowerResolventSub (RG c) (RG d) (r + 1) f +
      higherPowerResolventSub (RG d) (RG e) (r + 1) f +
      higherPowerResolventSub (RG e) (RG f_param) (r + 1) f +
      higherPowerResolventSub (RG f_param) (RG g_param) (r + 1) f +
      higherPowerResolventSub (RG g_param) (RG h_param) (r + 1) f +
      higherPowerResolventSub (RG h_param) (RG i_param) (r + 1) f +
      higherPowerResolventSub (RG i_param) (RG a) (r + 1) f = 0 ∧
    higherPowerResolventSub (RG a) (RG i_param) (r + 1) f ∈
      growingPowerDomain ε hε h hh hb m g k (r + 2) ∧
    higherPowerIdentityPowerSub (RG a) (RG i_param) a i_param (r + 1) f ∈
      growingPowerDomain ε hε h hh hb m g k (r + 2) ∧
    ‖higherPowerResolventSub (RG a) (RG i_param) (r + 1) f‖ ≤
      ((a⁻¹) ^ (r + 2) + (i_param⁻¹) ^ (r + 2)) * ‖f‖ ∧
    ‖higherPowerIdentityPowerSub (RG a) (RG i_param) a i_param (r + 1) f‖ ≤ 2 * ‖f‖ := by
  have hpkg := higherPowerResolvent_and_identity_nine_parameter_nonagon_cocycle_and_regularity
    G RG a b c d e f_param g_param h_param i_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k)
    (KFCausalClosedGraphForm.hamiltonian_positive
      (KFCausalClockFloorGrowingHamiltonian.formData ε hε h hh hw m g k))
    (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k) r f
  exact ⟨hpkg.1, hpkg.2.1, hpkg.2.2.2.2.1, hpkg.2.2.2.2.2.1,
    hpkg.2.2.2.2.2.2.1, hpkg.2.2.2.2.2.2.2.2⟩

/-- Nine-parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param)` higher-power nonagon
cocycle and `residualPowerDomain ε hε h hh hb m g k t (r + 2)` regularity for `S(t)`. -/
theorem residual_higherPower_nine_parameter_nonagon_package
    (t a b c d e f_param g_param h_param i_param : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param) (hi_p : 0 < i_param)
    (r : ℕ) (f : Hilbert) :
    higherPowerResolventSub (RS t a) (RS t i_param) (r + 1) f =
      higherPowerResolventSub (RS t a) (RS t b) (r + 1) f +
      higherPowerResolventSub (RS t b) (RS t c) (r + 1) f +
      higherPowerResolventSub (RS t c) (RS t d) (r + 1) f +
      higherPowerResolventSub (RS t d) (RS t e) (r + 1) f +
      higherPowerResolventSub (RS t e) (RS t f_param) (r + 1) f +
      higherPowerResolventSub (RS t f_param) (RS t g_param) (r + 1) f +
      higherPowerResolventSub (RS t g_param) (RS t h_param) (r + 1) f +
      higherPowerResolventSub (RS t h_param) (RS t i_param) (r + 1) f ∧
    higherPowerResolventSub (RS t a) (RS t b) (r + 1) f +
      higherPowerResolventSub (RS t b) (RS t c) (r + 1) f +
      higherPowerResolventSub (RS t c) (RS t d) (r + 1) f +
      higherPowerResolventSub (RS t d) (RS t e) (r + 1) f +
      higherPowerResolventSub (RS t e) (RS t f_param) (r + 1) f +
      higherPowerResolventSub (RS t f_param) (RS t g_param) (r + 1) f +
      higherPowerResolventSub (RS t g_param) (RS t h_param) (r + 1) f +
      higherPowerResolventSub (RS t h_param) (RS t i_param) (r + 1) f +
      higherPowerResolventSub (RS t i_param) (RS t a) (r + 1) f = 0 ∧
    higherPowerResolventSub (RS t a) (RS t i_param) (r + 1) f ∈
      residualPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    higherPowerIdentityPowerSub (RS t a) (RS t i_param) a i_param (r + 1) f ∈
      residualPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    ‖higherPowerResolventSub (RS t a) (RS t i_param) (r + 1) f‖ ≤
      ((a⁻¹) ^ (r + 2) + (i_param⁻¹) ^ (r + 2)) * ‖f‖ ∧
    ‖higherPowerIdentityPowerSub (RS t a) (RS t i_param) a i_param (r + 1) f‖ ≤ 2 * ‖f‖ := by
  have hpkg := higherPowerResolvent_and_identity_nine_parameter_nonagon_cocycle_and_regularity
    (S t) (RS t) a b c d e f_param g_param h_param i_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t)
    (KFCausalClosedGraphForm.hamiltonian_positive (SD t))
    (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t) r f
  exact ⟨hpkg.1, hpkg.2.1, hpkg.2.2.2.2.1, hpkg.2.2.2.2.2.1,
    hpkg.2.2.2.2.2.2.1, hpkg.2.2.2.2.2.2.2.2⟩

/-- Nine-parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param)` higher-power nonagon
cocycle and `hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2)` regularity for `H(t)`. -/
theorem hamiltonian_higherPower_nine_parameter_nonagon_package
    (t a b c d e f_param g_param h_param i_param : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param) (hi_p : 0 < i_param)
    (r : ℕ) (f : Hilbert) :
    higherPowerResolventSub (RH t a) (RH t i_param) (r + 1) f =
      higherPowerResolventSub (RH t a) (RH t b) (r + 1) f +
      higherPowerResolventSub (RH t b) (RH t c) (r + 1) f +
      higherPowerResolventSub (RH t c) (RH t d) (r + 1) f +
      higherPowerResolventSub (RH t d) (RH t e) (r + 1) f +
      higherPowerResolventSub (RH t e) (RH t f_param) (r + 1) f +
      higherPowerResolventSub (RH t f_param) (RH t g_param) (r + 1) f +
      higherPowerResolventSub (RH t g_param) (RH t h_param) (r + 1) f +
      higherPowerResolventSub (RH t h_param) (RH t i_param) (r + 1) f ∧
    higherPowerResolventSub (RH t a) (RH t b) (r + 1) f +
      higherPowerResolventSub (RH t b) (RH t c) (r + 1) f +
      higherPowerResolventSub (RH t c) (RH t d) (r + 1) f +
      higherPowerResolventSub (RH t d) (RH t e) (r + 1) f +
      higherPowerResolventSub (RH t e) (RH t f_param) (r + 1) f +
      higherPowerResolventSub (RH t f_param) (RH t g_param) (r + 1) f +
      higherPowerResolventSub (RH t g_param) (RH t h_param) (r + 1) f +
      higherPowerResolventSub (RH t h_param) (RH t i_param) (r + 1) f +
      higherPowerResolventSub (RH t i_param) (RH t a) (r + 1) f = 0 ∧
    higherPowerResolventSub (RH t a) (RH t i_param) (r + 1) f ∈
      hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    higherPowerIdentityPowerSub (RH t a) (RH t i_param) a i_param (r + 1) f ∈
      hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    ‖higherPowerResolventSub (RH t a) (RH t i_param) (r + 1) f‖ ≤
      ((a⁻¹) ^ (r + 2) + (i_param⁻¹) ^ (r + 2)) * ‖f‖ ∧
    ‖higherPowerIdentityPowerSub (RH t a) (RH t i_param) a i_param (r + 1) f‖ ≤ 2 * ‖f‖ := by
  have hpkg := higherPowerResolvent_and_identity_nine_parameter_nonagon_cocycle_and_regularity
    (H t) (RH t) a b c d e f_param g_param h_param i_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
    (KFCausalClosedGraphForm.hamiltonian_positive
      (KFCausalClockFloorAveragedHamiltonian.formData ε hε h hh hw m g k t))
    (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t) r f
  exact ⟨hpkg.1, hpkg.2.1, hpkg.2.2.2.2.1, hpkg.2.2.2.2.2.1,
    hpkg.2.2.2.2.2.2.1, hpkg.2.2.2.2.2.2.2.2⟩

/-- Master Five-Operator Nine-Parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param)`
Higher-Power Nonagon Cocycle and `Dom(A^{r+2})` Regularity Synthesis Across `T`, `P`, `G`, `S(t)`,
and `H(t)`. -/
theorem fiveOperator_nine_parameter_higherPower_nonagon_master_synthesis
    (t a b c d e f_param g_param h_param i_param : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param) (hi_p : 0 < i_param)
    (r : ℕ) (f : Hilbert) :
    higherPowerResolventSub (RT a) (RT i_param) (r + 1) f ∈ staticPowerDomain ε hε h (r + 2) ∧
    higherPowerResolventSub (RP a) (RP i_param) (r + 1) f ∈
      potentialPowerDomain ε hε h hh hb m g k (r + 2) ∧
    higherPowerResolventSub (RG a) (RG i_param) (r + 1) f ∈
      growingPowerDomain ε hε h hh hb m g k (r + 2) ∧
    higherPowerResolventSub (RS t a) (RS t i_param) (r + 1) f ∈
      residualPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    higherPowerResolventSub (RH t a) (RH t i_param) (r + 1) f ∈
      hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    higherPowerResolventSub (RH t a) (RH t b) (r + 1) f +
      higherPowerResolventSub (RH t b) (RH t c) (r + 1) f +
      higherPowerResolventSub (RH t c) (RH t d) (r + 1) f +
      higherPowerResolventSub (RH t d) (RH t e) (r + 1) f +
      higherPowerResolventSub (RH t e) (RH t f_param) (r + 1) f +
      higherPowerResolventSub (RH t f_param) (RH t g_param) (r + 1) f +
      higherPowerResolventSub (RH t g_param) (RH t h_param) (r + 1) f +
      higherPowerResolventSub (RH t h_param) (RH t i_param) (r + 1) f +
      higherPowerResolventSub (RH t i_param) (RH t a) (r + 1) f = 0 ∧
    ‖higherPowerResolventSub (RH t a) (RH t i_param) (r + 1) f‖ ≤
      ((a⁻¹) ^ (r + 2) + (i_param⁻¹) ^ (r + 2)) * ‖f‖ ∧
    ‖higherPowerIdentityPowerSub (RH t a) (RH t i_param) a i_param (r + 1) f‖ ≤ 2 * ‖f‖ := by
  have hT := static_higherPower_nine_parameter_nonagon_package
    ε hε h hh hb a b c d e f_param g_param h_param i_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p r f
  have hP := potential_higherPower_nine_parameter_nonagon_package
    ε hε h hh hb m g k a b c d e f_param g_param h_param i_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p r f
  have hG := growing_higherPower_nine_parameter_nonagon_package
    ε hε h hh hb m g k a b c d e f_param g_param h_param i_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p r f
  have hS := residual_higherPower_nine_parameter_nonagon_package
    ε hε h hh hb m g k t a b c d e f_param g_param h_param i_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p r f
  have hH := hamiltonian_higherPower_nine_parameter_nonagon_package
    ε hε h hh hb m g k t a b c d e f_param g_param h_param i_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p r f
  exact ⟨hT.2.2.1, hP.2.2.1, hG.2.2.1, hS.2.2.1, hH.2.2.1,
    hH.2.1, hH.2.2.2.2.1, hH.2.2.2.2.2⟩

#print axioms higherPowerResolvent_and_identity_nine_parameter_nonagon_cocycle_and_regularity
#print axioms static_higherPower_nine_parameter_nonagon_package
#print axioms potential_higherPower_nine_parameter_nonagon_package
#print axioms growing_higherPower_nine_parameter_nonagon_package
#print axioms residual_higherPower_nine_parameter_nonagon_package
#print axioms hamiltonian_higherPower_nine_parameter_nonagon_package
#print axioms fiveOperator_nine_parameter_higherPower_nonagon_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorNineParameterHigherPowerNonagonCocycleAndYosida
