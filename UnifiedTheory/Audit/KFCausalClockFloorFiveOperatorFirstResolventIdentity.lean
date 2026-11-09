/- Unconditional First Resolvent (Hilbert) Identities, Resolvent Commutativity,
Second-Power Domain Regularity, Lipschitz Norm Bounds, and Two-Parameter Cross-Operator
Second Resolvent Identities across all Five Clock-Floor Hamiltonians
T, P, G, S(t), and H(t):
1. Establishes the abstract first resolvent identity
   R_A(a) f - R_A(b) f = ((b - a : ℝ) : ℂ) • R_A(a) (R_A(b) f),
   pointwise resolvent commutativity R_A(a) (R_A(b) f) = R_A(b) (R_A(a) f),
   second-power domain membership R_A(a) f - R_A(b) f ∈ secondPowerDomain A,
   and Lipschitz norm bound ‖R_A(a) f - R_A(b) f‖ ≤ |a - b| * (a⁻¹ * (b⁻¹ * ‖f‖))
   for any positive operator A with positive shifted resolvents.
2. Instantiates these identities and bounds across all five clock-floor Hamiltonians
   T, P, G, S(t), and H(t), proving in addition that R_{H(t)}(a) f - R_{H(t)}(b) f
   belongs simultaneously to all 10 operator, form, and clock domains.
3. Proves two-parameter (a, b) cross-operator second resolvent identities connecting
   (R_P(a), R_G(b)), (R_{S(t)}(a), R_{H(t)}(b)), (R_T(a), R_{S(t)}(b)), and
   (R_T(a), R_{H(t)}(b)). -/
import UnifiedTheory.Audit.KFCausalClockFloorFullFiveResolventChainSynthesis
import UnifiedTheory.Audit.KFCausalClockFloorIteratedResolventSecondPowerCore

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorFirstResolventIdentity
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
open KFCausalClockFloorSecondPowerOperatorCores
  (secondPowerDomain secondPowerDomain_le_domain hamiltonian_domain_mem_ten_domains)
open KFCausalClockFloorIteratedResolventSecondPowerCore
  (resolvent_output_eq_sub iterated_resolvent_mem_secondPowerDomain
   iterated_resolvent_norm_bound
   staticSecondPowerDomain potentialSecondPowerDomain growingSecondPowerDomain
   residualSecondPowerDomain hamiltonianSecondPowerDomain)
open KFCausalClockFloorPotentialResolventRadialRegularity
  (potential_resolvent_norm_le)
open KFCausalClockFloorResidualResolventRadialRootRegularity
  (residual_resolvent_norm_le)
open KFCausalClockFloorGrowingPotentialSecondResolventIdentity
  (potential_resolvent_left_inverse growing_resolvent_shifted_potential_eq)
open KFCausalClockFloorHamiltonianResidualSecondResolventIdentity
  (residual_resolvent_left_inverse hamiltonian_resolvent_shifted_residual_eq)
open KFCausalClockFloorStaticResidualSecondResolventIdentity
  (static_resolvent_left_inverse
   residual_resolvent_mem_static_of_potential
   residual_resolvent_shifted_static_eq)
open KFCausalClockFloorFullFiveResolventChainSynthesis
  (hamiltonian_resolvent_mem_growing_of_potential
   hamiltonian_resolvent_mem_static_of_potential
   hamiltonian_resolvent_shifted_static_eq)

/-! ### 1. Abstract First Resolvent Identity, Commutativity, and Lipschitz Bounds -/

section AbstractFirstResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem resolvent_shifted_at_other_eq
    (A : H →ₗ.[ℂ] H) (Rb : H →L[ℂ] H) (a b : ℝ)
    (hrb : Resolves A Rb b) (f : H) :
    A (point A Rb b hrb f) + (a : ℂ) • Rb f =
      f - ((b - a : ℝ) : ℂ) • Rb f := by
  rw [resolvent_output_eq_sub A Rb b hrb f]
  push_cast
  module

theorem resolvent_eq_other_resolvent_sub_iterated
    (A : H →ₗ.[ℂ] H) (Ra Rb : H →L[ℂ] H) (a b : ℝ)
    (hrb : Resolves A Rb b)
    (hla : ∀ z : A.domain, Ra (A z + a • (z : H)) = (z : H)) (f : H) :
    Rb f = Ra f - ((b - a : ℝ) : ℂ) • Ra (Rb f) := by
  let u : A.domain := point A Rb b hrb f
  have hlin := hla u
  change Ra (A u + a • Rb f) = Rb f at hlin
  rw [← Complex.coe_smul, resolvent_shifted_at_other_eq A Rb a b hrb f,
    map_sub, map_smul] at hlin
  exact hlin.symm

theorem first_resolvent_identity
    (A : H →ₗ.[ℂ] H) (Ra Rb : H →L[ℂ] H) (a b : ℝ)
    (hrb : Resolves A Rb b)
    (hla : ∀ z : A.domain, Ra (A z + a • (z : H)) = (z : H)) (f : H) :
    Ra f - Rb f = ((b - a : ℝ) : ℂ) • Ra (Rb f) :=
  (congrArg (fun v : H => Ra f - v)
    (resolvent_eq_other_resolvent_sub_iterated A Ra Rb a b hrb hla f)).trans
    (sub_sub_cancel _ _)

theorem resolvent_sub_mem_secondPowerDomain
    (A : H →ₗ.[ℂ] H) (Ra Rb : H →L[ℂ] H) (a b : ℝ)
    (hra : Resolves A Ra a) (hrb : Resolves A Rb b)
    (hla : ∀ z : A.domain, Ra (A z + a • (z : H)) = (z : H)) (f : H) :
    Ra f - Rb f ∈ secondPowerDomain A := by
  rw [first_resolvent_identity A Ra Rb a b hrb hla f]
  exact (secondPowerDomain A).smul_mem ((b - a : ℝ) : ℂ)
    (iterated_resolvent_mem_secondPowerDomain A Ra Rb a b hra hrb f)

theorem first_resolvent_norm_bound
    (A : H →ₗ.[ℂ] H) (Ra Rb : H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hra : Resolves A Ra a) (hrb : Resolves A Rb b)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hla : ∀ z : A.domain, Ra (A z + a • (z : H)) = (z : H)) (f : H) :
    ‖Ra f - Rb f‖ ≤ |a - b| * (a⁻¹ * (b⁻¹ * ‖f‖)) := by
  rw [first_resolvent_identity A Ra Rb a b hrb hla f,
    norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  exact mul_le_mul_of_nonneg_left
    (iterated_resolvent_norm_bound A Ra Rb a b ha hb hra hrb hp f)
    (abs_nonneg (a - b))

theorem resolvent_apply_comm
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ c, 0 < c → Resolves A (R c) c)
    (hl : ∀ c, 0 < c → ∀ z : A.domain, R c (A z + c • (z : H)) = (z : H))
    (f : H) :
    R a (R b f) = R b (R a f) := by
  by_cases hab : a = b
  · subst hab
    rfl
  · have hsub_ne : ((b - a : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hab))
    apply smul_right_injective H hsub_ne
    change ((b - a : ℝ) : ℂ) • R a (R b f) = ((b - a : ℝ) : ℂ) • R b (R a f)
    have h1 := first_resolvent_identity A (R a) (R b) a b (hr b hb) (hl a ha) f
    have h2 := first_resolvent_identity A (R b) (R a) b a (hr a ha) (hl b hb) f
    have hneg : R a f - R b f = -(R b f - R a f) := (neg_sub (R b f) (R a f)).symm
    rw [← h1, hneg, h2]
    push_cast
    module

end AbstractFirstResolvent

/-! ### 2. Concrete Five-Operator First Resolvent Identities, Commutativity, and Bounds -/

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k t : ℝ)

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

theorem quarterStripResolvent_sub_quarterStripResolvent
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    RT a f - RT b f = ((b - a : ℝ) : ℂ) • RT a (RT b f) :=
  first_resolvent_identity T (RT a) (RT b) a b
    (KFCausalClockFloorStaticResidualSecondResolventIdentity.static_resolves
      ε hε h hh hb m g k b hb_pos)
    (static_resolvent_left_inverse ε hε h hh hb m g k a ha) f

theorem quarterStripResolvent_comm
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    RT a (RT b f) = RT b (RT a f) :=
  resolvent_apply_comm T RT a b ha hb_pos
    (KFCausalClockFloorStaticResidualSecondResolventIdentity.static_resolves ε hε h hh hb m g k)
    (static_resolvent_left_inverse ε hε h hh hb m g k) f

theorem quarterStripResolvent_sub_mem_quarterStripSecondPowerDomain
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    RT a f - RT b f ∈ staticSecondPowerDomain ε hε h :=
  resolvent_sub_mem_secondPowerDomain T (RT a) (RT b) a b
    (KFCausalClockFloorStaticResidualSecondResolventIdentity.static_resolves
      ε hε h hh hb m g k a ha)
    (KFCausalClockFloorStaticResidualSecondResolventIdentity.static_resolves
      ε hε h hh hb m g k b hb_pos)
    (static_resolvent_left_inverse ε hε h hh hb m g k a ha) f

theorem norm_quarterStripResolvent_sub_le
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    ‖RT a f - RT b f‖ ≤ |a - b| * (a⁻¹ * (b⁻¹ * ‖f‖)) :=
  first_resolvent_norm_bound T (RT a) (RT b) a b ha hb_pos
    (KFCausalClockFloorStaticResidualSecondResolventIdentity.static_resolves
      ε hε h hh hb m g k a ha)
    (KFCausalClockFloorStaticResidualSecondResolventIdentity.static_resolves
      ε hε h hh hb m g k b hb_pos)
    (KFCausalClockFloorStaticResidualSecondResolventIdentity.static_operator_positive ε hε h)
    (static_resolvent_left_inverse ε hε h hh hb m g k a ha) f

theorem potentialResolvent_sub_potentialResolvent
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    RP a f - RP b f = ((b - a : ℝ) : ℂ) • RP a (RP b f) :=
  first_resolvent_identity P (RP a) (RP b) a b
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k b hb_pos)
    (potential_resolvent_left_inverse ε hε h hh hb m g k a ha) f

theorem potentialResolvent_comm
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    RP a (RP b f) = RP b (RP a f) :=
  resolvent_apply_comm P RP a b ha hb_pos
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k)
    (potential_resolvent_left_inverse ε hε h hh hb m g k) f

theorem potentialResolvent_sub_mem_potentialSecondPowerDomain
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    RP a f - RP b f ∈ potentialSecondPowerDomain ε hε h hh hb m g k :=
  resolvent_sub_mem_secondPowerDomain P (RP a) (RP b) a b
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha)
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k b hb_pos)
    (potential_resolvent_left_inverse ε hε h hh hb m g k a ha) f

theorem norm_potentialResolvent_sub_le
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    ‖RP a f - RP b f‖ ≤ |a - b| * (a⁻¹ * (b⁻¹ * ‖f‖)) :=
  first_resolvent_norm_bound P (RP a) (RP b) a b ha hb_pos
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha)
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k b hb_pos)
    (KFCausalClosedGraphForm.hamiltonian_positive PD)
    (potential_resolvent_left_inverse ε hε h hh hb m g k a ha) f

theorem staticGeneratorResolvent_sub_staticGeneratorResolvent
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    RG a f - RG b f = ((b - a : ℝ) : ℂ) • RG a (RG b f) :=
  first_resolvent_identity G (RG a) (RG b) a b
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k b hb_pos)
    (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k a ha) f

theorem staticGeneratorResolvent_comm
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    RG a (RG b f) = RG b (RG a f) :=
  resolvent_apply_comm G RG a b ha hb_pos
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k)
    (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k) f

theorem staticGeneratorResolvent_sub_mem_staticGeneratorSecondPowerDomain
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    RG a f - RG b f ∈ growingSecondPowerDomain ε hε h hh hb m g k :=
  resolvent_sub_mem_secondPowerDomain G (RG a) (RG b) a b
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha)
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k b hb_pos)
    (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k a ha) f

theorem norm_staticGeneratorResolvent_sub_le
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    ‖RG a f - RG b f‖ ≤ |a - b| * (a⁻¹ * (b⁻¹ * ‖f‖)) :=
  first_resolvent_norm_bound G (RG a) (RG b) a b ha hb_pos
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha)
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k b hb_pos)
    (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k)
    (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k a ha) f

theorem staticResidualResolvent_sub_staticResidualResolvent
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    RS t a f - RS t b f = ((b - a : ℝ) : ℂ) • RS t a (RS t b f) :=
  first_resolvent_identity (S t) (RS t a) (RS t b) a b
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t b hb_pos)
    (residual_resolvent_left_inverse ε hε h hh hb m g k t a ha) f

theorem staticResidualResolvent_comm
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    RS t a (RS t b f) = RS t b (RS t a f) :=
  resolvent_apply_comm (S t) (RS t) a b ha hb_pos
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t)
    (residual_resolvent_left_inverse ε hε h hh hb m g k t) f

theorem staticResidualResolvent_sub_mem_staticResidualSecondPowerDomain
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    RS t a f - RS t b f ∈ residualSecondPowerDomain ε hε h hh hb m g k t :=
  resolvent_sub_mem_secondPowerDomain (S t) (RS t a) (RS t b) a b
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha)
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t b hb_pos)
    (residual_resolvent_left_inverse ε hε h hh hb m g k t a ha) f

theorem norm_staticResidualResolvent_sub_le
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    ‖RS t a f - RS t b f‖ ≤ |a - b| * (a⁻¹ * (b⁻¹ * ‖f‖)) :=
  first_resolvent_norm_bound (S t) (RS t a) (RS t b) a b ha hb_pos
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha)
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t b hb_pos)
    (KFCausalClosedGraphForm.hamiltonian_positive (SD t))
    (residual_resolvent_left_inverse ε hε h hh hb m g k t a ha) f

theorem hamiltonianResolvent_sub_hamiltonianResolvent
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    RH t a f - RH t b f = ((b - a : ℝ) : ℂ) • RH t a (RH t b f) :=
  first_resolvent_identity (H t) (RH t a) (RH t b) a b
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t b hb_pos)
    (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t a ha) f

theorem hamiltonianResolvent_comm
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    RH t a (RH t b f) = RH t b (RH t a f) :=
  resolvent_apply_comm (H t) (RH t) a b ha hb_pos
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
    (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t) f

theorem hamiltonianResolvent_sub_mem_hamiltonianSecondPowerDomain
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    RH t a f - RH t b f ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t :=
  resolvent_sub_mem_secondPowerDomain (H t) (RH t a) (RH t b) a b
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t b hb_pos)
    (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t a ha) f

theorem norm_hamiltonianResolvent_sub_le
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    ‖RH t a f - RH t b f‖ ≤ |a - b| * (a⁻¹ * (b⁻¹ * ‖f‖)) :=
  first_resolvent_norm_bound (H t) (RH t a) (RH t b) a b ha hb_pos
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t b hb_pos)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
    (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t a ha) f

theorem hamiltonianResolvent_sub_mem_ten_domains
    (s a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let d : Hilbert := RH t a f - RH t b f
    d ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t ∧
    d ∈ (H t).domain ∧
    d ∈ (K).domain ∧
    d ∈ (S t).domain ∧
    d ∈ (Eavg s).domain ∧
    d ∈ (Tstat).domain ∧
    d ∈ (Kroot).domain ∧
    d ∈ (Tpot).domain ∧
    d ∈ (Tgrow).domain ∧
    d ∈ (Tres s).domain ∧
    d ∈ (clockHalf ε).domain := by
  intro d
  have h2 := hamiltonianResolvent_sub_mem_hamiltonianSecondPowerDomain
    ε hε h hh hb m g k t a b ha hb_pos f
  have hdom : d ∈ (H t).domain := secondPowerDomain_le_domain (H t) h2
  exact ⟨h2, hamiltonian_domain_mem_ten_domains ε hε h hh hb m g k t s hdom⟩

/-! ### 3. Two-Parameter `(a, b)` Cross-Operator Second Resolvent Identities -/

theorem potential_sub_growing_two_param_resolvent_eq
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    RP a f - RG b f =
      RP a (K ⟨RG b f,
        KFCausalClockFloorGrowingComponentResolventBounds.resolvent_mem_radial_domain
          ε hε h hh hb m g k b hb_pos f⟩) +
        ((b - a : ℝ) : ℂ) • RP a (RG b f) := by
  let hp_b := KFCausalClockFloorGrowingComponentResolventBounds.resolvent_mem_potential_domain
    ε hε h hh hb m g k b hb_pos f
  let hk_b := KFCausalClockFloorGrowingComponentResolventBounds.resolvent_mem_radial_domain
    ε hε h hh hb m g k b hb_pos f
  have hshift_b := growing_resolvent_shifted_potential_eq ε hε h hh hb m g k b hb_pos f
  have hshift_a : P ⟨RG b f, hp_b⟩ + a • RG b f =
      f - K ⟨RG b f, hk_b⟩ - ((b - a : ℝ) : ℂ) • RG b f := by
    rw [← Complex.coe_smul]
    have h1 : P ⟨RG b f, hp_b⟩ + (a : ℂ) • RG b f =
        (P ⟨RG b f, hp_b⟩ + (b : ℂ) • RG b f) - ((b - a : ℝ) : ℂ) • RG b f := by
      push_cast
      module
    rw [h1, hshift_b]
  have hlinv := potential_resolvent_left_inverse ε hε h hh hb m g k a ha ⟨RG b f, hp_b⟩
  change RP a (P ⟨RG b f, hp_b⟩ + a • RG b f) = RG b f at hlinv
  rw [hshift_a, map_sub, map_sub, map_smul] at hlinv
  exact (congrArg (fun v : Hilbert => RP a f - v) hlinv.symm).trans (by abel)

theorem residual_sub_hamiltonian_two_param_resolvent_eq
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    RS t a f - RH t b f =
      (Real.exp (2 * t) : ℂ) •
        RS t a (K ⟨RH t b f,
          KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_radial_domain
            ε hε h hh hb m g k t b hb_pos f⟩) +
        ((b - a : ℝ) : ℂ) • RS t a (RH t b f) := by
  let hs_b := KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_residual_domain
    ε hε h hh hb m g k t b hb_pos f
  let hk_b := KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_radial_domain
    ε hε h hh hb m g k t b hb_pos f
  have hshift_b := hamiltonian_resolvent_shifted_residual_eq ε hε h hh hb m g k t b hb_pos f
  have hshift_a : S t ⟨RH t b f, hs_b⟩ + a • RH t b f =
      f - (Real.exp (2 * t) : ℂ) • K ⟨RH t b f, hk_b⟩ - ((b - a : ℝ) : ℂ) • RH t b f := by
    rw [← Complex.coe_smul]
    have h1 : S t ⟨RH t b f, hs_b⟩ + (a : ℂ) • RH t b f =
        (S t ⟨RH t b f, hs_b⟩ + (b : ℂ) • RH t b f) - ((b - a : ℝ) : ℂ) • RH t b f := by
      push_cast
      module
    rw [h1, hshift_b]
  have hlinv := residual_resolvent_left_inverse ε hε h hh hb m g k t a ha ⟨RH t b f, hs_b⟩
  change RS t a (S t ⟨RH t b f, hs_b⟩ + a • RH t b f) = RH t b f at hlinv
  rw [hshift_a, map_sub, map_sub, map_smul, map_smul] at hlinv
  exact (congrArg (fun v : Hilbert => RS t a f - v) hlinv.symm).trans (by abel)

theorem static_sub_residual_two_param_resolvent_eq
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert)
    (hp : RS t b f ∈ (P).domain) :
    RT a f - RS t b f =
      (Real.exp (2 * t) : ℂ) • RT a (P ⟨RS t b f, hp⟩) +
        ((b - a : ℝ) : ℂ) • RT a (RS t b f) := by
  let ht_b := residual_resolvent_mem_static_of_potential ε hε h hh hb m g k t b hb_pos f hp
  have hshift_b := residual_resolvent_shifted_static_eq ε hε h hh hb m g k t b hb_pos f hp
  have hshift_a : T ⟨RS t b f, ht_b⟩ + a • RS t b f =
      f - (Real.exp (2 * t) : ℂ) • P ⟨RS t b f, hp⟩ - ((b - a : ℝ) : ℂ) • RS t b f := by
    rw [← Complex.coe_smul]
    have h1 : T ⟨RS t b f, ht_b⟩ + (a : ℂ) • RS t b f =
        (T ⟨RS t b f, ht_b⟩ + (b : ℂ) • RS t b f) - ((b - a : ℝ) : ℂ) • RS t b f := by
      push_cast
      module
    rw [h1, hshift_b]
  have hlinv := static_resolvent_left_inverse ε hε h hh hb m g k a ha ⟨RS t b f, ht_b⟩
  change RT a (T ⟨RS t b f, ht_b⟩ + a • RS t b f) = RS t b f at hlinv
  rw [hshift_a, map_sub, map_sub, map_smul, map_smul] at hlinv
  exact (congrArg (fun v : Hilbert => RT a f - v) hlinv.symm).trans (by abel)

theorem static_sub_hamiltonian_two_param_resolvent_eq
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert)
    (hp : RH t b f ∈ (P).domain) :
    RT a f - RH t b f =
      (Real.exp (2 * t) : ℂ) •
        RT a (G ⟨RH t b f,
          hamiltonian_resolvent_mem_growing_of_potential ε hε h hh hb m g k t b hb_pos f hp⟩) +
        ((b - a : ℝ) : ℂ) • RT a (RH t b f) := by
  let ht_b := hamiltonian_resolvent_mem_static_of_potential ε hε h hh hb m g k t b hb_pos f hp
  let hg_b := hamiltonian_resolvent_mem_growing_of_potential ε hε h hh hb m g k t b hb_pos f hp
  have hshift_b := hamiltonian_resolvent_shifted_static_eq ε hε h hh hb m g k t b hb_pos f hp
  have hshift_a : T ⟨RH t b f, ht_b⟩ + a • RH t b f =
      f - (Real.exp (2 * t) : ℂ) • G ⟨RH t b f, hg_b⟩ - ((b - a : ℝ) : ℂ) • RH t b f := by
    rw [← Complex.coe_smul]
    have h1 : T ⟨RH t b f, ht_b⟩ + (a : ℂ) • RH t b f =
        (T ⟨RH t b f, ht_b⟩ + (b : ℂ) • RH t b f) - ((b - a : ℝ) : ℂ) • RH t b f := by
      push_cast
      module
    rw [h1, hshift_b]
  have hlinv := static_resolvent_left_inverse ε hε h hh hb m g k a ha ⟨RH t b f, ht_b⟩
  change RT a (T ⟨RH t b f, ht_b⟩ + a • RH t b f) = RH t b f at hlinv
  rw [hshift_a, map_sub, map_sub, map_smul, map_smul] at hlinv
  exact (congrArg (fun v : Hilbert => RT a f - v) hlinv.symm).trans (by abel)

theorem norm_potential_sub_growing_two_param_resolvent_le
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    ‖RP a f - RG b f‖ ≤
      a⁻¹ * ‖K ⟨RG b f,
        KFCausalClockFloorGrowingComponentResolventBounds.resolvent_mem_radial_domain
          ε hε h hh hb m g k b hb_pos f⟩‖ +
        |a - b| * (a⁻¹ * (b⁻¹ * ‖f‖)) := by
  rw [potential_sub_growing_two_param_resolvent_eq ε hε h hh hb m g k a b ha hb_pos f]
  have htri := norm_add_le
    (RP a (K ⟨RG b f,
      KFCausalClockFloorGrowingComponentResolventBounds.resolvent_mem_radial_domain
        ε hε h hh hb m g k b hb_pos f⟩))
    (((b - a : ℝ) : ℂ) • RP a (RG b f))
  have h1 := potential_resolvent_norm_le ε hε h hb hh m g k a ha
    (K ⟨RG b f,
      KFCausalClockFloorGrowingComponentResolventBounds.resolvent_mem_radial_domain
        ε hε h hh hb m g k b hb_pos f⟩)
  have h2 : ‖((b - a : ℝ) : ℂ) • RP a (RG b f)‖ ≤ |a - b| * (a⁻¹ * (b⁻¹ * ‖f‖)) := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg (a - b))
    exact (potential_resolvent_norm_le ε hε h hb hh m g k a ha (RG b f)).trans
      (mul_le_mul_of_nonneg_left
        (KFCausalClockFloorGrowingComponentResolventBounds.resolvent_norm_le
          ε hε h hh hb m g k b hb_pos f)
        (inv_nonneg.mpr ha.le))
  linarith

theorem norm_residual_sub_hamiltonian_two_param_resolvent_le
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    ‖RS t a f - RH t b f‖ ≤
      a⁻¹ * Real.exp (2 * t) *
        ‖K ⟨RH t b f,
          KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_radial_domain
            ε hε h hh hb m g k t b hb_pos f⟩‖ +
        |a - b| * (a⁻¹ * (b⁻¹ * ‖f‖)) := by
  let kVec := K ⟨RH t b f,
    KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_radial_domain
      ε hε h hh hb m g k t b hb_pos f⟩
  rw [residual_sub_hamiltonian_two_param_resolvent_eq ε hε h hh hb m g k t a b ha hb_pos f]
  have htri := norm_add_le
    ((Real.exp (2 * t) : ℂ) • RS t a kVec)
    (((b - a : ℝ) : ℂ) • RS t a (RH t b f))
  have h1 : ‖(Real.exp (2 * t) : ℂ) • RS t a kVec‖ ≤ a⁻¹ * Real.exp (2 * t) * ‖kVec‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (2 * t))]
    have hr := residual_resolvent_norm_le ε hε h hh hb m g k t a ha kVec
    calc
      Real.exp (2 * t) * ‖RS t a kVec‖ ≤ Real.exp (2 * t) * (a⁻¹ * ‖kVec‖) :=
        mul_le_mul_of_nonneg_left hr (Real.exp_pos (2 * t)).le
      _ = a⁻¹ * Real.exp (2 * t) * ‖kVec‖ := by ring
  have h2 : ‖((b - a : ℝ) : ℂ) • RS t a (RH t b f)‖ ≤ |a - b| * (a⁻¹ * (b⁻¹ * ‖f‖)) := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg (a - b))
    exact (residual_resolvent_norm_le ε hε h hh hb m g k t a ha (RH t b f)).trans
      (mul_le_mul_of_nonneg_left
        (KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_norm_le
          ε hε h hh hb m g k t b hb_pos f)
        (inv_nonneg.mpr ha.le))
  linarith

theorem five_operator_first_and_second_resolvent_master_synthesis
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    (RT a f - RT b f = ((b - a : ℝ) : ℂ) • RT a (RT b f) ∧
     RP a f - RP b f = ((b - a : ℝ) : ℂ) • RP a (RP b f) ∧
     RG a f - RG b f = ((b - a : ℝ) : ℂ) • RG a (RG b f) ∧
     RS t a f - RS t b f = ((b - a : ℝ) : ℂ) • RS t a (RS t b f) ∧
     RH t a f - RH t b f = ((b - a : ℝ) : ℂ) • RH t a (RH t b f)) ∧
    (RT a (RT b f) = RT b (RT a f) ∧
     RP a (RP b f) = RP b (RP a f) ∧
     RG a (RG b f) = RG b (RG a f) ∧
     RS t a (RS t b f) = RS t b (RS t a f) ∧
     RH t a (RH t b f) = RH t b (RH t a f)) ∧
    (RT a f - RT b f ∈ staticSecondPowerDomain ε hε h ∧
     RP a f - RP b f ∈ potentialSecondPowerDomain ε hε h hh hb m g k ∧
     RG a f - RG b f ∈ growingSecondPowerDomain ε hε h hh hb m g k ∧
     RS t a f - RS t b f ∈ residualSecondPowerDomain ε hε h hh hb m g k t ∧
     RH t a f - RH t b f ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t) :=
  ⟨⟨quarterStripResolvent_sub_quarterStripResolvent ε hε h hh hb m g k a b ha hb_pos f,
    potentialResolvent_sub_potentialResolvent ε hε h hh hb m g k a b ha hb_pos f,
    staticGeneratorResolvent_sub_staticGeneratorResolvent ε hε h hh hb m g k a b ha hb_pos f,
    staticResidualResolvent_sub_staticResidualResolvent ε hε h hh hb m g k t a b ha hb_pos f,
    hamiltonianResolvent_sub_hamiltonianResolvent ε hε h hh hb m g k t a b ha hb_pos f⟩,
   ⟨quarterStripResolvent_comm ε hε h hh hb m g k a b ha hb_pos f,
    potentialResolvent_comm ε hε h hh hb m g k a b ha hb_pos f,
    staticGeneratorResolvent_comm ε hε h hh hb m g k a b ha hb_pos f,
    staticResidualResolvent_comm ε hε h hh hb m g k t a b ha hb_pos f,
    hamiltonianResolvent_comm ε hε h hh hb m g k t a b ha hb_pos f⟩,
   ⟨quarterStripResolvent_sub_mem_quarterStripSecondPowerDomain ε hε h hh hb m g k a b ha hb_pos f,
    potentialResolvent_sub_mem_potentialSecondPowerDomain ε hε h hh hb m g k a b ha hb_pos f,
    staticGeneratorResolvent_sub_mem_staticGeneratorSecondPowerDomain ε hε h hh hb m g k a b ha hb_pos f,
    staticResidualResolvent_sub_mem_staticResidualSecondPowerDomain ε hε h hh hb m g k t a b ha hb_pos f,
    hamiltonianResolvent_sub_mem_hamiltonianSecondPowerDomain ε hε h hh hb m g k t a b ha hb_pos f⟩⟩

#print axioms resolvent_shifted_at_other_eq
#print axioms resolvent_eq_other_resolvent_sub_iterated
#print axioms first_resolvent_identity
#print axioms resolvent_sub_mem_secondPowerDomain
#print axioms first_resolvent_norm_bound
#print axioms resolvent_apply_comm
#print axioms quarterStripResolvent_sub_quarterStripResolvent
#print axioms quarterStripResolvent_comm
#print axioms quarterStripResolvent_sub_mem_quarterStripSecondPowerDomain
#print axioms norm_quarterStripResolvent_sub_le
#print axioms potentialResolvent_sub_potentialResolvent
#print axioms potentialResolvent_comm
#print axioms potentialResolvent_sub_mem_potentialSecondPowerDomain
#print axioms norm_potentialResolvent_sub_le
#print axioms staticGeneratorResolvent_sub_staticGeneratorResolvent
#print axioms staticGeneratorResolvent_comm
#print axioms staticGeneratorResolvent_sub_mem_staticGeneratorSecondPowerDomain
#print axioms norm_staticGeneratorResolvent_sub_le
#print axioms staticResidualResolvent_sub_staticResidualResolvent
#print axioms staticResidualResolvent_comm
#print axioms staticResidualResolvent_sub_mem_staticResidualSecondPowerDomain
#print axioms norm_staticResidualResolvent_sub_le
#print axioms hamiltonianResolvent_sub_hamiltonianResolvent
#print axioms hamiltonianResolvent_comm
#print axioms hamiltonianResolvent_sub_mem_hamiltonianSecondPowerDomain
#print axioms norm_hamiltonianResolvent_sub_le
#print axioms hamiltonianResolvent_sub_mem_ten_domains
#print axioms potential_sub_growing_two_param_resolvent_eq
#print axioms residual_sub_hamiltonian_two_param_resolvent_eq
#print axioms static_sub_residual_two_param_resolvent_eq
#print axioms static_sub_hamiltonian_two_param_resolvent_eq
#print axioms norm_potential_sub_growing_two_param_resolvent_le
#print axioms norm_residual_sub_hamiltonian_two_param_resolvent_le
#print axioms five_operator_first_and_second_resolvent_master_synthesis
end
end UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorFirstResolventIdentity
