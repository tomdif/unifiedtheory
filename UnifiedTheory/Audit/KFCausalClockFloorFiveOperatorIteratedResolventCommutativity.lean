/- Triple and r-Fold Iterated Resolvent Commutativity, Exact Second-Order
Hilbert Identities for Squared Resolvents, Third-Power Domain Regularity,
and Ten-Domain Synthesis across all Five Clock-Floor Hamiltonians
T, P, G, S(t), and H(t):
1. Proves for any positive operator A with positive shifted resolvents R(a):
   - Triple resolvent all-permutations commutativity:
     R(a)(R(b)(R(c) f)) = R(b)(R(a)(R(c) f)) = R(a)(R(c)(R(b) f)) = R(c)(R(b)(R(a) f)),
   - Commutativity of R(a) with iteratedResolventPower (R b) r for all r : ℕ,
   - Commutativity of iteratedResolventPower (R a) r with iteratedResolventPower (R b) s
     for all r, s : ℕ, and the addition law iteratedResolventPower R (r + s) f =
     iteratedResolventPower R r (iteratedResolventPower R s f),
   - Exact second-order Hilbert difference identity for squared resolvents:
     R(a)(R(a) f) - R(b)(R(b) f) = ((b - a : ℝ) : ℂ) • (R(a)(R(a)(R(b) f)) + R(a)(R(b)(R(b) f))),
   - Membership R(a)(R(a) f) - R(b)(R(b) f) ∈ operatorPowerDomain A 3 (Dom(A³)) and
     explicit norm bound ‖R(a)(R(a) f) - R(b)(R(b) f)‖ ≤ |a - b| * ((a⁻¹ + b⁻¹) * a⁻¹ * b⁻¹ * ‖f‖).
2. Instantiates all of these identities, higher-power domain memberships, and norm bounds
   across all five clock-floor Hamiltonians T, P, G, S(t), and H(t), including simultaneous
   10-domain membership for R_{H(t)}(a)² f - R_{H(t)}(b)² f. -/
import UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorFirstResolventIdentity
import UnifiedTheory.Audit.KFCausalClockFloorHigherPowerOperatorCores

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorIteratedResolventCommutativity
noncomputable section
open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalPositiveResolventBounds
  (Resolves point point_value resolvent_apply_norm_bound)
open KFCausalClockFloorSecondPowerOperatorCores
  (secondPowerDomain hamiltonian_domain_mem_ten_domains)
open KFCausalClockFloorIteratedResolventSecondPowerCore
  (iterated_resolvent_norm_bound)
open KFCausalClockFloorHigherPowerOperatorCores
  (operatorPowerDomain operatorPowerDomain_zero operatorPowerDomain_succ_le_domain
   resolvent_mem_operatorPowerDomain_succ
   iteratedResolventPower iteratedResolventPower_zero_apply iteratedResolventPower_succ_apply
   staticPowerDomain potentialPowerDomain growingPowerDomain
   residualPowerDomain hamiltonianPowerDomain
   hamiltonianPowerDomain_succ_mem_ten_domains)
open KFCausalClockFloorGrowingPotentialSecondResolventIdentity
  (potential_resolvent_left_inverse)
open KFCausalClockFloorHamiltonianResidualSecondResolventIdentity
  (residual_resolvent_left_inverse)
open KFCausalClockFloorStaticResidualSecondResolventIdentity
  (static_resolvent_left_inverse)
open KFCausalClockFloorFiveOperatorFirstResolventIdentity
  (first_resolvent_identity resolvent_apply_comm)

/-! ### 1. Abstract Triple and `r`-Fold Resolvent Commutativity and Squared-Resolvent Calculus -/

section AbstractIteratedCommutativity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem resolvent_triple_comm_left
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hl : ∀ d, 0 < d → ∀ z : A.domain, R d (A z + d • (z : H)) = (z : H))
    (f : H) :
    R a (R b (R c f)) = R b (R a (R c f)) :=
  resolvent_apply_comm A R a b ha hb hr hl (R c f)

theorem resolvent_triple_comm_right
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b c : ℝ)
    (hb : 0 < b) (hc : 0 < c)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hl : ∀ d, 0 < d → ∀ z : A.domain, R d (A z + d • (z : H)) = (z : H))
    (f : H) :
    R a (R b (R c f)) = R a (R c (R b f)) :=
  congrArg (R a) (resolvent_apply_comm A R b c hb hc hr hl f)

theorem resolvent_triple_comm_swap_outer
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hl : ∀ d, 0 < d → ∀ z : A.domain, R d (A z + d • (z : H)) = (z : H))
    (f : H) :
    R a (R b (R c f)) = R c (R b (R a f)) := by
  rw [resolvent_triple_comm_right A R a b c hb hc hr hl f,
    resolvent_apply_comm A R a c ha hc hr hl (R b f),
    congrArg (R c) (resolvent_apply_comm A R a b ha hb hr hl f)]

theorem resolvent_comm_iteratedResolventPower
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hl : ∀ d, 0 < d → ∀ z : A.domain, R d (A z + d • (z : H)) = (z : H)) :
    ∀ r : ℕ, ∀ f : H,
      R a (iteratedResolventPower (R b) r f) =
        iteratedResolventPower (R b) r (R a f)
  | 0, _ => rfl
  | r + 1, f => by
    rw [iteratedResolventPower_succ_apply,
      resolvent_apply_comm A R a b ha hb hr hl (iteratedResolventPower (R b) r f),
      resolvent_comm_iteratedResolventPower A R a b ha hb hr hl r f,
      ← iteratedResolventPower_succ_apply]

theorem iteratedResolventPower_comm
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hl : ∀ d, 0 < d → ∀ z : A.domain, R d (A z + d • (z : H)) = (z : H)) :
    ∀ r s : ℕ, ∀ f : H,
      iteratedResolventPower (R a) r (iteratedResolventPower (R b) s f) =
        iteratedResolventPower (R b) s (iteratedResolventPower (R a) r f)
  | 0, _, _ => rfl
  | r + 1, s, f => by
    rw [iteratedResolventPower_succ_apply,
      iteratedResolventPower_comm A R a b ha hb hr hl r s f,
      resolvent_comm_iteratedResolventPower A R a b ha hb hr hl s
        (iteratedResolventPower (R a) r f),
      ← iteratedResolventPower_succ_apply]

theorem iteratedResolventPower_add
    (R : H →L[ℂ] H) :
    ∀ r s : ℕ, ∀ f : H,
      iteratedResolventPower R (r + s) f =
        iteratedResolventPower R r (iteratedResolventPower R s f)
  | 0, s, f => by
    rw [Nat.zero_add, iteratedResolventPower_zero_apply]
  | r + 1, s, f => by
    rw [Nat.succ_add, iteratedResolventPower_succ_apply,
      iteratedResolventPower_add R r s f,
      iteratedResolventPower_succ_apply]

theorem triple_resolvent_mem_thirdPowerDomain
    (A : H →ₗ.[ℂ] H) (Ra Rb Rc : H →L[ℂ] H) (a b c : ℝ)
    (hra : Resolves A Ra a) (hrb : Resolves A Rb b) (hrc : Resolves A Rc c) (f : H) :
    Ra (Rb (Rc f)) ∈ operatorPowerDomain A 3 :=
  resolvent_mem_operatorPowerDomain_succ A Ra a hra 2
    (resolvent_mem_operatorPowerDomain_succ A Rb b hrb 1
      (resolvent_mem_operatorPowerDomain_succ A Rc c hrc 0 Submodule.mem_top))

theorem triple_resolvent_norm_bound
    (A : H →ₗ.[ℂ] H) (Ra Rb Rc : H →L[ℂ] H) (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hra : Resolves A Ra a) (hrb : Resolves A Rb b) (hrc : Resolves A Rc c)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re) (f : H) :
    ‖Ra (Rb (Rc f))‖ ≤ a⁻¹ * (b⁻¹ * (c⁻¹ * ‖f‖)) :=
  (resolvent_apply_norm_bound A Ra a ha hra hp (Rb (Rc f))).trans
    (mul_le_mul_of_nonneg_left
      (iterated_resolvent_norm_bound A Rb Rc b c hb hc hrb hrc hp f)
      (inv_nonneg.mpr ha.le))

theorem squared_resolvent_sub_eq
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hl : ∀ d, 0 < d → ∀ z : A.domain, R d (A z + d • (z : H)) = (z : H))
    (f : H) :
    R a (R a f) - R b (R b f) =
      ((b - a : ℝ) : ℂ) • (R a (R a (R b f)) + R a (R b (R b f))) := by
  have hsplit :
      R a (R a f) - R b (R b f) =
        (R a (R a f) - R a (R b f)) + (R a (R b f) - R b (R b f)) := by
    abel
  have h1 :
      R a (R a f) - R a (R b f) =
        ((b - a : ℝ) : ℂ) • R a (R a (R b f)) := by
    rw [← map_sub, first_resolvent_identity A (R a) (R b) a b (hr b hb) (hl a ha) f, map_smul]
  have h2 :
      R a (R b f) - R b (R b f) =
        ((b - a : ℝ) : ℂ) • R a (R b (R b f)) :=
    first_resolvent_identity A (R a) (R b) a b (hr b hb) (hl a ha) (R b f)
  rw [hsplit, h1, h2, ← smul_add]

theorem squared_resolvent_sub_mem_thirdPowerDomain
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hl : ∀ d, 0 < d → ∀ z : A.domain, R d (A z + d • (z : H)) = (z : H))
    (f : H) :
    R a (R a f) - R b (R b f) ∈ operatorPowerDomain A 3 := by
  rw [squared_resolvent_sub_eq A R a b ha hb hr hl f]
  exact (operatorPowerDomain A 3).smul_mem ((b - a : ℝ) : ℂ)
    ((operatorPowerDomain A 3).add_mem
      (triple_resolvent_mem_thirdPowerDomain A (R a) (R a) (R b) a a b
        (hr a ha) (hr a ha) (hr b hb) f)
      (triple_resolvent_mem_thirdPowerDomain A (R a) (R b) (R b) a b b
        (hr a ha) (hr b hb) (hr b hb) f))

theorem squared_resolvent_sub_norm_bound
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves A (R d) d)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ d, 0 < d → ∀ z : A.domain, R d (A z + d • (z : H)) = (z : H))
    (f : H) :
    ‖R a (R a f) - R b (R b f)‖ ≤
      |a - b| * ((a⁻¹ + b⁻¹) * a⁻¹ * b⁻¹ * ‖f‖) := by
  rw [squared_resolvent_sub_eq A R a b ha hb hr hl f,
    norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg (a - b))
  have htri := norm_add_le (R a (R a (R b f))) (R a (R b (R b f)))
  have h1 := triple_resolvent_norm_bound A (R a) (R a) (R b) a a b ha ha hb
    (hr a ha) (hr a ha) (hr b hb) hp f
  have h2 := triple_resolvent_norm_bound A (R a) (R b) (R b) a b b ha hb hb
    (hr a ha) (hr b hb) (hr b hb) hp f
  have hsum :
      a⁻¹ * (a⁻¹ * (b⁻¹ * ‖f‖)) + a⁻¹ * (b⁻¹ * (b⁻¹ * ‖f‖)) =
        (a⁻¹ + b⁻¹) * a⁻¹ * b⁻¹ * ‖f‖ := by
    ring
  linarith

end AbstractIteratedCommutativity

/-! ### 2. Concrete Five-Operator Instantiations for `T`, `P`, `G`, `S(t)`, and `H(t)` -/

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k t : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "SD" => KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hw m g k
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

theorem staticResolvent_triple_comm
    (a b c : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (f : Hilbert) :
    RT a (RT b (RT c f)) = RT b (RT a (RT c f)) ∧
    RT a (RT b (RT c f)) = RT a (RT c (RT b f)) ∧
    RT a (RT b (RT c f)) = RT c (RT b (RT a f)) :=
  ⟨resolvent_triple_comm_left T RT a b c ha hb_pos
    (KFCausalClockFloorStaticResidualSecondResolventIdentity.static_resolves ε hε h hh hb m g k)
    (static_resolvent_left_inverse ε hε h hh hb m g k) f,
   resolvent_triple_comm_right T RT a b c hb_pos hc
    (KFCausalClockFloorStaticResidualSecondResolventIdentity.static_resolves ε hε h hh hb m g k)
    (static_resolvent_left_inverse ε hε h hh hb m g k) f,
   resolvent_triple_comm_swap_outer T RT a b c ha hb_pos hc
    (KFCausalClockFloorStaticResidualSecondResolventIdentity.static_resolves ε hε h hh hb m g k)
    (static_resolvent_left_inverse ε hε h hh hb m g k) f⟩

theorem staticResolvent_iteratedResolventPower_comm
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r s : ℕ) (f : Hilbert) :
    iteratedResolventPower (RT a) r (iteratedResolventPower (RT b) s f) =
      iteratedResolventPower (RT b) s (iteratedResolventPower (RT a) r f) :=
  iteratedResolventPower_comm T RT a b ha hb_pos
    (KFCausalClockFloorStaticResidualSecondResolventIdentity.static_resolves ε hε h hh hb m g k)
    (static_resolvent_left_inverse ε hε h hh hb m g k) r s f

theorem staticResolvent_squared_sub_eq
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    RT a (RT a f) - RT b (RT b f) =
      ((b - a : ℝ) : ℂ) • (RT a (RT a (RT b f)) + RT a (RT b (RT b f))) :=
  squared_resolvent_sub_eq T RT a b ha hb_pos
    (KFCausalClockFloorStaticResidualSecondResolventIdentity.static_resolves ε hε h hh hb m g k)
    (static_resolvent_left_inverse ε hε h hh hb m g k) f

theorem staticResolvent_squared_sub_mem_thirdPowerDomain
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    RT a (RT a f) - RT b (RT b f) ∈ staticPowerDomain ε hε h 3 :=
  squared_resolvent_sub_mem_thirdPowerDomain T RT a b ha hb_pos
    (KFCausalClockFloorStaticResidualSecondResolventIdentity.static_resolves ε hε h hh hb m g k)
    (static_resolvent_left_inverse ε hε h hh hb m g k) f

theorem staticResolvent_squared_sub_norm_le
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    ‖RT a (RT a f) - RT b (RT b f)‖ ≤
      |a - b| * ((a⁻¹ + b⁻¹) * a⁻¹ * b⁻¹ * ‖f‖) :=
  squared_resolvent_sub_norm_bound T RT a b ha hb_pos
    (KFCausalClockFloorStaticResidualSecondResolventIdentity.static_resolves ε hε h hh hb m g k)
    (KFCausalClockFloorStaticResidualSecondResolventIdentity.static_operator_positive ε hε h)
    (static_resolvent_left_inverse ε hε h hh hb m g k) f

theorem potentialResolvent_triple_comm
    (a b c : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (f : Hilbert) :
    RP a (RP b (RP c f)) = RP b (RP a (RP c f)) ∧
    RP a (RP b (RP c f)) = RP a (RP c (RP b f)) ∧
    RP a (RP b (RP c f)) = RP c (RP b (RP a f)) :=
  ⟨resolvent_triple_comm_left P RP a b c ha hb_pos
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k)
    (potential_resolvent_left_inverse ε hε h hh hb m g k) f,
   resolvent_triple_comm_right P RP a b c hb_pos hc
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k)
    (potential_resolvent_left_inverse ε hε h hh hb m g k) f,
   resolvent_triple_comm_swap_outer P RP a b c ha hb_pos hc
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k)
    (potential_resolvent_left_inverse ε hε h hh hb m g k) f⟩

theorem potentialResolvent_iteratedResolventPower_comm
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r s : ℕ) (f : Hilbert) :
    iteratedResolventPower (RP a) r (iteratedResolventPower (RP b) s f) =
      iteratedResolventPower (RP b) s (iteratedResolventPower (RP a) r f) :=
  iteratedResolventPower_comm P RP a b ha hb_pos
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k)
    (potential_resolvent_left_inverse ε hε h hh hb m g k) r s f

theorem potentialResolvent_squared_sub_eq
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    RP a (RP a f) - RP b (RP b f) =
      ((b - a : ℝ) : ℂ) • (RP a (RP a (RP b f)) + RP a (RP b (RP b f))) :=
  squared_resolvent_sub_eq P RP a b ha hb_pos
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k)
    (potential_resolvent_left_inverse ε hε h hh hb m g k) f

theorem potentialResolvent_squared_sub_mem_thirdPowerDomain
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    RP a (RP a f) - RP b (RP b f) ∈ potentialPowerDomain ε hε h hh hb m g k 3 :=
  squared_resolvent_sub_mem_thirdPowerDomain P RP a b ha hb_pos
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k)
    (potential_resolvent_left_inverse ε hε h hh hb m g k) f

theorem potentialResolvent_squared_sub_norm_le
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    ‖RP a (RP a f) - RP b (RP b f)‖ ≤
      |a - b| * ((a⁻¹ + b⁻¹) * a⁻¹ * b⁻¹ * ‖f‖) :=
  squared_resolvent_sub_norm_bound P RP a b ha hb_pos
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k)
    (KFCausalClosedGraphForm.hamiltonian_positive PD)
    (potential_resolvent_left_inverse ε hε h hh hb m g k) f

theorem growingResolvent_triple_comm
    (a b c : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (f : Hilbert) :
    RG a (RG b (RG c f)) = RG b (RG a (RG c f)) ∧
    RG a (RG b (RG c f)) = RG a (RG c (RG b f)) ∧
    RG a (RG b (RG c f)) = RG c (RG b (RG a f)) :=
  ⟨resolvent_triple_comm_left G RG a b c ha hb_pos
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k)
    (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k) f,
   resolvent_triple_comm_right G RG a b c hb_pos hc
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k)
    (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k) f,
   resolvent_triple_comm_swap_outer G RG a b c ha hb_pos hc
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k)
    (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k) f⟩

theorem growingResolvent_iteratedResolventPower_comm
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r s : ℕ) (f : Hilbert) :
    iteratedResolventPower (RG a) r (iteratedResolventPower (RG b) s f) =
      iteratedResolventPower (RG b) s (iteratedResolventPower (RG a) r f) :=
  iteratedResolventPower_comm G RG a b ha hb_pos
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k)
    (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k) r s f

theorem growingResolvent_squared_sub_eq
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    RG a (RG a f) - RG b (RG b f) =
      ((b - a : ℝ) : ℂ) • (RG a (RG a (RG b f)) + RG a (RG b (RG b f))) :=
  squared_resolvent_sub_eq G RG a b ha hb_pos
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k)
    (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k) f

theorem growingResolvent_squared_sub_mem_thirdPowerDomain
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    RG a (RG a f) - RG b (RG b f) ∈ growingPowerDomain ε hε h hh hb m g k 3 :=
  squared_resolvent_sub_mem_thirdPowerDomain G RG a b ha hb_pos
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k)
    (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k) f

theorem growingResolvent_squared_sub_norm_le
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    ‖RG a (RG a f) - RG b (RG b f)‖ ≤
      |a - b| * ((a⁻¹ + b⁻¹) * a⁻¹ * b⁻¹ * ‖f‖) :=
  squared_resolvent_sub_norm_bound G RG a b ha hb_pos
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k)
    (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k)
    (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k) f

theorem residualResolvent_triple_comm
    (a b c : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (f : Hilbert) :
    RS t a (RS t b (RS t c f)) = RS t b (RS t a (RS t c f)) ∧
    RS t a (RS t b (RS t c f)) = RS t a (RS t c (RS t b f)) ∧
    RS t a (RS t b (RS t c f)) = RS t c (RS t b (RS t a f)) :=
  ⟨resolvent_triple_comm_left (S t) (RS t) a b c ha hb_pos
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t)
    (residual_resolvent_left_inverse ε hε h hh hb m g k t) f,
   resolvent_triple_comm_right (S t) (RS t) a b c hb_pos hc
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t)
    (residual_resolvent_left_inverse ε hε h hh hb m g k t) f,
   resolvent_triple_comm_swap_outer (S t) (RS t) a b c ha hb_pos hc
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t)
    (residual_resolvent_left_inverse ε hε h hh hb m g k t) f⟩

theorem residualResolvent_iteratedResolventPower_comm
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r s : ℕ) (f : Hilbert) :
    iteratedResolventPower (RS t a) r (iteratedResolventPower (RS t b) s f) =
      iteratedResolventPower (RS t b) s (iteratedResolventPower (RS t a) r f) :=
  iteratedResolventPower_comm (S t) (RS t) a b ha hb_pos
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t)
    (residual_resolvent_left_inverse ε hε h hh hb m g k t) r s f

theorem residualResolvent_squared_sub_eq
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    RS t a (RS t a f) - RS t b (RS t b f) =
      ((b - a : ℝ) : ℂ) • (RS t a (RS t a (RS t b f)) + RS t a (RS t b (RS t b f))) :=
  squared_resolvent_sub_eq (S t) (RS t) a b ha hb_pos
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t)
    (residual_resolvent_left_inverse ε hε h hh hb m g k t) f

theorem residualResolvent_squared_sub_mem_thirdPowerDomain
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    RS t a (RS t a f) - RS t b (RS t b f) ∈ residualPowerDomain ε hε h hh hb m g k t 3 :=
  squared_resolvent_sub_mem_thirdPowerDomain (S t) (RS t) a b ha hb_pos
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t)
    (residual_resolvent_left_inverse ε hε h hh hb m g k t) f

theorem residualResolvent_squared_sub_norm_le
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    ‖RS t a (RS t a f) - RS t b (RS t b f)‖ ≤
      |a - b| * ((a⁻¹ + b⁻¹) * a⁻¹ * b⁻¹ * ‖f‖) :=
  squared_resolvent_sub_norm_bound (S t) (RS t) a b ha hb_pos
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t)
    (KFCausalClosedGraphForm.hamiltonian_positive (SD t))
    (residual_resolvent_left_inverse ε hε h hh hb m g k t) f

theorem hamiltonianResolvent_triple_comm
    (a b c : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (f : Hilbert) :
    RH t a (RH t b (RH t c f)) = RH t b (RH t a (RH t c f)) ∧
    RH t a (RH t b (RH t c f)) = RH t a (RH t c (RH t b f)) ∧
    RH t a (RH t b (RH t c f)) = RH t c (RH t b (RH t a f)) :=
  ⟨resolvent_triple_comm_left (H t) (RH t) a b c ha hb_pos
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
    (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t) f,
   resolvent_triple_comm_right (H t) (RH t) a b c hb_pos hc
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
    (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t) f,
   resolvent_triple_comm_swap_outer (H t) (RH t) a b c ha hb_pos hc
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
    (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t) f⟩

theorem hamiltonianResolvent_iteratedResolventPower_comm
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r s : ℕ) (f : Hilbert) :
    iteratedResolventPower (RH t a) r (iteratedResolventPower (RH t b) s f) =
      iteratedResolventPower (RH t b) s (iteratedResolventPower (RH t a) r f) :=
  iteratedResolventPower_comm (H t) (RH t) a b ha hb_pos
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
    (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t) r s f

theorem hamiltonianResolvent_squared_sub_eq
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    RH t a (RH t a f) - RH t b (RH t b f) =
      ((b - a : ℝ) : ℂ) • (RH t a (RH t a (RH t b f)) + RH t a (RH t b (RH t b f))) :=
  squared_resolvent_sub_eq (H t) (RH t) a b ha hb_pos
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
    (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t) f

theorem hamiltonianResolvent_squared_sub_mem_thirdPowerDomain
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    RH t a (RH t a f) - RH t b (RH t b f) ∈ hamiltonianPowerDomain ε hε h hh hb m g k t 3 :=
  squared_resolvent_sub_mem_thirdPowerDomain (H t) (RH t) a b ha hb_pos
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
    (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t) f

theorem hamiltonianResolvent_squared_sub_norm_le
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    ‖RH t a (RH t a f) - RH t b (RH t b f)‖ ≤
      |a - b| * ((a⁻¹ + b⁻¹) * a⁻¹ * b⁻¹ * ‖f‖) :=
  squared_resolvent_sub_norm_bound (H t) (RH t) a b ha hb_pos
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
    (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t) f

theorem hamiltonianResolvent_squared_sub_mem_ten_domains
    (s a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let d : Hilbert := RH t a (RH t a f) - RH t b (RH t b f)
    d ∈ hamiltonianPowerDomain ε hε h hh hb m g k t 3 ∧
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
  have h3 := hamiltonianResolvent_squared_sub_mem_thirdPowerDomain
    ε hε h hh hb m g k t a b ha hb_pos f
  exact ⟨h3, hamiltonianPowerDomain_succ_mem_ten_domains ε hε h hh hb m g k t s 2 h3⟩

theorem five_operator_iterated_resolvent_commutativity_master_synthesis
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (r s : ℕ) (f : Hilbert) :
    (iteratedResolventPower (RT a) r (iteratedResolventPower (RT b) s f) =
       iteratedResolventPower (RT b) s (iteratedResolventPower (RT a) r f) ∧
     iteratedResolventPower (RP a) r (iteratedResolventPower (RP b) s f) =
       iteratedResolventPower (RP b) s (iteratedResolventPower (RP a) r f) ∧
     iteratedResolventPower (RG a) r (iteratedResolventPower (RG b) s f) =
       iteratedResolventPower (RG b) s (iteratedResolventPower (RG a) r f) ∧
     iteratedResolventPower (RS t a) r (iteratedResolventPower (RS t b) s f) =
       iteratedResolventPower (RS t b) s (iteratedResolventPower (RS t a) r f) ∧
     iteratedResolventPower (RH t a) r (iteratedResolventPower (RH t b) s f) =
       iteratedResolventPower (RH t b) s (iteratedResolventPower (RH t a) r f)) ∧
    (RT a (RT a f) - RT b (RT b f) ∈ staticPowerDomain ε hε h 3 ∧
     RP a (RP a f) - RP b (RP b f) ∈ potentialPowerDomain ε hε h hh hb m g k 3 ∧
     RG a (RG a f) - RG b (RG b f) ∈ growingPowerDomain ε hε h hh hb m g k 3 ∧
     RS t a (RS t a f) - RS t b (RS t b f) ∈ residualPowerDomain ε hε h hh hb m g k t 3 ∧
     RH t a (RH t a f) - RH t b (RH t b f) ∈ hamiltonianPowerDomain ε hε h hh hb m g k t 3) :=
  ⟨⟨staticResolvent_iteratedResolventPower_comm ε hε h hh hb m g k a b ha hb_pos r s f,
    potentialResolvent_iteratedResolventPower_comm ε hε h hh hb m g k a b ha hb_pos r s f,
    growingResolvent_iteratedResolventPower_comm ε hε h hh hb m g k a b ha hb_pos r s f,
    residualResolvent_iteratedResolventPower_comm ε hε h hh hb m g k t a b ha hb_pos r s f,
    hamiltonianResolvent_iteratedResolventPower_comm ε hε h hh hb m g k t a b ha hb_pos r s f⟩,
   ⟨staticResolvent_squared_sub_mem_thirdPowerDomain ε hε h hh hb m g k a b ha hb_pos f,
    potentialResolvent_squared_sub_mem_thirdPowerDomain ε hε h hh hb m g k a b ha hb_pos f,
    growingResolvent_squared_sub_mem_thirdPowerDomain ε hε h hh hb m g k a b ha hb_pos f,
    residualResolvent_squared_sub_mem_thirdPowerDomain ε hε h hh hb m g k t a b ha hb_pos f,
    hamiltonianResolvent_squared_sub_mem_thirdPowerDomain ε hε h hh hb m g k t a b ha hb_pos f⟩⟩

#print axioms resolvent_triple_comm_left
#print axioms resolvent_triple_comm_right
#print axioms resolvent_triple_comm_swap_outer
#print axioms resolvent_comm_iteratedResolventPower
#print axioms iteratedResolventPower_comm
#print axioms iteratedResolventPower_add
#print axioms triple_resolvent_mem_thirdPowerDomain
#print axioms triple_resolvent_norm_bound
#print axioms squared_resolvent_sub_eq
#print axioms squared_resolvent_sub_mem_thirdPowerDomain
#print axioms squared_resolvent_sub_norm_bound
#print axioms staticResolvent_triple_comm
#print axioms staticResolvent_iteratedResolventPower_comm
#print axioms staticResolvent_squared_sub_eq
#print axioms staticResolvent_squared_sub_mem_thirdPowerDomain
#print axioms staticResolvent_squared_sub_norm_le
#print axioms potentialResolvent_triple_comm
#print axioms potentialResolvent_iteratedResolventPower_comm
#print axioms potentialResolvent_squared_sub_eq
#print axioms potentialResolvent_squared_sub_mem_thirdPowerDomain
#print axioms potentialResolvent_squared_sub_norm_le
#print axioms growingResolvent_triple_comm
#print axioms growingResolvent_iteratedResolventPower_comm
#print axioms growingResolvent_squared_sub_eq
#print axioms growingResolvent_squared_sub_mem_thirdPowerDomain
#print axioms growingResolvent_squared_sub_norm_le
#print axioms residualResolvent_triple_comm
#print axioms residualResolvent_iteratedResolventPower_comm
#print axioms residualResolvent_squared_sub_eq
#print axioms residualResolvent_squared_sub_mem_thirdPowerDomain
#print axioms residualResolvent_squared_sub_norm_le
#print axioms hamiltonianResolvent_triple_comm
#print axioms hamiltonianResolvent_iteratedResolventPower_comm
#print axioms hamiltonianResolvent_squared_sub_eq
#print axioms hamiltonianResolvent_squared_sub_mem_thirdPowerDomain
#print axioms hamiltonianResolvent_squared_sub_norm_le
#print axioms hamiltonianResolvent_squared_sub_mem_ten_domains
#print axioms five_operator_iterated_resolvent_commutativity_master_synthesis
end
end UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorIteratedResolventCommutativity
