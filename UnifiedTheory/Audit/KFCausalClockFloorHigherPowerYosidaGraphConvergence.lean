/- Higher-Power Yosida Identity Approximants, Semigroup Laws, Uniform Contraction,
and Domain Convergence Across All Five Clock-Floor Hamiltonians T, P, G, S(t), and H(t):
1. Establishes the exponent addition semigroup law
   `iteratedResolventPower R (r + s) = (iteratedResolventPower R r).comp (iteratedResolventPower R s)`,
   commutativity `iteratedResolventPower R r (iteratedResolventPower R s f) = iteratedResolventPower R s (iteratedResolventPower R r f)`,
   and the multi-step domain shift `f ∈ operatorPowerDomain A r → iteratedResolventPower R s f ∈ operatorPowerDomain A (r + s)`
   for all `r, s : ℕ`.
2. Defines the r-th order Yosida-scaled identity approximant
   `iteratedIdentityPower R a r f := ((a ^ r : ℝ) : ℂ) • iteratedResolventPower R r f`,
   proving that for every `a > 0`, `r : ℕ`, and `f : H`,
   `iteratedIdentityPower R a r f ∈ operatorPowerDomain A r` and `‖iteratedIdentityPower R a r f‖ ≤ ‖f‖`
   (uniform contraction for all powers `r : ℕ`).
3. Proves the telescoping difference identities, the explicit `O(a⁻¹)` rate bound
   `‖iteratedIdentityPower R a r (x : H) - (x : H)‖ ≤ (r : ℝ) * a⁻¹ * ‖A x‖` for every `x : A.domain`,
   and strong convergence `Tendsto (fun n : ℕ => iteratedIdentityPower (R (n + 1)) (n + 1) r (x : H)) atTop (𝓝 (x : H))`
   across all five clock-floor Hamiltonians `T`, `P`, `G`, `S t`, and `H t`. -/
import UnifiedTheory.Audit.KFCausalClockFloorHigherPowerOperatorCores
import UnifiedTheory.Audit.KFCausalClockFloorFrameworkCapstone2026MasterBridge

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorHigherPowerYosidaGraphConvergence

noncomputable section

open Filter
open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalPositiveResolventBounds
  (Resolves point resolvent_apply_norm_bound)
open KFCausalClockFloorStaticResolventRadialCommutator
  (staticOperator_positive staticResolvent staticResolvent_resolves staticResolvent_left_inverse)
open KFCausalClockFloorAveragedEvolution (evolution evolution_norm)
open KFCausalClockFloorSecondPowerOperatorCores (hamiltonian_domain_mem_ten_domains)
open KFCausalClockFloorIteratedResolventSecondPowerCore (scaled_resolvent_norm_bound)
open KFCausalClockFloorHigherPowerOperatorCores
  (operatorPowerDomain operatorPowerDomain_succ_le_domain
   resolvent_mem_operatorPowerDomain_succ
   iteratedResolventPower iteratedResolventPower_zero_apply iteratedResolventPower_succ_apply
   iteratedResolventPower_mem_operatorPowerDomain
   staticPowerDomain potentialPowerDomain growingPowerDomain
   residualPowerDomain hamiltonianPowerDomain
   hamiltonianPowerDomain_succ_mem_ten_domains)

/-! ### 1. Abstract Semigroup Laws, Yosida Identity Towers, and `O(a⁻¹)` Domain Convergence -/

section AbstractHigherPowerYosida

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Semigroup addition law for `iteratedResolventPower`:
`iteratedResolventPower R (r + s) = (iteratedResolventPower R r).comp (iteratedResolventPower R s)`. -/
theorem iteratedResolventPower_add (R : H →L[ℂ] H) :
    ∀ r s : ℕ,
      iteratedResolventPower R (r + s) =
        (iteratedResolventPower R r).comp (iteratedResolventPower R s)
  | 0, s => by
    rw [Nat.zero_add]
    rfl
  | r + 1, s => by
    rw [Nat.succ_add]
    ext f
    change R (iteratedResolventPower R (r + s) f) =
      R (iteratedResolventPower R r (iteratedResolventPower R s f))
    rw [iteratedResolventPower_add R r s]
    rfl

/-- Pointwise semigroup addition law for `iteratedResolventPower`. -/
theorem iteratedResolventPower_add_apply (R : H →L[ℂ] H) (r s : ℕ) (f : H) :
    iteratedResolventPower R (r + s) f =
      iteratedResolventPower R r (iteratedResolventPower R s f) :=
  congrFun (congrArg DFunLike.coe (iteratedResolventPower_add R r s)) f

/-- Commutativity of `iteratedResolventPower R r` and `iteratedResolventPower R s`. -/
theorem iteratedResolventPower_comm_apply (R : H →L[ℂ] H) (r s : ℕ) (f : H) :
    iteratedResolventPower R r (iteratedResolventPower R s f) =
      iteratedResolventPower R s (iteratedResolventPower R r f) := by
  rw [← iteratedResolventPower_add_apply, Nat.add_comm, iteratedResolventPower_add_apply]

/-- Right-step evaluation `iteratedResolventPower R (r + 1) f = iteratedResolventPower R r (R f)`. -/
theorem iteratedResolventPower_succ_right_apply (R : H →L[ℂ] H) (r : ℕ) (f : H) :
    iteratedResolventPower R (r + 1) f = iteratedResolventPower R r (R f) :=
  iteratedResolventPower_add_apply R r 1 f

/-- Multi-step domain shift: if `Resolves A R a` and `f ∈ operatorPowerDomain A r`, then
`iteratedResolventPower R s f ∈ operatorPowerDomain A (r + s)` for all `r, s : ℕ`. -/
theorem iteratedResolventPower_maps_operatorPowerDomain_add (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H)
    (a : ℝ) (hr : Resolves A R a) (r : ℕ) :
    ∀ s : ℕ, ∀ {f : H},
      f ∈ operatorPowerDomain A r →
        iteratedResolventPower R s f ∈ operatorPowerDomain A (r + s)
  | 0, _, hf => by
    rw [Nat.add_zero, iteratedResolventPower_zero_apply]
    exact hf
  | s + 1, _, hf => by
    rw [Nat.add_succ, iteratedResolventPower_succ_apply]
    exact resolvent_mem_operatorPowerDomain_succ A R a hr (r + s)
      (iteratedResolventPower_maps_operatorPowerDomain_add A R a hr r s hf)

/-- The `r`-th order Yosida-scaled identity approximant
`((a ^ r : ℝ) : ℂ) • iteratedResolventPower R r f`. -/
def iteratedIdentityPower (R : H →L[ℂ] H) (a : ℝ) (r : ℕ) (f : H) : H :=
  ((a ^ r : ℝ) : ℂ) • iteratedResolventPower R r f

/-- At `r = 0`, `iteratedIdentityPower R a 0 f = f`. -/
theorem iteratedIdentityPower_zero (R : H →L[ℂ] H) (a : ℝ) (f : H) :
    iteratedIdentityPower R a 0 f = f := by
  simp [iteratedIdentityPower, iteratedResolventPower_zero_apply]

/-- At `r = 1`, `iteratedIdentityPower R a 1 f = (a : ℂ) • R f`. -/
theorem iteratedIdentityPower_one (R : H →L[ℂ] H) (a : ℝ) (f : H) :
    iteratedIdentityPower R a 1 f = (a : ℂ) • R f := by
  simp [iteratedIdentityPower, iteratedResolventPower_succ_apply,
    iteratedResolventPower_zero_apply]

/-- Left-step recurrence `iteratedIdentityPower R a (r + 1) f = (a : ℂ) • R (iteratedIdentityPower R a r f)`. -/
theorem iteratedIdentityPower_succ (R : H →L[ℂ] H) (a : ℝ) (r : ℕ) (f : H) :
    iteratedIdentityPower R a (r + 1) f =
      (a : ℂ) • R (iteratedIdentityPower R a r f) := by
  unfold iteratedIdentityPower
  rw [iteratedResolventPower_succ_apply, map_smul, pow_succ', Complex.ofReal_mul, mul_smul]

/-- Right-step recurrence `iteratedIdentityPower R a (r + 1) f = iteratedIdentityPower R a r ((a : ℂ) • R f)`. -/
theorem iteratedIdentityPower_succ_right (R : H →L[ℂ] H) (a : ℝ) (r : ℕ) (f : H) :
    iteratedIdentityPower R a (r + 1) f =
      iteratedIdentityPower R a r ((a : ℂ) • R f) := by
  unfold iteratedIdentityPower
  rw [iteratedResolventPower_succ_right_apply, map_smul, pow_succ, Complex.ofReal_mul, mul_smul]

/-- Semigroup addition law for `iteratedIdentityPower`:
`iteratedIdentityPower R a (r + s) f = iteratedIdentityPower R a r (iteratedIdentityPower R a s f)`. -/
theorem iteratedIdentityPower_add (R : H →L[ℂ] H) (a : ℝ) (r s : ℕ) (f : H) :
    iteratedIdentityPower R a (r + s) f =
      iteratedIdentityPower R a r (iteratedIdentityPower R a s f) := by
  unfold iteratedIdentityPower
  rw [iteratedResolventPower_add_apply, map_smul, pow_add, Complex.ofReal_mul, mul_smul]

/-- Linearity of `iteratedIdentityPower R a r` over subtraction. -/
theorem iteratedIdentityPower_sub (R : H →L[ℂ] H) (a : ℝ) (r : ℕ) (f g : H) :
    iteratedIdentityPower R a r (f - g) =
      iteratedIdentityPower R a r f - iteratedIdentityPower R a r g := by
  unfold iteratedIdentityPower
  rw [map_sub, smul_sub]

/-- Unconditionally for EVERY `f : H`, `a : ℝ`, and `r : ℕ`, `iteratedIdentityPower R a r f`
belongs to `operatorPowerDomain A r`. -/
theorem iteratedIdentityPower_mem_operatorPowerDomain (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves A R a) (r : ℕ) (f : H) :
    iteratedIdentityPower R a r f ∈ operatorPowerDomain A r :=
  (operatorPowerDomain A r).smul_mem ((a ^ r : ℝ) : ℂ)
    (iteratedResolventPower_mem_operatorPowerDomain A R a hr r f)

/-- Uniform contraction bound: for all `0 < a`, `r : ℕ`, and `f : H`,
`‖iteratedIdentityPower R a r f‖ ≤ ‖f‖`. -/
theorem iteratedIdentityPower_norm_le (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves A R a) (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re) :
    ∀ r : ℕ, ∀ f : H, ‖iteratedIdentityPower R a r f‖ ≤ ‖f‖
  | 0, f => by rw [iteratedIdentityPower_zero]
  | r + 1, f => by
    rw [iteratedIdentityPower_succ]
    exact (scaled_resolvent_norm_bound A R a ha hr hp (iteratedIdentityPower R a r f)).trans
      (iteratedIdentityPower_norm_le A R a ha hr hp r f)

/-- Left-telescoping step identity for `iteratedIdentityPower`:
`iteratedIdentityPower R a (r + 1) f - f = ((a : ℂ) • R (iteratedIdentityPower R a r f) - iteratedIdentityPower R a r f) + (iteratedIdentityPower R a r f - f)`. -/
theorem iteratedIdentityPower_sub_self_left_step (R : H →L[ℂ] H) (a : ℝ) (r : ℕ) (f : H) :
    iteratedIdentityPower R a (r + 1) f - f =
      ((a : ℂ) • R (iteratedIdentityPower R a r f) - iteratedIdentityPower R a r f) +
        (iteratedIdentityPower R a r f - f) := by
  rw [iteratedIdentityPower_succ]
  abel

/-- Right-telescoping step identity for `iteratedIdentityPower`:
`iteratedIdentityPower R a (r + 1) f - f = iteratedIdentityPower R a r ((a : ℂ) • R f - f) + (iteratedIdentityPower R a r f - f)`. -/
theorem iteratedIdentityPower_sub_self_right_step (R : H →L[ℂ] H) (a : ℝ) (r : ℕ) (f : H) :
    iteratedIdentityPower R a (r + 1) f - f =
      iteratedIdentityPower R a r ((a : ℂ) • R f - f) +
        (iteratedIdentityPower R a r f - f) := by
  rw [iteratedIdentityPower_sub, ← iteratedIdentityPower_succ_right]
  abel

/-- Exact first-order Yosida defect identity on `A.domain`:
`(a : ℂ) • R (x : H) - (x : H) = - R (A x)` and `‖(a : ℂ) • R (x : H) - (x : H)‖ ≤ a⁻¹ * ‖A x‖`. -/
theorem single_yosida_defect_on_domain (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves A R a) (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hla : ∀ z : A.domain, R (A z + a • (z : H)) = (z : H)) (x : A.domain) :
    (a : ℂ) • R (x : H) - (x : H) = -R (A x) ∧
    ‖(a : ℂ) • R (x : H) - (x : H)‖ ≤ a⁻¹ * ‖A x‖ := by
  have hlin : R (A x) + (a : ℂ) • R (x : H) = (x : H) := by
    have h1 := hla x
    rw [← Complex.coe_smul (a : ℝ) (x : H), map_add, map_smul] at h1
    exact h1
  have hdef : (a : ℂ) • R (x : H) - (x : H) = -R (A x) := by
    calc (a : ℂ) • R (x : H) - (x : H)
        = (R (A x) + (a : ℂ) • R (x : H)) - (x : H) - R (A x) := by abel
      _ = (x : H) - (x : H) - R (A x) := by rw [hlin]
      _ = -R (A x) := by abel
  refine ⟨hdef, ?_⟩
  rw [hdef, norm_neg]
  exact resolvent_apply_norm_bound A R a ha hr hp (A x)

/-- Explicit `O(a⁻¹)` rate bound for the `r`-th order Yosida identity approximant on `A.domain`:
`‖iteratedIdentityPower R a r (x : H) - (x : H)‖ ≤ (r : ℝ) * a⁻¹ * ‖A x‖` for all `r : ℕ`. -/
theorem iteratedIdentityPower_domain_rate_bound (A : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (ha : 0 < a) (hr : Resolves A R a)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hla : ∀ z : A.domain, R (A z + a • (z : H)) = (z : H)) :
    ∀ r : ℕ, ∀ x : A.domain,
      ‖iteratedIdentityPower R a r (x : H) - (x : H)‖ ≤ (r : ℝ) * a⁻¹ * ‖A x‖
  | 0, x => by
    rw [iteratedIdentityPower_zero, sub_self, norm_zero, Nat.cast_zero, zero_mul, zero_mul]
  | r + 1, x => by
    rw [iteratedIdentityPower_sub_self_right_step, Nat.cast_succ]
    have htri :=
      norm_add_le
        (iteratedIdentityPower R a r ((a : ℂ) • R (x : H) - (x : H)))
        (iteratedIdentityPower R a r (x : H) - (x : H))
    have h1 :
        ‖iteratedIdentityPower R a r ((a : ℂ) • R (x : H) - (x : H))‖ ≤
          a⁻¹ * ‖A x‖ :=
      (iteratedIdentityPower_norm_le A R a ha hr hp r
        ((a : ℂ) • R (x : H) - (x : H))).trans
        (single_yosida_defect_on_domain A R a ha hr hp hla x).2
    have h2 := iteratedIdentityPower_domain_rate_bound A R a ha hr hp hla r x
    linarith

/-- Strong convergence as `n → ∞` (`a = (n : ℝ) + 1`): for every `r : ℕ` and every `x : A.domain`,
`iteratedIdentityPower (R ((n : ℝ) + 1)) ((n : ℝ) + 1) r (x : H)` lies in `operatorPowerDomain A r`
and converges in norm to `(x : H)`. -/
theorem iteratedIdentityPower_tendsto_on_domain (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H)
    (hr : ∀ a : ℝ, 0 < a → Resolves A (R a) a)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hla : ∀ a : ℝ, 0 < a → ∀ z : A.domain, R a (A z + a • (z : H)) = (z : H))
    (r : ℕ) (x : A.domain) :
    (∀ n : ℕ,
      iteratedIdentityPower (R ((n : ℝ) + 1)) ((n : ℝ) + 1) r (x : H) ∈
        operatorPowerDomain A r) ∧
    Tendsto
      (fun n : ℕ => iteratedIdentityPower (R ((n : ℝ) + 1)) ((n : ℝ) + 1) r (x : H))
      atTop (𝓝 (x : H)) := by
  have hpos : ∀ n : ℕ, 0 < (n : ℝ) + 1 := fun n => by positivity
  refine ⟨fun n =>
    iteratedIdentityPower_mem_operatorPowerDomain A (R ((n : ℝ) + 1)) ((n : ℝ) + 1)
      (hr ((n : ℝ) + 1) (hpos n)) r (x : H), ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hlim : Tendsto (fun n : ℕ => (r : ℝ) * ((n : ℝ) + 1)⁻¹ * ‖A x‖) atTop (𝓝 0) := by
    have h0 := (hinv.const_mul (r : ℝ)).mul_const ‖A x‖
    simpa using h0
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n =>
      iteratedIdentityPower_domain_rate_bound A (R ((n : ℝ) + 1)) ((n : ℝ) + 1)
        (hpos n) (hr ((n : ℝ) + 1) (hpos n)) hp (hla ((n : ℝ) + 1) (hpos n)) r x)
    hlim

end AbstractHigherPowerYosida

/-! ### 2. Concrete Higher-Power Yosida Contraction and Convergence for `T`, `P`, `G`, `S t`, and `H t` -/

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
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
local notation "U" => evolution ε hε h hh hw m g k
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "Kroot" => KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Tgrow" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (hamiltonian_bound ε h hw) hh m g k

/-- Higher-power domain membership, uniform contraction, and `O(a⁻¹)` rate bound for the
static operator `T` and its Yosida approximant `iteratedIdentityPower (RT a) a r`. -/
theorem static_iteratedIdentityPower_contraction_and_rate
    (a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert) (x : (T).domain) :
    iteratedIdentityPower (RT a) a r f ∈ staticPowerDomain ε hε h r ∧
    ‖iteratedIdentityPower (RT a) a r f‖ ≤ ‖f‖ ∧
    ‖iteratedIdentityPower (RT a) a r (x : Hilbert) - (x : Hilbert)‖ ≤ (r : ℝ) * a⁻¹ * ‖T x‖ :=
  ⟨iteratedIdentityPower_mem_operatorPowerDomain T (RT a) a
     (staticResolvent_resolves ε hε h hb hh a ha) r f,
   iteratedIdentityPower_norm_le T (RT a) a ha
     (staticResolvent_resolves ε hε h hb hh a ha)
     (staticOperator_positive ε hε h) r f,
   iteratedIdentityPower_domain_rate_bound T (RT a) a ha
     (staticResolvent_resolves ε hε h hb hh a ha)
     (staticOperator_positive ε hε h)
     (staticResolvent_left_inverse ε hε h hb hh a ha) r x⟩

/-- Higher-power domain membership, uniform contraction, and `O(a⁻¹)` rate bound for the
potential Hamiltonian `P` and its Yosida approximant `iteratedIdentityPower (RP a) a r`. -/
theorem potential_iteratedIdentityPower_contraction_and_rate
    (a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert) (x : (P).domain) :
    iteratedIdentityPower (RP a) a r f ∈ potentialPowerDomain ε hε h hh hb m g k r ∧
    ‖iteratedIdentityPower (RP a) a r f‖ ≤ ‖f‖ ∧
    ‖iteratedIdentityPower (RP a) a r (x : Hilbert) - (x : Hilbert)‖ ≤ (r : ℝ) * a⁻¹ * ‖P x‖ :=
  ⟨iteratedIdentityPower_mem_operatorPowerDomain P (RP a) a
     (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha) r f,
   iteratedIdentityPower_norm_le P (RP a) a ha
     (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha)
     (KFCausalClosedGraphForm.hamiltonian_positive PD) r f,
   iteratedIdentityPower_domain_rate_bound P (RP a) a ha
     (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha)
     (KFCausalClosedGraphForm.hamiltonian_positive PD)
     (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k a ha) r x⟩

/-- Higher-power domain membership, uniform contraction, and `O(a⁻¹)` rate bound for the
growing Hamiltonian `G` and its Yosida approximant `iteratedIdentityPower (RG a) a r`. -/
theorem growing_iteratedIdentityPower_contraction_and_rate
    (a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert) (x : (G).domain) :
    iteratedIdentityPower (RG a) a r f ∈ growingPowerDomain ε hε h hh hb m g k r ∧
    ‖iteratedIdentityPower (RG a) a r f‖ ≤ ‖f‖ ∧
    ‖iteratedIdentityPower (RG a) a r (x : Hilbert) - (x : Hilbert)‖ ≤ (r : ℝ) * a⁻¹ * ‖G x‖ :=
  ⟨iteratedIdentityPower_mem_operatorPowerDomain G (RG a) a
     (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha) r f,
   iteratedIdentityPower_norm_le G (RG a) a ha
     (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha)
     (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k) r f,
   iteratedIdentityPower_domain_rate_bound G (RG a) a ha
     (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha)
     (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k)
     (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k a ha) r x⟩

/-- Higher-power domain membership, uniform contraction, and `O(a⁻¹)` rate bound for the
residual Hamiltonian `S t` and its Yosida approximant `iteratedIdentityPower (RS t a) a r`. -/
theorem residual_iteratedIdentityPower_contraction_and_rate
    (t a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert) (x : (S t).domain) :
    iteratedIdentityPower (RS t a) a r f ∈ residualPowerDomain ε hε h hh hb m g k t r ∧
    ‖iteratedIdentityPower (RS t a) a r f‖ ≤ ‖f‖ ∧
    ‖iteratedIdentityPower (RS t a) a r (x : Hilbert) - (x : Hilbert)‖ ≤
      (r : ℝ) * a⁻¹ * ‖S t x‖ :=
  ⟨iteratedIdentityPower_mem_operatorPowerDomain (S t) (RS t a) a
     (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha) r f,
   iteratedIdentityPower_norm_le (S t) (RS t a) a ha
     (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha)
     (KFCausalClosedGraphForm.hamiltonian_positive (SD t)) r f,
   iteratedIdentityPower_domain_rate_bound (S t) (RS t a) a ha
     (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha)
     (KFCausalClosedGraphForm.hamiltonian_positive (SD t))
     (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t a ha) r x⟩

/-- Higher-power domain membership, uniform contraction, and `O(a⁻¹)` rate bound for the
full Hamiltonian `H t` and its Yosida approximant `iteratedIdentityPower (RH t a) a r`. -/
theorem hamiltonian_iteratedIdentityPower_contraction_and_rate
    (t a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert) (x : (H t).domain) :
    iteratedIdentityPower (RH t a) a r f ∈ hamiltonianPowerDomain ε hε h hh hb m g k t r ∧
    ‖iteratedIdentityPower (RH t a) a r f‖ ≤ ‖f‖ ∧
    ‖iteratedIdentityPower (RH t a) a r (x : Hilbert) - (x : Hilbert)‖ ≤
      (r : ℝ) * a⁻¹ * ‖H t x‖ :=
  ⟨iteratedIdentityPower_mem_operatorPowerDomain (H t) (RH t a) a
     (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha) r f,
   iteratedIdentityPower_norm_le (H t) (RH t a) a ha
     (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
     (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t) r f,
   iteratedIdentityPower_domain_rate_bound (H t) (RH t a) a ha
     (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
     (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
     (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t a ha) r x⟩

/-- Strong convergence on `(T).domain` of the `r`-th order static Yosida approximants
in `staticPowerDomain ε hε h r`. -/
theorem static_iteratedIdentityPower_tendsto (r : ℕ) (x : (T).domain) :
    (∀ n : ℕ,
      iteratedIdentityPower (RT ((n : ℝ) + 1)) ((n : ℝ) + 1) r (x : Hilbert) ∈
        staticPowerDomain ε hε h r) ∧
    Tendsto
      (fun n : ℕ => iteratedIdentityPower (RT ((n : ℝ) + 1)) ((n : ℝ) + 1) r (x : Hilbert))
      atTop (𝓝 (x : Hilbert)) :=
  iteratedIdentityPower_tendsto_on_domain T RT
    (staticResolvent_resolves ε hε h hb hh)
    (staticOperator_positive ε hε h)
    (staticResolvent_left_inverse ε hε h hb hh) r x

/-- Strong convergence on `(P).domain` of the `r`-th order potential Yosida approximants
in `potentialPowerDomain ε hε h hh hb m g k r`. -/
theorem potential_iteratedIdentityPower_tendsto (r : ℕ) (x : (P).domain) :
    (∀ n : ℕ,
      iteratedIdentityPower (RP ((n : ℝ) + 1)) ((n : ℝ) + 1) r (x : Hilbert) ∈
        potentialPowerDomain ε hε h hh hb m g k r) ∧
    Tendsto
      (fun n : ℕ => iteratedIdentityPower (RP ((n : ℝ) + 1)) ((n : ℝ) + 1) r (x : Hilbert))
      atTop (𝓝 (x : Hilbert)) :=
  iteratedIdentityPower_tendsto_on_domain P RP
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k)
    (KFCausalClosedGraphForm.hamiltonian_positive PD)
    (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k) r x

/-- Strong convergence on `(G).domain` of the `r`-th order growing Yosida approximants
in `growingPowerDomain ε hε h hh hb m g k r`. -/
theorem growing_iteratedIdentityPower_tendsto (r : ℕ) (x : (G).domain) :
    (∀ n : ℕ,
      iteratedIdentityPower (RG ((n : ℝ) + 1)) ((n : ℝ) + 1) r (x : Hilbert) ∈
        growingPowerDomain ε hε h hh hb m g k r) ∧
    Tendsto
      (fun n : ℕ => iteratedIdentityPower (RG ((n : ℝ) + 1)) ((n : ℝ) + 1) r (x : Hilbert))
      atTop (𝓝 (x : Hilbert)) :=
  iteratedIdentityPower_tendsto_on_domain G RG
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k)
    (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k)
    (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k) r x

/-- Strong convergence on `(S t).domain` of the `r`-th order residual Yosida approximants
in `residualPowerDomain ε hε h hh hb m g k t r`. -/
theorem residual_iteratedIdentityPower_tendsto (t : ℝ) (r : ℕ) (x : (S t).domain) :
    (∀ n : ℕ,
      iteratedIdentityPower (RS t ((n : ℝ) + 1)) ((n : ℝ) + 1) r (x : Hilbert) ∈
        residualPowerDomain ε hε h hh hb m g k t r) ∧
    Tendsto
      (fun n : ℕ => iteratedIdentityPower (RS t ((n : ℝ) + 1)) ((n : ℝ) + 1) r (x : Hilbert))
      atTop (𝓝 (x : Hilbert)) :=
  iteratedIdentityPower_tendsto_on_domain (S t) (RS t)
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t)
    (KFCausalClosedGraphForm.hamiltonian_positive (SD t))
    (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t) r x

/-- Strong convergence on `(H t).domain` of the `r`-th order full Hamiltonian Yosida approximants
in `hamiltonianPowerDomain ε hε h hh hb m g k t r`. -/
theorem hamiltonian_iteratedIdentityPower_tendsto (t : ℝ) (r : ℕ) (x : (H t).domain) :
    (∀ n : ℕ,
      iteratedIdentityPower (RH t ((n : ℝ) + 1)) ((n : ℝ) + 1) r (x : Hilbert) ∈
        hamiltonianPowerDomain ε hε h hh hb m g k t r) ∧
    Tendsto
      (fun n : ℕ => iteratedIdentityPower (RH t ((n : ℝ) + 1)) ((n : ℝ) + 1) r (x : Hilbert))
      atTop (𝓝 (x : Hilbert)) :=
  iteratedIdentityPower_tendsto_on_domain (H t) (RH t)
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
    (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t) r x

/-! ### 3. 10-Domain Regularity and Master Synthesis for Higher-Power Yosida Approximants -/

/-- Unconditionally for EVERY `f : Hilbert`, `r : ℕ`, `0 < a`, and `t, s : ℝ`, the
`(r + 1)`-th order Hamiltonian Yosida approximant `iteratedIdentityPower (RH t a) a (r + 1) f`
lies in `hamiltonianPowerDomain t (r + 1)` and in all 10 domains, with uniform contraction
bound `‖iteratedIdentityPower (RH t a) a (r + 1) f‖ ≤ ‖f‖`. -/
theorem hamiltonian_iteratedIdentityPower_succ_mem_ten_domains
    (t s a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert) :
    let y : Hilbert := iteratedIdentityPower (RH t a) a (r + 1) f
    y ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 1) ∧
    (y ∈ (H t).domain ∧
     y ∈ (K).domain ∧
     y ∈ (S t).domain ∧
     y ∈ (Eavg s).domain ∧
     y ∈ (Tstat).domain ∧
     y ∈ (Kroot).domain ∧
     y ∈ (Tpot).domain ∧
     y ∈ (Tgrow).domain ∧
     y ∈ (Tres s).domain ∧
     y ∈ (clockHalf ε).domain) ∧
    ‖y‖ ≤ ‖f‖ := by
  intro y
  have hy : y ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 1) :=
    iteratedIdentityPower_mem_operatorPowerDomain (H t) (RH t a) a
      (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha) (r + 1) f
  have hnorm : ‖y‖ ≤ ‖f‖ :=
    iteratedIdentityPower_norm_le (H t) (RH t a) a ha
      (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
      (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t) (r + 1) f
  exact ⟨hy, hamiltonianPowerDomain_succ_mem_ten_domains ε hε h hh hb m g k t s r hy, hnorm⟩

/-- Unconditionally for EVERY `f : Hilbert`, `r : ℕ`, `0 < a`, and `s₁, s₂, t, s : ℝ`,
applying `iteratedIdentityPower (RH t a) a (r + 1)` to the unitarily evolved state `U s₁ s₂ f`
places the output in `hamiltonianPowerDomain t (r + 1)` and in all 10 domains with
`(s₁, s₂)`-independent contraction bound `‖iteratedIdentityPower (RH t a) a (r + 1) (U s₁ s₂ f)‖ ≤ ‖f‖`. -/
theorem evolved_hamiltonian_iteratedIdentityPower_succ_regularity
    (s₁ s₂ t s a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert) :
    let w : Hilbert := U s₁ s₂ f
    let y : Hilbert := iteratedIdentityPower (RH t a) a (r + 1) w
    y ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 1) ∧
    (y ∈ (H t).domain ∧
     y ∈ (K).domain ∧
     y ∈ (S t).domain ∧
     y ∈ (Eavg s).domain ∧
     y ∈ (Tstat).domain ∧
     y ∈ (Kroot).domain ∧
     y ∈ (Tpot).domain ∧
     y ∈ (Tgrow).domain ∧
     y ∈ (Tres s).domain ∧
     y ∈ (clockHalf ε).domain) ∧
    ‖y‖ ≤ ‖f‖ := by
  intro w y
  have hpkg :=
    hamiltonian_iteratedIdentityPower_succ_mem_ten_domains ε hε h hh hb m g k t s a ha r w
  have hnorm : ‖w‖ = ‖f‖ := evolution_norm ε hε h hh hw m g k s₁ s₂ f
  exact ⟨hpkg.1, hpkg.2.1, hpkg.2.2.trans_eq hnorm⟩

/-- Master Higher-Power Yosida Contraction and Domain Convergence Synthesis across all five
clock-floor Hamiltonians `T, P, G, S t, H t`. -/
theorem five_hamiltonians_higher_power_yosida_convergence_master
    (t a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert)
    (xT : (T).domain) (xP : (P).domain) (xG : (G).domain)
    (xS : (S t).domain) (xH : (H t).domain) :
    (iteratedIdentityPower (RT a) a r f ∈ staticPowerDomain ε hε h r ∧
     iteratedIdentityPower (RP a) a r f ∈ potentialPowerDomain ε hε h hh hb m g k r ∧
     iteratedIdentityPower (RG a) a r f ∈ growingPowerDomain ε hε h hh hb m g k r ∧
     iteratedIdentityPower (RS t a) a r f ∈ residualPowerDomain ε hε h hh hb m g k t r ∧
     iteratedIdentityPower (RH t a) a r f ∈ hamiltonianPowerDomain ε hε h hh hb m g k t r) ∧
    (‖iteratedIdentityPower (RT a) a r f‖ ≤ ‖f‖ ∧
     ‖iteratedIdentityPower (RP a) a r f‖ ≤ ‖f‖ ∧
     ‖iteratedIdentityPower (RG a) a r f‖ ≤ ‖f‖ ∧
     ‖iteratedIdentityPower (RS t a) a r f‖ ≤ ‖f‖ ∧
     ‖iteratedIdentityPower (RH t a) a r f‖ ≤ ‖f‖) ∧
    (Tendsto (fun n : ℕ => iteratedIdentityPower (RT ((n : ℝ) + 1)) ((n : ℝ) + 1) r (xT : Hilbert))
       atTop (𝓝 (xT : Hilbert)) ∧
     Tendsto (fun n : ℕ => iteratedIdentityPower (RP ((n : ℝ) + 1)) ((n : ℝ) + 1) r (xP : Hilbert))
       atTop (𝓝 (xP : Hilbert)) ∧
     Tendsto (fun n : ℕ => iteratedIdentityPower (RG ((n : ℝ) + 1)) ((n : ℝ) + 1) r (xG : Hilbert))
       atTop (𝓝 (xG : Hilbert)) ∧
     Tendsto (fun n : ℕ => iteratedIdentityPower (RS t ((n : ℝ) + 1)) ((n : ℝ) + 1) r (xS : Hilbert))
       atTop (𝓝 (xS : Hilbert)) ∧
     Tendsto (fun n : ℕ => iteratedIdentityPower (RH t ((n : ℝ) + 1)) ((n : ℝ) + 1) r (xH : Hilbert))
       atTop (𝓝 (xH : Hilbert))) := by
  have hT := static_iteratedIdentityPower_contraction_and_rate ε hε h hh hb a ha r f xT
  have hP := potential_iteratedIdentityPower_contraction_and_rate ε hε h hh hb m g k a ha r f xP
  have hG := growing_iteratedIdentityPower_contraction_and_rate ε hε h hh hb m g k a ha r f xG
  have hS := residual_iteratedIdentityPower_contraction_and_rate ε hε h hh hb m g k t a ha r f xS
  have hH := hamiltonian_iteratedIdentityPower_contraction_and_rate ε hε h hh hb m g k t a ha r f xH
  exact ⟨⟨hT.1, hP.1, hG.1, hS.1, hH.1⟩,
    ⟨hT.2.1, hP.2.1, hG.2.1, hS.2.1, hH.2.1⟩,
    ⟨(static_iteratedIdentityPower_tendsto ε hε h hh hb r xT).2,
     (potential_iteratedIdentityPower_tendsto ε hε h hh hb m g k r xP).2,
     (growing_iteratedIdentityPower_tendsto ε hε h hh hb m g k r xG).2,
     (residual_iteratedIdentityPower_tendsto ε hε h hh hb m g k t r xS).2,
     (hamiltonian_iteratedIdentityPower_tendsto ε hε h hh hb m g k t r xH).2⟩⟩

#print axioms iteratedResolventPower_add
#print axioms iteratedResolventPower_add_apply
#print axioms iteratedResolventPower_comm_apply
#print axioms iteratedResolventPower_succ_right_apply
#print axioms iteratedResolventPower_maps_operatorPowerDomain_add
#print axioms iteratedIdentityPower_zero
#print axioms iteratedIdentityPower_one
#print axioms iteratedIdentityPower_succ
#print axioms iteratedIdentityPower_succ_right
#print axioms iteratedIdentityPower_add
#print axioms iteratedIdentityPower_sub
#print axioms iteratedIdentityPower_mem_operatorPowerDomain
#print axioms iteratedIdentityPower_norm_le
#print axioms iteratedIdentityPower_sub_self_left_step
#print axioms iteratedIdentityPower_sub_self_right_step
#print axioms single_yosida_defect_on_domain
#print axioms iteratedIdentityPower_domain_rate_bound
#print axioms iteratedIdentityPower_tendsto_on_domain
#print axioms static_iteratedIdentityPower_contraction_and_rate
#print axioms potential_iteratedIdentityPower_contraction_and_rate
#print axioms growing_iteratedIdentityPower_contraction_and_rate
#print axioms residual_iteratedIdentityPower_contraction_and_rate
#print axioms hamiltonian_iteratedIdentityPower_contraction_and_rate
#print axioms static_iteratedIdentityPower_tendsto
#print axioms potential_iteratedIdentityPower_tendsto
#print axioms growing_iteratedIdentityPower_tendsto
#print axioms residual_iteratedIdentityPower_tendsto
#print axioms hamiltonian_iteratedIdentityPower_tendsto
#print axioms hamiltonian_iteratedIdentityPower_succ_mem_ten_domains
#print axioms evolved_hamiltonian_iteratedIdentityPower_succ_regularity
#print axioms five_hamiltonians_higher_power_yosida_convergence_master

end

end UnifiedTheory.Audit.KFCausalClockFloorHigherPowerYosidaGraphConvergence
