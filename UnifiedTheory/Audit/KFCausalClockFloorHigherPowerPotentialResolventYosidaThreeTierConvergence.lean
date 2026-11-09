/- Higher-Power Shifted and Double-Shifted Potential-Resolvent Radial-Yosida Smoothers,
Two-Scale Defect Decompositions, and Three-Tier `Dom(P²)` / `Dom(P³)` Graph Convergence:
1. Establishes the higher-power domain hierarchy `operatorPowerDomain P r` (`r : ℕ`),
   `secondPowerGraph P`, `secondPowerDomain P`, `secondPowerGraphNormSq`, the `r`-fold
   iterated resolvent `iteratedResolventPower R r`, and the `r`-th power Yosida identity
   approximant `iteratedIdentityPower R a r`, together with `r`-th power domain regularity,
   contractive stability, and `(r : ℝ) * a⁻¹ * ‖P x‖` Yosida rate bounds.
2. Defines the higher-power potential-resolvent radial-Yosida state
   `higherPowerPotentialResolventYosidaState R J r f`, the Yosida-scaled identity state
   `higherPowerPotentialIdentityYosidaState R J a r f`, the `(r + 1)`-fold shifted smoother
   `higherPowerShiftedPotentialResolventYosidaApprox P R J a r x` on `x : P.domain`,
   and the `(r + 2)`-fold double-shifted smoother
   `higherPowerDoubleShiftedPotentialResolventYosidaApprox P R J a r x hx2` on `Dom(P²)`,
   proving `operatorPowerDomain` regularity, exact left-inverse collapse when `J = id`,
   and strong convergence as `n → ∞` along any strong approximant family `J n → id`.
3. Proves two-scale defect decompositions, uniform 3-tier `secondPowerGraphNormSq`
   contraction, radial-Yosida defect domination, simultaneous 3-tier convergence on
   `Dom(P²)` and `Dom(P³)` to the commuting `secondPowerGraph P` state
   `(iteratedIdentityPower R a r x, iteratedIdentityPower R a r (P x), iteratedIdentityPower R a r (P (P x)))`,
   and concrete instantiation for the self-adjoint positive closed-graph-form Hamiltonian
   `KFCausalClosedGraphForm.hamiltonian D`. -/
import UnifiedTheory.Audit.KFCausalPositiveResolventBounds
import UnifiedTheory.Audit.KFCausalClosedGraphForm
import UnifiedTheory.Audit.KFCausalFormContractiveResolventTransfer
import UnifiedTheory.Audit.KFCausalFormResolventError

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaThreeTierConvergence

noncomputable section

open Filter
open scoped Topology InnerProduct
open KFCausalPositiveResolventBounds
  (Resolves point point_value resolvent_apply_norm_bound approximation_error)
open KFCausalClosedGraphForm
  (Data FormSpace hamiltonian hamiltonian_selfAdjoint hamiltonian_positive hamiltonian_energy)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ### 1. Second-Power and Inductive Higher-Power Operator Domains -/

/-- The second-power graph of `P : H →ₗ.[ℂ] H`: pairs `(x, y) ∈ P.graph` whose output
`y = P x` also belongs to `P.domain`. -/
def secondPowerGraph (P : H →ₗ.[ℂ] H) : Submodule ℂ (H × H) :=
  P.graph ⊓ P.domain.comap (LinearMap.snd ℂ H H)

/-- The second-power domain `Dom(P²)` of `P : H →ₗ.[ℂ] H`: vectors `x ∈ P.domain`
whose first-order output `P ⟨x, hx⟩` also belongs to `P.domain`. -/
def secondPowerDomain (P : H →ₗ.[ℂ] H) : Submodule ℂ H :=
  (secondPowerGraph P).map (LinearMap.fst ℂ H H)

/-- Explicit membership characterization for `secondPowerDomain P`:
`x ∈ secondPowerDomain P ↔ ∃ hx : x ∈ P.domain, P ⟨x, hx⟩ ∈ P.domain`. -/
theorem mem_secondPowerDomain_iff (P : H →ₗ.[ℂ] H) (x : H) :
    x ∈ secondPowerDomain P ↔ ∃ hx : x ∈ P.domain, P ⟨x, hx⟩ ∈ P.domain := by
  change (∃ p : H × H, (p ∈ P.graph ∧ p.2 ∈ P.domain) ∧ p.1 = x) ↔
    ∃ hx : x ∈ P.domain, P ⟨x, hx⟩ ∈ P.domain
  constructor
  · rintro ⟨⟨f, y⟩, ⟨hfy, hy⟩, rfl⟩
    let hx : f ∈ P.domain := LinearPMap.mem_domain_of_mem_graph hfy
    have heq : P ⟨f, hx⟩ = y := P.mem_graph_snd_inj' (P.mem_graph ⟨f, hx⟩) hfy rfl
    exact ⟨hx, heq.symm ▸ hy⟩
  · rintro ⟨hx, hPx⟩
    exact ⟨(x, P ⟨x, hx⟩), ⟨P.mem_graph ⟨x, hx⟩, hPx⟩, rfl⟩

/-- The inductive `r`-th power domain `Dom(P^r)` of `P : H →ₗ.[ℂ] H`:
`operatorPowerDomain P 0 = ⊤`, and `operatorPowerDomain P (r + 1)` is the first-coordinate
image of `P.graph ⊓ (operatorPowerDomain P r).comap snd`. -/
def operatorPowerDomain (P : H →ₗ.[ℂ] H) : ℕ → Submodule ℂ H
  | 0 => ⊤
  | r + 1 =>
    (P.graph ⊓ (operatorPowerDomain P r).comap (LinearMap.snd ℂ H H)).map
      (LinearMap.fst ℂ H H)

/-- Explicit membership characterization for `operatorPowerDomain P (r + 1)`:
`x ∈ operatorPowerDomain P (r + 1) ↔ ∃ hx : x ∈ P.domain, P ⟨x, hx⟩ ∈ operatorPowerDomain P r`. -/
theorem mem_operatorPowerDomain_succ_iff (P : H →ₗ.[ℂ] H) (r : ℕ) (x : H) :
    x ∈ operatorPowerDomain P (r + 1) ↔
      ∃ hx : x ∈ P.domain, P ⟨x, hx⟩ ∈ operatorPowerDomain P r := by
  change (∃ p : H × H,
      (p ∈ P.graph ∧ p.2 ∈ operatorPowerDomain P r) ∧ p.1 = x) ↔
    ∃ hx : x ∈ P.domain, P ⟨x, hx⟩ ∈ operatorPowerDomain P r
  constructor
  · rintro ⟨⟨f, y⟩, ⟨hfy, hy⟩, rfl⟩
    let hx : f ∈ P.domain := LinearPMap.mem_domain_of_mem_graph hfy
    have heq : P ⟨f, hx⟩ = y := P.mem_graph_snd_inj' (P.mem_graph ⟨f, hx⟩) hfy rfl
    exact ⟨hx, heq.symm ▸ hy⟩
  · rintro ⟨hx, hPx⟩
    exact ⟨(x, P ⟨x, hx⟩), ⟨P.mem_graph ⟨x, hx⟩, hPx⟩, rfl⟩

/-- Exact identifications of the first three power domains:
`operatorPowerDomain P 0 = ⊤`, `operatorPowerDomain P 1 = P.domain`, and
`operatorPowerDomain P 2 = secondPowerDomain P`. -/
theorem operatorPowerDomain_zero_one_two_eq (P : H →ₗ.[ℂ] H) :
    operatorPowerDomain P 0 = ⊤ ∧
    operatorPowerDomain P 1 = P.domain ∧
    operatorPowerDomain P 2 = secondPowerDomain P := by
  refine ⟨rfl, ?_, ?_⟩
  · ext x
    rw [mem_operatorPowerDomain_succ_iff]
    exact ⟨fun ⟨hx, _⟩ => hx, fun hx => ⟨hx, Submodule.mem_top⟩⟩
  · ext x
    rw [mem_operatorPowerDomain_succ_iff, mem_secondPowerDomain_iff]
    constructor
    · rintro ⟨hx, hPx⟩
      rw [mem_operatorPowerDomain_succ_iff] at hPx
      exact ⟨hx, hPx.1⟩
    · rintro ⟨hx, hPx⟩
      refine ⟨hx, ?_⟩
      rw [mem_operatorPowerDomain_succ_iff]
      exact ⟨hPx, Submodule.mem_top⟩

/-- Step inclusion of higher-power domains:
`operatorPowerDomain P (r + 1) ≤ operatorPowerDomain P r` for all `r : ℕ`. -/
theorem operatorPowerDomain_succ_le (P : H →ₗ.[ℂ] H) :
    ∀ r : ℕ, operatorPowerDomain P (r + 1) ≤ operatorPowerDomain P r
  | 0 => le_top
  | r + 1 => by
    intro x hx
    rw [mem_operatorPowerDomain_succ_iff] at hx ⊢
    rcases hx with ⟨hx_dom, hPx⟩
    exact ⟨hx_dom, operatorPowerDomain_succ_le P r hPx⟩

/-- Antitonicity and low-order inclusions of `operatorPowerDomain P`:
`(k ≤ r → operatorPowerDomain P r ≤ operatorPowerDomain P k)`,
`operatorPowerDomain P (r + 1) ≤ P.domain`, and
`operatorPowerDomain P (r + 2) ≤ secondPowerDomain P`. -/
theorem operatorPowerDomain_le_and_low_order_inclusions (P : H →ₗ.[ℂ] H) (r : ℕ) :
    (∀ k : ℕ, k ≤ r → operatorPowerDomain P r ≤ operatorPowerDomain P k) ∧
    operatorPowerDomain P (r + 1) ≤ P.domain ∧
    operatorPowerDomain P (r + 2) ≤ secondPowerDomain P := by
  have hant : ∀ {k m : ℕ}, k ≤ m → operatorPowerDomain P m ≤ operatorPowerDomain P k :=
    fun hkm => antitone_nat_of_succ_le (operatorPowerDomain_succ_le P) hkm
  refine ⟨fun k hkr => hant hkr, ?_, ?_⟩
  · rw [← (operatorPowerDomain_zero_one_two_eq P).2.1]
    exact hant (Nat.succ_le_succ (Nat.zero_le r))
  · rw [← (operatorPowerDomain_zero_one_two_eq P).2.2]
    exact hant (Nat.add_le_add_right (Nat.zero_le r) 2)

/-- Inductive resolvent regularity shift across all higher-power domains:
if `Resolves P R a`, then `f ∈ operatorPowerDomain P r → R f ∈ operatorPowerDomain P (r + 1)`. -/
theorem resolvent_mem_operatorPowerDomain_succ (P : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves P R a) :
    ∀ r : ℕ, ∀ {f : H}, f ∈ operatorPowerDomain P r → R f ∈ operatorPowerDomain P (r + 1)
  | 0, f, _ => by
    rw [(operatorPowerDomain_zero_one_two_eq P).2.1]
    exact (point P R a hr f).property
  | r + 1, f, hf => by
    rw [mem_operatorPowerDomain_succ_iff]
    refine ⟨(point P R a hr f).property, ?_⟩
    have hpt : P ⟨R f, (point P R a hr f).property⟩ = f - (a : ℂ) • R f := by
      simpa [Complex.real_smul] using point_value P R a hr f
    rw [hpt]
    have hf_r : f ∈ operatorPowerDomain P r := operatorPowerDomain_succ_le P r hf
    have hRf : R f ∈ operatorPowerDomain P (r + 1) :=
      resolvent_mem_operatorPowerDomain_succ P R a hr r hf_r
    exact (operatorPowerDomain P (r + 1)).sub_mem hf
      ((operatorPowerDomain P (r + 1)).smul_mem (a : ℂ) hRf)

/-! ### 2. Iterated Resolvent Towers and Yosida Identity Approximants -/

/-- The `r`-fold iterated resolvent operator `R^r : H →L[ℂ] H`. -/
def iteratedResolventPower (R : H →L[ℂ] H) : ℕ → H →L[ℂ] H
  | 0 => ContinuousLinearMap.id ℂ H
  | r + 1 => R.comp (iteratedResolventPower R r)

/-- The `r`-th power Yosida identity approximant `(a • R)^r = a^r • R^r : H →L[ℂ] H`. -/
def iteratedIdentityPower (R : H →L[ℂ] H) (a : ℝ) (r : ℕ) : H →L[ℂ] H :=
  ((a ^ r : ℝ) : ℂ) • iteratedResolventPower R r

/-- Basic recurrence identities for `iteratedResolventPower` and `iteratedIdentityPower`. -/
theorem iteratedResolvent_and_identity_recurrences (R : H →L[ℂ] H) (a : ℝ) (r : ℕ) (f : H) :
    iteratedResolventPower R 0 f = f ∧
    iteratedResolventPower R 1 f = R f ∧
    iteratedResolventPower R (r + 1) f = R (iteratedResolventPower R r f) ∧
    iteratedIdentityPower R a 0 f = f ∧
    iteratedIdentityPower R a 1 f = (a : ℂ) • R f ∧
    iteratedIdentityPower R a (r + 1) f = (a : ℂ) • R (iteratedIdentityPower R a r f) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [iteratedIdentityPower, iteratedResolventPower]
  · simp [iteratedIdentityPower, iteratedResolventPower]
  · simp only [iteratedIdentityPower, iteratedResolventPower, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, map_smul, smul_smul, pow_succ', Complex.ofReal_mul]

/-- Addition law `(R^(r + s)) f = R^r (R^s f)` and one-step commutation `R^r (R f) = R (R^r f)`. -/
theorem iteratedResolventPower_add_and_comm (R : H →L[ℂ] H) (r s : ℕ) (f : H) :
    iteratedResolventPower R (r + s) f =
      iteratedResolventPower R r (iteratedResolventPower R s f) ∧
    iteratedResolventPower R r (R f) = R (iteratedResolventPower R r f) := by
  have hadd : ∀ k : ℕ, iteratedResolventPower R (k + s) f =
      iteratedResolventPower R k (iteratedResolventPower R s f) := by
    intro k
    induction k with
    | zero =>
      rw [Nat.zero_add]
      rfl
    | succ k ih =>
      rw [Nat.add_right_comm k 1 s]
      change R (iteratedResolventPower R (k + s) f) =
        R (iteratedResolventPower R k (iteratedResolventPower R s f))
      rw [ih]
  have hcomm : ∀ k : ℕ, iteratedResolventPower R k (R f) = R (iteratedResolventPower R k f) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      change R (iteratedResolventPower R k (R f)) = R (R (iteratedResolventPower R k f))
      rw [ih]
  exact ⟨hadd r, hcomm r⟩

/-- Unconditional `r`-th power domain regularity for both `iteratedResolventPower R r f`
and `iteratedIdentityPower R a r f`. -/
theorem iteratedResolvent_and_identity_mem_operatorPowerDomain
    (P : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (hr : Resolves P R a) :
    ∀ r : ℕ, ∀ f : H,
      iteratedResolventPower R r f ∈ operatorPowerDomain P r ∧
      iteratedIdentityPower R a r f ∈ operatorPowerDomain P r
  | 0, _ => ⟨Submodule.mem_top, Submodule.mem_top⟩
  | r + 1, f => by
    have hrec := (iteratedResolvent_and_identity_mem_operatorPowerDomain P R a hr r f).1
    have hres : iteratedResolventPower R (r + 1) f ∈ operatorPowerDomain P (r + 1) :=
      resolvent_mem_operatorPowerDomain_succ P R a hr r hrec
    exact ⟨hres, (operatorPowerDomain P (r + 1)).smul_mem ((a ^ (r + 1) : ℝ) : ℂ) hres⟩

/-- Geometric norm bound `‖iteratedResolventPower R r f‖ ≤ (a⁻¹) ^ r * ‖f‖` and
uniform contractive bound `‖iteratedIdentityPower R a r f‖ ≤ ‖f‖` for any positive
operator `P` resolved by `R` at `a > 0`. -/
theorem iteratedResolvent_and_identity_norm_bounds
    (P : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves P R a) (hp : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re) :
    ∀ r : ℕ, ∀ f : H,
      ‖iteratedResolventPower R r f‖ ≤ (a⁻¹) ^ r * ‖f‖ ∧
      ‖iteratedIdentityPower R a r f‖ ≤ ‖f‖ := by
  have hres : ∀ r : ℕ, ∀ f : H, ‖iteratedResolventPower R r f‖ ≤ (a⁻¹) ^ r * ‖f‖ := by
    intro r
    induction r with
    | zero => intro f; simp [iteratedResolventPower]
    | succ r ih =>
      intro f
      change ‖R (iteratedResolventPower R r f)‖ ≤ (a⁻¹) ^ (r + 1) * ‖f‖
      rw [pow_succ', mul_assoc]
      exact (resolvent_apply_norm_bound P R a ha hr hp (iteratedResolventPower R r f)).trans
        (mul_le_mul_of_nonneg_left (ih f) (inv_pos.mpr ha).le)
  intro r f
  refine ⟨hres r f, ?_⟩
  unfold iteratedIdentityPower
  rw [ContinuousLinearMap.smul_apply, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (pow_nonneg ha.le r)]
  calc
    a ^ r * ‖iteratedResolventPower R r f‖ ≤ a ^ r * ((a⁻¹) ^ r * ‖f‖) :=
      mul_le_mul_of_nonneg_left (hres r f) (pow_nonneg ha.le r)
    _ = (a * a⁻¹) ^ r * ‖f‖ := by rw [← mul_assoc, ← mul_pow]
    _ = ‖f‖ := by rw [mul_inv_cancel₀ ha.ne', one_pow, one_mul]

/-- If `R` is a left-inverse for `P + a I` on `P.domain`, then `R` preserves `P.domain`
and commutes with `P`: `P ⟨R x, hx'⟩ = R (P x)` for every `x : P.domain`. -/
theorem resolvent_commutes_with_operator_on_domain
    (P : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves P R a)
    (hl : ∀ z : P.domain, R (P z + a • (z : H)) = (z : H)) (x : P.domain) :
    P (point P R a hr (x : H)) = R (P x) := by
  have hpt := point_value P R a hr (x : H)
  have hleft := hl x
  have hmap : R (P x) + (a : ℂ) • R (x : H) = (x : H) := by
    simpa only [map_add, ContinuousLinearMap.map_smul_of_tower, Complex.real_smul] using hleft
  have hsub : (x : H) - (a : ℂ) • R (x : H) = R (P x) :=
    sub_eq_iff_eq_add.mpr hmap.symm
  simpa only [Complex.real_smul] using hpt.trans hsub

/-- By induction on `r : ℕ`, `iteratedIdentityPower R a r` preserves `P.domain` and
commutes with `P`: `P ⟨iteratedIdentityPower R a r x, _⟩ = iteratedIdentityPower R a r (P x)`. -/
theorem iteratedIdentityPower_commutes_with_operator_on_domain
    (P : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves P R a)
    (hl : ∀ z : P.domain, R (P z + a • (z : H)) = (z : H)) :
    ∀ r : ℕ, ∀ x : P.domain,
      ∃ hx : iteratedIdentityPower R a r (x : H) ∈ P.domain,
        P ⟨iteratedIdentityPower R a r (x : H), hx⟩ = iteratedIdentityPower R a r (P x)
  | 0, x => by
    have h0x : iteratedIdentityPower R a 0 (x : H) = (x : H) :=
      (iteratedResolvent_and_identity_recurrences R a 0 (x : H)).2.2.2.1
    have h0Px : iteratedIdentityPower R a 0 (P x) = P x :=
      (iteratedResolvent_and_identity_recurrences R a 0 (P x)).2.2.2.1
    refine ⟨h0x.symm ▸ x.property, ?_⟩
    have hsub : (⟨iteratedIdentityPower R a 0 (x : H), h0x.symm ▸ x.property⟩ : P.domain) = x := by
      ext
      exact h0x
    rw [hsub, h0Px]
  | r + 1, x => by
    rcases iteratedIdentityPower_commutes_with_operator_on_domain P R a hr hl r x with ⟨hxr, hPr⟩
    let ur : P.domain := ⟨iteratedIdentityPower R a r (x : H), hxr⟩
    have hstep := resolvent_commutes_with_operator_on_domain P R a hr hl ur
    have hdom : (a : ℂ) • R (ur : H) ∈ P.domain :=
      P.domain.smul_mem (a : ℂ) (point P R a hr (ur : H)).property
    have hEq : iteratedIdentityPower R a (r + 1) (x : H) = (a : ℂ) • R (ur : H) :=
      (iteratedResolvent_and_identity_recurrences R a r (x : H)).2.2.2.2.2
    refine ⟨hEq.symm ▸ hdom, ?_⟩
    have hsub : (⟨iteratedIdentityPower R a (r + 1) (x : H), hEq.symm ▸ hdom⟩ : P.domain) =
        (a : ℂ) • point P R a hr (ur : H) := by
      ext
      exact hEq
    rw [hsub, P.map_smul, hstep, hPr]
    exact ((iteratedResolvent_and_identity_recurrences R a r (P x)).2.2.2.2.2).symm

/-- Quantitative `r`-th power Yosida approximation rate on `P.domain`:
`‖iteratedIdentityPower R a r x - x‖ ≤ (r : ℝ) * a⁻¹ * ‖P x‖`. -/
theorem iteratedIdentityPower_domain_rate_bound
    (P : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves P R a) (hp : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (hl : ∀ z : P.domain, R (P z + a • (z : H)) = (z : H)) :
    ∀ r : ℕ, ∀ x : P.domain,
      ‖iteratedIdentityPower R a r (x : H) - (x : H)‖ ≤ (r : ℝ) * a⁻¹ * ‖P x‖
  | 0, x => by
    simp [(iteratedResolvent_and_identity_recurrences R a 0 (x : H)).2.2.2.1]
  | r + 1, x => by
    have hsplit :
        iteratedIdentityPower R a (r + 1) (x : H) - (x : H) =
          iteratedIdentityPower R a r ((a : ℂ) • R (x : H) - (x : H)) +
            (iteratedIdentityPower R a r (x : H) - (x : H)) := by
      have hcomm : iteratedIdentityPower R a (r + 1) (x : H) =
          iteratedIdentityPower R a r ((a : ℂ) • R (x : H)) := by
        simp only [iteratedIdentityPower, ContinuousLinearMap.smul_apply, map_smul,
          (iteratedResolventPower_add_and_comm R r 1 (x : H)).2,
          (iteratedResolvent_and_identity_recurrences R a r (x : H)).2.2.1,
          pow_succ, Complex.ofReal_mul, smul_smul, mul_comm (a ^ r) a]
      rw [hcomm, map_sub]
      abel
    rw [hsplit]
    have htri := norm_add_le
      (iteratedIdentityPower R a r ((a : ℂ) • R (x : H) - (x : H)))
      (iteratedIdentityPower R a r (x : H) - (x : H))
    have h1 :
        ‖iteratedIdentityPower R a r ((a : ℂ) • R (x : H) - (x : H))‖ ≤ a⁻¹ * ‖P x‖ := by
      refine (iteratedResolvent_and_identity_norm_bounds P R a ha hr hp r
        ((a : ℂ) • R (x : H) - (x : H))).2.trans ?_
      simpa only [Complex.real_smul] using approximation_error P R a ha hr hp hl x
    have h2 := iteratedIdentityPower_domain_rate_bound P R a ha hr hp hl r x
    push_cast
    linarith

/-! ### 3. Higher-Power Potential-Resolvent Radial-Yosida States and Shifted Smoothers -/

/-- The `r`-fold potential-resolvent radial-Yosida state `R^r (J f)` for any bounded
regularizer `J : H →L[ℂ] H`. -/
def higherPowerPotentialResolventYosidaState
    (R J : H →L[ℂ] H) (r : ℕ) (f : H) : H :=
  iteratedResolventPower R r (J f)

/-- The `r`-th power Yosida-scaled identity radial-Yosida state `(a • R)^r (J f)`. -/
def higherPowerPotentialIdentityYosidaState
    (R J : H →L[ℂ] H) (a : ℝ) (r : ℕ) (f : H) : H :=
  iteratedIdentityPower R a r (J f)

/-- The `(r + 1)`-fold shifted potential-resolvent radial-Yosida smoother on `x : P.domain`:
`R^{r+1} (J (P x + a • x))`. -/
def higherPowerShiftedPotentialResolventYosidaApprox
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (r : ℕ) (x : P.domain) : H :=
  higherPowerPotentialResolventYosidaState R J (r + 1) (P x + (a : ℂ) • (x : H))

/-- The `(r + 2)`-fold double-shifted potential-resolvent radial-Yosida smoother on
`x ∈ secondPowerDomain P`: `R^{r+2} (J (P(P x) + 2 a P x + a² x))`. -/
def higherPowerDoubleShiftedPotentialResolventYosidaApprox
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (r : ℕ)
    (x : H) (hx2 : x ∈ secondPowerDomain P) : H :=
  let hx1 : x ∈ P.domain := ((mem_secondPowerDomain_iff P x).mp hx2).choose
  let hPx1 : P ⟨x, hx1⟩ ∈ P.domain := ((mem_secondPowerDomain_iff P x).mp hx2).choose_spec
  higherPowerPotentialResolventYosidaState R J (r + 2)
    (P ⟨P ⟨x, hx1⟩, hPx1⟩ + ((2 * a : ℝ) : ℂ) • P ⟨x, hx1⟩ + ((a ^ 2 : ℝ) : ℂ) • x)

/-- Higher-power domain regularity of `higherPowerPotentialResolventYosidaState`,
`higherPowerPotentialIdentityYosidaState`, `higherPowerShiftedPotentialResolventYosidaApprox`,
and `higherPowerDoubleShiftedPotentialResolventYosidaApprox`. -/
theorem higherPowerPotentialResolventYosida_domain_regularity_package
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (hr : Resolves P R a)
    (r : ℕ) (f : H) (x : P.domain) (y : H) (hy2 : y ∈ secondPowerDomain P) :
    higherPowerPotentialResolventYosidaState R J r f ∈ operatorPowerDomain P r ∧
    higherPowerPotentialIdentityYosidaState R J a r f ∈ operatorPowerDomain P r ∧
    higherPowerShiftedPotentialResolventYosidaApprox P R J a r x ∈
      operatorPowerDomain P (r + 1) ∧
    higherPowerShiftedPotentialResolventYosidaApprox P R J a r x ∈ P.domain ∧
    higherPowerDoubleShiftedPotentialResolventYosidaApprox P R J a r y hy2 ∈
      operatorPowerDomain P (r + 2) ∧
    higherPowerDoubleShiftedPotentialResolventYosidaApprox P R J a r y hy2 ∈
      secondPowerDomain P := by
  have h1 := iteratedResolvent_and_identity_mem_operatorPowerDomain P R a hr r (J f)
  have hshift := (iteratedResolvent_and_identity_mem_operatorPowerDomain P R a hr (r + 1)
    (J (P x + (a : ℂ) • (x : H)))).1
  let hy1 : y ∈ P.domain := ((mem_secondPowerDomain_iff P y).mp hy2).choose
  let hPy1 : P ⟨y, hy1⟩ ∈ P.domain := ((mem_secondPowerDomain_iff P y).mp hy2).choose_spec
  have hdouble := (iteratedResolvent_and_identity_mem_operatorPowerDomain P R a hr (r + 2)
    (J (P ⟨P ⟨y, hy1⟩, hPy1⟩ + ((2 * a : ℝ) : ℂ) • P ⟨y, hy1⟩ + ((a ^ 2 : ℝ) : ℂ) • y))).1
  exact ⟨h1.1, h1.2, hshift,
    (operatorPowerDomain_le_and_low_order_inclusions P r).2.1 hshift,
    hdouble,
    (operatorPowerDomain_le_and_low_order_inclusions P r).2.2 hdouble⟩

/-- Exact left-inverse collapse of the shifted smoother when `J = id`:
`iteratedResolventPower R (r + 1) (P x + a • x) = iteratedResolventPower R r x`. -/
theorem higherPower_shifted_left_inverse_eq
    (P : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hl : ∀ z : P.domain, R (P z + a • (z : H)) = (z : H))
    (r : ℕ) (x : P.domain) :
    iteratedResolventPower R (r + 1) (P x + (a : ℂ) • (x : H)) =
      iteratedResolventPower R r (x : H) := by
  rw [(iteratedResolvent_and_identity_recurrences R a r (P x + (a : ℂ) • (x : H))).2.2.1,
    ← (iteratedResolventPower_add_and_comm R r 1 (P x + (a : ℂ) • (x : H))).2]
  have hlx : R (P x + (a : ℂ) • (x : H)) = (x : H) := by
    simpa only [Complex.real_smul] using hl x
  rw [hlx]

/-- Exact left-inverse collapse of the double-shifted smoother on `secondPowerDomain P` when `J = id`:
`iteratedResolventPower R (r + 2) (P(P x) + 2 a P x + a² x) = iteratedResolventPower R r x`. -/
theorem higherPower_double_shifted_left_inverse_eq
    (P : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hl : ∀ z : P.domain, R (P z + a • (z : H)) = (z : H))
    (r : ℕ) (x : H) (hx2 : x ∈ secondPowerDomain P) :
    let hx1 : x ∈ P.domain := ((mem_secondPowerDomain_iff P x).mp hx2).choose
    let hPx1 : P ⟨x, hx1⟩ ∈ P.domain := ((mem_secondPowerDomain_iff P x).mp hx2).choose_spec
    iteratedResolventPower R (r + 2)
        (P ⟨P ⟨x, hx1⟩, hPx1⟩ + ((2 * a : ℝ) : ℂ) • P ⟨x, hx1⟩ + ((a ^ 2 : ℝ) : ℂ) • x) =
      iteratedResolventPower R r x := by
  intro hx1 hPx1
  let u : P.domain := ⟨x, hx1⟩
  let v : P.domain := ⟨P u, hPx1⟩
  let w : P.domain := v + (a : ℂ) • u
  have hw_eq :
      P v + ((2 * a : ℝ) : ℂ) • P u + ((a ^ 2 : ℝ) : ℂ) • x =
        P w + (a : ℂ) • (w : H) := by
    change P v + ((2 * a : ℝ) : ℂ) • P u + ((a ^ 2 : ℝ) : ℂ) • (u : H) =
      P (v + (a : ℂ) • u) + (a : ℂ) • ((v : H) + (a : ℂ) • (u : H))
    rw [P.map_add, P.map_smul]
    change P v + ((2 * a : ℝ) : ℂ) • P u + ((a ^ 2 : ℝ) : ℂ) • (u : H) =
      (P v + (a : ℂ) • P u) + (a : ℂ) • (P u + (a : ℂ) • (u : H))
    rw [smul_add, smul_smul]
    push_cast
    module
  have hw_val : (w : H) = P u + (a : ℂ) • (u : H) := rfl
  rw [hw_eq,
    higherPower_shifted_left_inverse_eq P R a hl (r + 1) w,
    hw_val,
    higherPower_shifted_left_inverse_eq P R a hl r u]

/-- Quantitative defect bounds comparing the shifted and double-shifted smoothers
against `iteratedResolventPower R r x`. -/
theorem higherPower_shifted_and_double_shifted_defect_bounds
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves P R a) (hp : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (hl : ∀ z : P.domain, R (P z + a • (z : H)) = (z : H))
    (r : ℕ) (x : P.domain) (y : H) (hy2 : y ∈ secondPowerDomain P) :
    let hy1 : y ∈ P.domain := ((mem_secondPowerDomain_iff P y).mp hy2).choose
    let hPy1 : P ⟨y, hy1⟩ ∈ P.domain := ((mem_secondPowerDomain_iff P y).mp hy2).choose_spec
    let src2 : H := P ⟨P ⟨y, hy1⟩, hPy1⟩ + ((2 * a : ℝ) : ℂ) • P ⟨y, hy1⟩ + ((a ^ 2 : ℝ) : ℂ) • y
    ‖higherPowerShiftedPotentialResolventYosidaApprox P R J a r x -
        iteratedResolventPower R r (x : H)‖ ≤
      (a⁻¹) ^ (r + 1) * ‖J (P x + (a : ℂ) • (x : H)) - (P x + (a : ℂ) • (x : H))‖ ∧
    ‖higherPowerDoubleShiftedPotentialResolventYosidaApprox P R J a r y hy2 -
        iteratedResolventPower R r y‖ ≤
      (a⁻¹) ^ (r + 2) * ‖J src2 - src2‖ := by
  intro hy1 hPy1 src2
  constructor
  · unfold higherPowerShiftedPotentialResolventYosidaApprox higherPowerPotentialResolventYosidaState
    rw [← higherPower_shifted_left_inverse_eq P R a hl r x, ← map_sub]
    exact (iteratedResolvent_and_identity_norm_bounds P R a ha hr hp (r + 1) _).1
  · unfold higherPowerDoubleShiftedPotentialResolventYosidaApprox higherPowerPotentialResolventYosidaState
    change ‖iteratedResolventPower R (r + 2) (J src2) - iteratedResolventPower R r y‖ ≤ _
    rw [← higherPower_double_shifted_left_inverse_eq P R a hl r y hy2, ← map_sub]
    exact (iteratedResolvent_and_identity_norm_bounds P R a ha hr hp (r + 2) _).1

/-- Strong convergence as `n → ∞` of `higherPowerPotentialResolventYosidaState R (J n) r f`,
`higherPowerPotentialIdentityYosidaState R (J n) a r f`, and the shifted/double-shifted
smoothers along any strongly convergent regularizer sequence `J n → id`. -/
theorem tendsto_higherPower_smoothers_of_tendsto
    (P : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (J : ℕ → H →L[ℂ] H)
    (hJ : ∀ g : H, Tendsto (fun n => J n g) atTop (𝓝 g))
    (a : ℝ) (hl : ∀ z : P.domain, R (P z + a • (z : H)) = (z : H))
    (r : ℕ) (f : H) (x : P.domain) (y : H) (hy2 : y ∈ secondPowerDomain P) :
    Tendsto (fun n => higherPowerPotentialResolventYosidaState R (J n) r f)
      atTop (𝓝 (iteratedResolventPower R r f)) ∧
    Tendsto (fun n => higherPowerPotentialIdentityYosidaState R (J n) a r f)
      atTop (𝓝 (iteratedIdentityPower R a r f)) ∧
    Tendsto (fun n => higherPowerShiftedPotentialResolventYosidaApprox P R (J n) a r x)
      atTop (𝓝 (iteratedResolventPower R r (x : H))) ∧
    Tendsto (fun n => higherPowerDoubleShiftedPotentialResolventYosidaApprox P R (J n) a r y hy2)
      atTop (𝓝 (iteratedResolventPower R r y)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((iteratedResolventPower R r).continuous.tendsto f).comp (hJ f)
  · exact ((iteratedIdentityPower R a r).continuous.tendsto f).comp (hJ f)
  · rw [← higherPower_shifted_left_inverse_eq P R a hl r x]
    exact ((iteratedResolventPower R (r + 1)).continuous.tendsto _).comp
      (hJ (P x + (a : ℂ) • (x : H)))
  · rw [← higherPower_double_shifted_left_inverse_eq P R a hl r y hy2]
    exact ((iteratedResolventPower R (r + 2)).continuous.tendsto _).comp (hJ _)

/-! ### 4. Two-Scale Defect Decompositions and Three-Tier `Dom(P²)` / `Dom(P³)` Convergence -/

/-- The 3-tier squared graph norm `‖u‖² + ‖v‖² + ‖w‖²` for second-order operator triples. -/
def secondPowerGraphNormSq (u v w : H) : ℝ :=
  ‖u‖ ^ 2 + ‖v‖ ^ 2 + ‖w‖ ^ 2

omit [InnerProductSpace ℂ H] in
/-- Nonnegativity and zero-characterization of `secondPowerGraphNormSq`. -/
theorem secondPowerGraphNormSq_nonneg_and_zero (u v w : H) :
    0 ≤ secondPowerGraphNormSq u v w ∧
    secondPowerGraphNormSq (0 : H) (0 : H) (0 : H) = 0 := by
  unfold secondPowerGraphNormSq
  refine ⟨by positivity, by simp⟩

/-- Two-scale defect decomposition for `higherPowerPotentialIdentityYosidaState R J a r f - f`:
splits into the radial-Yosida defect `iteratedIdentityPower R a r (J f) - iteratedIdentityPower R a r f`
plus the `r`-th power Yosida identity defect `iteratedIdentityPower R a r f - f`. -/
theorem higherPowerPotentialIdentityYosidaState_two_scale_sub_eq
    (R J : H →L[ℂ] H) (a : ℝ) (r : ℕ) (f : H) :
    higherPowerPotentialIdentityYosidaState R J a r f - f =
      (higherPowerPotentialIdentityYosidaState R J a r f - iteratedIdentityPower R a r f) +
        (iteratedIdentityPower R a r f - f) := by
  abel

/-- Quantitative two-scale approximation bound on `P.domain`:
`‖higherPowerPotentialIdentityYosidaState R J a r x - x‖ ≤ ‖J x - x‖ + (r : ℝ) * a⁻¹ * ‖P x‖`. -/
theorem higherPowerPotentialIdentityYosidaState_sub_self_norm_le
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves P R a) (hp : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (hl : ∀ z : P.domain, R (P z + a • (z : H)) = (z : H))
    (r : ℕ) (x : P.domain) :
    ‖higherPowerPotentialIdentityYosidaState R J a r (x : H) - (x : H)‖ ≤
      ‖J (x : H) - (x : H)‖ + (r : ℝ) * a⁻¹ * ‖P x‖ := by
  rw [higherPowerPotentialIdentityYosidaState_two_scale_sub_eq R J a r (x : H)]
  have htri := norm_add_le
    (higherPowerPotentialIdentityYosidaState R J a r (x : H) - iteratedIdentityPower R a r (x : H))
    (iteratedIdentityPower R a r (x : H) - (x : H))
  have h1 :
      ‖higherPowerPotentialIdentityYosidaState R J a r (x : H) -
          iteratedIdentityPower R a r (x : H)‖ ≤ ‖J (x : H) - (x : H)‖ := by
    unfold higherPowerPotentialIdentityYosidaState
    rw [← map_sub]
    exact (iteratedResolvent_and_identity_norm_bounds P R a ha hr hp r (J (x : H) - (x : H))).2
  have h2 := iteratedIdentityPower_domain_rate_bound P R a ha hr hp hl r x
  linarith

/-- First-order operator action identity on `higherPowerPotentialIdentityYosidaState R J a (r + 1) f`:
`P ⟨(a • R)^{r+1}(J f), _⟩ = a • ((a • R)^r (J f) - (a • R)^{r+1} (J f))`. -/
theorem higherPowerPotentialIdentityYosidaState_first_order_action_eq
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (hr : Resolves P R a)
    (r : ℕ) (f : H) :
    P ⟨higherPowerPotentialIdentityYosidaState R J a (r + 1) f,
        (operatorPowerDomain_le_and_low_order_inclusions P r).2.1
          (higherPowerPotentialResolventYosida_domain_regularity_package
            P R J a hr (r + 1) f 0 0 (Submodule.zero_mem _)).2.1⟩ =
      (a : ℂ) • (higherPowerPotentialIdentityYosidaState R J a r f -
        higherPowerPotentialIdentityYosidaState R J a (r + 1) f) := by
  let u := higherPowerPotentialIdentityYosidaState R J a r f
  have hrec : higherPowerPotentialIdentityYosidaState R J a (r + 1) f = (a : ℂ) • R u :=
    (iteratedResolvent_and_identity_recurrences R a r (J f)).2.2.2.2.2
  have hsub :
      (⟨higherPowerPotentialIdentityYosidaState R J a (r + 1) f,
        (operatorPowerDomain_le_and_low_order_inclusions P r).2.1
          (higherPowerPotentialResolventYosida_domain_regularity_package
            P R J a hr (r + 1) f 0 0 (Submodule.zero_mem _)).2.1⟩ : P.domain) =
        (a : ℂ) • point P R a hr u := by
    ext
    exact hrec
  rw [hsub, P.map_smul, point_value P R a hr u]
  simp only [hrec]
  rfl

/-- Second-order commutation and `secondPowerGraph P` membership for `iteratedIdentityPower R a r`
on `secondPowerDomain P`. -/
theorem iteratedIdentityPower_secondPower_comm_and_graph_mem
    (P : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : Resolves P R a)
    (hl : ∀ z : P.domain, R (P z + a • (z : H)) = (z : H))
    (r : ℕ) (x : H) (hx2 : x ∈ secondPowerDomain P) :
    let hx1 : x ∈ P.domain := ((mem_secondPowerDomain_iff P x).mp hx2).choose
    let hPx1 : P ⟨x, hx1⟩ ∈ P.domain := ((mem_secondPowerDomain_iff P x).mp hx2).choose_spec
    ∃ (hu1 : iteratedIdentityPower R a r x ∈ P.domain)
      (hPu1 : P ⟨iteratedIdentityPower R a r x, hu1⟩ ∈ P.domain),
      P ⟨iteratedIdentityPower R a r x, hu1⟩ = iteratedIdentityPower R a r (P ⟨x, hx1⟩) ∧
      P ⟨P ⟨iteratedIdentityPower R a r x, hu1⟩, hPu1⟩ =
        iteratedIdentityPower R a r (P ⟨P ⟨x, hx1⟩, hPx1⟩) := by
  intro hx1 hPx1
  rcases iteratedIdentityPower_commutes_with_operator_on_domain P R a hr hl r ⟨x, hx1⟩ with ⟨hu1, hEq1⟩
  rcases iteratedIdentityPower_commutes_with_operator_on_domain P R a hr hl r ⟨P ⟨x, hx1⟩, hPx1⟩ with
    ⟨hPu1', hEq2⟩
  have hPu1 : P ⟨iteratedIdentityPower R a r x, hu1⟩ ∈ P.domain := hEq1.symm ▸ hPu1'
  refine ⟨hu1, hPu1, hEq1, ?_⟩
  have hsub : (⟨P ⟨iteratedIdentityPower R a r x, hu1⟩, hPu1⟩ : P.domain) =
      ⟨iteratedIdentityPower R a r (P ⟨x, hx1⟩), hPu1'⟩ := by
    ext
    exact hEq1
  rw [hsub, hEq2]

/-- Two-tier quantitative rate bounds on `secondPowerDomain P`:
simultaneous `‖J - id‖ + (r : ℝ) * a⁻¹ * ‖P ·‖` bounds on both tiers `(x, P x)`. -/
theorem higherPowerPotentialIdentityYosidaState_two_tier_bounds_on_secondPowerDomain
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves P R a) (hp : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (hl : ∀ z : P.domain, R (P z + a • (z : H)) = (z : H))
    (r : ℕ) (x : H) (hx2 : x ∈ secondPowerDomain P) :
    let hx1 : x ∈ P.domain := ((mem_secondPowerDomain_iff P x).mp hx2).choose
    let hPx1 : P ⟨x, hx1⟩ ∈ P.domain := ((mem_secondPowerDomain_iff P x).mp hx2).choose_spec
    ‖higherPowerPotentialIdentityYosidaState R J a r x - x‖ ≤
      ‖J x - x‖ + (r : ℝ) * a⁻¹ * ‖P ⟨x, hx1⟩‖ ∧
    ‖higherPowerPotentialIdentityYosidaState R J a r (P ⟨x, hx1⟩) - P ⟨x, hx1⟩‖ ≤
      ‖J (P ⟨x, hx1⟩) - P ⟨x, hx1⟩‖ + (r : ℝ) * a⁻¹ * ‖P ⟨P ⟨x, hx1⟩, hPx1⟩‖ := by
  intro hx1 hPx1
  exact ⟨higherPowerPotentialIdentityYosidaState_sub_self_norm_le P R J a ha hr hp hl r ⟨x, hx1⟩,
    higherPowerPotentialIdentityYosidaState_sub_self_norm_le P R J a ha hr hp hl r ⟨P ⟨x, hx1⟩, hPx1⟩⟩

/-- Three-tier quantitative rate bounds on `operatorPowerDomain P 3` (`Dom(P³)`):
simultaneous two-scale rate bounds across all three tiers `(x, P x, P(P x))`. -/
theorem higherPowerPotentialIdentityYosidaState_three_tier_bounds_on_thirdPowerDomain
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves P R a) (hp : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (hl : ∀ z : P.domain, R (P z + a • (z : H)) = (z : H))
    (r : ℕ) (x : H) (hx3 : x ∈ operatorPowerDomain P 3) :
    let hx1 : x ∈ P.domain := ((mem_operatorPowerDomain_succ_iff P 2 x).mp hx3).choose
    let hPx2 : P ⟨x, hx1⟩ ∈ operatorPowerDomain P 2 :=
      ((mem_operatorPowerDomain_succ_iff P 2 x).mp hx3).choose_spec
    let hPx1 : P ⟨x, hx1⟩ ∈ P.domain :=
      ((mem_operatorPowerDomain_succ_iff P 1 (P ⟨x, hx1⟩)).mp hPx2).choose
    let hPPx1 : P ⟨P ⟨x, hx1⟩, hPx1⟩ ∈ operatorPowerDomain P 1 :=
      ((mem_operatorPowerDomain_succ_iff P 1 (P ⟨x, hx1⟩)).mp hPx2).choose_spec
    let hPPx_dom : P ⟨P ⟨x, hx1⟩, hPx1⟩ ∈ P.domain :=
      (operatorPowerDomain_le_and_low_order_inclusions P 0).2.1 hPPx1
    ‖higherPowerPotentialIdentityYosidaState R J a r x - x‖ ≤
      ‖J x - x‖ + (r : ℝ) * a⁻¹ * ‖P ⟨x, hx1⟩‖ ∧
    ‖higherPowerPotentialIdentityYosidaState R J a r (P ⟨x, hx1⟩) - P ⟨x, hx1⟩‖ ≤
      ‖J (P ⟨x, hx1⟩) - P ⟨x, hx1⟩‖ + (r : ℝ) * a⁻¹ * ‖P ⟨P ⟨x, hx1⟩, hPx1⟩‖ ∧
    ‖higherPowerPotentialIdentityYosidaState R J a r (P ⟨P ⟨x, hx1⟩, hPx1⟩) -
        P ⟨P ⟨x, hx1⟩, hPx1⟩‖ ≤
      ‖J (P ⟨P ⟨x, hx1⟩, hPx1⟩) - P ⟨P ⟨x, hx1⟩, hPx1⟩‖ +
        (r : ℝ) * a⁻¹ * ‖P ⟨P ⟨P ⟨x, hx1⟩, hPx1⟩, hPPx_dom⟩‖ := by
  intro hx1 hPx2 hPx1 hPPx1 hPPx_dom
  exact ⟨higherPowerPotentialIdentityYosidaState_sub_self_norm_le P R J a ha hr hp hl r ⟨x, hx1⟩,
    higherPowerPotentialIdentityYosidaState_sub_self_norm_le P R J a ha hr hp hl r ⟨P ⟨x, hx1⟩, hPx1⟩,
    higherPowerPotentialIdentityYosidaState_sub_self_norm_le P R J a ha hr hp hl r
      ⟨P ⟨P ⟨x, hx1⟩, hPx1⟩, hPPx_dom⟩⟩

/-- Uniform 3-tier `secondPowerGraphNormSq` contraction and radial-Yosida defect domination:
`secondPowerGraphNormSq` of `higherPowerPotentialIdentityYosidaState` is bounded by
`secondPowerGraphNormSq (J u) (J v) (J w)` and its difference from `iteratedIdentityPower`
is dominated by `secondPowerGraphNormSq (J u - u) (J v - v) (J w - w)`. -/
theorem higherPowerPotentialIdentityYosidaState_three_tier_normSq_bounds
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves P R a) (hp : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (r : ℕ) (u v w : H) :
    secondPowerGraphNormSq
        (higherPowerPotentialIdentityYosidaState R J a r u)
        (higherPowerPotentialIdentityYosidaState R J a r v)
        (higherPowerPotentialIdentityYosidaState R J a r w) ≤
      secondPowerGraphNormSq (J u) (J v) (J w) ∧
    secondPowerGraphNormSq
        (higherPowerPotentialIdentityYosidaState R J a r u - iteratedIdentityPower R a r u)
        (higherPowerPotentialIdentityYosidaState R J a r v - iteratedIdentityPower R a r v)
        (higherPowerPotentialIdentityYosidaState R J a r w - iteratedIdentityPower R a r w) ≤
      secondPowerGraphNormSq (J u - u) (J v - v) (J w - w) := by
  unfold secondPowerGraphNormSq higherPowerPotentialIdentityYosidaState
  have h1u := (iteratedResolvent_and_identity_norm_bounds P R a ha hr hp r (J u)).2
  have h1v := (iteratedResolvent_and_identity_norm_bounds P R a ha hr hp r (J v)).2
  have h1w := (iteratedResolvent_and_identity_norm_bounds P R a ha hr hp r (J w)).2
  have h2u : ‖iteratedIdentityPower R a r (J u) - iteratedIdentityPower R a r u‖ ≤ ‖J u - u‖ := by
    rw [← map_sub]
    exact (iteratedResolvent_and_identity_norm_bounds P R a ha hr hp r (J u - u)).2
  have h2v : ‖iteratedIdentityPower R a r (J v) - iteratedIdentityPower R a r v‖ ≤ ‖J v - v‖ := by
    rw [← map_sub]
    exact (iteratedResolvent_and_identity_norm_bounds P R a ha hr hp r (J v - v)).2
  have h2w : ‖iteratedIdentityPower R a r (J w) - iteratedIdentityPower R a r w‖ ≤ ‖J w - w‖ := by
    rw [← map_sub]
    exact (iteratedResolvent_and_identity_norm_bounds P R a ha hr hp r (J w - w)).2
  constructor
  · gcongr
  · gcongr

/-- Simultaneous 3-tier convergence as `n → ∞` of `higherPowerPotentialIdentityYosidaState`
and `secondPowerGraphNormSq` along any strongly convergent regularizer sequence `J n → id`. -/
theorem tendsto_higherPowerPotentialIdentityYosidaState_three_tier
    (R : H →L[ℂ] H) (J : ℕ → H →L[ℂ] H)
    (hJ : ∀ g : H, Tendsto (fun n => J n g) atTop (𝓝 g))
    (a : ℝ) (r : ℕ) (u v w : H) :
    Tendsto (fun n => higherPowerPotentialIdentityYosidaState R (J n) a r u)
      atTop (𝓝 (iteratedIdentityPower R a r u)) ∧
    Tendsto (fun n => higherPowerPotentialIdentityYosidaState R (J n) a r v)
      atTop (𝓝 (iteratedIdentityPower R a r v)) ∧
    Tendsto (fun n => higherPowerPotentialIdentityYosidaState R (J n) a r w)
      atTop (𝓝 (iteratedIdentityPower R a r w)) ∧
    Tendsto (fun n =>
        secondPowerGraphNormSq
          (higherPowerPotentialIdentityYosidaState R (J n) a r u - iteratedIdentityPower R a r u)
          (higherPowerPotentialIdentityYosidaState R (J n) a r v - iteratedIdentityPower R a r v)
          (higherPowerPotentialIdentityYosidaState R (J n) a r w - iteratedIdentityPower R a r w))
      atTop (𝓝 0) := by
  have hu : Tendsto (fun n => higherPowerPotentialIdentityYosidaState R (J n) a r u)
      atTop (𝓝 (iteratedIdentityPower R a r u)) :=
    ((iteratedIdentityPower R a r).continuous.tendsto u).comp (hJ u)
  have hv : Tendsto (fun n => higherPowerPotentialIdentityYosidaState R (J n) a r v)
      atTop (𝓝 (iteratedIdentityPower R a r v)) :=
    ((iteratedIdentityPower R a r).continuous.tendsto v).comp (hJ v)
  have hw : Tendsto (fun n => higherPowerPotentialIdentityYosidaState R (J n) a r w)
      atTop (𝓝 (iteratedIdentityPower R a r w)) :=
    ((iteratedIdentityPower R a r).continuous.tendsto w).comp (hJ w)
  refine ⟨hu, hv, hw, ?_⟩
  unfold secondPowerGraphNormSq
  have hu0 : Tendsto (fun n =>
      ‖higherPowerPotentialIdentityYosidaState R (J n) a r u - iteratedIdentityPower R a r u‖ ^ 2)
      atTop (𝓝 0) := by
    simpa using ((tendsto_iff_norm_sub_tendsto_zero.mp hu).pow 2)
  have hv0 : Tendsto (fun n =>
      ‖higherPowerPotentialIdentityYosidaState R (J n) a r v - iteratedIdentityPower R a r v‖ ^ 2)
      atTop (𝓝 0) := by
    simpa using ((tendsto_iff_norm_sub_tendsto_zero.mp hv).pow 2)
  have hw0 : Tendsto (fun n =>
      ‖higherPowerPotentialIdentityYosidaState R (J n) a r w - iteratedIdentityPower R a r w‖ ^ 2)
      atTop (𝓝 0) := by
    simpa using ((tendsto_iff_norm_sub_tendsto_zero.mp hw).pow 2)
  simpa using (hu0.add hv0).add hw0

/-! ### 5. Concrete Instantiation for Closed-Graph-Form Self-Adjoint Positive Hamiltonians -/

section ClosedGraphFormInstantiation

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
variable [CompleteSpace H] [CompleteSpace K]

/-- For any closed-graph-form data `D : Data H K` whose self-adjoint positive Hamiltonian
`hamiltonian D` is resolved at `a > 0` by `R : H →L[ℂ] H`, the `r`-fold iterated resolvent
and `r`-th power Yosida identity approximant satisfy unconditional `operatorPowerDomain`
regularity, geometric norm decay `(a⁻¹)^r * ‖f‖`, contractive stability `≤ ‖f‖`, and the
`r`-th power Yosida domain rate bound `(r : ℝ) * a⁻¹ * ‖hamiltonian D x‖`. -/
theorem closedGraphForm_hamiltonian_higherPower_yosida_package
    (D : Data H K) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves (hamiltonian D) R a)
    (hl : ∀ z : (hamiltonian D).domain, R (hamiltonian D z + a • (z : H)) = (z : H))
    (r : ℕ) (f : H) (x : (hamiltonian D).domain) :
    IsSelfAdjoint (hamiltonian D) ∧
    (inner ℂ (hamiltonian D x) (x : H)).re =
      ‖KFCausalClosedGraphForm.energyOutput D (KFCausalClosedGraphForm.formLift D x)‖ ^ 2 ∧
    iteratedResolventPower R r f ∈ operatorPowerDomain (hamiltonian D) r ∧
    iteratedIdentityPower R a r f ∈ operatorPowerDomain (hamiltonian D) r ∧
    ‖iteratedResolventPower R r f‖ ≤ (a⁻¹) ^ r * ‖f‖ ∧
    ‖iteratedIdentityPower R a r f‖ ≤ ‖f‖ ∧
    ‖iteratedIdentityPower R a r (x : H) - (x : H)‖ ≤
      (r : ℝ) * a⁻¹ * ‖hamiltonian D x‖ := by
  have hmem := iteratedResolvent_and_identity_mem_operatorPowerDomain (hamiltonian D) R a hr r f
  have hnorm := iteratedResolvent_and_identity_norm_bounds
    (hamiltonian D) R a ha hr (hamiltonian_positive D) r f
  exact ⟨hamiltonian_selfAdjoint D,
    hamiltonian_energy D x,
    hmem.1, hmem.2, hnorm.1, hnorm.2,
    iteratedIdentityPower_domain_rate_bound
      (hamiltonian D) R a ha hr (hamiltonian_positive D) hl r x⟩

/-- Master 3-tier convergence and two-scale bound synthesis for `hamiltonian D` on
`secondPowerDomain (hamiltonian D)`. -/
theorem closedGraphForm_hamiltonian_three_tier_convergence_synthesis
    (D : Data H K) (R : H →L[ℂ] H) (J : ℕ → H →L[ℂ] H)
    (hJ : ∀ g : H, Tendsto (fun n => J n g) atTop (𝓝 g))
    (a : ℝ) (ha : 0 < a)
    (hr : Resolves (hamiltonian D) R a)
    (hl : ∀ z : (hamiltonian D).domain, R (hamiltonian D z + a • (z : H)) = (z : H))
    (r : ℕ) (n : ℕ) (x : H) (hx2 : x ∈ secondPowerDomain (hamiltonian D)) :
    let hx1 : x ∈ (hamiltonian D).domain :=
      ((mem_secondPowerDomain_iff (hamiltonian D) x).mp hx2).choose
    let hPx1 : hamiltonian D ⟨x, hx1⟩ ∈ (hamiltonian D).domain :=
      ((mem_secondPowerDomain_iff (hamiltonian D) x).mp hx2).choose_spec
    higherPowerShiftedPotentialResolventYosidaApprox (hamiltonian D) R (J n) a r ⟨x, hx1⟩ ∈
      operatorPowerDomain (hamiltonian D) (r + 1) ∧
    higherPowerDoubleShiftedPotentialResolventYosidaApprox (hamiltonian D) R (J n) a r x hx2 ∈
      operatorPowerDomain (hamiltonian D) (r + 2) ∧
    ‖higherPowerPotentialIdentityYosidaState R (J n) a r x - x‖ ≤
      ‖J n x - x‖ + (r : ℝ) * a⁻¹ * ‖hamiltonian D ⟨x, hx1⟩‖ ∧
    ‖higherPowerPotentialIdentityYosidaState R (J n) a r (hamiltonian D ⟨x, hx1⟩) -
        hamiltonian D ⟨x, hx1⟩‖ ≤
      ‖J n (hamiltonian D ⟨x, hx1⟩) - hamiltonian D ⟨x, hx1⟩‖ +
        (r : ℝ) * a⁻¹ * ‖hamiltonian D ⟨hamiltonian D ⟨x, hx1⟩, hPx1⟩‖ ∧
    Tendsto (fun k =>
        secondPowerGraphNormSq
          (higherPowerPotentialIdentityYosidaState R (J k) a r x -
            iteratedIdentityPower R a r x)
          (higherPowerPotentialIdentityYosidaState R (J k) a r (hamiltonian D ⟨x, hx1⟩) -
            iteratedIdentityPower R a r (hamiltonian D ⟨x, hx1⟩))
          (higherPowerPotentialIdentityYosidaState R (J k) a r
              (hamiltonian D ⟨hamiltonian D ⟨x, hx1⟩, hPx1⟩) -
            iteratedIdentityPower R a r (hamiltonian D ⟨hamiltonian D ⟨x, hx1⟩, hPx1⟩)))
      atTop (𝓝 0) := by
  intro hx1 hPx1
  have hreg := higherPowerPotentialResolventYosida_domain_regularity_package
    (hamiltonian D) R (J n) a hr r x ⟨x, hx1⟩ x hx2
  have htwo := higherPowerPotentialIdentityYosidaState_two_tier_bounds_on_secondPowerDomain
    (hamiltonian D) R (J n) a ha hr (hamiltonian_positive D) hl r x hx2
  have htend := (tendsto_higherPowerPotentialIdentityYosidaState_three_tier R J hJ a r
    x (hamiltonian D ⟨x, hx1⟩) (hamiltonian D ⟨hamiltonian D ⟨x, hx1⟩, hPx1⟩)).2.2.2
  exact ⟨hreg.2.2.1, hreg.2.2.2.2.1, htwo.1, htwo.2, htend⟩

/-- Contractive energy-form transfer for the positive resolvent `R` of `hamiltonian D`. -/
theorem closedGraphForm_resolvent_difference_contraction_bridge
    (D : Data H K) (F : H →L[ℂ] H)
    (lift : FormSpace D →L[ℂ] FormSpace D)
    (hJ : ∀ v, KFCausalClosedGraphForm.embedding D (lift v) =
      F (KFCausalClosedGraphForm.embedding D v))
    (hB : ∀ v, ‖KFCausalClosedGraphForm.energyOutput D (lift v)‖ ≤
      ‖KFCausalClosedGraphForm.energyOutput D v‖)
    (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hR : Resolves (hamiltonian D) R a)
    (hs : IsSelfAdjoint F) (hc : ∀ x, ‖F x‖ ≤ ‖x‖) (x : H) :
    (inner ℂ (R (a • x)) (R (a • x) - F (R (a • x)))).re ≤
      (inner ℂ x (x - F x)).re :=
  KFCausalFormContractiveResolventTransfer.resolvent_difference_contraction
    D F lift hJ hB R a ha hR hs hc x

omit [CompleteSpace H] [CompleteSpace K] in
/-- Variational form-domain approximation error and sandwich expectation error bridge
for higher-power Yosida states. -/
theorem variational_and_sandwich_error_bridge
    (J : K →L[ℂ] H) (L : K →L[ℂ] K) (R D : H →L[ℂ] H)
    (a : ℝ) (ha : 0 < a) (u v : K)
    (hv : ∀ z, inner ℂ (L v) (L z) = (a : ℂ) * inner ℂ (J u - J v) (J z))
    (hR : ∀ x, ‖R x‖ ≤ ‖x‖)
    (hs : ∀ x y, inner ℂ (R x) y = inner ℂ x (R y)) (x : H) :
    ‖J u - J v‖ ^ 2 ≤ ‖L u‖ ^ 2 / (4 * a) ∧
    ‖inner ℂ x (R (D (R x))) - inner ℂ x (D x)‖ ≤ 2 * ‖D‖ * ‖x‖ * ‖R x - x‖ :=
  ⟨KFCausalFormResolventError.variational_error_square J L a ha u v hv,
    KFCausalFormResolventError.sandwich_expectation_error R D hR hs x⟩

end ClosedGraphFormInstantiation

/-! ### 6. Additional Higher-Power Smoother Recurrences and Stability Theorems -/

/-- At `r = 0`, `higherPowerPotentialResolventYosidaState R J 0 f = J f` and
`higherPowerPotentialIdentityYosidaState R J a 0 f = J f`. -/
theorem higherPowerPotentialResolvent_and_identity_zero_eq
    (R J : H →L[ℂ] H) (a : ℝ) (f : H) :
    higherPowerPotentialResolventYosidaState R J 0 f = J f ∧
    higherPowerPotentialIdentityYosidaState R J a 0 f = J f := by
  exact ⟨rfl, (iteratedResolvent_and_identity_recurrences R a 0 (J f)).2.2.2.1⟩

/-- Step recurrence for `higherPowerPotentialResolventYosidaState` and
`higherPowerPotentialIdentityYosidaState` at order `r + 1`. -/
theorem higherPowerPotentialResolvent_and_identity_succ_eq
    (R J : H →L[ℂ] H) (a : ℝ) (r : ℕ) (f : H) :
    higherPowerPotentialResolventYosidaState R J (r + 1) f =
      R (higherPowerPotentialResolventYosidaState R J r f) ∧
    higherPowerPotentialIdentityYosidaState R J a (r + 1) f =
      (a : ℂ) • R (higherPowerPotentialIdentityYosidaState R J a r f) := by
  exact ⟨rfl, (iteratedResolvent_and_identity_recurrences R a r (J f)).2.2.2.2.2⟩

/-- Scaling relation `higherPowerPotentialIdentityYosidaState R J a r f = a^r • higherPowerPotentialResolventYosidaState R J r f`. -/
theorem higherPowerPotentialIdentityYosidaState_eq_smul
    (R J : H →L[ℂ] H) (a : ℝ) (r : ℕ) (f : H) :
    higherPowerPotentialIdentityYosidaState R J a r f =
      ((a ^ r : ℝ) : ℂ) • higherPowerPotentialResolventYosidaState R J r f :=
  rfl

/-- Step recurrence for `higherPowerShiftedPotentialResolventYosidaApprox` and
`higherPowerDoubleShiftedPotentialResolventYosidaApprox`. -/
theorem higherPowerShifted_and_doubleShifted_succ_eq
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (r : ℕ)
    (x : P.domain) (y : H) (hy2 : y ∈ secondPowerDomain P) :
    higherPowerShiftedPotentialResolventYosidaApprox P R J a (r + 1) x =
      R (higherPowerShiftedPotentialResolventYosidaApprox P R J a r x) ∧
    higherPowerDoubleShiftedPotentialResolventYosidaApprox P R J a (r + 1) y hy2 =
      R (higherPowerDoubleShiftedPotentialResolventYosidaApprox P R J a r y hy2) :=
  ⟨rfl, rfl⟩

/-- Norm bounds on `higherPowerShiftedPotentialResolventYosidaApprox` and
`higherPowerDoubleShiftedPotentialResolventYosidaApprox` when `‖J g‖ ≤ ‖g‖`. -/
theorem higherPowerShifted_and_doubleShifted_norm_bounds
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves P R a) (hp : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (hJ : ∀ g : H, ‖J g‖ ≤ ‖g‖)
    (r : ℕ) (x : P.domain) (y : H) (hy2 : y ∈ secondPowerDomain P) :
    let hy1 : y ∈ P.domain := ((mem_secondPowerDomain_iff P y).mp hy2).choose
    let hPy1 : P ⟨y, hy1⟩ ∈ P.domain := ((mem_secondPowerDomain_iff P y).mp hy2).choose_spec
    let src2 : H := P ⟨P ⟨y, hy1⟩, hPy1⟩ + ((2 * a : ℝ) : ℂ) • P ⟨y, hy1⟩ + ((a ^ 2 : ℝ) : ℂ) • y
    ‖higherPowerShiftedPotentialResolventYosidaApprox P R J a r x‖ ≤
      (a⁻¹) ^ (r + 1) * ‖P x + (a : ℂ) • (x : H)‖ ∧
    ‖higherPowerDoubleShiftedPotentialResolventYosidaApprox P R J a r y hy2‖ ≤
      (a⁻¹) ^ (r + 2) * ‖src2‖ := by
  intro hy1 hPy1 src2
  constructor
  · exact (iteratedResolvent_and_identity_norm_bounds P R a ha hr hp (r + 1)
      (J (P x + (a : ℂ) • (x : H)))).1.trans
      (mul_le_mul_of_nonneg_left (hJ _) (pow_nonneg (inv_pos.mpr ha).le (r + 1)))
  · exact (iteratedResolvent_and_identity_norm_bounds P R a ha hr hp (r + 2) (J src2)).1.trans
      (mul_le_mul_of_nonneg_left (hJ src2) (pow_nonneg (inv_pos.mpr ha).le (r + 2)))

/-- First-order operator action identity on `higherPowerShiftedPotentialResolventYosidaApprox`
and `higherPowerDoubleShiftedPotentialResolventYosidaApprox`. -/
theorem higherPowerShifted_and_doubleShifted_first_order_action_eq
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (hr : Resolves P R a)
    (r : ℕ) (x : P.domain) (y : H) (hy2 : y ∈ secondPowerDomain P) :
    let hy1 : y ∈ P.domain := ((mem_secondPowerDomain_iff P y).mp hy2).choose
    let hPy1 : P ⟨y, hy1⟩ ∈ P.domain := ((mem_secondPowerDomain_iff P y).mp hy2).choose_spec
    let src2 : H := P ⟨P ⟨y, hy1⟩, hPy1⟩ + ((2 * a : ℝ) : ℂ) • P ⟨y, hy1⟩ + ((a ^ 2 : ℝ) : ℂ) • y
    P ⟨higherPowerShiftedPotentialResolventYosidaApprox P R J a r x,
        (higherPowerPotentialResolventYosida_domain_regularity_package
          P R J a hr r x x y hy2).2.2.2.1⟩ =
      higherPowerPotentialResolventYosidaState R J r (P x + (a : ℂ) • (x : H)) -
        (a : ℂ) • higherPowerShiftedPotentialResolventYosidaApprox P R J a r x ∧
    P ⟨higherPowerDoubleShiftedPotentialResolventYosidaApprox P R J a r y hy2,
        (operatorPowerDomain_le_and_low_order_inclusions P (r + 1)).2.1
          (higherPowerPotentialResolventYosida_domain_regularity_package
            P R J a hr r x x y hy2).2.2.2.2.1⟩ =
      higherPowerPotentialResolventYosidaState R J (r + 1) src2 -
        (a : ℂ) • higherPowerDoubleShiftedPotentialResolventYosidaApprox P R J a r y hy2 := by
  intro hy1 hPy1 src2
  constructor
  · have hpt1 := point_value P R a hr
      (higherPowerPotentialResolventYosidaState R J r (P x + (a : ℂ) • (x : H)))
    have hsub1 :
        (⟨higherPowerShiftedPotentialResolventYosidaApprox P R J a r x,
          (higherPowerPotentialResolventYosida_domain_regularity_package
            P R J a hr r x x y hy2).2.2.2.1⟩ : P.domain) =
        point P R a hr
          (higherPowerPotentialResolventYosidaState R J r (P x + (a : ℂ) • (x : H))) := rfl
    rw [hsub1, hpt1]
    rfl
  · have hpt2 := point_value P R a hr
      (higherPowerPotentialResolventYosidaState R J (r + 1) src2)
    have hsub2 :
        (⟨higherPowerDoubleShiftedPotentialResolventYosidaApprox P R J a r y hy2,
          (operatorPowerDomain_le_and_low_order_inclusions P (r + 1)).2.1
            (higherPowerPotentialResolventYosida_domain_regularity_package
              P R J a hr r x x y hy2).2.2.2.2.1⟩ : P.domain) =
        point P R a hr
          (higherPowerPotentialResolventYosidaState R J (r + 1) src2) := rfl
    rw [hsub2, hpt2]
    rfl

/-- Scaled shifted smoother defect bound against `iteratedIdentityPower R a r (x : H)`:
`‖((a ^ r : ℝ) : ℂ) • higherPowerShiftedPotentialResolventYosidaApprox P R J a r x - iteratedIdentityPower R a r x‖ ≤ a⁻¹ * ‖J (P x + a • x) - (P x + a • x)‖`. -/
theorem scaled_shifted_sub_iteratedIdentityPower_norm_le
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves P R a) (hp : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (hl : ∀ z : P.domain, R (P z + a • (z : H)) = (z : H))
    (r : ℕ) (x : P.domain) :
    ‖((a ^ r : ℝ) : ℂ) • higherPowerShiftedPotentialResolventYosidaApprox P R J a r x -
        iteratedIdentityPower R a r (x : H)‖ ≤
      a⁻¹ * ‖J (P x + (a : ℂ) • (x : H)) - (P x + (a : ℂ) • (x : H))‖ := by
  unfold iteratedIdentityPower
  rw [ContinuousLinearMap.smul_apply, ← smul_sub, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (pow_nonneg ha.le r)]
  have hdef := (higherPower_shifted_and_double_shifted_defect_bounds
    P R J a ha hr hp hl r x 0 (Submodule.zero_mem _)).1
  calc
    a ^ r * ‖higherPowerShiftedPotentialResolventYosidaApprox P R J a r x -
        iteratedResolventPower R r (x : H)‖ ≤
      a ^ r * ((a⁻¹) ^ (r + 1) * ‖J (P x + (a : ℂ) • (x : H)) - (P x + (a : ℂ) • (x : H))‖) :=
      mul_le_mul_of_nonneg_left hdef (pow_nonneg ha.le r)
    _ = (a * a⁻¹) ^ r * a⁻¹ * ‖J (P x + (a : ℂ) • (x : H)) - (P x + (a : ℂ) • (x : H))‖ := by
      rw [pow_succ, ← mul_assoc, ← mul_assoc, ← mul_pow]
    _ = a⁻¹ * ‖J (P x + (a : ℂ) • (x : H)) - (P x + (a : ℂ) • (x : H))‖ := by
      rw [mul_inv_cancel₀ ha.ne', one_pow, one_mul]

/-- Mutual difference bound between the scaled shifted smoother
`((a ^ r : ℝ) : ℂ) • higherPowerShiftedPotentialResolventYosidaApprox P R J a r x`
and `higherPowerPotentialIdentityYosidaState R J a r x`. -/
theorem scaled_shifted_sub_identityYosidaState_norm_le
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves P R a) (hp : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (hl : ∀ z : P.domain, R (P z + a • (z : H)) = (z : H))
    (r : ℕ) (x : P.domain) :
    ‖((a ^ r : ℝ) : ℂ) • higherPowerShiftedPotentialResolventYosidaApprox P R J a r x -
        higherPowerPotentialIdentityYosidaState R J a r (x : H)‖ ≤
      a⁻¹ * ‖J (P x + (a : ℂ) • (x : H)) - (P x + (a : ℂ) • (x : H))‖ +
        ‖J (x : H) - (x : H)‖ := by
  have hsplit :
      ((a ^ r : ℝ) : ℂ) • higherPowerShiftedPotentialResolventYosidaApprox P R J a r x -
          higherPowerPotentialIdentityYosidaState R J a r (x : H) =
        (((a ^ r : ℝ) : ℂ) • higherPowerShiftedPotentialResolventYosidaApprox P R J a r x -
          iteratedIdentityPower R a r (x : H)) -
        (higherPowerPotentialIdentityYosidaState R J a r (x : H) -
          iteratedIdentityPower R a r (x : H)) := by
    abel
  rw [hsplit]
  have htri := norm_sub_le
    (((a ^ r : ℝ) : ℂ) • higherPowerShiftedPotentialResolventYosidaApprox P R J a r x -
      iteratedIdentityPower R a r (x : H))
    (higherPowerPotentialIdentityYosidaState R J a r (x : H) -
      iteratedIdentityPower R a r (x : H))
  have h1 := scaled_shifted_sub_iteratedIdentityPower_norm_le P R J a ha hr hp hl r x
  have h2 :
      ‖higherPowerPotentialIdentityYosidaState R J a r (x : H) -
          iteratedIdentityPower R a r (x : H)‖ ≤ ‖J (x : H) - (x : H)‖ := by
    unfold higherPowerPotentialIdentityYosidaState
    rw [← map_sub]
    exact (iteratedResolvent_and_identity_norm_bounds P R a ha hr hp r (J (x : H) - (x : H))).2
  linarith

/-- Scaled double-shifted smoother defect bound against `iteratedIdentityPower R a r y` on
`secondPowerDomain P`. -/
theorem scaled_doubleShifted_sub_iteratedIdentityPower_norm_le
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves P R a) (hp : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (hl : ∀ z : P.domain, R (P z + a • (z : H)) = (z : H))
    (r : ℕ) (y : H) (hy2 : y ∈ secondPowerDomain P) :
    let hy1 : y ∈ P.domain := ((mem_secondPowerDomain_iff P y).mp hy2).choose
    let hPy1 : P ⟨y, hy1⟩ ∈ P.domain := ((mem_secondPowerDomain_iff P y).mp hy2).choose_spec
    let src2 : H := P ⟨P ⟨y, hy1⟩, hPy1⟩ + ((2 * a : ℝ) : ℂ) • P ⟨y, hy1⟩ + ((a ^ 2 : ℝ) : ℂ) • y
    ‖((a ^ r : ℝ) : ℂ) • higherPowerDoubleShiftedPotentialResolventYosidaApprox P R J a r y hy2 -
        iteratedIdentityPower R a r y‖ ≤
      (a⁻¹) ^ 2 * ‖J src2 - src2‖ := by
  intro hy1 hPy1 src2
  unfold iteratedIdentityPower
  rw [ContinuousLinearMap.smul_apply, ← smul_sub, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (pow_nonneg ha.le r)]
  have hdef := (higherPower_shifted_and_double_shifted_defect_bounds
    P R J a ha hr hp hl r 0 y hy2).2
  calc
    a ^ r * ‖higherPowerDoubleShiftedPotentialResolventYosidaApprox P R J a r y hy2 -
        iteratedResolventPower R r y‖ ≤
      a ^ r * ((a⁻¹) ^ (r + 2) * ‖J src2 - src2‖) :=
      mul_le_mul_of_nonneg_left hdef (pow_nonneg ha.le r)
    _ = (a * a⁻¹) ^ r * (a⁻¹) ^ 2 * ‖J src2 - src2‖ := by
      rw [pow_add, ← mul_assoc, ← mul_assoc, ← mul_pow]
    _ = (a⁻¹) ^ 2 * ‖J src2 - src2‖ := by
      rw [mul_inv_cancel₀ ha.ne', one_pow, one_mul]

/-- Mutual difference bound between the scaled double-shifted smoother
`((a ^ r : ℝ) : ℂ) • higherPowerDoubleShiftedPotentialResolventYosidaApprox P R J a r y hy2`
and `higherPowerPotentialIdentityYosidaState R J a r y`. -/
theorem scaled_doubleShifted_sub_identityYosidaState_norm_le
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves P R a) (hp : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (hl : ∀ z : P.domain, R (P z + a • (z : H)) = (z : H))
    (r : ℕ) (y : H) (hy2 : y ∈ secondPowerDomain P) :
    let hy1 : y ∈ P.domain := ((mem_secondPowerDomain_iff P y).mp hy2).choose
    let hPy1 : P ⟨y, hy1⟩ ∈ P.domain := ((mem_secondPowerDomain_iff P y).mp hy2).choose_spec
    let src2 : H := P ⟨P ⟨y, hy1⟩, hPy1⟩ + ((2 * a : ℝ) : ℂ) • P ⟨y, hy1⟩ + ((a ^ 2 : ℝ) : ℂ) • y
    ‖((a ^ r : ℝ) : ℂ) • higherPowerDoubleShiftedPotentialResolventYosidaApprox P R J a r y hy2 -
        higherPowerPotentialIdentityYosidaState R J a r y‖ ≤
      (a⁻¹) ^ 2 * ‖J src2 - src2‖ + ‖J y - y‖ := by
  intro hy1 hPy1 src2
  have hsplit :
      ((a ^ r : ℝ) : ℂ) • higherPowerDoubleShiftedPotentialResolventYosidaApprox P R J a r y hy2 -
          higherPowerPotentialIdentityYosidaState R J a r y =
        (((a ^ r : ℝ) : ℂ) • higherPowerDoubleShiftedPotentialResolventYosidaApprox P R J a r y hy2 -
          iteratedIdentityPower R a r y) -
        (higherPowerPotentialIdentityYosidaState R J a r y -
          iteratedIdentityPower R a r y) := by
    abel
  rw [hsplit]
  have htri := norm_sub_le
    (((a ^ r : ℝ) : ℂ) • higherPowerDoubleShiftedPotentialResolventYosidaApprox P R J a r y hy2 -
      iteratedIdentityPower R a r y)
    (higherPowerPotentialIdentityYosidaState R J a r y -
      iteratedIdentityPower R a r y)
  have h1 := scaled_doubleShifted_sub_iteratedIdentityPower_norm_le P R J a ha hr hp hl r y hy2
  have h2 :
      ‖higherPowerPotentialIdentityYosidaState R J a r y -
          iteratedIdentityPower R a r y‖ ≤ ‖J y - y‖ := by
    unfold higherPowerPotentialIdentityYosidaState
    rw [← map_sub]
    exact (iteratedResolvent_and_identity_norm_bounds P R a ha hr hp r (J y - y)).2
  linarith

/-- Two-scale approximation bound for the scaled shifted smoother against `(x : H)` on `P.domain`:
`‖((a ^ r : ℝ) : ℂ) • higherPowerShiftedPotentialResolventYosidaApprox P R J a r x - x‖ ≤ a⁻¹ * ‖J (P x + a • x) - (P x + a • x)‖ + (r : ℝ) * a⁻¹ * ‖P x‖`. -/
theorem scaled_shifted_sub_self_two_scale_norm_le
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves P R a) (hp : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (hl : ∀ z : P.domain, R (P z + a • (z : H)) = (z : H))
    (r : ℕ) (x : P.domain) :
    ‖((a ^ r : ℝ) : ℂ) • higherPowerShiftedPotentialResolventYosidaApprox P R J a r x -
        (x : H)‖ ≤
      a⁻¹ * ‖J (P x + (a : ℂ) • (x : H)) - (P x + (a : ℂ) • (x : H))‖ +
        (r : ℝ) * a⁻¹ * ‖P x‖ := by
  have hsplit :
      ((a ^ r : ℝ) : ℂ) • higherPowerShiftedPotentialResolventYosidaApprox P R J a r x - (x : H) =
        (((a ^ r : ℝ) : ℂ) • higherPowerShiftedPotentialResolventYosidaApprox P R J a r x -
          iteratedIdentityPower R a r (x : H)) +
        (iteratedIdentityPower R a r (x : H) - (x : H)) := by
    abel
  rw [hsplit]
  have htri := norm_add_le
    (((a ^ r : ℝ) : ℂ) • higherPowerShiftedPotentialResolventYosidaApprox P R J a r x -
      iteratedIdentityPower R a r (x : H))
    (iteratedIdentityPower R a r (x : H) - (x : H))
  have h1 := scaled_shifted_sub_iteratedIdentityPower_norm_le P R J a ha hr hp hl r x
  have h2 := iteratedIdentityPower_domain_rate_bound P R a ha hr hp hl r x
  linarith

/-- Two-scale approximation bound for the scaled double-shifted smoother against `y` on
`secondPowerDomain P`. -/
theorem scaled_doubleShifted_sub_self_two_scale_norm_le
    (P : H →ₗ.[ℂ] H) (R J : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves P R a) (hp : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (hl : ∀ z : P.domain, R (P z + a • (z : H)) = (z : H))
    (r : ℕ) (y : H) (hy2 : y ∈ secondPowerDomain P) :
    let hy1 : y ∈ P.domain := ((mem_secondPowerDomain_iff P y).mp hy2).choose
    let hPy1 : P ⟨y, hy1⟩ ∈ P.domain := ((mem_secondPowerDomain_iff P y).mp hy2).choose_spec
    let src2 : H := P ⟨P ⟨y, hy1⟩, hPy1⟩ + ((2 * a : ℝ) : ℂ) • P ⟨y, hy1⟩ + ((a ^ 2 : ℝ) : ℂ) • y
    ‖((a ^ r : ℝ) : ℂ) • higherPowerDoubleShiftedPotentialResolventYosidaApprox P R J a r y hy2 -
        y‖ ≤
      (a⁻¹) ^ 2 * ‖J src2 - src2‖ + (r : ℝ) * a⁻¹ * ‖P ⟨y, hy1⟩‖ := by
  intro hy1 hPy1 src2
  have hsplit :
      ((a ^ r : ℝ) : ℂ) • higherPowerDoubleShiftedPotentialResolventYosidaApprox P R J a r y hy2 - y =
        (((a ^ r : ℝ) : ℂ) • higherPowerDoubleShiftedPotentialResolventYosidaApprox P R J a r y hy2 -
          iteratedIdentityPower R a r y) +
        (iteratedIdentityPower R a r y - y) := by
    abel
  rw [hsplit]
  have htri := norm_add_le
    (((a ^ r : ℝ) : ℂ) • higherPowerDoubleShiftedPotentialResolventYosidaApprox P R J a r y hy2 -
      iteratedIdentityPower R a r y)
    (iteratedIdentityPower R a r y - y)
  have h1 := scaled_doubleShifted_sub_iteratedIdentityPower_norm_le P R J a ha hr hp hl r y hy2
  have h2 := iteratedIdentityPower_domain_rate_bound P R a ha hr hp hl r ⟨y, hy1⟩
  linarith

#print axioms mem_secondPowerDomain_iff
#print axioms mem_operatorPowerDomain_succ_iff
#print axioms operatorPowerDomain_zero_one_two_eq
#print axioms operatorPowerDomain_succ_le
#print axioms operatorPowerDomain_le_and_low_order_inclusions
#print axioms resolvent_mem_operatorPowerDomain_succ
#print axioms iteratedResolvent_and_identity_recurrences
#print axioms iteratedResolventPower_add_and_comm
#print axioms iteratedResolvent_and_identity_mem_operatorPowerDomain
#print axioms iteratedResolvent_and_identity_norm_bounds
#print axioms resolvent_commutes_with_operator_on_domain
#print axioms iteratedIdentityPower_commutes_with_operator_on_domain
#print axioms iteratedIdentityPower_domain_rate_bound
#print axioms higherPowerPotentialResolventYosida_domain_regularity_package
#print axioms higherPower_shifted_left_inverse_eq
#print axioms higherPower_double_shifted_left_inverse_eq
#print axioms higherPower_shifted_and_double_shifted_defect_bounds
#print axioms tendsto_higherPower_smoothers_of_tendsto
#print axioms secondPowerGraphNormSq_nonneg_and_zero
#print axioms higherPowerPotentialIdentityYosidaState_two_scale_sub_eq
#print axioms higherPowerPotentialIdentityYosidaState_sub_self_norm_le
#print axioms higherPowerPotentialIdentityYosidaState_first_order_action_eq
#print axioms iteratedIdentityPower_secondPower_comm_and_graph_mem
#print axioms higherPowerPotentialIdentityYosidaState_two_tier_bounds_on_secondPowerDomain
#print axioms higherPowerPotentialIdentityYosidaState_three_tier_bounds_on_thirdPowerDomain
#print axioms higherPowerPotentialIdentityYosidaState_three_tier_normSq_bounds
#print axioms tendsto_higherPowerPotentialIdentityYosidaState_three_tier
#print axioms closedGraphForm_hamiltonian_higherPower_yosida_package
#print axioms closedGraphForm_hamiltonian_three_tier_convergence_synthesis
#print axioms closedGraphForm_resolvent_difference_contraction_bridge
#print axioms variational_and_sandwich_error_bridge
#print axioms higherPowerPotentialResolvent_and_identity_zero_eq
#print axioms higherPowerPotentialResolvent_and_identity_succ_eq
#print axioms higherPowerPotentialIdentityYosidaState_eq_smul
#print axioms higherPowerShifted_and_doubleShifted_succ_eq
#print axioms higherPowerShifted_and_doubleShifted_norm_bounds
#print axioms higherPowerShifted_and_doubleShifted_first_order_action_eq
#print axioms scaled_shifted_sub_iteratedIdentityPower_norm_le
#print axioms scaled_shifted_sub_identityYosidaState_norm_le
#print axioms scaled_doubleShifted_sub_iteratedIdentityPower_norm_le
#print axioms scaled_doubleShifted_sub_identityYosidaState_norm_le
#print axioms scaled_shifted_sub_self_two_scale_norm_le
#print axioms scaled_doubleShifted_sub_self_two_scale_norm_le

end

end UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaThreeTierConvergence
