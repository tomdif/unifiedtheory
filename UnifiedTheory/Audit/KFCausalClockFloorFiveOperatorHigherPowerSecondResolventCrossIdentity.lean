/- Five-Operator Higher-Power Second Resolvent Cross-Identities, `operatorPowerDomain`
Regularity Lifts, and Yosida Identity Cross-Difference Calculus:
1. Establishes the general higher-power cross-operator iterated resolvent difference calculus
   `iteratedResolventPower R1 r f - iteratedResolventPower R2 r f` and Yosida-scaled identity
   cross-difference calculus `iteratedIdentityPower R1 a r f - iteratedIdentityPower R2 a r f`
   for any two positive operators `A1, A2 : H →ₗ.[ℂ] H` resolved by `R1, R2` at `a > 0`:
   - Left and right step telescoping recurrences at order `r + 1` and second-order `r = 2`,
   - Geometric cross-resolvent norm bound `2 * (a⁻¹) ^ r * ‖f‖`,
   - Uniform Yosida cross-difference stability bound `≤ 2 * ‖f‖`,
   - Quantitative common-domain Yosida rate bound `(r : ℝ) * a⁻¹ * (‖A1 x‖ + ‖A2 x‖)`.
2. Proves the general operator-domain second resolvent identity
   `R1 f - R2 f = R1 (K ⟨R2 f, hK⟩)` whenever `A2 z = A1 z + K z` on `A2.domain ≤ A1.domain ⊓ K.domain`,
   and lifts it to all higher powers `r + 1`:
   - Left and right `(r + 1)`-th power second resolvent cross-identities,
   - Unconditional `operatorPowerDomain A1 (r + 1)`, `A1.domain`, and `secondPowerDomain A1`
     regularity of both `iteratedResolventPower R1 (r + 1) f - iteratedResolventPower R2 (r + 1) f`
     and `iteratedIdentityPower R1 a (r + 1) f - iteratedIdentityPower R2 a (r + 1) f`
     whenever `A2.domain ≤ A1.domain`,
   - Bounded-perturbation (`‖K z‖ ≤ M * ‖z‖`) geometric cross-resolvent bound
     `(r + 1 : ℝ) * M * (a⁻¹) ^ (r + 2) * ‖f‖` and Yosida cross-identity decay bound
     `(r + 1 : ℝ) * a⁻¹ * M * ‖f‖`.
3. Instantiates the higher-power second resolvent cross-identities, recursive perturbation
   norm bounds, `operatorPowerDomain` / `secondPowerDomain` regularity lifts, and Yosida
   identity cross-difference recurrences across all five coupled clock-floor operator pairs
   `(P, G)`, `(S, H)`, `(T, S)`, `(T, H)`, and `(P, H)` as well as coupled closed-graph-form
   self-adjoint positive Hamiltonians `KFCausalClosedGraphForm.hamiltonian D`. -/
import UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaThreeTierConvergence

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorHigherPowerSecondResolventCrossIdentity

noncomputable section

open scoped Topology InnerProduct
open KFCausalPositiveResolventBounds
  (Resolves point point_value resolvent_apply_norm_bound)
open KFCausalClosedGraphForm
  (Data hamiltonian hamiltonian_selfAdjoint hamiltonian_positive)
open KFCausalClockFloorHigherPowerPotentialResolventYosidaThreeTierConvergence
  (secondPowerDomain mem_secondPowerDomain_iff
   operatorPowerDomain mem_operatorPowerDomain_succ_iff
   operatorPowerDomain_zero_one_two_eq operatorPowerDomain_succ_le
   operatorPowerDomain_le_and_low_order_inclusions
   resolvent_mem_operatorPowerDomain_succ
   iteratedResolventPower iteratedIdentityPower
   iteratedResolvent_and_identity_recurrences
   iteratedResolventPower_add_and_comm
   iteratedResolvent_and_identity_mem_operatorPowerDomain
   iteratedResolvent_and_identity_norm_bounds
   iteratedIdentityPower_domain_rate_bound)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ### 1. Abstract Cross-Operator Iterated Resolvent and Yosida Difference Calculus -/

/-- At `r = 0`, the cross-operator iterated resolvent difference vanishes. -/
theorem iteratedResolventPower_cross_sub_zero
    (R1 R2 : H →L[ℂ] H) (f : H) :
    iteratedResolventPower R1 0 f - iteratedResolventPower R2 0 f = 0 :=
  sub_self f

/-- At `r = 1`, the cross-operator iterated resolvent difference is `R1 f - R2 f`. -/
theorem iteratedResolventPower_cross_sub_one
    (R1 R2 : H →L[ℂ] H) (f : H) :
    iteratedResolventPower R1 1 f - iteratedResolventPower R2 1 f = R1 f - R2 f :=
  rfl

/-- Left step telescoping recurrence for the cross-operator iterated resolvent difference
at order `r + 1`:
`R1^{r+1} f - R2^{r+1} f = (R1 (R1^r f) - R2 (R1^r f)) + R2 (R1^r f - R2^r f)`. -/
theorem iteratedResolventPower_cross_sub_succ_left
    (R1 R2 : H →L[ℂ] H) (r : ℕ) (f : H) :
    iteratedResolventPower R1 (r + 1) f - iteratedResolventPower R2 (r + 1) f =
      (R1 (iteratedResolventPower R1 r f) - R2 (iteratedResolventPower R1 r f)) +
        R2 (iteratedResolventPower R1 r f - iteratedResolventPower R2 r f) := by
  change R1 (iteratedResolventPower R1 r f) - R2 (iteratedResolventPower R2 r f) = _
  rw [map_sub]
  abel

/-- Right step telescoping recurrence for the cross-operator iterated resolvent difference
at order `r + 1`:
`R1^{r+1} f - R2^{r+1} f = R1 (R1^r f - R2^r f) + (R1 (R2^r f) - R2 (R2^r f))`. -/
theorem iteratedResolventPower_cross_sub_succ_right
    (R1 R2 : H →L[ℂ] H) (r : ℕ) (f : H) :
    iteratedResolventPower R1 (r + 1) f - iteratedResolventPower R2 (r + 1) f =
      R1 (iteratedResolventPower R1 r f - iteratedResolventPower R2 r f) +
        (R1 (iteratedResolventPower R2 r f) - R2 (iteratedResolventPower R2 r f)) := by
  change R1 (iteratedResolventPower R1 r f) - R2 (iteratedResolventPower R2 r f) = _
  rw [map_sub]
  abel

/-- Second-order (`r = 2`) left cross-resolvent expansion:
`R1^2 f - R2^2 f = (R1 (R1 f) - R2 (R1 f)) + R2 (R1 f - R2 f)`. -/
theorem iteratedResolventPower_cross_sub_two_left
    (R1 R2 : H →L[ℂ] H) (f : H) :
    iteratedResolventPower R1 2 f - iteratedResolventPower R2 2 f =
      (R1 (R1 f) - R2 (R1 f)) + R2 (R1 f - R2 f) :=
  iteratedResolventPower_cross_sub_succ_left R1 R2 1 f

/-- Second-order (`r = 2`) right cross-resolvent expansion:
`R1^2 f - R2^2 f = R1 (R1 f - R2 f) + (R1 (R2 f) - R2 (R2 f))`. -/
theorem iteratedResolventPower_cross_sub_two_right
    (R1 R2 : H →L[ℂ] H) (f : H) :
    iteratedResolventPower R1 2 f - iteratedResolventPower R2 2 f =
      R1 (R1 f - R2 f) + (R1 (R2 f) - R2 (R2 f)) :=
  iteratedResolventPower_cross_sub_succ_right R1 R2 1 f

/-- Geometric norm bound on the cross-operator iterated resolvent difference for any two
positive operators `A1, A2` resolved by `R1, R2` at `a > 0`:
`‖iteratedResolventPower R1 r f - iteratedResolventPower R2 r f‖ ≤ 2 * (a⁻¹) ^ r * ‖f‖`. -/
theorem iteratedResolventPower_cross_sub_norm_bound
    (A1 A2 : H →ₗ.[ℂ] H) (R1 R2 : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr1 : Resolves A1 R1 a) (hr2 : Resolves A2 R2 a)
    (hp1 : ∀ z : A1.domain, 0 ≤ (inner ℂ (A1 z) (z : H)).re)
    (hp2 : ∀ z : A2.domain, 0 ≤ (inner ℂ (A2 z) (z : H)).re)
    (r : ℕ) (f : H) :
    ‖iteratedResolventPower R1 r f - iteratedResolventPower R2 r f‖ ≤
      2 * (a⁻¹) ^ r * ‖f‖ := by
  have htri := norm_sub_le (iteratedResolventPower R1 r f) (iteratedResolventPower R2 r f)
  have h1 := (iteratedResolvent_and_identity_norm_bounds A1 R1 a ha hr1 hp1 r f).1
  have h2 := (iteratedResolvent_and_identity_norm_bounds A2 R2 a ha hr2 hp2 r f).1
  linarith

/-- Scaling relation between the cross-operator `iteratedIdentityPower` difference and
the cross-operator `iteratedResolventPower` difference. -/
theorem iteratedIdentityPower_cross_sub_eq_smul
    (R1 R2 : H →L[ℂ] H) (a : ℝ) (r : ℕ) (f : H) :
    iteratedIdentityPower R1 a r f - iteratedIdentityPower R2 a r f =
      ((a ^ r : ℝ) : ℂ) • (iteratedResolventPower R1 r f - iteratedResolventPower R2 r f) := by
  unfold iteratedIdentityPower
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_sub]

/-- At `r = 0`, `iteratedIdentityPower R1 a 0 f - iteratedIdentityPower R2 a 0 f = 0`. -/
theorem iteratedIdentityPower_cross_sub_zero
    (R1 R2 : H →L[ℂ] H) (a : ℝ) (f : H) :
    iteratedIdentityPower R1 a 0 f - iteratedIdentityPower R2 a 0 f = 0 := by
  rw [(iteratedResolvent_and_identity_recurrences R1 a 0 f).2.2.2.1,
    (iteratedResolvent_and_identity_recurrences R2 a 0 f).2.2.2.1, sub_self]

/-- At `r = 1`, `iteratedIdentityPower R1 a 1 f - iteratedIdentityPower R2 a 1 f = (a : ℂ) • (R1 f - R2 f)`. -/
theorem iteratedIdentityPower_cross_sub_one
    (R1 R2 : H →L[ℂ] H) (a : ℝ) (f : H) :
    iteratedIdentityPower R1 a 1 f - iteratedIdentityPower R2 a 1 f =
      (a : ℂ) • (R1 f - R2 f) := by
  rw [(iteratedResolvent_and_identity_recurrences R1 a 0 f).2.2.2.2.1,
    (iteratedResolvent_and_identity_recurrences R2 a 0 f).2.2.2.2.1, smul_sub]

/-- Left step recurrence for the cross-operator Yosida-scaled identity difference at `r + 1`. -/
theorem iteratedIdentityPower_cross_sub_succ_left
    (R1 R2 : H →L[ℂ] H) (a : ℝ) (r : ℕ) (f : H) :
    iteratedIdentityPower R1 a (r + 1) f - iteratedIdentityPower R2 a (r + 1) f =
      (a : ℂ) • (R1 (iteratedIdentityPower R1 a r f) - R2 (iteratedIdentityPower R1 a r f)) +
        (a : ℂ) • R2 (iteratedIdentityPower R1 a r f - iteratedIdentityPower R2 a r f) := by
  rw [(iteratedResolvent_and_identity_recurrences R1 a r f).2.2.2.2.2,
    (iteratedResolvent_and_identity_recurrences R2 a r f).2.2.2.2.2,
    map_sub, smul_sub, smul_sub]
  abel

/-- Right step recurrence for the cross-operator Yosida-scaled identity difference at `r + 1`. -/
theorem iteratedIdentityPower_cross_sub_succ_right
    (R1 R2 : H →L[ℂ] H) (a : ℝ) (r : ℕ) (f : H) :
    iteratedIdentityPower R1 a (r + 1) f - iteratedIdentityPower R2 a (r + 1) f =
      (a : ℂ) • R1 (iteratedIdentityPower R1 a r f - iteratedIdentityPower R2 a r f) +
        (a : ℂ) • (R1 (iteratedIdentityPower R2 a r f) - R2 (iteratedIdentityPower R2 a r f)) := by
  rw [(iteratedResolvent_and_identity_recurrences R1 a r f).2.2.2.2.2,
    (iteratedResolvent_and_identity_recurrences R2 a r f).2.2.2.2.2,
    map_sub, smul_sub, smul_sub]
  abel

/-- Uniform stability bound `≤ 2 * ‖f‖` on the cross-operator Yosida-scaled identity difference. -/
theorem iteratedIdentityPower_cross_sub_norm_le_two
    (A1 A2 : H →ₗ.[ℂ] H) (R1 R2 : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr1 : Resolves A1 R1 a) (hr2 : Resolves A2 R2 a)
    (hp1 : ∀ z : A1.domain, 0 ≤ (inner ℂ (A1 z) (z : H)).re)
    (hp2 : ∀ z : A2.domain, 0 ≤ (inner ℂ (A2 z) (z : H)).re)
    (r : ℕ) (f : H) :
    ‖iteratedIdentityPower R1 a r f - iteratedIdentityPower R2 a r f‖ ≤ 2 * ‖f‖ := by
  have htri := norm_sub_le (iteratedIdentityPower R1 a r f) (iteratedIdentityPower R2 a r f)
  have h1 := (iteratedResolvent_and_identity_norm_bounds A1 R1 a ha hr1 hp1 r f).2
  have h2 := (iteratedResolvent_and_identity_norm_bounds A2 R2 a ha hr2 hp2 r f).2
  linarith

/-- Decomposition of the cross-operator Yosida identity difference through `f`:
`iteratedIdentityPower R1 a r f - iteratedIdentityPower R2 a r f = (iteratedIdentityPower R1 a r f - f) - (iteratedIdentityPower R2 a r f - f)`. -/
theorem iteratedIdentityPower_cross_sub_split_via_self
    (R1 R2 : H →L[ℂ] H) (a : ℝ) (r : ℕ) (f : H) :
    iteratedIdentityPower R1 a r f - iteratedIdentityPower R2 a r f =
      (iteratedIdentityPower R1 a r f - f) - (iteratedIdentityPower R2 a r f - f) := by
  abel

/-- Quantitative cross-operator Yosida rate bound on `A1.domain ∩ A2.domain`:
`‖iteratedIdentityPower R1 a r x - iteratedIdentityPower R2 a r x‖ ≤ (r : ℝ) * a⁻¹ * (‖A1 ⟨x, hx1⟩‖ + ‖A2 ⟨x, hx2⟩‖)`. -/
theorem iteratedIdentityPower_cross_sub_domain_rate_bound
    (A1 A2 : H →ₗ.[ℂ] H) (R1 R2 : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr1 : Resolves A1 R1 a) (hr2 : Resolves A2 R2 a)
    (hp1 : ∀ z : A1.domain, 0 ≤ (inner ℂ (A1 z) (z : H)).re)
    (hp2 : ∀ z : A2.domain, 0 ≤ (inner ℂ (A2 z) (z : H)).re)
    (hl1 : ∀ z : A1.domain, R1 (A1 z + a • (z : H)) = (z : H))
    (hl2 : ∀ z : A2.domain, R2 (A2 z + a • (z : H)) = (z : H))
    (r : ℕ) (x : H) (hx1 : x ∈ A1.domain) (hx2 : x ∈ A2.domain) :
    ‖iteratedIdentityPower R1 a r x - iteratedIdentityPower R2 a r x‖ ≤
      (r : ℝ) * a⁻¹ * (‖A1 ⟨x, hx1⟩‖ + ‖A2 ⟨x, hx2⟩‖) := by
  rw [iteratedIdentityPower_cross_sub_split_via_self R1 R2 a r x]
  have htri := norm_sub_le
    (iteratedIdentityPower R1 a r x - x)
    (iteratedIdentityPower R2 a r x - x)
  have h1 := iteratedIdentityPower_domain_rate_bound A1 R1 a ha hr1 hp1 hl1 r ⟨x, hx1⟩
  have h2 := iteratedIdentityPower_domain_rate_bound A2 R2 a ha hr2 hp2 hl2 r ⟨x, hx2⟩
  have hring :
      (r : ℝ) * a⁻¹ * ‖A1 ⟨x, hx1⟩‖ + (r : ℝ) * a⁻¹ * ‖A2 ⟨x, hx2⟩‖ =
        (r : ℝ) * a⁻¹ * (‖A1 ⟨x, hx1⟩‖ + ‖A2 ⟨x, hx2⟩‖) := by
    ring
  linarith

/-! ### 2. General Second Resolvent Identity and Higher-Power Domain Regularity Lifts -/

/-- General second resolvent identity: if `A2` is a perturbation of `A1` by `K` on `A2.domain`
(`hdom : A2.domain ≤ A1.domain`, `hK : A2.domain ≤ K.domain`, and
`hadd : ∀ z : A2.domain, A2 z = A1 ⟨z, hdom z.2⟩ + K ⟨z, hK z.2⟩`), `R2` resolves `A2` at `a`,
and `R1` is left-inverse for `A1 + a I` on `A1.domain`, then for every `f : H`,
`R1 f - R2 f = R1 (K ⟨R2 f, hK (point A2 R2 a hr2 f).2⟩)`. -/
theorem general_second_resolvent_identity
    (A1 A2 K : H →ₗ.[ℂ] H) (R1 R2 : H →L[ℂ] H) (a : ℝ)
    (hr2 : Resolves A2 R2 a)
    (hl1 : ∀ z : A1.domain, R1 (A1 z + a • (z : H)) = (z : H))
    (hdom : A2.domain ≤ A1.domain) (hK : A2.domain ≤ K.domain)
    (hadd : ∀ z : A2.domain, A2 z = A1 ⟨(z : H), hdom z.property⟩ + K ⟨(z : H), hK z.property⟩)
    (f : H) :
    R1 f - R2 f = R1 (K ⟨R2 f, hK (point A2 R2 a hr2 f).property⟩) := by
  let u2 : A2.domain := point A2 R2 a hr2 f
  let u1 : A1.domain := ⟨R2 f, hdom u2.property⟩
  let uK : K.domain := ⟨R2 f, hK u2.property⟩
  have hpt : A2 u2 = f - a • R2 f := point_value A2 R2 a hr2 f
  have hf_eq : f = (A1 u1 + a • (u1 : H)) + K uK := by
    have h1 : f = A2 u2 + a • (u1 : H) := sub_eq_iff_eq_add.mp hpt.symm
    have h2 : A2 u2 = A1 u1 + K uK := hadd u2
    calc
      f = A2 u2 + a • (u1 : H) := h1
      _ = (A1 u1 + K uK) + a • (u1 : H) := by rw [h2]
      _ = (A1 u1 + a • (u1 : H)) + K uK := by abel
  have hR1f : R1 f = R2 f + R1 (K uK) := by
    calc
      R1 f = R1 ((A1 u1 + a • (u1 : H)) + K uK) := congrArg R1 hf_eq
      _ = R1 (A1 u1 + a • (u1 : H)) + R1 (K uK) := map_add R1 _ _
      _ = R2 f + R1 (K uK) := by rw [hl1 u1]
  exact sub_eq_iff_eq_add'.mpr hR1f

/-- Whenever `A2.domain ≤ A1.domain`, for every `r : ℕ` and `f : H`, the `(r + 1)`-th power
cross-operator resolvent difference `iteratedResolventPower R1 (r + 1) f - iteratedResolventPower R2 (r + 1) f`
and Yosida identity cross-difference `iteratedIdentityPower R1 a (r + 1) f - iteratedIdentityPower R2 a (r + 1) f`
both belong to `A1.domain`. -/
theorem cross_sub_succ_mem_first_domain
    (A1 A2 : H →ₗ.[ℂ] H) (R1 R2 : H →L[ℂ] H) (a : ℝ)
    (hr1 : Resolves A1 R1 a) (hr2 : Resolves A2 R2 a)
    (hdom : A2.domain ≤ A1.domain) (r : ℕ) (f : H) :
    iteratedResolventPower R1 (r + 1) f - iteratedResolventPower R2 (r + 1) f ∈ A1.domain ∧
    iteratedIdentityPower R1 a (r + 1) f - iteratedIdentityPower R2 a (r + 1) f ∈ A1.domain := by
  have h1 : iteratedResolventPower R1 (r + 1) f ∈ A1.domain :=
    (point A1 R1 a hr1 (iteratedResolventPower R1 r f)).property
  have h2 : iteratedResolventPower R2 (r + 1) f ∈ A1.domain :=
    hdom (point A2 R2 a hr2 (iteratedResolventPower R2 r f)).property
  have hsub := A1.domain.sub_mem h1 h2
  refine ⟨hsub, ?_⟩
  rw [iteratedIdentityPower_cross_sub_eq_smul]
  exact A1.domain.smul_mem ((a ^ (r + 1) : ℝ) : ℂ) hsub

/-- If `K` maps `A2.domain` into `A1.domain` (`∀ z : A2.domain, K ⟨z, hK z.2⟩ ∈ A1.domain`)
and `R2` preserves `A1.domain` (`∀ g ∈ A1.domain, R2 g ∈ A1.domain`), then for every `r : ℕ`
and `f : H`, the cross-operator iterated resolvent difference
`iteratedResolventPower R1 (r + 1) f - iteratedResolventPower R2 (r + 1) f` belongs to
`secondPowerDomain A1`! -/
theorem cross_sub_succ_mem_secondPowerDomain
    (A1 A2 K : H →ₗ.[ℂ] H) (R1 R2 : H →L[ℂ] H) (a : ℝ)
    (hr1 : Resolves A1 R1 a) (hr2 : Resolves A2 R2 a)
    (hl1 : ∀ z : A1.domain, R1 (A1 z + a • (z : H)) = (z : H))
    (hdom : A2.domain ≤ A1.domain) (hK : A2.domain ≤ K.domain)
    (hadd : ∀ z : A2.domain, A2 z = A1 ⟨(z : H), hdom z.property⟩ + K ⟨(z : H), hK z.property⟩)
    (hK_dom : ∀ z : A2.domain, K ⟨(z : H), hK z.property⟩ ∈ A1.domain)
    (hR2_pres : ∀ g : H, g ∈ secondPowerDomain A1 → R2 g ∈ secondPowerDomain A1) :
    ∀ r : ℕ, ∀ f : H,
      iteratedResolventPower R1 (r + 1) f - iteratedResolventPower R2 (r + 1) f ∈
        secondPowerDomain A1 ∧
      iteratedIdentityPower R1 a (r + 1) f - iteratedIdentityPower R2 a (r + 1) f ∈
        secondPowerDomain A1
  | 0, f => by
    have hbase : iteratedResolventPower R1 1 f - iteratedResolventPower R2 1 f =
        R1 (K ⟨R2 f, hK (point A2 R2 a hr2 f).property⟩) :=
      general_second_resolvent_identity A1 A2 K R1 R2 a hr2 hl1 hdom hK hadd f
    have hK_in : K ⟨R2 f, hK (point A2 R2 a hr2 f).property⟩ ∈ operatorPowerDomain A1 1 := by
      rw [(operatorPowerDomain_zero_one_two_eq A1).2.1]
      exact hK_dom (point A2 R2 a hr2 f)
    have hR1K : R1 (K ⟨R2 f, hK (point A2 R2 a hr2 f).property⟩) ∈ secondPowerDomain A1 := by
      rw [← (operatorPowerDomain_zero_one_two_eq A1).2.2]
      exact resolvent_mem_operatorPowerDomain_succ A1 R1 a hr1 1 hK_in
    have hres : iteratedResolventPower R1 1 f - iteratedResolventPower R2 1 f ∈
        secondPowerDomain A1 := hbase.symm ▸ hR1K
    refine ⟨hres, ?_⟩
    rw [iteratedIdentityPower_cross_sub_eq_smul]
    exact (secondPowerDomain A1).smul_mem ((a ^ 1 : ℝ) : ℂ) hres
  | r + 1, f => by
    have hrec := (cross_sub_succ_mem_secondPowerDomain A1 A2 K R1 R2 a hr1 hr2 hl1
      hdom hK hadd hK_dom hR2_pres r f).1
    have hlead :
        R1 (iteratedResolventPower R1 (r + 1) f) - R2 (iteratedResolventPower R1 (r + 1) f) ∈
          secondPowerDomain A1 :=
      (cross_sub_succ_mem_secondPowerDomain A1 A2 K R1 R2 a hr1 hr2 hl1
        hdom hK hadd hK_dom hR2_pres 0 (iteratedResolventPower R1 (r + 1) f)).1
    have hstep :
        R2 (iteratedResolventPower R1 (r + 1) f - iteratedResolventPower R2 (r + 1) f) ∈
          secondPowerDomain A1 :=
      hR2_pres _ hrec
    have hsum : iteratedResolventPower R1 (r + 2) f - iteratedResolventPower R2 (r + 2) f ∈
        secondPowerDomain A1 := by
      rw [iteratedResolventPower_cross_sub_succ_left R1 R2 (r + 1) f]
      exact (secondPowerDomain A1).add_mem hlead hstep
    refine ⟨hsum, ?_⟩
    rw [iteratedIdentityPower_cross_sub_eq_smul]
    exact (secondPowerDomain A1).smul_mem ((a ^ (r + 2) : ℝ) : ℂ) hsum

/-- Left and right higher-power second resolvent cross-identities at order `r + 1`
under `general_second_resolvent_identity`. -/
theorem higherPower_second_resolvent_cross_identities_left_and_right
    (A1 A2 K : H →ₗ.[ℂ] H) (R1 R2 : H →L[ℂ] H) (a : ℝ)
    (hr2 : Resolves A2 R2 a)
    (hl1 : ∀ z : A1.domain, R1 (A1 z + a • (z : H)) = (z : H))
    (hdom : A2.domain ≤ A1.domain) (hK : A2.domain ≤ K.domain)
    (hadd : ∀ z : A2.domain, A2 z = A1 ⟨(z : H), hdom z.property⟩ + K ⟨(z : H), hK z.property⟩)
    (r : ℕ) (f : H) :
    iteratedResolventPower R1 (r + 1) f - iteratedResolventPower R2 (r + 1) f =
      R1 (K ⟨R2 (iteratedResolventPower R1 r f),
        hK (point A2 R2 a hr2 (iteratedResolventPower R1 r f)).property⟩) +
      R2 (iteratedResolventPower R1 r f - iteratedResolventPower R2 r f) ∧
    iteratedResolventPower R1 (r + 1) f - iteratedResolventPower R2 (r + 1) f =
      R1 (iteratedResolventPower R1 r f - iteratedResolventPower R2 r f) +
      R1 (K ⟨R2 (iteratedResolventPower R2 r f),
        hK (point A2 R2 a hr2 (iteratedResolventPower R2 r f)).property⟩) := by
  constructor
  · rw [iteratedResolventPower_cross_sub_succ_left R1 R2 r f,
      general_second_resolvent_identity A1 A2 K R1 R2 a hr2 hl1 hdom hK hadd
        (iteratedResolventPower R1 r f)]
  · rw [iteratedResolventPower_cross_sub_succ_right R1 R2 r f,
      general_second_resolvent_identity A1 A2 K R1 R2 a hr2 hl1 hdom hK hadd
        (iteratedResolventPower R2 r f)]

/-- Recursive perturbation norm bound for `iteratedResolventPower R1 (r + 1) f - iteratedResolventPower R2 (r + 1) f`
and `iteratedIdentityPower R1 a (r + 1) f - iteratedIdentityPower R2 a (r + 1) f`. -/
theorem higherPower_second_resolvent_recursive_norm_bounds
    (A1 A2 K : H →ₗ.[ℂ] H) (R1 R2 : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr1 : Resolves A1 R1 a) (hr2 : Resolves A2 R2 a)
    (hp1 : ∀ z : A1.domain, 0 ≤ (inner ℂ (A1 z) (z : H)).re)
    (hp2 : ∀ z : A2.domain, 0 ≤ (inner ℂ (A2 z) (z : H)).re)
    (hl1 : ∀ z : A1.domain, R1 (A1 z + a • (z : H)) = (z : H))
    (hdom : A2.domain ≤ A1.domain) (hK : A2.domain ≤ K.domain)
    (hadd : ∀ z : A2.domain, A2 z = A1 ⟨(z : H), hdom z.property⟩ + K ⟨(z : H), hK z.property⟩)
    (r : ℕ) (f : H) :
    ‖iteratedResolventPower R1 (r + 1) f - iteratedResolventPower R2 (r + 1) f‖ ≤
      a⁻¹ * ‖K ⟨R2 (iteratedResolventPower R1 r f),
        hK (point A2 R2 a hr2 (iteratedResolventPower R1 r f)).property⟩‖ +
      a⁻¹ * ‖iteratedResolventPower R1 r f - iteratedResolventPower R2 r f‖ ∧
    ‖iteratedIdentityPower R1 a (r + 1) f - iteratedIdentityPower R2 a (r + 1) f‖ ≤
      ‖K ⟨R2 (iteratedIdentityPower R1 a r f),
        hK (point A2 R2 a hr2 (iteratedIdentityPower R1 a r f)).property⟩‖ +
      ‖iteratedIdentityPower R1 a r f - iteratedIdentityPower R2 a r f‖ := by
  constructor
  · rw [(higherPower_second_resolvent_cross_identities_left_and_right
      A1 A2 K R1 R2 a hr2 hl1 hdom hK hadd r f).1]
    have htri := norm_add_le
      (R1 (K ⟨R2 (iteratedResolventPower R1 r f),
        hK (point A2 R2 a hr2 (iteratedResolventPower R1 r f)).property⟩))
      (R2 (iteratedResolventPower R1 r f - iteratedResolventPower R2 r f))
    have h1 := resolvent_apply_norm_bound A1 R1 a ha hr1 hp1
      (K ⟨R2 (iteratedResolventPower R1 r f),
        hK (point A2 R2 a hr2 (iteratedResolventPower R1 r f)).property⟩)
    have h2 := resolvent_apply_norm_bound A2 R2 a ha hr2 hp2
      (iteratedResolventPower R1 r f - iteratedResolventPower R2 r f)
    linarith
  · rw [iteratedIdentityPower_cross_sub_succ_left R1 R2 a r f,
      general_second_resolvent_identity A1 A2 K R1 R2 a hr2 hl1 hdom hK hadd
        (iteratedIdentityPower R1 a r f)]
    have htri := norm_add_le
      ((a : ℂ) • R1 (K ⟨R2 (iteratedIdentityPower R1 a r f),
        hK (point A2 R2 a hr2 (iteratedIdentityPower R1 a r f)).property⟩))
      ((a : ℂ) • R2 (iteratedIdentityPower R1 a r f - iteratedIdentityPower R2 a r f))
    have h1 :
        ‖(a : ℂ) • R1 (K ⟨R2 (iteratedIdentityPower R1 a r f),
          hK (point A2 R2 a hr2 (iteratedIdentityPower R1 a r f)).property⟩)‖ ≤
          ‖K ⟨R2 (iteratedIdentityPower R1 a r f),
            hK (point A2 R2 a hr2 (iteratedIdentityPower R1 a r f)).property⟩‖ := by
      rw [← (iteratedResolvent_and_identity_recurrences R1 a 0 _).2.2.2.2.1]
      exact (iteratedResolvent_and_identity_norm_bounds A1 R1 a ha hr1 hp1 1 _).2
    have h2 :
        ‖(a : ℂ) • R2 (iteratedIdentityPower R1 a r f - iteratedIdentityPower R2 a r f)‖ ≤
          ‖iteratedIdentityPower R1 a r f - iteratedIdentityPower R2 a r f‖ := by
      rw [← (iteratedResolvent_and_identity_recurrences R2 a 0 _).2.2.2.2.1]
      exact (iteratedResolvent_and_identity_norm_bounds A2 R2 a ha hr2 hp2 1 _).2
    linarith

/-- Closed-form geometric perturbation bound `(r : ℝ) * M * (a⁻¹) ^ (r + 1) * ‖f‖` for
`‖iteratedResolventPower R1 r f - iteratedResolventPower R2 r f‖` and `(r : ℝ) * a⁻¹ * M * ‖f‖`
for `‖iteratedIdentityPower R1 a r f - iteratedIdentityPower R2 a r f‖` whenever `K` satisfies
`‖K z‖ ≤ M * ‖z‖`. -/
theorem higherPower_second_resolvent_bounded_perturbation_rates
    (A1 A2 K : H →ₗ.[ℂ] H) (R1 R2 : H →L[ℂ] H) (a M : ℝ) (ha : 0 < a) (hM : 0 ≤ M)
    (hr1 : Resolves A1 R1 a) (hr2 : Resolves A2 R2 a)
    (hp1 : ∀ z : A1.domain, 0 ≤ (inner ℂ (A1 z) (z : H)).re)
    (hp2 : ∀ z : A2.domain, 0 ≤ (inner ℂ (A2 z) (z : H)).re)
    (hl1 : ∀ z : A1.domain, R1 (A1 z + a • (z : H)) = (z : H))
    (hdom : A2.domain ≤ A1.domain) (hK : A2.domain ≤ K.domain)
    (hadd : ∀ z : A2.domain, A2 z = A1 ⟨(z : H), hdom z.property⟩ + K ⟨(z : H), hK z.property⟩)
    (hK_bound : ∀ z : K.domain, ‖K z‖ ≤ M * ‖(z : H)‖) :
    ∀ r : ℕ, ∀ f : H,
      ‖iteratedResolventPower R1 r f - iteratedResolventPower R2 r f‖ ≤
        (r : ℝ) * M * (a⁻¹) ^ (r + 1) * ‖f‖ ∧
      ‖iteratedIdentityPower R1 a r f - iteratedIdentityPower R2 a r f‖ ≤
        (r : ℝ) * a⁻¹ * M * ‖f‖
  | 0, f => by
    simp [iteratedResolventPower_cross_sub_zero, iteratedIdentityPower_cross_sub_zero]
  | r + 1, f => by
    have ih := higherPower_second_resolvent_bounded_perturbation_rates
      A1 A2 K R1 R2 a M ha hM hr1 hr2 hp1 hp2 hl1 hdom hK hadd hK_bound r f
    have hrec := higherPower_second_resolvent_recursive_norm_bounds
      A1 A2 K R1 R2 a ha hr1 hr2 hp1 hp2 hl1 hdom hK hadd r f
    have hK1 :
        ‖K ⟨R2 (iteratedResolventPower R1 r f),
          hK (point A2 R2 a hr2 (iteratedResolventPower R1 r f)).property⟩‖ ≤
          M * (a⁻¹) ^ (r + 1) * ‖f‖ := by
      have hb1 := hK_bound ⟨R2 (iteratedResolventPower R1 r f),
        hK (point A2 R2 a hr2 (iteratedResolventPower R1 r f)).property⟩
      have hb2 := resolvent_apply_norm_bound A2 R2 a ha hr2 hp2 (iteratedResolventPower R1 r f)
      have hb3 := (iteratedResolvent_and_identity_norm_bounds A1 R1 a ha hr1 hp1 r f).1
      calc
        ‖K ⟨R2 (iteratedResolventPower R1 r f), _⟩‖ ≤
          M * ‖R2 (iteratedResolventPower R1 r f)‖ := hb1
        _ ≤ M * (a⁻¹ * ‖iteratedResolventPower R1 r f‖) :=
          mul_le_mul_of_nonneg_left hb2 hM
        _ ≤ M * (a⁻¹ * ((a⁻¹) ^ r * ‖f‖)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hb3 (inv_pos.mpr ha).le) hM
        _ = M * (a⁻¹) ^ (r + 1) * ‖f‖ := by
          rw [pow_succ']
          ring
    have hK2 :
        ‖K ⟨R2 (iteratedIdentityPower R1 a r f),
          hK (point A2 R2 a hr2 (iteratedIdentityPower R1 a r f)).property⟩‖ ≤
          a⁻¹ * M * ‖f‖ := by
      have hb1 := hK_bound ⟨R2 (iteratedIdentityPower R1 a r f),
        hK (point A2 R2 a hr2 (iteratedIdentityPower R1 a r f)).property⟩
      have hb2 := resolvent_apply_norm_bound A2 R2 a ha hr2 hp2 (iteratedIdentityPower R1 a r f)
      have hb3 := (iteratedResolvent_and_identity_norm_bounds A1 R1 a ha hr1 hp1 r f).2
      calc
        ‖K ⟨R2 (iteratedIdentityPower R1 a r f), _⟩‖ ≤
          M * ‖R2 (iteratedIdentityPower R1 a r f)‖ := hb1
        _ ≤ M * (a⁻¹ * ‖iteratedIdentityPower R1 a r f‖) :=
          mul_le_mul_of_nonneg_left hb2 hM
        _ ≤ M * (a⁻¹ * ‖f‖) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hb3 (inv_pos.mpr ha).le) hM
        _ = a⁻¹ * M * ‖f‖ := by ring
    constructor
    · calc
        ‖iteratedResolventPower R1 (r + 1) f - iteratedResolventPower R2 (r + 1) f‖ ≤
          a⁻¹ * (M * (a⁻¹) ^ (r + 1) * ‖f‖) +
            a⁻¹ * ((r : ℝ) * M * (a⁻¹) ^ (r + 1) * ‖f‖) := by
          refine hrec.1.trans (add_le_add ?_ ?_)
          · exact mul_le_mul_of_nonneg_left hK1 (inv_pos.mpr ha).le
          · exact mul_le_mul_of_nonneg_left ih.1 (inv_pos.mpr ha).le
        _ = ((r + 1 : ℕ) : ℝ) * M * (a⁻¹) ^ (r + 2) * ‖f‖ := by
          push_cast
          rw [pow_succ' (a⁻¹) (r + 1)]
          ring
    · calc
        ‖iteratedIdentityPower R1 a (r + 1) f - iteratedIdentityPower R2 a (r + 1) f‖ ≤
          a⁻¹ * M * ‖f‖ + (r : ℝ) * a⁻¹ * M * ‖f‖ :=
          hrec.2.trans (add_le_add hK2 ih.2)
        _ = ((r + 1 : ℕ) : ℝ) * a⁻¹ * M * ‖f‖ := by
          push_cast
          ring

/-! ### 3. Five-Operator Clock-Floor Hamiltonian System `(T, P, G, S, H)` Cross-Identities -/

/-- Bundled five-operator clock-floor Hamiltonian system `(T, P, G, S, H)` with positive
resolvents `(RT, RP, RG, RS, RH)` at shift `a > 0` and radial perturbation `K`:
1. `G = P + K` on `G.domain ≤ P.domain ⊓ K.domain`,
2. `H = S + K` on `H.domain ≤ S.domain ⊓ K.domain`,
3. `S = T + P` on `S.domain ≤ T.domain ⊓ P.domain`,
4. `H = T + G` on `H.domain ≤ T.domain ⊓ G.domain`,
5. `H = P + (T + K)` on `H.domain ≤ P.domain`. -/
structure FiveOperatorResolventSystem (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (a : ℝ) where
  T : H →ₗ.[ℂ] H
  P : H →ₗ.[ℂ] H
  G : H →ₗ.[ℂ] H
  S : H →ₗ.[ℂ] H
  H_op : H →ₗ.[ℂ] H
  K : H →ₗ.[ℂ] H
  RT : H →L[ℂ] H
  RP : H →L[ℂ] H
  RG : H →L[ℂ] H
  RS : H →L[ℂ] H
  RH : H →L[ℂ] H
  res_T : Resolves T RT a
  res_P : Resolves P RP a
  res_G : Resolves G RG a
  res_S : Resolves S RS a
  res_H : Resolves H_op RH a
  pos_T : ∀ z : T.domain, 0 ≤ (inner ℂ (T z) (z : H)).re
  pos_P : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re
  pos_G : ∀ z : G.domain, 0 ≤ (inner ℂ (G z) (z : H)).re
  pos_S : ∀ z : S.domain, 0 ≤ (inner ℂ (S z) (z : H)).re
  pos_H : ∀ z : H_op.domain, 0 ≤ (inner ℂ (H_op z) (z : H)).re
  left_T : ∀ z : T.domain, RT (T z + a • (z : H)) = (z : H)
  left_P : ∀ z : P.domain, RP (P z + a • (z : H)) = (z : H)
  left_G : ∀ z : G.domain, RG (G z + a • (z : H)) = (z : H)
  left_S : ∀ z : S.domain, RS (S z + a • (z : H)) = (z : H)
  left_H : ∀ z : H_op.domain, RH (H_op z + a • (z : H)) = (z : H)
  dom_GP : G.domain ≤ P.domain
  dom_GK : G.domain ≤ K.domain
  eq_GP : ∀ z : G.domain, G z = P ⟨(z : H), dom_GP z.property⟩ + K ⟨(z : H), dom_GK z.property⟩
  dom_HS : H_op.domain ≤ S.domain
  dom_HK : H_op.domain ≤ K.domain
  eq_HS : ∀ z : H_op.domain, H_op z = S ⟨(z : H), dom_HS z.property⟩ + K ⟨(z : H), dom_HK z.property⟩
  dom_ST : S.domain ≤ T.domain
  dom_SP : S.domain ≤ P.domain
  eq_ST : ∀ z : S.domain, S z = T ⟨(z : H), dom_ST z.property⟩ + P ⟨(z : H), dom_SP z.property⟩
  dom_HT : H_op.domain ≤ T.domain
  dom_HG : H_op.domain ≤ G.domain
  eq_HT : ∀ z : H_op.domain, H_op z = T ⟨(z : H), dom_HT z.property⟩ + G ⟨(z : H), dom_HG z.property⟩

/-- Derived domain inclusion `H_op.domain ≤ P.domain` and operator decomposition
`H_op z = P z + (T z + K z)` for the fifth coupled pair `(P, H_op)`. -/
theorem fiveOperator_HP_domain_and_decomposition
    {a : ℝ} (sys : FiveOperatorResolventSystem H a) (z : sys.H_op.domain) :
    (z : H) ∈ sys.P.domain ∧
    sys.H_op z =
      sys.P ⟨(z : H), sys.dom_GP (sys.dom_HG z.property)⟩ +
        (sys.T ⟨(z : H), sys.dom_HT z.property⟩ +
          sys.K ⟨(z : H), sys.dom_GK (sys.dom_HG z.property)⟩) := by
  refine ⟨sys.dom_GP (sys.dom_HG z.property), ?_⟩
  rw [sys.eq_HT z, sys.eq_GP ⟨(z : H), sys.dom_HG z.property⟩]
  abel

/-- First-order (`r = 1`) second resolvent identities across all five coupled pairs
`(P, G)`, `(S, H)`, `(T, S)`, `(T, H)`, and `(P, H)`. -/
theorem fiveOperator_first_order_second_resolvent_identities
    {a : ℝ} (sys : FiveOperatorResolventSystem H a) (f : H) :
    sys.RP f - sys.RG f =
      sys.RP (sys.K ⟨sys.RG f, sys.dom_GK (point sys.G sys.RG a sys.res_G f).property⟩) ∧
    sys.RS f - sys.RH f =
      sys.RS (sys.K ⟨sys.RH f, sys.dom_HK (point sys.H_op sys.RH a sys.res_H f).property⟩) ∧
    sys.RT f - sys.RS f =
      sys.RT (sys.P ⟨sys.RS f, sys.dom_SP (point sys.S sys.RS a sys.res_S f).property⟩) ∧
    sys.RT f - sys.RH f =
      sys.RT (sys.G ⟨sys.RH f, sys.dom_HG (point sys.H_op sys.RH a sys.res_H f).property⟩) ∧
    sys.RP f - sys.RH f =
      sys.RP (sys.T ⟨sys.RH f, sys.dom_HT (point sys.H_op sys.RH a sys.res_H f).property⟩ +
        sys.K ⟨sys.RH f, sys.dom_GK (sys.dom_HG (point sys.H_op sys.RH a sys.res_H f).property)⟩) := by
  refine ⟨
    general_second_resolvent_identity sys.P sys.G sys.K sys.RP sys.RG a
      sys.res_G sys.left_P sys.dom_GP sys.dom_GK sys.eq_GP f,
    general_second_resolvent_identity sys.S sys.H_op sys.K sys.RS sys.RH a
      sys.res_H sys.left_S sys.dom_HS sys.dom_HK sys.eq_HS f,
    general_second_resolvent_identity sys.T sys.S sys.P sys.RT sys.RS a
      sys.res_S sys.left_T sys.dom_ST sys.dom_SP sys.eq_ST f,
    general_second_resolvent_identity sys.T sys.H_op sys.G sys.RT sys.RH a
      sys.res_H sys.left_T sys.dom_HT sys.dom_HG sys.eq_HT f,
    ?_⟩
  let uH : sys.H_op.domain := point sys.H_op sys.RH a sys.res_H f
  let uP : sys.P.domain := ⟨sys.RH f, sys.dom_GP (sys.dom_HG uH.property)⟩
  let uT : sys.T.domain := ⟨sys.RH f, sys.dom_HT uH.property⟩
  let uK : sys.K.domain := ⟨sys.RH f, sys.dom_GK (sys.dom_HG uH.property)⟩
  have hpt : sys.H_op uH = f - a • sys.RH f := point_value sys.H_op sys.RH a sys.res_H f
  have hdec : sys.H_op uH = sys.P uP + (sys.T uT + sys.K uK) :=
    (fiveOperator_HP_domain_and_decomposition sys uH).2
  have hf_eq : f = (sys.P uP + a • (uP : H)) + (sys.T uT + sys.K uK) := by
    have h1 : f = sys.H_op uH + a • (uP : H) := sub_eq_iff_eq_add.mp hpt.symm
    calc
      f = sys.H_op uH + a • (uP : H) := h1
      _ = (sys.P uP + (sys.T uT + sys.K uK)) + a • (uP : H) := by rw [hdec]
      _ = (sys.P uP + a • (uP : H)) + (sys.T uT + sys.K uK) := by abel
  have hRPf : sys.RP f = sys.RH f + sys.RP (sys.T uT + sys.K uK) := by
    calc
      sys.RP f = sys.RP ((sys.P uP + a • (uP : H)) + (sys.T uT + sys.K uK)) :=
        congrArg sys.RP hf_eq
      _ = sys.RP (sys.P uP + a • (uP : H)) + sys.RP (sys.T uT + sys.K uK) :=
        map_add sys.RP _ _
      _ = sys.RH f + sys.RP (sys.T uT + sys.K uK) := by
        rw [sys.left_P uP]
  exact sub_eq_iff_eq_add'.mpr hRPf

/-- Pair 1 `(P, G)`: Left and right `(r + 1)`-th power second resolvent cross-identities
between `sys.RP` and `sys.RG`. -/
theorem pair1_potential_sub_growing_higherPower_cross_identities
    {a : ℝ} (sys : FiveOperatorResolventSystem H a) (r : ℕ) (f : H) :
    iteratedResolventPower sys.RP (r + 1) f - iteratedResolventPower sys.RG (r + 1) f =
      sys.RP (sys.K ⟨sys.RG (iteratedResolventPower sys.RP r f),
        sys.dom_GK (point sys.G sys.RG a sys.res_G (iteratedResolventPower sys.RP r f)).property⟩) +
      sys.RG (iteratedResolventPower sys.RP r f - iteratedResolventPower sys.RG r f) ∧
    iteratedResolventPower sys.RP (r + 1) f - iteratedResolventPower sys.RG (r + 1) f =
      sys.RP (iteratedResolventPower sys.RP r f - iteratedResolventPower sys.RG r f) +
      sys.RP (sys.K ⟨sys.RG (iteratedResolventPower sys.RG r f),
        sys.dom_GK (point sys.G sys.RG a sys.res_G (iteratedResolventPower sys.RG r f)).property⟩) :=
  higherPower_second_resolvent_cross_identities_left_and_right
    sys.P sys.G sys.K sys.RP sys.RG a sys.res_G sys.left_P
    sys.dom_GP sys.dom_GK sys.eq_GP r f

/-- Pair 2 `(S, H_op)`: Left and right `(r + 1)`-th power second resolvent cross-identities
between `sys.RS` and `sys.RH`. -/
theorem pair2_residual_sub_hamiltonian_higherPower_cross_identities
    {a : ℝ} (sys : FiveOperatorResolventSystem H a) (r : ℕ) (f : H) :
    iteratedResolventPower sys.RS (r + 1) f - iteratedResolventPower sys.RH (r + 1) f =
      sys.RS (sys.K ⟨sys.RH (iteratedResolventPower sys.RS r f),
        sys.dom_HK (point sys.H_op sys.RH a sys.res_H (iteratedResolventPower sys.RS r f)).property⟩) +
      sys.RH (iteratedResolventPower sys.RS r f - iteratedResolventPower sys.RH r f) ∧
    iteratedResolventPower sys.RS (r + 1) f - iteratedResolventPower sys.RH (r + 1) f =
      sys.RS (iteratedResolventPower sys.RS r f - iteratedResolventPower sys.RH r f) +
      sys.RS (sys.K ⟨sys.RH (iteratedResolventPower sys.RH r f),
        sys.dom_HK (point sys.H_op sys.RH a sys.res_H (iteratedResolventPower sys.RH r f)).property⟩) :=
  higherPower_second_resolvent_cross_identities_left_and_right
    sys.S sys.H_op sys.K sys.RS sys.RH a sys.res_H sys.left_S
    sys.dom_HS sys.dom_HK sys.eq_HS r f

/-- Pair 3 `(T, S)`: Left and right `(r + 1)`-th power second resolvent cross-identities
between `sys.RT` and `sys.RS`. -/
theorem pair3_static_sub_residual_higherPower_cross_identities
    {a : ℝ} (sys : FiveOperatorResolventSystem H a) (r : ℕ) (f : H) :
    iteratedResolventPower sys.RT (r + 1) f - iteratedResolventPower sys.RS (r + 1) f =
      sys.RT (sys.P ⟨sys.RS (iteratedResolventPower sys.RT r f),
        sys.dom_SP (point sys.S sys.RS a sys.res_S (iteratedResolventPower sys.RT r f)).property⟩) +
      sys.RS (iteratedResolventPower sys.RT r f - iteratedResolventPower sys.RS r f) ∧
    iteratedResolventPower sys.RT (r + 1) f - iteratedResolventPower sys.RS (r + 1) f =
      sys.RT (iteratedResolventPower sys.RT r f - iteratedResolventPower sys.RS r f) +
      sys.RT (sys.P ⟨sys.RS (iteratedResolventPower sys.RS r f),
        sys.dom_SP (point sys.S sys.RS a sys.res_S (iteratedResolventPower sys.RS r f)).property⟩) :=
  higherPower_second_resolvent_cross_identities_left_and_right
    sys.T sys.S sys.P sys.RT sys.RS a sys.res_S sys.left_T
    sys.dom_ST sys.dom_SP sys.eq_ST r f

/-- Pair 4 `(T, H_op)`: Left and right `(r + 1)`-th power second resolvent cross-identities
between `sys.RT` and `sys.RH`. -/
theorem pair4_static_sub_hamiltonian_higherPower_cross_identities
    {a : ℝ} (sys : FiveOperatorResolventSystem H a) (r : ℕ) (f : H) :
    iteratedResolventPower sys.RT (r + 1) f - iteratedResolventPower sys.RH (r + 1) f =
      sys.RT (sys.G ⟨sys.RH (iteratedResolventPower sys.RT r f),
        sys.dom_HG (point sys.H_op sys.RH a sys.res_H (iteratedResolventPower sys.RT r f)).property⟩) +
      sys.RH (iteratedResolventPower sys.RT r f - iteratedResolventPower sys.RH r f) ∧
    iteratedResolventPower sys.RT (r + 1) f - iteratedResolventPower sys.RH (r + 1) f =
      sys.RT (iteratedResolventPower sys.RT r f - iteratedResolventPower sys.RH r f) +
      sys.RT (sys.G ⟨sys.RH (iteratedResolventPower sys.RH r f),
        sys.dom_HG (point sys.H_op sys.RH a sys.res_H (iteratedResolventPower sys.RH r f)).property⟩) :=
  higherPower_second_resolvent_cross_identities_left_and_right
    sys.T sys.H_op sys.G sys.RT sys.RH a sys.res_H sys.left_T
    sys.dom_HT sys.dom_HG sys.eq_HT r f

/-- Pair 5 `(P, H_op)`: Left and right `(r + 1)`-th power second resolvent cross-identities
between `sys.RP` and `sys.RH`. -/
theorem pair5_potential_sub_hamiltonian_higherPower_cross_identities
    {a : ℝ} (sys : FiveOperatorResolventSystem H a) (r : ℕ) (f : H) :
    iteratedResolventPower sys.RP (r + 1) f - iteratedResolventPower sys.RH (r + 1) f =
      sys.RP (sys.T ⟨sys.RH (iteratedResolventPower sys.RP r f),
          sys.dom_HT (point sys.H_op sys.RH a sys.res_H (iteratedResolventPower sys.RP r f)).property⟩ +
        sys.K ⟨sys.RH (iteratedResolventPower sys.RP r f),
          sys.dom_GK (sys.dom_HG (point sys.H_op sys.RH a sys.res_H (iteratedResolventPower sys.RP r f)).property)⟩) +
      sys.RH (iteratedResolventPower sys.RP r f - iteratedResolventPower sys.RH r f) ∧
    iteratedResolventPower sys.RP (r + 1) f - iteratedResolventPower sys.RH (r + 1) f =
      sys.RP (iteratedResolventPower sys.RP r f - iteratedResolventPower sys.RH r f) +
      sys.RP (sys.T ⟨sys.RH (iteratedResolventPower sys.RH r f),
          sys.dom_HT (point sys.H_op sys.RH a sys.res_H (iteratedResolventPower sys.RH r f)).property⟩ +
        sys.K ⟨sys.RH (iteratedResolventPower sys.RH r f),
          sys.dom_GK (sys.dom_HG (point sys.H_op sys.RH a sys.res_H (iteratedResolventPower sys.RH r f)).property)⟩) := by
  constructor
  · rw [iteratedResolventPower_cross_sub_succ_left sys.RP sys.RH r f,
      (fiveOperator_first_order_second_resolvent_identities sys (iteratedResolventPower sys.RP r f)).2.2.2.2]
  · rw [iteratedResolventPower_cross_sub_succ_right sys.RP sys.RH r f,
      (fiveOperator_first_order_second_resolvent_identities sys (iteratedResolventPower sys.RH r f)).2.2.2.2]

/-- Simultaneous first-order domain regularity for all five coupled higher-power resolvent
differences and Yosida identity cross-differences at order `r + 1`. -/
theorem fiveOperator_higherPower_cross_sub_domain_regularity
    {a : ℝ} (sys : FiveOperatorResolventSystem H a) (r : ℕ) (f : H) :
    iteratedResolventPower sys.RP (r + 1) f - iteratedResolventPower sys.RG (r + 1) f ∈ sys.P.domain ∧
    iteratedIdentityPower sys.RP a (r + 1) f - iteratedIdentityPower sys.RG a (r + 1) f ∈ sys.P.domain ∧
    iteratedResolventPower sys.RS (r + 1) f - iteratedResolventPower sys.RH (r + 1) f ∈ sys.S.domain ∧
    iteratedIdentityPower sys.RS a (r + 1) f - iteratedIdentityPower sys.RH a (r + 1) f ∈ sys.S.domain ∧
    iteratedResolventPower sys.RT (r + 1) f - iteratedResolventPower sys.RS (r + 1) f ∈ sys.T.domain ∧
    iteratedIdentityPower sys.RT a (r + 1) f - iteratedIdentityPower sys.RS a (r + 1) f ∈ sys.T.domain ∧
    iteratedResolventPower sys.RT (r + 1) f - iteratedResolventPower sys.RH (r + 1) f ∈ sys.T.domain ∧
    iteratedIdentityPower sys.RT a (r + 1) f - iteratedIdentityPower sys.RH a (r + 1) f ∈ sys.T.domain ∧
    iteratedResolventPower sys.RP (r + 1) f - iteratedResolventPower sys.RH (r + 1) f ∈ sys.P.domain ∧
    iteratedIdentityPower sys.RP a (r + 1) f - iteratedIdentityPower sys.RH a (r + 1) f ∈ sys.P.domain := by
  have h1 := cross_sub_succ_mem_first_domain sys.P sys.G sys.RP sys.RG a sys.res_P sys.res_G sys.dom_GP r f
  have h2 := cross_sub_succ_mem_first_domain sys.S sys.H_op sys.RS sys.RH a sys.res_S sys.res_H sys.dom_HS r f
  have h3 := cross_sub_succ_mem_first_domain sys.T sys.S sys.RT sys.RS a sys.res_T sys.res_S sys.dom_ST r f
  have h4 := cross_sub_succ_mem_first_domain sys.T sys.H_op sys.RT sys.RH a sys.res_T sys.res_H sys.dom_HT r f
  have h5 := cross_sub_succ_mem_first_domain sys.P sys.H_op sys.RP sys.RH a sys.res_P sys.res_H
    (sys.dom_HG.trans sys.dom_GP) r f
  exact ⟨h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2⟩

/-- Recursive perturbation norm bounds across all five coupled operator pairs at order `r + 1`. -/
theorem fiveOperator_higherPower_recursive_perturbation_norm_bounds
    {a : ℝ} (ha : 0 < a) (sys : FiveOperatorResolventSystem H a) (r : ℕ) (f : H) :
    ‖iteratedResolventPower sys.RP (r + 1) f - iteratedResolventPower sys.RG (r + 1) f‖ ≤
      a⁻¹ * ‖sys.K ⟨sys.RG (iteratedResolventPower sys.RP r f),
        sys.dom_GK (point sys.G sys.RG a sys.res_G (iteratedResolventPower sys.RP r f)).property⟩‖ +
      a⁻¹ * ‖iteratedResolventPower sys.RP r f - iteratedResolventPower sys.RG r f‖ ∧
    ‖iteratedResolventPower sys.RS (r + 1) f - iteratedResolventPower sys.RH (r + 1) f‖ ≤
      a⁻¹ * ‖sys.K ⟨sys.RH (iteratedResolventPower sys.RS r f),
        sys.dom_HK (point sys.H_op sys.RH a sys.res_H (iteratedResolventPower sys.RS r f)).property⟩‖ +
      a⁻¹ * ‖iteratedResolventPower sys.RS r f - iteratedResolventPower sys.RH r f‖ ∧
    ‖iteratedResolventPower sys.RT (r + 1) f - iteratedResolventPower sys.RS (r + 1) f‖ ≤
      a⁻¹ * ‖sys.P ⟨sys.RS (iteratedResolventPower sys.RT r f),
        sys.dom_SP (point sys.S sys.RS a sys.res_S (iteratedResolventPower sys.RT r f)).property⟩‖ +
      a⁻¹ * ‖iteratedResolventPower sys.RT r f - iteratedResolventPower sys.RS r f‖ ∧
    ‖iteratedResolventPower sys.RT (r + 1) f - iteratedResolventPower sys.RH (r + 1) f‖ ≤
      a⁻¹ * ‖sys.G ⟨sys.RH (iteratedResolventPower sys.RT r f),
        sys.dom_HG (point sys.H_op sys.RH a sys.res_H (iteratedResolventPower sys.RT r f)).property⟩‖ +
      a⁻¹ * ‖iteratedResolventPower sys.RT r f - iteratedResolventPower sys.RH r f‖ := by
  exact ⟨
    (higherPower_second_resolvent_recursive_norm_bounds sys.P sys.G sys.K sys.RP sys.RG a ha
      sys.res_P sys.res_G sys.pos_P sys.pos_G sys.left_P sys.dom_GP sys.dom_GK sys.eq_GP r f).1,
    (higherPower_second_resolvent_recursive_norm_bounds sys.S sys.H_op sys.K sys.RS sys.RH a ha
      sys.res_S sys.res_H sys.pos_S sys.pos_H sys.left_S sys.dom_HS sys.dom_HK sys.eq_HS r f).1,
    (higherPower_second_resolvent_recursive_norm_bounds sys.T sys.S sys.P sys.RT sys.RS a ha
      sys.res_T sys.res_S sys.pos_T sys.pos_S sys.left_T sys.dom_ST sys.dom_SP sys.eq_ST r f).1,
    (higherPower_second_resolvent_recursive_norm_bounds sys.T sys.H_op sys.G sys.RT sys.RH a ha
      sys.res_T sys.res_H sys.pos_T sys.pos_H sys.left_T sys.dom_HT sys.dom_HG sys.eq_HT r f).1⟩

/-- Recursive Yosida identity cross-difference bounds across all four primary coupled pairs
`(P, G)`, `(S, H_op)`, `(T, S)`, and `(T, H_op)`. -/
theorem fiveOperator_higherPower_yosida_identity_recursive_bounds
    {a : ℝ} (ha : 0 < a) (sys : FiveOperatorResolventSystem H a) (r : ℕ) (f : H) :
    ‖iteratedIdentityPower sys.RP a (r + 1) f - iteratedIdentityPower sys.RG a (r + 1) f‖ ≤
      ‖sys.K ⟨sys.RG (iteratedIdentityPower sys.RP a r f),
        sys.dom_GK (point sys.G sys.RG a sys.res_G (iteratedIdentityPower sys.RP a r f)).property⟩‖ +
      ‖iteratedIdentityPower sys.RP a r f - iteratedIdentityPower sys.RG a r f‖ ∧
    ‖iteratedIdentityPower sys.RS a (r + 1) f - iteratedIdentityPower sys.RH a (r + 1) f‖ ≤
      ‖sys.K ⟨sys.RH (iteratedIdentityPower sys.RS a r f),
        sys.dom_HK (point sys.H_op sys.RH a sys.res_H (iteratedIdentityPower sys.RS a r f)).property⟩‖ +
      ‖iteratedIdentityPower sys.RS a r f - iteratedIdentityPower sys.RH a r f‖ ∧
    ‖iteratedIdentityPower sys.RT a (r + 1) f - iteratedIdentityPower sys.RS a (r + 1) f‖ ≤
      ‖sys.P ⟨sys.RS (iteratedIdentityPower sys.RT a r f),
        sys.dom_SP (point sys.S sys.RS a sys.res_S (iteratedIdentityPower sys.RT a r f)).property⟩‖ +
      ‖iteratedIdentityPower sys.RT a r f - iteratedIdentityPower sys.RS a r f‖ ∧
    ‖iteratedIdentityPower sys.RT a (r + 1) f - iteratedIdentityPower sys.RH a (r + 1) f‖ ≤
      ‖sys.G ⟨sys.RH (iteratedIdentityPower sys.RT a r f),
        sys.dom_HG (point sys.H_op sys.RH a sys.res_H (iteratedIdentityPower sys.RT a r f)).property⟩‖ +
      ‖iteratedIdentityPower sys.RT a r f - iteratedIdentityPower sys.RH a r f‖ := by
  exact ⟨
    (higherPower_second_resolvent_recursive_norm_bounds sys.P sys.G sys.K sys.RP sys.RG a ha
      sys.res_P sys.res_G sys.pos_P sys.pos_G sys.left_P sys.dom_GP sys.dom_GK sys.eq_GP r f).2,
    (higherPower_second_resolvent_recursive_norm_bounds sys.S sys.H_op sys.K sys.RS sys.RH a ha
      sys.res_S sys.res_H sys.pos_S sys.pos_H sys.left_S sys.dom_HS sys.dom_HK sys.eq_HS r f).2,
    (higherPower_second_resolvent_recursive_norm_bounds sys.T sys.S sys.P sys.RT sys.RS a ha
      sys.res_T sys.res_S sys.pos_T sys.pos_S sys.left_T sys.dom_ST sys.dom_SP sys.eq_ST r f).2,
    (higherPower_second_resolvent_recursive_norm_bounds sys.T sys.H_op sys.G sys.RT sys.RH a ha
      sys.res_T sys.res_H sys.pos_T sys.pos_H sys.left_T sys.dom_HT sys.dom_HG sys.eq_HT r f).2⟩

/-- Pair 5 `(P, H_op)` recursive norm bounds for `iteratedResolventPower sys.RP (r + 1) f - iteratedResolventPower sys.RH (r + 1) f`
and `iteratedIdentityPower sys.RP a (r + 1) f - iteratedIdentityPower sys.RH a (r + 1) f`. -/
theorem pair5_potential_sub_hamiltonian_recursive_norm_bounds
    {a : ℝ} (ha : 0 < a) (sys : FiveOperatorResolventSystem H a) (r : ℕ) (f : H) :
    ‖iteratedResolventPower sys.RP (r + 1) f - iteratedResolventPower sys.RH (r + 1) f‖ ≤
      a⁻¹ * ‖sys.T ⟨sys.RH (iteratedResolventPower sys.RP r f),
        sys.dom_HT (point sys.H_op sys.RH a sys.res_H (iteratedResolventPower sys.RP r f)).property⟩‖ +
      a⁻¹ * ‖sys.K ⟨sys.RH (iteratedResolventPower sys.RP r f),
        sys.dom_GK (sys.dom_HG (point sys.H_op sys.RH a sys.res_H (iteratedResolventPower sys.RP r f)).property)⟩‖ +
      a⁻¹ * ‖iteratedResolventPower sys.RP r f - iteratedResolventPower sys.RH r f‖ ∧
    ‖iteratedIdentityPower sys.RP a (r + 1) f - iteratedIdentityPower sys.RH a (r + 1) f‖ ≤
      ‖sys.T ⟨sys.RH (iteratedIdentityPower sys.RP a r f),
        sys.dom_HT (point sys.H_op sys.RH a sys.res_H (iteratedIdentityPower sys.RP a r f)).property⟩‖ +
      ‖sys.K ⟨sys.RH (iteratedIdentityPower sys.RP a r f),
        sys.dom_GK (sys.dom_HG (point sys.H_op sys.RH a sys.res_H (iteratedIdentityPower sys.RP a r f)).property)⟩‖ +
      ‖iteratedIdentityPower sys.RP a r f - iteratedIdentityPower sys.RH a r f‖ := by
  constructor
  · rw [(pair5_potential_sub_hamiltonian_higherPower_cross_identities sys r f).1]
    let uT := sys.T ⟨sys.RH (iteratedResolventPower sys.RP r f),
      sys.dom_HT (point sys.H_op sys.RH a sys.res_H (iteratedResolventPower sys.RP r f)).property⟩
    let uK := sys.K ⟨sys.RH (iteratedResolventPower sys.RP r f),
      sys.dom_GK (sys.dom_HG (point sys.H_op sys.RH a sys.res_H (iteratedResolventPower sys.RP r f)).property)⟩
    have htri1 := norm_add_le (sys.RP (uT + uK))
      (sys.RH (iteratedResolventPower sys.RP r f - iteratedResolventPower sys.RH r f))
    have h1 := resolvent_apply_norm_bound sys.P sys.RP a ha sys.res_P sys.pos_P (uT + uK)
    have h2 := resolvent_apply_norm_bound sys.H_op sys.RH a ha sys.res_H sys.pos_H
      (iteratedResolventPower sys.RP r f - iteratedResolventPower sys.RH r f)
    have htri2 : a⁻¹ * ‖uT + uK‖ ≤ a⁻¹ * ‖uT‖ + a⁻¹ * ‖uK‖ := by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (norm_add_le uT uK) (inv_pos.mpr ha).le
    linarith
  · rw [iteratedIdentityPower_cross_sub_succ_left sys.RP sys.RH a r f,
      (fiveOperator_first_order_second_resolvent_identities sys (iteratedIdentityPower sys.RP a r f)).2.2.2.2]
    let vT := sys.T ⟨sys.RH (iteratedIdentityPower sys.RP a r f),
      sys.dom_HT (point sys.H_op sys.RH a sys.res_H (iteratedIdentityPower sys.RP a r f)).property⟩
    let vK := sys.K ⟨sys.RH (iteratedIdentityPower sys.RP a r f),
      sys.dom_GK (sys.dom_HG (point sys.H_op sys.RH a sys.res_H (iteratedIdentityPower sys.RP a r f)).property)⟩
    have htri1 := norm_add_le ((a : ℂ) • sys.RP (vT + vK))
      ((a : ℂ) • sys.RH (iteratedIdentityPower sys.RP a r f - iteratedIdentityPower sys.RH a r f))
    have h1 : ‖(a : ℂ) • sys.RP (vT + vK)‖ ≤ ‖vT + vK‖ := by
      rw [← (iteratedResolvent_and_identity_recurrences sys.RP a 0 (vT + vK)).2.2.2.2.1]
      exact (iteratedResolvent_and_identity_norm_bounds sys.P sys.RP a ha sys.res_P sys.pos_P 1 (vT + vK)).2
    have h2 : ‖(a : ℂ) • sys.RH (iteratedIdentityPower sys.RP a r f - iteratedIdentityPower sys.RH a r f)‖ ≤
        ‖iteratedIdentityPower sys.RP a r f - iteratedIdentityPower sys.RH a r f‖ := by
      rw [← (iteratedResolvent_and_identity_recurrences sys.RH a 0 _).2.2.2.2.1]
      exact (iteratedResolvent_and_identity_norm_bounds sys.H_op sys.RH a ha sys.res_H sys.pos_H 1 _).2
    have htri2 := norm_add_le vT vK
    linarith

/-- Simultaneous common-domain Yosida rate bounds across all five coupled operator pairs
on `z : sys.H_op.domain`. -/
theorem fiveOperator_common_domain_yosida_cross_rate_bounds
    {a : ℝ} (ha : 0 < a) (sys : FiveOperatorResolventSystem H a)
    (r : ℕ) (z : sys.H_op.domain) :
    let zG : sys.G.domain := ⟨(z : H), sys.dom_HG z.property⟩
    let zP : sys.P.domain := ⟨(z : H), sys.dom_GP zG.property⟩
    let zS : sys.S.domain := ⟨(z : H), sys.dom_HS z.property⟩
    let zT : sys.T.domain := ⟨(z : H), sys.dom_HT z.property⟩
    ‖iteratedIdentityPower sys.RP a r (z : H) - iteratedIdentityPower sys.RG a r (z : H)‖ ≤
      (r : ℝ) * a⁻¹ * (‖sys.P zP‖ + ‖sys.G zG‖) ∧
    ‖iteratedIdentityPower sys.RS a r (z : H) - iteratedIdentityPower sys.RH a r (z : H)‖ ≤
      (r : ℝ) * a⁻¹ * (‖sys.S zS‖ + ‖sys.H_op z‖) ∧
    ‖iteratedIdentityPower sys.RT a r (z : H) - iteratedIdentityPower sys.RS a r (z : H)‖ ≤
      (r : ℝ) * a⁻¹ * (‖sys.T zT‖ + ‖sys.S zS‖) ∧
    ‖iteratedIdentityPower sys.RT a r (z : H) - iteratedIdentityPower sys.RH a r (z : H)‖ ≤
      (r : ℝ) * a⁻¹ * (‖sys.T zT‖ + ‖sys.H_op z‖) ∧
    ‖iteratedIdentityPower sys.RP a r (z : H) - iteratedIdentityPower sys.RH a r (z : H)‖ ≤
      (r : ℝ) * a⁻¹ * (‖sys.P zP‖ + ‖sys.H_op z‖) := by
  intro zG zP zS zT
  exact ⟨
    iteratedIdentityPower_cross_sub_domain_rate_bound sys.P sys.G sys.RP sys.RG a ha
      sys.res_P sys.res_G sys.pos_P sys.pos_G sys.left_P sys.left_G r (z : H) zP.property zG.property,
    iteratedIdentityPower_cross_sub_domain_rate_bound sys.S sys.H_op sys.RS sys.RH a ha
      sys.res_S sys.res_H sys.pos_S sys.pos_H sys.left_S sys.left_H r (z : H) zS.property z.property,
    iteratedIdentityPower_cross_sub_domain_rate_bound sys.T sys.S sys.RT sys.RS a ha
      sys.res_T sys.res_S sys.pos_T sys.pos_S sys.left_T sys.left_S r (z : H) zT.property zS.property,
    iteratedIdentityPower_cross_sub_domain_rate_bound sys.T sys.H_op sys.RT sys.RH a ha
      sys.res_T sys.res_H sys.pos_T sys.pos_H sys.left_T sys.left_H r (z : H) zT.property z.property,
    iteratedIdentityPower_cross_sub_domain_rate_bound sys.P sys.H_op sys.RP sys.RH a ha
      sys.res_P sys.res_H sys.pos_P sys.pos_H sys.left_P sys.left_H r (z : H) zP.property z.property⟩

/-- Closed-loop triangle identity for the higher-power resolvents of `(RT, RP, RG, RS, RH)`:
`(RT^r - RH^r) = (RT^r - RS^r) + (RS^r - RH^r)` and
`(RP^r - RH^r) = (RP^r - RG^r) + (RG^r - RH^r)`. -/
theorem fiveOperator_higherPower_resolvent_triangle_identities
    {a : ℝ} (sys : FiveOperatorResolventSystem H a) (r : ℕ) (f : H) :
    iteratedResolventPower sys.RT r f - iteratedResolventPower sys.RH r f =
      (iteratedResolventPower sys.RT r f - iteratedResolventPower sys.RS r f) +
        (iteratedResolventPower sys.RS r f - iteratedResolventPower sys.RH r f) ∧
    iteratedResolventPower sys.RP r f - iteratedResolventPower sys.RH r f =
      (iteratedResolventPower sys.RP r f - iteratedResolventPower sys.RG r f) +
        (iteratedResolventPower sys.RG r f - iteratedResolventPower sys.RH r f) ∧
    iteratedIdentityPower sys.RT a r f - iteratedIdentityPower sys.RH a r f =
      (iteratedIdentityPower sys.RT a r f - iteratedIdentityPower sys.RS a r f) +
        (iteratedIdentityPower sys.RS a r f - iteratedIdentityPower sys.RH a r f) ∧
    iteratedIdentityPower sys.RP a r f - iteratedIdentityPower sys.RH a r f =
      (iteratedIdentityPower sys.RP a r f - iteratedIdentityPower sys.RG a r f) +
        (iteratedIdentityPower sys.RG a r f - iteratedIdentityPower sys.RH a r f) := by
  refine ⟨by abel, by abel, by abel, by abel⟩

/-! ### 4. First Resolvent Identity and Multi-Parameter Cross-Identities -/

/-- First resolvent identity for any single operator `A` resolved at shifts `a` and `b`:
`R a f - R b f = ((b - a : ℝ) : ℂ) • R a (R b f)`. -/
theorem singleOperator_first_resolvent_identity
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ)
    (hrb : Resolves A (R b) b)
    (hla : ∀ z : A.domain, R a (A z + a • (z : H)) = (z : H))
    (f : H) :
    R a f - R b f = ((b - a : ℝ) : ℂ) • R a (R b f) := by
  let u : A.domain := point A (R b) b hrb f
  have hpt : A u = f - b • R b f := point_value A (R b) b hrb f
  have hf_eq : f = (A u + a • (u : H)) + ((b - a : ℝ) : ℂ) • (u : H) := by
    have h1 : f = A u + b • (u : H) := sub_eq_iff_eq_add.mp hpt.symm
    have h2 : A u + b • (u : H) = (A u + a • (u : H)) + ((b - a : ℝ) : ℂ) • (u : H) := by
      change A u + (b : ℂ) • (u : H) = (A u + (a : ℂ) • (u : H)) + ((b - a : ℝ) : ℂ) • (u : H)
      rw [Complex.ofReal_sub, sub_smul]
      abel
    exact h1.trans h2
  have hRaf : R a f = R b f + ((b - a : ℝ) : ℂ) • R a (R b f) := by
    calc
      R a f = R a ((A u + a • (u : H)) + ((b - a : ℝ) : ℂ) • (u : H)) := congrArg (R a) hf_eq
      _ = R a (A u + a • (u : H)) + R a (((b - a : ℝ) : ℂ) • (u : H)) := map_add (R a) _ _
      _ = R b f + ((b - a : ℝ) : ℂ) • R a (R b f) := by
        rw [hla u, map_smul]
        rfl
  exact sub_eq_iff_eq_add'.mpr hRaf

/-- Higher-power multi-parameter resolvent difference recurrence for a single operator `A`
at shifts `a` and `b`, and inductive `operatorPowerDomain A (r + 2)` regularity lift. -/
theorem singleOperator_higherPower_sub_succ_eq_and_regularity
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ)
    (hra : Resolves A (R a) a) (hrb : Resolves A (R b) b)
    (hla : ∀ z : A.domain, R a (A z + a • (z : H)) = (z : H)) :
    ∀ r : ℕ, ∀ f : H,
      iteratedResolventPower (R a) (r + 1) f - iteratedResolventPower (R b) (r + 1) f =
        ((b - a : ℝ) : ℂ) • R a (R b (iteratedResolventPower (R a) r f)) +
          R b (iteratedResolventPower (R a) r f - iteratedResolventPower (R b) r f) ∧
      iteratedResolventPower (R a) (r + 1) f - iteratedResolventPower (R b) (r + 1) f ∈
        operatorPowerDomain A (r + 2)
  | 0, f => by
    have h1 : iteratedResolventPower (R a) 1 f - iteratedResolventPower (R b) 1 f =
        ((b - a : ℝ) : ℂ) • R a (R b (iteratedResolventPower (R a) 0 f)) +
          R b (iteratedResolventPower (R a) 0 f - iteratedResolventPower (R b) 0 f) := by
      rw [iteratedResolventPower_cross_sub_succ_left (R a) (R b) 0 f,
        singleOperator_first_resolvent_identity A R a b hrb hla (iteratedResolventPower (R a) 0 f)]
    refine ⟨h1, ?_⟩
    rw [h1, iteratedResolventPower_cross_sub_zero (R a) (R b) f, map_zero, add_zero]
    exact (operatorPowerDomain A 2).smul_mem ((b - a : ℝ) : ℂ)
      (resolvent_mem_operatorPowerDomain_succ A (R a) a hra 1
        (resolvent_mem_operatorPowerDomain_succ A (R b) b hrb 0 Submodule.mem_top))
  | r + 1, f => by
    have h1 : iteratedResolventPower (R a) (r + 2) f - iteratedResolventPower (R b) (r + 2) f =
        ((b - a : ℝ) : ℂ) • R a (R b (iteratedResolventPower (R a) (r + 1) f)) +
          R b (iteratedResolventPower (R a) (r + 1) f - iteratedResolventPower (R b) (r + 1) f) := by
      rw [iteratedResolventPower_cross_sub_succ_left (R a) (R b) (r + 1) f,
        singleOperator_first_resolvent_identity A R a b hrb hla
          (iteratedResolventPower (R a) (r + 1) f)]
    refine ⟨h1, ?_⟩
    rw [h1]
    have hlead :
        ((b - a : ℝ) : ℂ) • R a (R b (iteratedResolventPower (R a) (r + 1) f)) ∈
          operatorPowerDomain A (r + 3) :=
      (operatorPowerDomain A (r + 3)).smul_mem ((b - a : ℝ) : ℂ)
        (resolvent_mem_operatorPowerDomain_succ A (R a) a hra (r + 2)
          (resolvent_mem_operatorPowerDomain_succ A (R b) b hrb (r + 1)
            (iteratedResolvent_and_identity_mem_operatorPowerDomain A (R a) a hra (r + 1) f).1))
    have hstep :
        R b (iteratedResolventPower (R a) (r + 1) f - iteratedResolventPower (R b) (r + 1) f) ∈
          operatorPowerDomain A (r + 3) :=
      resolvent_mem_operatorPowerDomain_succ A (R b) b hrb (r + 2)
        (singleOperator_higherPower_sub_succ_eq_and_regularity A R a b hra hrb hla r f).2
    exact (operatorPowerDomain A (r + 3)).add_mem hlead hstep

/-- Two-parameter mutual Cauchy bound on `A.domain`:
`‖iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b r x‖ ≤ (r : ℝ) * (a⁻¹ + b⁻¹) * ‖A x‖`. -/
theorem singleOperator_two_parameter_yosida_cauchy_bound
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hra : Resolves A (R a) a) (hrb : Resolves A (R b) b)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hla : ∀ z : A.domain, R a (A z + a • (z : H)) = (z : H))
    (hlb : ∀ z : A.domain, R b (A z + b • (z : H)) = (z : H))
    (r : ℕ) (x : A.domain) :
    ‖iteratedIdentityPower (R a) a r (x : H) - iteratedIdentityPower (R b) b r (x : H)‖ ≤
      (r : ℝ) * (a⁻¹ + b⁻¹) * ‖A x‖ := by
  have hsplit :
      iteratedIdentityPower (R a) a r (x : H) - iteratedIdentityPower (R b) b r (x : H) =
        (iteratedIdentityPower (R a) a r (x : H) - (x : H)) -
          (iteratedIdentityPower (R b) b r (x : H) - (x : H)) := by
    abel
  rw [hsplit]
  have htri := norm_sub_le
    (iteratedIdentityPower (R a) a r (x : H) - (x : H))
    (iteratedIdentityPower (R b) b r (x : H) - (x : H))
  have h1 := iteratedIdentityPower_domain_rate_bound A (R a) a ha hra hp hla r x
  have h2 := iteratedIdentityPower_domain_rate_bound A (R b) b hb hrb hp hlb r x
  have hring :
      (r : ℝ) * a⁻¹ * ‖A x‖ + (r : ℝ) * b⁻¹ * ‖A x‖ =
        (r : ℝ) * (a⁻¹ + b⁻¹) * ‖A x‖ := by
    ring
  linarith

/-! ### 5. Coupled Closed-Graph-Form Self-Adjoint Positive Hamiltonians -/

section CoupledClosedGraphForms

variable {K1 K2 : Type*}
  [NormedAddCommGroup K1] [InnerProductSpace ℂ K1]
  [NormedAddCommGroup K2] [InnerProductSpace ℂ K2]
  [CompleteSpace H] [CompleteSpace K1] [CompleteSpace K2]

/-- Higher-power cross-operator second resolvent and Yosida difference package for any
two closed-graph-form Hamiltonians `hamiltonian D1` and `hamiltonian D2`. -/
theorem coupled_closedGraphForm_hamiltonians_cross_resolvent_package
    (D1 : Data H K1) (D2 : Data H K2) (K : H →ₗ.[ℂ] H)
    (R1 R2 : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr1 : Resolves (hamiltonian D1) R1 a)
    (hr2 : Resolves (hamiltonian D2) R2 a)
    (hl1 : ∀ z : (hamiltonian D1).domain, R1 (hamiltonian D1 z + a • (z : H)) = (z : H))
    (hdom : (hamiltonian D2).domain ≤ (hamiltonian D1).domain)
    (hK : (hamiltonian D2).domain ≤ K.domain)
    (hadd : ∀ z : (hamiltonian D2).domain,
      hamiltonian D2 z = hamiltonian D1 ⟨(z : H), hdom z.property⟩ + K ⟨(z : H), hK z.property⟩)
    (r : ℕ) (f : H) :
    IsSelfAdjoint (hamiltonian D1) ∧
    IsSelfAdjoint (hamiltonian D2) ∧
    iteratedResolventPower R1 (r + 1) f - iteratedResolventPower R2 (r + 1) f ∈
      (hamiltonian D1).domain ∧
    iteratedIdentityPower R1 a (r + 1) f - iteratedIdentityPower R2 a (r + 1) f ∈
      (hamiltonian D1).domain ∧
    ‖iteratedResolventPower R1 r f - iteratedResolventPower R2 r f‖ ≤
      2 * (a⁻¹) ^ r * ‖f‖ ∧
    ‖iteratedIdentityPower R1 a r f - iteratedIdentityPower R2 a r f‖ ≤ 2 * ‖f‖ ∧
    ‖iteratedResolventPower R1 (r + 1) f - iteratedResolventPower R2 (r + 1) f‖ ≤
      a⁻¹ * ‖K ⟨R2 (iteratedResolventPower R1 r f),
        hK (point (hamiltonian D2) R2 a hr2 (iteratedResolventPower R1 r f)).property⟩‖ +
      a⁻¹ * ‖iteratedResolventPower R1 r f - iteratedResolventPower R2 r f‖ := by
  have hmem := cross_sub_succ_mem_first_domain
    (hamiltonian D1) (hamiltonian D2) R1 R2 a hr1 hr2 hdom r f
  have hrec := higherPower_second_resolvent_recursive_norm_bounds
    (hamiltonian D1) (hamiltonian D2) K R1 R2 a ha hr1 hr2
    (hamiltonian_positive D1) (hamiltonian_positive D2) hl1 hdom hK hadd r f
  exact ⟨hamiltonian_selfAdjoint D1,
    hamiltonian_selfAdjoint D2,
    hmem.1, hmem.2,
    iteratedResolventPower_cross_sub_norm_bound
      (hamiltonian D1) (hamiltonian D2) R1 R2 a ha hr1 hr2
      (hamiltonian_positive D1) (hamiltonian_positive D2) r f,
    iteratedIdentityPower_cross_sub_norm_le_two
      (hamiltonian D1) (hamiltonian D2) R1 R2 a ha hr1 hr2
      (hamiltonian_positive D1) (hamiltonian_positive D2) r f,
    hrec.1⟩

/-- Bounded-perturbation rate specialization for two coupled closed-graph-form Hamiltonians
`hamiltonian D1` and `hamiltonian D2`. -/
theorem coupled_closedGraphForm_hamiltonians_bounded_perturbation_rates
    (D1 : Data H K1) (D2 : Data H K2) (K : H →ₗ.[ℂ] H)
    (R1 R2 : H →L[ℂ] H) (a M : ℝ) (ha : 0 < a) (hM : 0 ≤ M)
    (hr1 : Resolves (hamiltonian D1) R1 a)
    (hr2 : Resolves (hamiltonian D2) R2 a)
    (hl1 : ∀ z : (hamiltonian D1).domain, R1 (hamiltonian D1 z + a • (z : H)) = (z : H))
    (hdom : (hamiltonian D2).domain ≤ (hamiltonian D1).domain)
    (hK : (hamiltonian D2).domain ≤ K.domain)
    (hadd : ∀ z : (hamiltonian D2).domain,
      hamiltonian D2 z = hamiltonian D1 ⟨(z : H), hdom z.property⟩ + K ⟨(z : H), hK z.property⟩)
    (hK_bound : ∀ z : K.domain, ‖K z‖ ≤ M * ‖(z : H)‖)
    (r : ℕ) (f : H) :
    ‖iteratedResolventPower R1 r f - iteratedResolventPower R2 r f‖ ≤
      (r : ℝ) * M * (a⁻¹) ^ (r + 1) * ‖f‖ ∧
    ‖iteratedIdentityPower R1 a r f - iteratedIdentityPower R2 a r f‖ ≤
      (r : ℝ) * a⁻¹ * M * ‖f‖ :=
  higherPower_second_resolvent_bounded_perturbation_rates
    (hamiltonian D1) (hamiltonian D2) K R1 R2 a M ha hM hr1 hr2
    (hamiltonian_positive D1) (hamiltonian_positive D2) hl1 hdom hK hadd hK_bound r f

end CoupledClosedGraphForms

/-- Master 5-Pair Higher-Power Second Resolvent Cross-Identity Synthesis Theorem. -/
theorem fiveOperator_higherPower_second_resolvent_master_synthesis
    {a : ℝ} (ha : 0 < a) (sys : FiveOperatorResolventSystem H a)
    (r : ℕ) (f : H) (z : sys.H_op.domain) :
    (iteratedResolventPower sys.RP (r + 1) f - iteratedResolventPower sys.RG (r + 1) f ∈ sys.P.domain ∧
     iteratedResolventPower sys.RS (r + 1) f - iteratedResolventPower sys.RH (r + 1) f ∈ sys.S.domain ∧
     iteratedResolventPower sys.RT (r + 1) f - iteratedResolventPower sys.RS (r + 1) f ∈ sys.T.domain ∧
     iteratedResolventPower sys.RT (r + 1) f - iteratedResolventPower sys.RH (r + 1) f ∈ sys.T.domain ∧
     iteratedResolventPower sys.RP (r + 1) f - iteratedResolventPower sys.RH (r + 1) f ∈ sys.P.domain) ∧
    (‖iteratedIdentityPower sys.RP a r f - iteratedIdentityPower sys.RG a r f‖ ≤ 2 * ‖f‖ ∧
     ‖iteratedIdentityPower sys.RS a r f - iteratedIdentityPower sys.RH a r f‖ ≤ 2 * ‖f‖ ∧
     ‖iteratedIdentityPower sys.RT a r f - iteratedIdentityPower sys.RS a r f‖ ≤ 2 * ‖f‖ ∧
     ‖iteratedIdentityPower sys.RT a r f - iteratedIdentityPower sys.RH a r f‖ ≤ 2 * ‖f‖ ∧
     ‖iteratedIdentityPower sys.RP a r f - iteratedIdentityPower sys.RH a r f‖ ≤ 2 * ‖f‖) ∧
    ‖iteratedIdentityPower sys.RT a r (z : H) - iteratedIdentityPower sys.RH a r (z : H)‖ ≤
      (r : ℝ) * a⁻¹ * (‖sys.T ⟨(z : H), sys.dom_HT z.property⟩‖ + ‖sys.H_op z‖) := by
  have hdom := fiveOperator_higherPower_cross_sub_domain_regularity sys r f
  have hrate := (fiveOperator_common_domain_yosida_cross_rate_bounds ha sys r z).2.2.2.1
  refine ⟨⟨hdom.1, hdom.2.2.1, hdom.2.2.2.2.1, hdom.2.2.2.2.2.2.1, hdom.2.2.2.2.2.2.2.2.1⟩,
    ⟨iteratedIdentityPower_cross_sub_norm_le_two sys.P sys.G sys.RP sys.RG a ha
      sys.res_P sys.res_G sys.pos_P sys.pos_G r f,
     iteratedIdentityPower_cross_sub_norm_le_two sys.S sys.H_op sys.RS sys.RH a ha
      sys.res_S sys.res_H sys.pos_S sys.pos_H r f,
     iteratedIdentityPower_cross_sub_norm_le_two sys.T sys.S sys.RT sys.RS a ha
      sys.res_T sys.res_S sys.pos_T sys.pos_S r f,
     iteratedIdentityPower_cross_sub_norm_le_two sys.T sys.H_op sys.RT sys.RH a ha
      sys.res_T sys.res_H sys.pos_T sys.pos_H r f,
     iteratedIdentityPower_cross_sub_norm_le_two sys.P sys.H_op sys.RP sys.RH a ha
      sys.res_P sys.res_H sys.pos_P sys.pos_H r f⟩,
    hrate⟩

#print axioms iteratedResolventPower_cross_sub_zero
#print axioms iteratedResolventPower_cross_sub_one
#print axioms iteratedResolventPower_cross_sub_succ_left
#print axioms iteratedResolventPower_cross_sub_succ_right
#print axioms iteratedResolventPower_cross_sub_two_left
#print axioms iteratedResolventPower_cross_sub_two_right
#print axioms iteratedResolventPower_cross_sub_norm_bound
#print axioms iteratedIdentityPower_cross_sub_eq_smul
#print axioms iteratedIdentityPower_cross_sub_zero
#print axioms iteratedIdentityPower_cross_sub_one
#print axioms iteratedIdentityPower_cross_sub_succ_left
#print axioms iteratedIdentityPower_cross_sub_succ_right
#print axioms iteratedIdentityPower_cross_sub_norm_le_two
#print axioms iteratedIdentityPower_cross_sub_split_via_self
#print axioms iteratedIdentityPower_cross_sub_domain_rate_bound
#print axioms general_second_resolvent_identity
#print axioms cross_sub_succ_mem_first_domain
#print axioms cross_sub_succ_mem_secondPowerDomain
#print axioms higherPower_second_resolvent_cross_identities_left_and_right
#print axioms higherPower_second_resolvent_recursive_norm_bounds
#print axioms higherPower_second_resolvent_bounded_perturbation_rates
#print axioms fiveOperator_HP_domain_and_decomposition
#print axioms fiveOperator_first_order_second_resolvent_identities
#print axioms pair1_potential_sub_growing_higherPower_cross_identities
#print axioms pair2_residual_sub_hamiltonian_higherPower_cross_identities
#print axioms pair3_static_sub_residual_higherPower_cross_identities
#print axioms pair4_static_sub_hamiltonian_higherPower_cross_identities
#print axioms pair5_potential_sub_hamiltonian_higherPower_cross_identities
#print axioms fiveOperator_higherPower_cross_sub_domain_regularity
#print axioms fiveOperator_higherPower_recursive_perturbation_norm_bounds
#print axioms fiveOperator_higherPower_yosida_identity_recursive_bounds
#print axioms pair5_potential_sub_hamiltonian_recursive_norm_bounds
#print axioms fiveOperator_common_domain_yosida_cross_rate_bounds
#print axioms fiveOperator_higherPower_resolvent_triangle_identities
#print axioms singleOperator_first_resolvent_identity
#print axioms singleOperator_higherPower_sub_succ_eq_and_regularity
#print axioms singleOperator_two_parameter_yosida_cauchy_bound
#print axioms coupled_closedGraphForm_hamiltonians_cross_resolvent_package
#print axioms coupled_closedGraphForm_hamiltonians_bounded_perturbation_rates
#print axioms fiveOperator_higherPower_second_resolvent_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorHigherPowerSecondResolventCrossIdentity
