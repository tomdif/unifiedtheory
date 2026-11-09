/- Two-Parameter Higher-Power Potential-Resolvent Radial-Yosida Tier Differences,
`(r + 2)`-Power Regularity Gain, Four-Parameter `((a, J₁), (b, J₂))` Joint Cauchy Rate Bounds,
and Simultaneous `(m + 1)`-Tier Cauchy Convergence on `Dom(P^{m+1})`:
1. Defines the two-parameter potential-resolvent radial-Yosida tier difference
   `arbitraryOrderPotentialResolventYosidaTierSub P Ra Rb J r j x`,
   the two-parameter Yosida-scaled identity radial-Yosida tier difference
   `arbitraryOrderPotentialIdentityYosidaTierSub P Ra Rb J a b r j x`,
   the two-regularizer cutoff tier difference
   `arbitraryOrderPotentialIdentityYosidaCutoffSub P R J₁ J₂ a r j x`,
   and the `m`-th order squared two-parameter Cauchy graph norm
   `arbitraryOrderPotentialYosidaCauchyGraphNormSq P R J a b r m x`.
2. Proves:
   - Diagonal vanishing (`a = b`), skew-symmetry (`a ↔ b`), and three-parameter (`a, b, c`)
     cocycle cancellation `(a, b) + (b, c) = (a, c)` across all tiers `j`,
   - Extra-power regularity gain `arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J (r + 1) j x ∈ operatorPowerDomain P (r + 2)`
     at every tier `j : ℕ`, alongside `operatorPowerDomain P r` membership of
     `arbitraryOrderPotentialIdentityYosidaTierSub`,
   - Geometric norm bound `((a⁻¹) ^ r + (b⁻¹) ^ r) * ‖J (P^j x)‖`, uniform `2 * ‖J (P^j x)‖`
     stability, and `4 * kthPowerGraphNormSq P m x` Cauchy graph-norm bound,
   - Contractive regularizer difference bound
     `‖arbitraryOrderPotentialIdentityYosidaCutoffSub P R J₁ J₂ a r j x‖ ≤ ‖J₁ (P^j x) - J₂ (P^j x)‖`,
   - Simultaneous `(m + 1)`-tier two-parameter Cauchy rate bound on `operatorPowerDomain P (m + 1)`:
     `‖arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x‖ ≤ 2 * ‖J (P^j x) - P^j x‖ + (r : ℝ) * (a⁻¹ + b⁻¹) * ‖P^{j+1} x‖`,
   - Joint four-parameter `((a, J₁), (b, J₂))` Cauchy rate bound on `operatorPowerDomain P (m + 1)`,
   - Strong sequential convergence as `n → ∞` along `J n → id` to the commuting operator-power
     Yosida difference `iteratedOperatorPower P j (iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b r x)`.
3. Instantiates the full two-parameter and four-parameter Cauchy rate hierarchy for the
   clock-floor potential Hamiltonian `P` and radial-Yosida regularizer `action ε hε h (cutoff n)`. -/
import UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaArbitraryOrderConvergence
import UnifiedTheory.Audit.KFCausalClockFloorArbitraryOrderTwoParameterYosidaCauchyRate

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaTwoParameterCauchyRate

noncomputable section

open Filter
open scoped Topology InnerProduct BigOperators
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialResolventRegularizer
  (action action_norm sequence_tendsto)
open KFCausalClockFloorPotentialClockApproximation (cutoff cutoff_pos)
open KFCausalPositiveResolventBounds (Resolves)
open KFCausalClockFloorHigherPowerOperatorCores
  (operatorPowerDomain operatorPowerDomain_le_of_le
   iteratedResolventPower potentialPowerDomain)
open KFCausalClockFloorHigherPowerYosidaGraphConvergence
  (iteratedIdentityPower iteratedIdentityPower_sub
   iteratedIdentityPower_norm_le)
open KFCausalClockFloorFiveOperatorHigherPowerResolventDifference
  (iteratedResolventPower_sub_succ_mem_operatorPowerDomain
   iteratedIdentityPower_sub_domain_rate_bound)
open KFCausalClockFloorHigherPowerArbitraryOrderGraphConvergence
  (iteratedOperatorPower iteratedOperatorPower_succ_apply
   totalOperator totalOperator_of_mem_domain
   iteratedOperatorPower_mem_domain_of_mem_succ
   kthPowerGraphNormSq)
open KFCausalClockFloorHigherPowerPotentialResolventYosidaArbitraryOrderConvergence
  (arbitraryOrderPotentialResolventYosidaTierState
   arbitraryOrderPotentialIdentityYosidaTierState
   arbitraryOrderPotentialYosidaTierState_mem_operatorPowerDomain
   arbitraryOrderPotentialYosidaTierState_norm_bounds
   arbitraryOrderPotentialIdentityYosidaTierState_norm_le_of_contractive
   arbitraryOrderPotentialYosidaDefect_bounds
   arbitraryOrderPotentialIdentityYosidaTierState_all_tiers_rate_bound_of_le
   tendsto_arbitraryOrderPotentialIdentityYosidaTierState_commuting_on_powerDomain
   clockFloorPotentialResolventYosidaTierState
   clockFloorPotentialIdentityYosidaTierState)
open KFCausalClockFloorArbitraryOrderTwoParameterYosidaCauchyRate
  (iteratedOperatorPower_iteratedIdentityPower_sub_comm
   iteratedOperatorPower_all_tiers_cauchy_rate_of_le)

/-! ### 1. Abstract Two-Parameter and Two-Regularizer Potential-Resolvent Yosida Tier Differences -/

section AbstractTwoParameterPotentialYosida

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The `j`-th tier `r`-fold two-parameter potential-resolvent radial-Yosida difference
`R_a^r (J (P^j x)) - R_b^r (J (P^j x))`. -/
def arbitraryOrderPotentialResolventYosidaTierSub
    (P : H →ₗ.[ℂ] H) (Ra Rb J : H →L[ℂ] H) (r j : ℕ) (x : H) : H :=
  arbitraryOrderPotentialResolventYosidaTierState P Ra J r j x -
    arbitraryOrderPotentialResolventYosidaTierState P Rb J r j x

/-- The `j`-th tier `r`-th power two-parameter Yosida-scaled identity radial-Yosida difference
`(a • R_a)^r (J (P^j x)) - (b • R_b)^r (J (P^j x))`. -/
def arbitraryOrderPotentialIdentityYosidaTierSub
    (P : H →ₗ.[ℂ] H) (Ra Rb J : H →L[ℂ] H) (a b : ℝ) (r j : ℕ) (x : H) : H :=
  arbitraryOrderPotentialIdentityYosidaTierState P Ra J a r j x -
    arbitraryOrderPotentialIdentityYosidaTierState P Rb J b r j x

/-- The `j`-th tier `r`-th power two-regularizer cutoff difference at fixed shift `a`:
`(a • R)^r (J₁ (P^j x)) - (a • R)^r (J₂ (P^j x))`. -/
def arbitraryOrderPotentialIdentityYosidaCutoffSub
    (P : H →ₗ.[ℂ] H) (R J₁ J₂ : H →L[ℂ] H) (a : ℝ) (r j : ℕ) (x : H) : H :=
  arbitraryOrderPotentialIdentityYosidaTierState P R J₁ a r j x -
    arbitraryOrderPotentialIdentityYosidaTierState P R J₂ a r j x

/-- The `m`-th order squared two-parameter Cauchy graph norm across tiers `0 ≤ j ≤ m`:
`∑ j ∈ Finset.range (m + 1), ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x‖ ^ 2`. -/
def arbitraryOrderPotentialYosidaCauchyGraphNormSq
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b : ℝ) (r m : ℕ) (x : H) : ℝ :=
  ∑ j ∈ Finset.range (m + 1),
    ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x‖ ^ 2

/-- Diagonal vanishing (`a = b`), skew-symmetry (`a ↔ b`), and three-parameter (`a, b, c`)
cocycle cancellation `(a, b) + (b, c) = (a, c)` for `arbitraryOrderPotentialResolventYosidaTierSub`
and `arbitraryOrderPotentialIdentityYosidaTierSub`. -/
theorem arbitraryOrderPotentialYosidaTierSub_zero_and_cocycle
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c : ℝ) (r j : ℕ) (x : H) :
    arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R a) J r j x = 0 ∧
    arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R a) J a a r j x = 0 ∧
    arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R a) J r j x =
      -arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J r j x ∧
    arbitraryOrderPotentialIdentityYosidaTierSub P (R b) (R a) J b a r j x =
      -arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x ∧
    arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R c) J r j x =
      arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R c) J r j x ∧
    arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R b) (R c) J b c r j x =
      arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R c) J a c r j x := by
  unfold arbitraryOrderPotentialResolventYosidaTierSub
    arbitraryOrderPotentialIdentityYosidaTierSub
  refine ⟨sub_self _, sub_self _, by abel, by abel, by abel, by abel⟩

/-- Extra-power regularity gain for the `(r + 1)`-fold two-parameter potential-resolvent
tier difference: `arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J (r + 1) j x ∈ operatorPowerDomain P (r + 2)`
at every tier `j : ℕ`, while `arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x ∈ operatorPowerDomain P r`. -/
theorem arbitraryOrderPotentialYosidaTierSub_mem_operatorPowerDomain
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves P (R d) d)
    (hl : ∀ d, 0 < d → ∀ z : P.domain, R d (P z + d • (z : H)) = (z : H))
    (r j : ℕ) (x : H) :
    arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J (r + 1) j x ∈
      operatorPowerDomain P (r + 2) ∧
    arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x ∈
      operatorPowerDomain P r := by
  have h1 :
      arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J (r + 1) j x ∈
        operatorPowerDomain P (r + 2) :=
    iteratedResolventPower_sub_succ_mem_operatorPowerDomain P R a b ha hb hr hl r
      (J (iteratedOperatorPower P j x))
  have h2a :=
    (arbitraryOrderPotentialYosidaTierState_mem_operatorPowerDomain P (R a) J a (hr a ha) r j x).2.1
  have h2b :=
    (arbitraryOrderPotentialYosidaTierState_mem_operatorPowerDomain P (R b) J b (hr b hb) r j x).2.1
  exact ⟨h1, (operatorPowerDomain P r).sub_mem h2a h2b⟩

/-- Two-parameter geometric norm bound on `arbitraryOrderPotentialResolventYosidaTierSub`
and uniform `2 * ‖J (P^j x)‖` stability bound on `arbitraryOrderPotentialIdentityYosidaTierSub`. -/
theorem arbitraryOrderPotentialYosidaTierSub_norm_bounds
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves P (R d) d)
    (hp : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (r j : ℕ) (x : H) :
    ‖arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J r j x‖ ≤
      ((a⁻¹) ^ r + (b⁻¹) ^ r) * ‖J (iteratedOperatorPower P j x)‖ ∧
    ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x‖ ≤
      2 * ‖J (iteratedOperatorPower P j x)‖ := by
  have hba := arbitraryOrderPotentialYosidaTierState_norm_bounds P (R a) J a ha (hr a ha) hp r j x
  have hbb := arbitraryOrderPotentialYosidaTierState_norm_bounds P (R b) J b hb (hr b hb) hp r j x
  constructor
  · unfold arbitraryOrderPotentialResolventYosidaTierSub
    have htri := norm_sub_le
      (arbitraryOrderPotentialResolventYosidaTierState P (R a) J r j x)
      (arbitraryOrderPotentialResolventYosidaTierState P (R b) J r j x)
    have hring :
        (a⁻¹) ^ r * ‖J (iteratedOperatorPower P j x)‖ +
          (b⁻¹) ^ r * ‖J (iteratedOperatorPower P j x)‖ =
        ((a⁻¹) ^ r + (b⁻¹) ^ r) * ‖J (iteratedOperatorPower P j x)‖ := by ring
    linarith [hba.1, hbb.1]
  · unfold arbitraryOrderPotentialIdentityYosidaTierSub
    have htri := norm_sub_le
      (arbitraryOrderPotentialIdentityYosidaTierState P (R a) J a r j x)
      (arbitraryOrderPotentialIdentityYosidaTierState P (R b) J b r j x)
    linarith [hba.2, hbb.2]

/-- Uniform `4 * kthPowerGraphNormSq P m x` bound on `arbitraryOrderPotentialYosidaCauchyGraphNormSq`
for any contractive regularizer `∀ g, ‖J g‖ ≤ ‖g‖`. -/
theorem arbitraryOrderPotentialYosidaCauchyGraphNormSq_le_four
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves P (R d) d)
    (hp : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (hJ : ∀ g : H, ‖J g‖ ≤ ‖g‖) (r m : ℕ) (x : H) :
    0 ≤ arbitraryOrderPotentialYosidaCauchyGraphNormSq P R J a b r m x ∧
    arbitraryOrderPotentialYosidaCauchyGraphNormSq P R J a b r m x ≤
      4 * kthPowerGraphNormSq P m x := by
  refine ⟨Finset.sum_nonneg (fun _ _ => sq_nonneg _), ?_⟩
  unfold arbitraryOrderPotentialYosidaCauchyGraphNormSq kthPowerGraphNormSq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hbd :
      ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x‖ ≤
        2 * ‖iteratedOperatorPower P j x‖ := by
    have h1 := (arbitraryOrderPotentialYosidaTierSub_norm_bounds P R J a b ha hb hr hp r j x).2
    have h2 := hJ (iteratedOperatorPower P j x)
    linarith
  have hsq :
      ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x‖ ^ 2 ≤
        (2 * ‖iteratedOperatorPower P j x‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hbd 2
  linarith

/-- Exact linearity and contractive bound for the two-regularizer cutoff difference
`arbitraryOrderPotentialIdentityYosidaCutoffSub P R J₁ J₂ a r j x`. -/
theorem arbitraryOrderPotentialIdentityYosidaCutoffSub_eq_and_norm_le
    (P : H →ₗ.[ℂ] H) (R J₁ J₂ : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves P R a) (hp : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (r j : ℕ) (x : H) :
    arbitraryOrderPotentialIdentityYosidaCutoffSub P R J₁ J₂ a r j x =
      iteratedIdentityPower R a r
        (J₁ (iteratedOperatorPower P j x) - J₂ (iteratedOperatorPower P j x)) ∧
    ‖arbitraryOrderPotentialIdentityYosidaCutoffSub P R J₁ J₂ a r j x‖ ≤
      ‖J₁ (iteratedOperatorPower P j x) - J₂ (iteratedOperatorPower P j x)‖ := by
  have heq :
      arbitraryOrderPotentialIdentityYosidaCutoffSub P R J₁ J₂ a r j x =
        iteratedIdentityPower R a r
          (J₁ (iteratedOperatorPower P j x) - J₂ (iteratedOperatorPower P j x)) :=
    (iteratedIdentityPower_sub R a r
      (J₁ (iteratedOperatorPower P j x))
      (J₂ (iteratedOperatorPower P j x))).symm
  refine ⟨heq, ?_⟩
  rw [heq]
  exact iteratedIdentityPower_norm_le P R a ha hr hp r
    (J₁ (iteratedOperatorPower P j x) - J₂ (iteratedOperatorPower P j x))

/-! ### 2. Two-Parameter and Four-Parameter Cauchy Rate Bounds on `Dom(P^{m+1})` -/

/-- Exact 3-piece decomposition of `arbitraryOrderPotentialIdentityYosidaTierSub` into two
regularizer defects at shifts `a` and `b` plus the unregularized two-parameter Yosida
difference `iteratedIdentityPower (R a) a r (P^j x) - iteratedIdentityPower (R b) b r (P^j x)`. -/
theorem arbitraryOrderPotentialIdentityYosidaTierSub_three_piece_split
    (P : H →ₗ.[ℂ] H) (Ra Rb J : H →L[ℂ] H) (a b : ℝ) (r j : ℕ) (x : H) :
    arbitraryOrderPotentialIdentityYosidaTierSub P Ra Rb J a b r j x =
      (arbitraryOrderPotentialIdentityYosidaTierState P Ra J a r j x -
        iteratedIdentityPower Ra a r (iteratedOperatorPower P j x)) -
      (arbitraryOrderPotentialIdentityYosidaTierState P Rb J b r j x -
        iteratedIdentityPower Rb b r (iteratedOperatorPower P j x)) +
      (iteratedIdentityPower Ra a r (iteratedOperatorPower P j x) -
        iteratedIdentityPower Rb b r (iteratedOperatorPower P j x)) := by
  unfold arbitraryOrderPotentialIdentityYosidaTierSub
  abel

/-- Pointwise `j`-th tier two-parameter Cauchy rate bound on `operatorPowerDomain P (j + 1)`:
`‖arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x‖ ≤ 2 * ‖J (P^j x) - P^j x‖ + (r : ℝ) * (a⁻¹ + b⁻¹) * ‖P^{j+1} x‖`. -/
theorem arbitraryOrderPotentialIdentityYosidaTierSub_cauchy_rate_on_succ
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves P (R d) d)
    (hp : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (hl : ∀ d, 0 < d → ∀ z : P.domain, R d (P z + d • (z : H)) = (z : H))
    (j r : ℕ) {x : H} (hx : x ∈ operatorPowerDomain P (j + 1)) :
    ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x‖ ≤
      2 * ‖J (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + b⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ := by
  rw [arbitraryOrderPotentialIdentityYosidaTierSub_three_piece_split P (R a) (R b) J a b r j x]
  have hda :=
    (arbitraryOrderPotentialYosidaDefect_bounds P (R a) J a ha (hr a ha) hp r j j x).1
  have hdb :=
    (arbitraryOrderPotentialYosidaDefect_bounds P (R b) J b hb (hr b hb) hp r j j x).1
  have hx_dom : iteratedOperatorPower P j x ∈ P.domain :=
    iteratedOperatorPower_mem_domain_of_mem_succ P j hx
  have hcauchy :
      ‖iteratedIdentityPower (R a) a r (iteratedOperatorPower P j x) -
          iteratedIdentityPower (R b) b r (iteratedOperatorPower P j x)‖ ≤
        (r : ℝ) * (a⁻¹ + b⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ := by
    rw [iteratedOperatorPower_succ_apply, totalOperator_of_mem_domain P hx_dom]
    exact iteratedIdentityPower_sub_domain_rate_bound P R a b ha hb hr hp hl r
      ⟨iteratedOperatorPower P j x, hx_dom⟩
  have htri1 := norm_add_le
    ((arbitraryOrderPotentialIdentityYosidaTierState P (R a) J a r j x -
        iteratedIdentityPower (R a) a r (iteratedOperatorPower P j x)) -
      (arbitraryOrderPotentialIdentityYosidaTierState P (R b) J b r j x -
        iteratedIdentityPower (R b) b r (iteratedOperatorPower P j x)))
    (iteratedIdentityPower (R a) a r (iteratedOperatorPower P j x) -
      iteratedIdentityPower (R b) b r (iteratedOperatorPower P j x))
  have htri2 := norm_sub_le
    (arbitraryOrderPotentialIdentityYosidaTierState P (R a) J a r j x -
      iteratedIdentityPower (R a) a r (iteratedOperatorPower P j x))
    (arbitraryOrderPotentialIdentityYosidaTierState P (R b) J b r j x -
      iteratedIdentityPower (R b) b r (iteratedOperatorPower P j x))
  linarith

/-- Simultaneous `(m + 1)`-tier two-parameter Cauchy rate bound for all `j ≤ m` when
`x ∈ operatorPowerDomain P (m + 1)`. -/
theorem arbitraryOrderPotentialIdentityYosidaTierSub_all_tiers_cauchy_rate_of_le
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves P (R d) d)
    (hp : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (hl : ∀ d, 0 < d → ∀ z : P.domain, R d (P z + d • (z : H)) = (z : H))
    (m j r : ℕ) (hjm : j ≤ m) {x : H} (hx : x ∈ operatorPowerDomain P (m + 1)) :
    ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x‖ ≤
      2 * ‖J (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + b⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ := by
  have hxj : x ∈ operatorPowerDomain P (j + 1) :=
    operatorPowerDomain_le_of_le P (Nat.succ_le_succ hjm) hx
  exact arbitraryOrderPotentialIdentityYosidaTierSub_cauchy_rate_on_succ
    P R J a b ha hb hr hp hl j r hxj

/-- Joint four-parameter `((a, J₁), (b, J₂))` Cauchy rate bound across both spectral shifts
`(a, b)` and both regularizers `(J₁, J₂)` for all `j ≤ m` on `operatorPowerDomain P (m + 1)`. -/
theorem arbitraryOrderPotentialIdentityYosida_joint_four_parameter_bound_of_le
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J₁ J₂ : H →L[ℂ] H)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves P (R d) d)
    (hp : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (hl : ∀ d, 0 < d → ∀ z : P.domain, R d (P z + d • (z : H)) = (z : H))
    (m j r : ℕ) (hjm : j ≤ m) {x : H} (hx : x ∈ operatorPowerDomain P (m + 1)) :
    ‖arbitraryOrderPotentialIdentityYosidaTierState P (R a) J₁ a r j x -
        arbitraryOrderPotentialIdentityYosidaTierState P (R b) J₂ b r j x‖ ≤
      ‖J₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        ‖J₂ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + b⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ := by
  have hsplit :
      arbitraryOrderPotentialIdentityYosidaTierState P (R a) J₁ a r j x -
        arbitraryOrderPotentialIdentityYosidaTierState P (R b) J₂ b r j x =
      (arbitraryOrderPotentialIdentityYosidaTierState P (R a) J₁ a r j x -
        iteratedOperatorPower P j x) -
      (arbitraryOrderPotentialIdentityYosidaTierState P (R b) J₂ b r j x -
        iteratedOperatorPower P j x) := by abel
  rw [hsplit]
  have htri := norm_sub_le
    (arbitraryOrderPotentialIdentityYosidaTierState P (R a) J₁ a r j x -
      iteratedOperatorPower P j x)
    (arbitraryOrderPotentialIdentityYosidaTierState P (R b) J₂ b r j x -
      iteratedOperatorPower P j x)
  have h1 := arbitraryOrderPotentialIdentityYosidaTierState_all_tiers_rate_bound_of_le
    P (R a) J₁ a ha (hr a ha) hp (hl a ha) m j r hjm hx
  have h2 := arbitraryOrderPotentialIdentityYosidaTierState_all_tiers_rate_bound_of_le
    P (R b) J₂ b hb (hr b hb) hp (hl b hb) m j r hjm hx
  linarith

/-- Strong sequential convergence as `n → ∞` along `J n → id` of
`arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) (J n) a b r j x` to the commuting
operator-power Yosida difference
`iteratedOperatorPower P j (iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b r x)`
for every `j ≤ m` on `operatorPowerDomain P m`. -/
theorem tendsto_arbitraryOrderPotentialIdentityYosidaTierSub_on_powerDomain
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : ℕ → H →L[ℂ] H)
    (hJ : ∀ g : H, Tendsto (fun n => J n g) atTop (𝓝 g))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hr : ∀ d, 0 < d → Resolves P (R d) d)
    (hl : ∀ d, 0 < d → ∀ z : P.domain, R d (P z + d • (z : H)) = (z : H))
    (m r j : ℕ) (hjm : j ≤ m) {x : H} (hx : x ∈ operatorPowerDomain P m) :
    Tendsto
      (fun n => arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) (J n) a b r j x)
      atTop
      (𝓝 (iteratedOperatorPower P j
            (iteratedIdentityPower (R a) a r x - iteratedIdentityPower (R b) b r x))) := by
  have hta :=
    tendsto_arbitraryOrderPotentialIdentityYosidaTierState_commuting_on_powerDomain
      P (R a) J hJ a (hr a ha) (hl a ha) m r j hjm hx
  have htb :=
    tendsto_arbitraryOrderPotentialIdentityYosidaTierState_commuting_on_powerDomain
      P (R b) J hJ b (hr b hb) (hl b hb) m r j hjm hx
  have hxj : x ∈ operatorPowerDomain P j := operatorPowerDomain_le_of_le P hjm hx
  have hcomm :=
    (iteratedOperatorPower_iteratedIdentityPower_sub_comm P R a b ha hb hr hl j r hxj).2.1
  rw [hcomm]
  exact hta.sub htb

end AbstractTwoParameterPotentialYosida

/-! ### 3. Concrete Clock-Floor Potential-Resolvent Two-Parameter Cauchy Rate Synthesis -/

section ClockFloorTwoParameterPotentialYosida

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m_mass g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m_mass g k
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m_mass g k
local notation "RP" => KFCausalClockFloorPotentialClockResolvent.resolvent ε hε h hh hw m_mass g k
local notation "Jcut" => fun n : ℕ => action ε hε h (cutoff n) (cutoff_pos n)

/-- Concrete `j`-th tier `r`-fold two-parameter potential-resolvent radial-Yosida difference
on `Hilbert`. -/
def clockFloorPotentialResolventYosidaTierSub
    (a b : ℝ) (n r j : ℕ) (x : Hilbert) : Hilbert :=
  arbitraryOrderPotentialResolventYosidaTierSub P (RP a) (RP b) (Jcut n) r j x

/-- Concrete `j`-th tier `r`-th power two-parameter Yosida-scaled identity radial-Yosida
difference on `Hilbert`. -/
def clockFloorPotentialIdentityYosidaTierSub
    (a b : ℝ) (n r j : ℕ) (x : Hilbert) : Hilbert :=
  arbitraryOrderPotentialIdentityYosidaTierSub P (RP a) (RP b) (Jcut n) a b r j x

/-- Extra-power `potentialPowerDomain (r + 2)` regularity of
`clockFloorPotentialResolventYosidaTierSub a b n (r + 1) j x`, `potentialPowerDomain r`
regularity of `clockFloorPotentialIdentityYosidaTierSub`, and `4 * kthPowerGraphNormSq P m x`
bound on `arbitraryOrderPotentialYosidaCauchyGraphNormSq`. -/
theorem clockFloorPotentialYosidaTierSub_regularity_and_bounds
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (n r m j : ℕ) (x : Hilbert) :
    clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n (r + 1) j x ∈
      potentialPowerDomain ε hε h hh hb m_mass g k (r + 2) ∧
    clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k a b n r j x ∈
      potentialPowerDomain ε hε h hh hb m_mass g k r ∧
    ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n r j x‖ ≤
      ((a⁻¹) ^ r + (b⁻¹) ^ r) * ‖Jcut n (iteratedOperatorPower P j x)‖ ∧
    arbitraryOrderPotentialYosidaCauchyGraphNormSq P RP (Jcut n) a b r m x ≤
      4 * kthPowerGraphNormSq P m x := by
  have hres := KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m_mass g k
  have hlinv := KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m_mass g k
  have hpos := KFCausalClosedGraphForm.hamiltonian_positive PD
  have hcontr : ∀ v : Hilbert, ‖Jcut n v‖ ≤ ‖v‖ :=
    fun v => action_norm ε hε h (cutoff n) (cutoff_pos n) v
  have hmem := arbitraryOrderPotentialYosidaTierSub_mem_operatorPowerDomain
    P RP (Jcut n) a b ha hb_pos hres hlinv r j x
  have hnorm := arbitraryOrderPotentialYosidaTierSub_norm_bounds
    P RP (Jcut n) a b ha hb_pos hres hpos r j x
  have hgr := arbitraryOrderPotentialYosidaCauchyGraphNormSq_le_four
    P RP (Jcut n) a b ha hb_pos hres hpos hcontr r m x
  exact ⟨hmem.1, hmem.2, hnorm.1, hgr.2⟩

/-- Master Two-Parameter and Four-Parameter Potential-Resolvent Radial-Yosida Cauchy Rate
Synthesis on `potentialPowerDomain (m + 1)`. -/
theorem clockFloorPotentialYosida_twoParameter_cauchy_rate_master_synthesis
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (n₁ n₂ m j r : ℕ) (hjm : j ≤ m)
    {x : Hilbert} (hx : x ∈ potentialPowerDomain ε hε h hh hb m_mass g k (m + 1)) :
    (clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n₁ (r + 1) j x ∈
       potentialPowerDomain ε hε h hh hb m_mass g k (r + 2) ∧
     clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x ∈
       potentialPowerDomain ε hε h hh hb m_mass g k r) ∧
    ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x‖ ≤
      2 * ‖Jcut n₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + b⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ ∧
    ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k a n₁ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k b n₂ r j x‖ ≤
      ‖Jcut n₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        ‖Jcut n₂ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + b⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ ∧
    Tendsto
      (fun n => clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k a b n r j x)
      atTop
      (𝓝 (iteratedOperatorPower P j
            (iteratedIdentityPower (RP a) a r x - iteratedIdentityPower (RP b) b r x))) := by
  have hres := KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m_mass g k
  have hlinv := KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m_mass g k
  have hpos := KFCausalClosedGraphForm.hamiltonian_positive PD
  have hJ : ∀ v : Hilbert, Tendsto (fun n => Jcut n v) atTop (𝓝 v) :=
    fun v => sequence_tendsto ε hε h v
  have hxm : x ∈ potentialPowerDomain ε hε h hh hb m_mass g k m :=
    operatorPowerDomain_le_of_le P (Nat.le_succ m) hx
  have hreg := clockFloorPotentialYosidaTierSub_regularity_and_bounds
    ε hε h hh hb m_mass g k a b ha hb_pos n₁ r m j x
  exact ⟨⟨hreg.1, hreg.2.1⟩,
    arbitraryOrderPotentialIdentityYosidaTierSub_all_tiers_cauchy_rate_of_le
      P RP (Jcut n₁) a b ha hb_pos hres hpos hlinv m j r hjm hx,
    arbitraryOrderPotentialIdentityYosida_joint_four_parameter_bound_of_le
      P RP (Jcut n₁) (Jcut n₂) a b ha hb_pos hres hpos hlinv m j r hjm hx,
    tendsto_arbitraryOrderPotentialIdentityYosidaTierSub_on_powerDomain
      P RP Jcut hJ a b ha hb_pos hres hlinv m r j hjm hxm⟩

end ClockFloorTwoParameterPotentialYosida

#print axioms arbitraryOrderPotentialYosidaTierSub_zero_and_cocycle
#print axioms arbitraryOrderPotentialYosidaTierSub_mem_operatorPowerDomain
#print axioms arbitraryOrderPotentialYosidaTierSub_norm_bounds
#print axioms arbitraryOrderPotentialYosidaCauchyGraphNormSq_le_four
#print axioms arbitraryOrderPotentialIdentityYosidaCutoffSub_eq_and_norm_le
#print axioms arbitraryOrderPotentialIdentityYosidaTierSub_three_piece_split
#print axioms arbitraryOrderPotentialIdentityYosidaTierSub_cauchy_rate_on_succ
#print axioms arbitraryOrderPotentialIdentityYosidaTierSub_all_tiers_cauchy_rate_of_le
#print axioms arbitraryOrderPotentialIdentityYosida_joint_four_parameter_bound_of_le
#print axioms tendsto_arbitraryOrderPotentialIdentityYosidaTierSub_on_powerDomain
#print axioms clockFloorPotentialYosidaTierSub_regularity_and_bounds
#print axioms clockFloorPotentialYosida_twoParameter_cauchy_rate_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaTwoParameterCauchyRate
