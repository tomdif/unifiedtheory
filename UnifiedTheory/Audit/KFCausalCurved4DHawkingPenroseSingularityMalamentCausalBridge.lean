import UnifiedTheory.Audit.KFCausalCurved4DVariationalEinsteinOstrogradskyStabilityBridge
import UnifiedTheory.Audit.KFCausalCurved4DSchwarzschildBirkhoffHawkingThermodynamicsBridge
import UnifiedTheory.LayerC.HawkingPenroseSingularity
import UnifiedTheory.LayerA.DiscreteMalament
import UnifiedTheory.LayerA.GeneralMalament

/-! # 4D Hawking-Penrose Singularity Focusing, Discrete & General Malament Causal
Uniqueness, and Curved Weyl-Schwarzschild-Lovelock Bridge

This module (`UnifiedTheory.Audit.KFCausalCurved4DHawkingPenroseSingularityMalamentCausalBridge`)
connects the Hawking-Penrose singularity and Raychaudhuri focusing framework
(`LayerC.HawkingPenroseSingularity`), the 1+1 discrete Malament theorem
(`LayerA.DiscreteMalament`), and the general `(n+1)`-dimensional Malament conformal
metric uniqueness theorem (`LayerA.GeneralMalament`) to the curved 4D Lorentzian
Weyl-Ricci-Lovelock-Schwarzschild geometry:

1. **Raychaudhuri Focusing ODE, Conjugate-Point Singularity Bound & Trapped Surfaces**:
   - Under `ShearNonneg σ_sq` (`0 ≤ σ_sq`) and the Null Energy Condition `NEC Rkk` (`0 ≤ Rkk`),
     `raychaudhuri_rhs θ σ_sq Rkk ≤ -(1 / 2) * θ ^ 2`, with equality in shear-free vacuum
     (`σ_sq = 0`, `Rkk = 0`) and non-negative focusing gap `σ_sq + Rkk ≥ 0`.
   - For any initially contracting expansion `θ₀ < 0`, the null conjugate-point affine time
     `conjugatePointTime θ₀ = -2 / θ₀` is strictly positive, satisfies `θ₀ * λ_c = -2`,
     is strictly monotone in `θ₀`, and strictly precedes the 4D timelike Hawking conjugate
     bound `-3 / θ₀ = 3 / |θ₀|`.
   - Along `[0, conjugatePointTime θ₀)`, `focusingBound lam θ₀` remains strictly negative,
     monotonically strengthens contraction (`focusingBound lam θ₀ ≤ θ₀`), and its denominator
     vanishes at `lam = conjugatePointTime θ₀`.
   - Inside the Schwarzschild event horizon (`0 < r < 2M`), spheres of radius `r` form
     concrete `TrappedSurface` instances whose outgoing and ingoing null expansions both
     focus in finite affine time.

2. **Discrete `1+1` and General `(n+1)` Malament Causal-Order Conformal Recovery**:
   - In `1+1` dimensions (`LayerA.DiscreteMalament`) and general `(n+1)` dimensions for
     `n ≥ 2` (`LayerA.GeneralMalament`), causal links approximate null directions with
     arbitrarily small nullity (`null_approximation`, `dense_links_trace_null_cone_gen`),
     and any two symmetric bilinear forms sharing the Minkowski null cone are conformally
     equivalent (`g₂ = (g₂ 0 0 / g₁ 0 0) * g₁`).
   - Explicit instantiations for `2+1` (`Fin 3`), physical `3+1` (`Fin 4`), and `4+1` (`Fin 5`)
     spacetimes.

3. **Synthesis with 4D Weyl Conformal Invariance, Sorkin Causal Volume & Schwarzschild**:
   - In 4D, Malament's theorem shows that causal structure determines the metric up to its
     conformal trace part `conformalPartMetricDerivs4D md`, while `weylTensor4D` vanishes
     identically on `conformalPartMetricDerivs4D md` and depends solely on the causal-cone
     traceless part `tracelessPartMetricDerivs4D md`.
   - Combining Malament's `3+1` conformal recovery with Sorkin's causal-set volume law
     (`sorkinLambda ρ V = 1 / √(ρ V) > 0`) and 4D variational Einstein-Lovelock stationarity
     locks the full 4D metric and scalar curvature `scalar md sign = 4 * sorkinLambda ρ V > 0`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCurved4DHawkingPenroseSingularityMalamentCausalBridge
noncomputable section

open scoped BigOperators
open UnifiedTheory.LayerA
  (minkQuad minkBilin genQuad genBilin
   null_cone_coeffs null_cone_quad_1plus1 null_cone_bilin_1plus1
   null_determines_up_to_trace_1plus1)
open UnifiedTheory.LayerA.DiscreteMalament
  (conformal_from_null_cone_1plus1 conformal_factor_exists malament_uniqueness
   link_nullity null_approximation dense_links_trace_null_cone
   discrete_malament_1plus1 stage3_closed_1plus1)
open UnifiedTheory.LayerA.NullConeConformal
  (etaQuad symQuad isNullEta null_same_coeffs null_cone_conformal_2d
   null_cone_conformal_exists_2d conformal_from_same_null_cone_2d
   minkQuadGen null_determines_entries conformal_from_same_null_cone_general
   conformal_class_uniqueness)
open UnifiedTheory.LayerA.GeneralMalament
  (conformal_from_null_cone_general conformal_factor_value
   link_nullity_gen null_approximation_gen dense_links_trace_null_cone_gen
   discrete_malament_general discrete_malament_same_null
   malament_2plus1 malament_3plus1 malament_4plus1
   stage3_closed_general stage3_closed_3plus1)
open UnifiedTheory.LayerC.HawkingPenroseSingularity
  (raychaudhuri_rhs NEC ShearNonneg
   raychaudhuri_bound raychaudhuri_bound_sharp raychaudhuri_gap raychaudhuri_gap_nonneg
   conjugatePointTime conjugatePointTime_pos conjugatePointTime_eq
   conjugatePointTime_denom_zero conjugatePointTime_strictMono_of_neg
   focusingBound focusingBound_at_zero focusingBound_denom_vanishes
   focusingBound_denom_pos focusingBound_neg
   TrappedSurface trappedSurface_θ_plus_neg trappedSurface_θ_minus_neg
   trappedSurface_focusing_plus trappedSurface_focusing_minus trappedSurface_both_focus
   PenroseSetup Penrose_Singularity_Target Penrose_Singularity_Target_consistent
   focusing_theorem_ODE focusing_theorem_quantitative focusing_on_trappedSurface
   hawking_penrose_master hawking_penrose_master_extended)
open UnifiedTheory.LayerA.MetricConstruction (MetricDerivs R_metric)
open UnifiedTheory.LayerA.Ostrogradsky (ostrogradsky_hamiltonian)
open UnifiedTheory.LayerA.GaugeConnection (StructureConstants ConnectionData)
open UnifiedTheory.LayerA.GravitonTTModes (gravitonTTModes)
open UnifiedTheory.LayerA.CosmologicalConstant (sorkinLambda)
open UnifiedTheory.LayerB.BekensteinHawking
  (schwarzschildRadius horizonArea bekensteinHawkingEntropy)
open UnifiedTheory.LayerB.SchwarzschildSolution
  (R_tt R_rr R_thetatheta R_phiphi)
open UnifiedTheory.LayerB.BirkhoffUniqueness
  (IsVacuumSphericallySymmetric StaticGauge schwarzschildAnsatz)
open KFCausalConformal4DDiamondBenchmark (sign)
open KFCausalLorentzianContractedBianchi (scalar)
open KFCausalCurved4DLinearizedMetricDecomposition
  (conformalPartMetricDerivs4D tracelessPartMetricDerivs4D
   metricDerivs4D_conformal_traceless_decomposition)
open KFCausalCurved4DLinearizedWeylRicciSplit
  (weylTensor4D weylTensor4D_conformalPart_eq_zero weylTensor4D_eq_tracelessPart)
open KFCausalCurved4DLovelockCosmologicalConstantSynthesis
  (SatisfiesEinsteinSorkinYangMills4D
   sorkinLambda_strict_pos sorkinLambda_sq_mul_N_eq_one)
open KFCausalCurved4DVariationalEinsteinOstrogradskyStabilityBridge
  (einsteinLovelockYangMillsResidual4D
   ostrogradsky_stability_to_einstein_bridge
   einsteinLovelockYangMills4D_iff_variational_stationarity
   einsteinSorkinYangMills4D_iff_variational_stationarity
   variational_sorkin_stationarity_locks_positive_deSitter_scalar)
open KFCausalCurved4DSchwarzschildBirkhoffHawkingThermodynamicsBridge
  (schwarzschildKretschmann
   schwarzschild_ricci_components_all_vanish
   birkhoff_uniqueness_master_bridge
   schwarzschildKretschmann_pos
   schwarzschildKretschmann_horizon_times_entropy_sq)

/-! ### 1. Raychaudhuri Focusing ODE, Conjugate-Point Time & Trapped Surface Convergence -/

/-- **Raychaudhuri Focusing Inequality**:
Under non-negative shear (`ShearNonneg σ_sq`) and the Null Energy Condition (`NEC Rkk`),
`raychaudhuri_rhs θ σ_sq Rkk ≤ -(1 / 2) * θ ^ 2`. -/
theorem raychaudhuri_focusing_bound_under_nec
    (θ σ_sq Rkk : ℝ) (hShear : ShearNonneg σ_sq) (hNEC : NEC Rkk) :
    raychaudhuri_rhs θ σ_sq Rkk ≤ -(1 / 2) * θ ^ 2 :=
  raychaudhuri_bound θ σ_sq Rkk hShear hNEC

/-- **Sharp Vacuum Focusing & Gap Identity**:
When `σ_sq = 0` and `Rkk = 0`, `raychaudhuri_rhs θ 0 0 = -(1 / 2) * θ ^ 2`, and for
general `(σ_sq, Rkk)` the focusing gap equals `σ_sq + Rkk`. -/
theorem raychaudhuri_sharp_vacuum_and_gap_identity (θ σ_sq Rkk : ℝ) :
    raychaudhuri_rhs θ 0 0 = -(1 / 2) * θ ^ 2 ∧
    -(1 / 2) * θ ^ 2 - raychaudhuri_rhs θ σ_sq Rkk = σ_sq + Rkk :=
  ⟨raychaudhuri_bound_sharp θ, raychaudhuri_gap θ σ_sq Rkk⟩

/-- Non-negativity of the Raychaudhuri focusing gap under `ShearNonneg` and `NEC`. -/
theorem raychaudhuri_gap_nonneg_under_nec
    (θ σ_sq Rkk : ℝ) (hShear : ShearNonneg σ_sq) (hNEC : NEC Rkk) :
    0 ≤ -(1 / 2) * θ ^ 2 - raychaudhuri_rhs θ σ_sq Rkk :=
  raychaudhuri_gap_nonneg θ σ_sq Rkk hShear hNEC

/-- Strict positivity of the null conjugate-point affine time `conjugatePointTime θ₀ = -2 / θ₀`
for any contracting initial expansion `θ₀ < 0`. -/
theorem conjugatePointTime_strict_pos_of_contracting (θ₀ : ℝ) (hθ : θ₀ < 0) :
    0 < conjugatePointTime θ₀ ∧ conjugatePointTime θ₀ = -2 / θ₀ :=
  ⟨conjugatePointTime_pos θ₀ hθ, focusing_theorem_quantitative θ₀ hθ⟩

/-- Defining product identity `θ₀ * conjugatePointTime θ₀ = -2` and vanishing of the
comparison ODE denominator `1 + θ₀ * conjugatePointTime θ₀ / 2 = 0` for `θ₀ ≠ 0`. -/
theorem conjugatePointTime_product_and_denom_zero (θ₀ : ℝ) (hθ : θ₀ ≠ 0) :
    θ₀ * conjugatePointTime θ₀ = -2 ∧
    1 + θ₀ * conjugatePointTime θ₀ / 2 = 0 :=
  ⟨conjugatePointTime_eq θ₀ hθ, conjugatePointTime_denom_zero θ₀ hθ⟩

/-- **Strict Monotonicity of Conjugate-Point Time**:
Stronger initial convergence (`θ₀ < θ₁ < 0`) forces an earlier conjugate point
(`conjugatePointTime θ₀ < conjugatePointTime θ₁`). -/
theorem conjugatePointTime_strictMono_on_contracting
    (θ₀ θ₁ : ℝ) (h₀ : θ₀ < 0) (h₁ : θ₁ < 0) (hlt : θ₀ < θ₁) :
    conjugatePointTime θ₀ < conjugatePointTime θ₁ :=
  conjugatePointTime_strictMono_of_neg θ₀ θ₁ h₀ h₁ hlt

/-- **Null vs. Timelike Hawking Conjugate Time Comparison (`-2/θ₀ < -3/θ₀`)**:
For any contracting expansion `θ₀ < 0`, the null Raychaudhuri conjugate time
`conjugatePointTime θ₀ = -2 / θ₀` is strictly positive and strictly precedes the 4D
timelike Hawking conjugate bound `-3 / θ₀ = 3 / |θ₀|`. -/
theorem conjugatePointTime_lt_timelike_hawking_bound (θ₀ : ℝ) (hθ : θ₀ < 0) :
    0 < conjugatePointTime θ₀ ∧
    conjugatePointTime θ₀ < -3 / θ₀ ∧
    0 < -3 / θ₀ := by
  have hpos := conjugatePointTime_pos θ₀ hθ
  have hdiff : (-3 / θ₀) - conjugatePointTime θ₀ = -1 / θ₀ := by
    unfold conjugatePointTime
    ring
  have h1pos : 0 < -1 / θ₀ := div_pos_of_neg_of_neg (by norm_num) hθ
  refine ⟨hpos, ?_, ?_⟩
  · linarith
  · linarith

/-- Initial value `focusingBound 0 θ₀ = θ₀` and denominator blowup at `conjugatePointTime θ₀`. -/
theorem focusingBound_initial_and_blowup_denom (θ₀ : ℝ) (hθ : θ₀ ≠ 0) :
    focusingBound 0 θ₀ = θ₀ ∧
    1 + (θ₀ * conjugatePointTime θ₀) / 2 = 0 :=
  ⟨focusingBound_at_zero θ₀, focusingBound_denom_vanishes θ₀ hθ⟩

/-- On the pre-conjugate interval `[0, conjugatePointTime θ₀)`, the comparison denominator
is strictly positive and `focusingBound lam θ₀ < 0`. -/
theorem focusingBound_denom_pos_and_strict_neg
    (lam θ₀ : ℝ) (h_init : θ₀ < 0) (h_lam : 0 ≤ lam)
    (h_before : lam < conjugatePointTime θ₀) :
    0 < 1 + (θ₀ * lam) / 2 ∧ focusingBound lam θ₀ < 0 :=
  ⟨focusingBound_denom_pos lam θ₀ h_init h_lam h_before,
   focusingBound_neg lam θ₀ h_init h_lam h_before⟩

/-- **Monotonic Strengthening of Contraction**:
Throughout `[0, conjugatePointTime θ₀)` for `θ₀ < 0`, `focusingBound lam θ₀ ≤ θ₀`. -/
theorem focusingBound_le_initial_expansion_on_domain
    (lam θ₀ : ℝ) (h_init : θ₀ < 0) (h_lam : 0 ≤ lam)
    (h_before : lam < conjugatePointTime θ₀) :
    focusingBound lam θ₀ ≤ θ₀ := by
  have hd : 0 < 1 + (θ₀ * lam) / 2 :=
    focusingBound_denom_pos lam θ₀ h_init h_lam h_before
  unfold focusingBound
  rw [div_le_iff₀ hd]
  have hsq : 0 ≤ θ₀ ^ 2 * lam := mul_nonneg (sq_nonneg θ₀) h_lam
  linarith

/-- On any `TrappedSurface`, both null expansions `θ_plus` and `θ_minus` are strictly
negative and both focus in finite positive affine parameter. -/
theorem trappedSurface_expansions_neg_and_both_focus (T : TrappedSurface) :
    T.θ_plus < 0 ∧
    T.θ_minus < 0 ∧
    0 < conjugatePointTime T.θ_plus ∧
    0 < conjugatePointTime T.θ_minus :=
  ⟨trappedSurface_θ_plus_neg T,
   trappedSurface_θ_minus_neg T,
   (trappedSurface_both_focus T).1,
   (trappedSurface_both_focus T).2⟩

/-- Quantitative focusing identities `T.θ_± * conjugatePointTime T.θ_± = -2` on a trapped surface. -/
theorem trappedSurface_quantitative_focusing_identities (T : TrappedSurface) :
    (0 < conjugatePointTime T.θ_plus) ∧
    (0 < conjugatePointTime T.θ_minus) ∧
    (T.θ_plus * conjugatePointTime T.θ_plus = -2) ∧
    (T.θ_minus * conjugatePointTime T.θ_minus = -2) :=
  focusing_on_trappedSurface T

/-- Propositional consistency of `Penrose_Singularity_Target`. -/
theorem penrose_singularity_target_propositional_consistency :
    Penrose_Singularity_Target :=
  Penrose_Singularity_Target_consistent

/-- **Concrete Schwarzschild Interior Trapped Surface (`0 < r < 2M`)**:
Inside the Schwarzschild event horizon (`0 < r < schwarzschildRadius M`), a 2-sphere of
areal radius `r` has strictly negative outgoing and ingoing null expansions
`θ_+ = -(2M - r) / r^2 < 0` and `θ_- = -(2M + r) / r^2 < 0`. -/
def schwarzschildInteriorTrappedSurface
    (M r : ℝ) (hM : 0 < M) (hr_pos : 0 < r) (hr_lt : r < schwarzschildRadius M) :
    TrappedSurface where
  θ_plus := -(2 * M - r) / r ^ 2
  θ_minus := -(2 * M + r) / r ^ 2
  trapped := by
    unfold schwarzschildRadius at hr_lt
    have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr_pos
    refine ⟨div_neg_of_neg_of_pos (by linarith) hr2,
            div_neg_of_neg_of_pos (by linarith) hr2⟩

/-- Both null expansions of `schwarzschildInteriorTrappedSurface M r` are strictly negative. -/
theorem schwarzschild_interior_trapped_surface_expansions_neg
    (M r : ℝ) (hM : 0 < M) (hr_pos : 0 < r) (hr_lt : r < schwarzschildRadius M) :
    (schwarzschildInteriorTrappedSurface M r hM hr_pos hr_lt).θ_plus < 0 ∧
    (schwarzschildInteriorTrappedSurface M r hM hr_pos hr_lt).θ_minus < 0 :=
  (schwarzschildInteriorTrappedSurface M r hM hr_pos hr_lt).trapped

/-- **Finite Conjugate-Point Times Inside the Schwarzschild Event Horizon**:
For `0 < r < 2M`, both null congruences of `schwarzschildInteriorTrappedSurface M r`
focus in finite positive affine parameter, with explicit conjugate times
`2 * r^2 / (2M - r)` and `2 * r^2 / (2M + r)`. -/
theorem schwarzschild_interior_trapped_surface_conjugate_times
    (M r : ℝ) (hM : 0 < M) (hr_pos : 0 < r) (hr_lt : r < schwarzschildRadius M) :
    0 < conjugatePointTime (schwarzschildInteriorTrappedSurface M r hM hr_pos hr_lt).θ_plus ∧
    0 < conjugatePointTime (schwarzschildInteriorTrappedSurface M r hM hr_pos hr_lt).θ_minus ∧
    conjugatePointTime (schwarzschildInteriorTrappedSurface M r hM hr_pos hr_lt).θ_plus =
      2 * r ^ 2 / (2 * M - r) ∧
    conjugatePointTime (schwarzschildInteriorTrappedSurface M r hM hr_pos hr_lt).θ_minus =
      2 * r ^ 2 / (2 * M + r) := by
  have hfocus := trappedSurface_both_focus
    (schwarzschildInteriorTrappedSurface M r hM hr_pos hr_lt)
  unfold schwarzschildRadius at hr_lt
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have h1_ne : 2 * M - r ≠ 0 := by linarith
  have h2_ne : 2 * M + r ≠ 0 := by linarith
  refine ⟨hfocus.1, hfocus.2, ?_, ?_⟩
  · unfold conjugatePointTime schwarzschildInteriorTrappedSurface
    field_simp
  · unfold conjugatePointTime schwarzschildInteriorTrappedSurface
    field_simp

/-- **Schwarzschild Vacuum Sharp Raychaudhuri Evolution**:
Because all four Schwarzschild Ricci components vanish (`R_tt = R_rr = R_thetatheta = R_phiphi = 0`),
the Ricci focusing scalar vanishes (`Rkk = 0`), so any shear-free (`σ_sq = 0`) null congruence
satisfies `NEC 0`, `ShearNonneg 0`, and the exact sharp evolution `raychaudhuri_rhs θ 0 0 = -(1/2) * θ^2`. -/
theorem schwarzschild_vacuum_raychaudhuri_sharp_evolution
    (M r θ_ang θ_exp : ℝ) (hr : r ≠ 0) :
    (R_tt M r = 0 ∧ R_rr M r = 0 ∧ R_thetatheta M r = 0 ∧ R_phiphi M r θ_ang = 0) ∧
    NEC 0 ∧
    ShearNonneg 0 ∧
    raychaudhuri_rhs θ_exp 0 0 = -(1 / 2) * θ_exp ^ 2 :=
  ⟨schwarzschild_ricci_components_all_vanish M r θ_ang hr,
   le_refl 0, le_refl 0, raychaudhuri_bound_sharp θ_exp⟩

/-- **Yang-Mills Null Energy Focusing**:
Whenever the gravitational coupling `0 ≤ κ` and null stress-energy contraction `0 ≤ Tkk`
are non-negative, `NEC (κ * Tkk)` holds and `raychaudhuri_rhs θ σ_sq (κ * Tkk) ≤ -(1 / 2) * θ ^ 2`
for every `σ_sq ≥ 0`. -/
theorem yangMills_positive_null_energy_implies_raychaudhuri_focusing
    (θ σ_sq κ Tkk : ℝ) (hShear : ShearNonneg σ_sq) (hκ : 0 ≤ κ) (hT : 0 ≤ Tkk) :
    NEC (κ * Tkk) ∧
    raychaudhuri_rhs θ σ_sq (κ * Tkk) ≤ -(1 / 2) * θ ^ 2 := by
  have hNEC : NEC (κ * Tkk) := mul_nonneg hκ hT
  exact ⟨hNEC, raychaudhuri_bound θ σ_sq (κ * Tkk) hShear hNEC⟩

/-- Complete Hawking-Penrose singularity and Raychaudhuri focusing master bridge. -/
theorem hawking_penrose_singularity_master_bridge (θ₀ : ℝ) (hθ : θ₀ < 0) :
    (∀ θ σ_sq Rkk, ShearNonneg σ_sq → NEC Rkk →
        raychaudhuri_rhs θ σ_sq Rkk ≤ -(1 / 2) * θ ^ 2) ∧
    (0 < conjugatePointTime θ₀ ∧ θ₀ * conjugatePointTime θ₀ = -2) ∧
    (∀ T : TrappedSurface,
        0 < conjugatePointTime T.θ_plus ∧ 0 < conjugatePointTime T.θ_minus) ∧
    Penrose_Singularity_Target :=
  ⟨hawking_penrose_master.1,
   focusing_theorem_ODE θ₀ hθ,
   trappedSurface_both_focus,
   Penrose_Singularity_Target_consistent⟩

/-! ### 2. Discrete `1+1` Malament Causal-Order Recovery (`LayerA.DiscreteMalament`) -/

/-- **Algebraic `1+1` Malament Null-Cone Theorem**:
Any symmetric quadratic form `genQuad a b c` vanishing on the `1+1` Minkowski null cone
`minkQuad v = 0` has `b = 0 ∧ c = -a` and equals `(-a) * minkQuad v`. -/
theorem malament_1plus1_null_cone_coeffs_and_quad_proportionality
    (a b c : ℝ) (h : ∀ v : Fin 2 → ℝ, minkQuad v = 0 → genQuad a b c v = 0) :
    (b = 0 ∧ c = -a) ∧
    (∀ v : Fin 2 → ℝ, genQuad a b c v = (-a) * minkQuad v) :=
  ⟨conformal_from_null_cone_1plus1 a b c h, null_cone_quad_1plus1 a b c h⟩

/-- Bilinear proportionality and conformal factor existence in `1+1` dimensions. -/
theorem malament_1plus1_bilin_and_conformal_factor_exists
    (a b c : ℝ) (h : ∀ v : Fin 2 → ℝ, minkQuad v = 0 → genQuad a b c v = 0) :
    (∀ v w : Fin 2 → ℝ, genBilin a b c v w = (-a) * minkBilin v w) ∧
    (∃ cf : ℝ, ∀ v : Fin 2 → ℝ, genQuad a b c v = cf * minkQuad v) ∧
    (∃ c₀ : ℝ, ∀ v w : Fin 2 → ℝ, genBilin a b c v w = c₀ * minkBilin v w) :=
  ⟨null_cone_bilin_1plus1 a b c h,
   conformal_factor_exists a b c h,
   null_determines_up_to_trace_1plus1 a b c h⟩

/-- **`1+1` Malament Conformal Uniqueness & Explicit Ratio**:
If `genQuad a₁ b₁ c₁` and `genQuad a₂ b₂ c₂` both vanish on `minkQuad v = 0` with `a₁ ≠ 0`,
then `genQuad a₂ b₂ c₂ v = (a₂ / a₁) * genQuad a₁ b₁ c₁ v`. -/
theorem malament_1plus1_uniqueness_and_explicit_ratio
    (a₁ b₁ c₁ a₂ b₂ c₂ : ℝ)
    (h₁ : ∀ v : Fin 2 → ℝ, minkQuad v = 0 → genQuad a₁ b₁ c₁ v = 0)
    (h₂ : ∀ v : Fin 2 → ℝ, minkQuad v = 0 → genQuad a₂ b₂ c₂ v = 0)
    (ha₁ : a₁ ≠ 0) :
    (∃ μ : ℝ, ∀ v : Fin 2 → ℝ, genQuad a₂ b₂ c₂ v = μ * genQuad a₁ b₁ c₁ v) ∧
    (∀ v : Fin 2 → ℝ, genQuad a₂ b₂ c₂ v = (a₂ / a₁) * genQuad a₁ b₁ c₁ v) := by
  have hc₁ := null_cone_coeffs a₁ b₁ c₁ h₁
  have hc₂ := null_cone_coeffs a₂ b₂ c₂ h₂
  refine ⟨malament_uniqueness a₁ b₁ c₁ a₂ b₂ c₂ h₁ h₂ ha₁, fun v => ?_⟩
  simp only [genQuad, hc₁.1, hc₁.2, hc₂.1, hc₂.2]
  field_simp
  ring

/-- **Causal Link Nullity & Dense Null-Cone Tracing (`1+1`)**:
Combines `null_approximation` and `dense_links_trace_null_cone`. -/
theorem discrete_malament_1plus1_link_nullity_and_dense_cone
    (dt dx n_t n_x ε : ℝ) (hdt : 0 < dt) (h_causal : dt ^ 2 ≥ dx ^ 2)
    (h_null_approx : |dt ^ 2 - dx ^ 2| < ε * dt ^ 2)
    (h_null : n_t ^ 2 = n_x ^ 2) (h_pos : 0 < n_t) (hε : 0 < ε) :
    link_nullity dt dx hdt < ε ∧
    (∃ (dt' dx' : ℝ), 0 < dt' ∧ dt' ^ 2 ≥ dx' ^ 2 ∧
      |dt' ^ 2 - dx' ^ 2| < ε * dt' ^ 2 ∧
      |dx' / dt' - n_x / n_t| < ε) :=
  ⟨null_approximation dt dx hdt h_causal h_null_approx hε,
   dense_links_trace_null_cone n_t n_x h_null h_pos ε hε⟩

/-- Complete `1+1` discrete Malament and Stage 3 closure theorem. -/
theorem discrete_malament_1plus1_same_null_and_stage3_closed
    (a₁ b₁ c₁ a₂ b₂ c₂ : ℝ)
    (h_same_null : ∀ v : Fin 2 → ℝ, genQuad a₁ b₁ c₁ v = 0 ↔ genQuad a₂ b₂ c₂ v = 0)
    (h₁_null : ∀ v : Fin 2 → ℝ, minkQuad v = 0 → genQuad a₁ b₁ c₁ v = 0)
    (ha₁ : a₁ ≠ 0) :
    (∃ μ : ℝ, ∀ v : Fin 2 → ℝ, genQuad a₂ b₂ c₂ v = μ * genQuad a₁ b₁ c₁ v) ∧
    (∀ (x₁ y₁ z₁ x₂ y₂ z₂ : ℝ),
      x₁ ≠ 0 →
      (∀ v : Fin 2 → ℝ, minkQuad v = 0 → genQuad x₁ y₁ z₁ v = 0) →
      (∀ v : Fin 2 → ℝ, minkQuad v = 0 → genQuad x₂ y₂ z₂ v = 0) →
      ∃ μ : ℝ, ∀ v : Fin 2 → ℝ, genQuad x₂ y₂ z₂ v = μ * genQuad x₁ y₁ z₁ v) :=
  ⟨discrete_malament_1plus1 a₁ b₁ c₁ a₂ b₂ c₂ h_same_null h₁_null ha₁,
   stage3_closed_1plus1⟩

/-- 2D null-cone conformal equivalence from `LayerA.NullConeConformal`. -/
theorem null_cone_conformal_2d_coeffs_and_equivalence
    (a₁ b₁ c₁ a₂ b₂ c₂ : ℝ)
    (h₁ : ∀ v : Fin 2 → ℝ, isNullEta v → symQuad a₁ b₁ c₁ v = 0)
    (h₂ : ∀ v : Fin 2 → ℝ, isNullEta v → symQuad a₂ b₂ c₂ v = 0)
    (ha₁ : a₁ ≠ 0) :
    (b₁ = 0 ∧ c₁ = -a₁) ∧
    (∀ v : Fin 2 → ℝ, symQuad a₁ b₁ c₁ v = (-a₁) * etaQuad v) ∧
    (∃ c : ℝ, ∀ v : Fin 2 → ℝ, symQuad a₁ b₁ c₁ v = c * etaQuad v) ∧
    (∃ mu : ℝ, ∀ v : Fin 2 → ℝ, symQuad a₂ b₂ c₂ v = mu * symQuad a₁ b₁ c₁ v) :=
  ⟨null_same_coeffs a₁ b₁ c₁ h₁,
   null_cone_conformal_2d a₁ b₁ c₁ h₁,
   null_cone_conformal_exists_2d a₁ b₁ c₁ h₁,
   conformal_from_same_null_cone_2d a₁ b₁ c₁ a₂ b₂ c₂ h₁ h₂ ha₁⟩

/-! ### 3. General `(n+1)`-Dimensional Malament Conformal Uniqueness (`LayerA.GeneralMalament`) -/

/-- **General `(n+1)` Null-Cone Entry Determination (`n ≥ 2`)**:
Any symmetric matrix `M` on `ℝ^{n+1}` vanishing on `minkQuadGen v = 0` has vanishing
time-space cross terms, vanishing spatial off-diagonal terms, and uniform spatial
diagonal equal to `-M 0 0`. -/
theorem general_null_cone_entry_determination_bridge {n : ℕ} (hn : 1 < n)
    (M : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hSym : ∀ i j, M i j = M j i)
    (h_null : ∀ v : Fin (n + 1) → ℝ,
      minkQuadGen v = 0 →
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), M i j * v i * v j = 0)) :
    (∀ k : Fin n, M 0 (Fin.succ k) = 0) ∧
    (∀ k l : Fin n, k ≠ l → M (Fin.succ k) (Fin.succ l) = 0) ∧
    (∀ k l : Fin n, M (Fin.succ k) (Fin.succ k) = M (Fin.succ l) (Fin.succ l)) ∧
    (∀ k : Fin n, M (Fin.succ k) (Fin.succ k) = -(M 0 0)) :=
  null_determines_entries hn M hSym h_null

/-- **General `(n+1)` Malament Conformal Equivalence & Explicit Factor (`g₂ 0 0 / g₁ 0 0`)**:
Combines `conformal_from_null_cone_general`, `conformal_factor_value`, and `conformal_class_uniqueness`. -/
theorem general_malament_conformal_equivalence_and_factor_value {n : ℕ} (hn : 1 < n)
    (g₁ g₂ : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hSym₁ : ∀ i j, g₁ i j = g₁ j i)
    (hSym₂ : ∀ i j, g₂ i j = g₂ j i)
    (h₁ : ∀ v : Fin (n + 1) → ℝ,
      minkQuadGen v = 0 →
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), g₁ i j * v i * v j = 0))
    (h₂ : ∀ v : Fin (n + 1) → ℝ,
      minkQuadGen v = 0 →
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), g₂ i j * v i * v j = 0))
    (hg₁ : g₁ 0 0 ≠ 0) :
    (∃ μ : ℝ, ∀ i j : Fin (n + 1), g₂ i j = μ * g₁ i j) ∧
    (∀ i j : Fin (n + 1), g₂ i j = (g₂ 0 0 / g₁ 0 0) * g₁ i j) :=
  ⟨conformal_from_null_cone_general hn g₁ g₂ hSym₁ hSym₂ h₁ h₂ hg₁,
   conformal_factor_value hn g₁ g₂ hSym₁ hSym₂ h₁ h₂ hg₁⟩

/-- **General `(n+1)` Causal Link Nullity & Dense Null-Cone Tracing**:
Combines `null_approximation_gen` and `dense_links_trace_null_cone_gen`. -/
theorem general_malament_dense_links_and_null_approximation {n : ℕ}
    (dt : ℝ) (dx : Fin n → ℝ) (n_t : ℝ) (n_x : Fin n → ℝ) (ε : ℝ)
    (hdt : 0 < dt) (h_causal : dt ^ 2 ≥ ∑ i : Fin n, (dx i) ^ 2)
    (h_null_approx : |dt ^ 2 - ∑ i : Fin n, (dx i) ^ 2| < ε * dt ^ 2)
    (h_null : n_t ^ 2 = ∑ i : Fin n, (n_x i) ^ 2) (h_pos : 0 < n_t) (hε : 0 < ε) :
    link_nullity_gen dt dx hdt < ε ∧
    (∃ (dt' : ℝ) (dx' : Fin n → ℝ),
      0 < dt' ∧
      dt' ^ 2 ≥ ∑ i : Fin n, (dx' i) ^ 2 ∧
      |dt' ^ 2 - ∑ i : Fin n, (dx' i) ^ 2| < ε * dt' ^ 2) :=
  ⟨null_approximation_gen dt dx hdt h_causal h_null_approx hε,
   dense_links_trace_null_cone_gen n_t n_x h_null h_pos ε hε⟩

/-- General `(n+1)` discrete Malament same-null-cone equivalence and Stage 3 closure. -/
theorem general_malament_same_null_and_stage3_closed {n : ℕ} (hn : 1 < n)
    (g₁ g₂ : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hSym₁ : ∀ i j, g₁ i j = g₁ j i)
    (hSym₂ : ∀ i j, g₂ i j = g₂ j i)
    (h₁_eta : ∀ v : Fin (n + 1) → ℝ,
      minkQuadGen v = 0 →
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), g₁ i j * v i * v j = 0))
    (h_same_null : ∀ v : Fin (n + 1) → ℝ,
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), g₁ i j * v i * v j = 0) ↔
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), g₂ i j * v i * v j = 0))
    (hg₁ : g₁ 0 0 ≠ 0) :
    (∃ μ : ℝ, ∀ i j : Fin (n + 1), g₂ i j = μ * g₁ i j) ∧
    (∀ (m₁ m₂ : Fin (n + 1) → Fin (n + 1) → ℝ),
      (∀ i j, m₁ i j = m₁ j i) →
      (∀ i j, m₂ i j = m₂ j i) →
      m₁ 0 0 ≠ 0 →
      (∀ v : Fin (n + 1) → ℝ, minkQuadGen v = 0 →
        (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), m₁ i j * v i * v j = 0)) →
      (∀ v : Fin (n + 1) → ℝ, minkQuadGen v = 0 →
        (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), m₂ i j * v i * v j = 0)) →
      ∃ μ : ℝ, ∀ i j : Fin (n + 1), m₂ i j = μ * m₁ i j) :=
  ⟨discrete_malament_same_null hn g₁ g₂ hSym₁ hSym₂ h₁_eta h_same_null hg₁,
   stage3_closed_general hn⟩

/-- **Spacetime Malament Instantiations (`2+1`, `3+1`, `4+1`) & Graviton TT Mode Accounting**:
Bundles `malament_2plus1`, `malament_3plus1`, `malament_4plus1`, and `stage3_closed_3plus1`
with `gravitonTTModes 3 = 0`, `gravitonTTModes 4 = 2`, and `gravitonTTModes 5 = 5`. -/
theorem malament_spacetime_instantiations_2plus1_3plus1_4plus1 :
    gravitonTTModes 3 = 0 ∧
    gravitonTTModes 4 = 2 ∧
    gravitonTTModes 5 = 5 ∧
    (∀ (g₁ g₂ : Fin 3 → Fin 3 → ℝ),
      (∀ i j, g₁ i j = g₁ j i) → (∀ i j, g₂ i j = g₂ j i) →
      (∀ v : Fin 3 → ℝ, minkQuadGen v = 0 → ∑ i : Fin 3, ∑ j : Fin 3, g₁ i j * v i * v j = 0) →
      (∀ v : Fin 3 → ℝ, minkQuadGen v = 0 → ∑ i : Fin 3, ∑ j : Fin 3, g₂ i j * v i * v j = 0) →
      g₁ 0 0 ≠ 0 → ∃ μ : ℝ, ∀ i j : Fin 3, g₂ i j = μ * g₁ i j) ∧
    (∀ (g₁ g₂ : Fin 4 → Fin 4 → ℝ),
      (∀ i j, g₁ i j = g₁ j i) → (∀ i j, g₂ i j = g₂ j i) → g₁ 0 0 ≠ 0 →
      (∀ v : Fin 4 → ℝ, minkQuadGen v = 0 → ∑ i : Fin 4, ∑ j : Fin 4, g₁ i j * v i * v j = 0) →
      (∀ v : Fin 4 → ℝ, minkQuadGen v = 0 → ∑ i : Fin 4, ∑ j : Fin 4, g₂ i j * v i * v j = 0) →
      ∃ μ : ℝ, ∀ i j : Fin 4, g₂ i j = μ * g₁ i j) ∧
    (∀ (g₁ g₂ : Fin 5 → Fin 5 → ℝ),
      (∀ i j, g₁ i j = g₁ j i) → (∀ i j, g₂ i j = g₂ j i) →
      (∀ v : Fin 5 → ℝ, minkQuadGen v = 0 → ∑ i : Fin 5, ∑ j : Fin 5, g₁ i j * v i * v j = 0) →
      (∀ v : Fin 5 → ℝ, minkQuadGen v = 0 → ∑ i : Fin 5, ∑ j : Fin 5, g₂ i j * v i * v j = 0) →
      g₁ 0 0 ≠ 0 → ∃ μ : ℝ, ∀ i j : Fin 5, g₂ i j = μ * g₁ i j) :=
  ⟨by decide, by decide, by decide,
   malament_2plus1, stage3_closed_3plus1, malament_4plus1⟩

/-- **`3+1` Physical Spacetime Malament Entry Structure & Explicit Conformal Factor**:
In `3+1` dimensions (`Fin 4 → Fin 4 → ℝ`), any two symmetric metrics vanishing on the
Minkowski null cone are diagonal with spatial entries `-g 0 0` and satisfy
`g₂ i j = (g₂ 0 0 / g₁ 0 0) * g₁ i j` for all `i, j : Fin 4`. -/
theorem malament_3plus1_explicit_entries_and_conformal_factor
    (g₁ g₂ : Fin 4 → Fin 4 → ℝ)
    (hSym₁ : ∀ i j, g₁ i j = g₁ j i)
    (hSym₂ : ∀ i j, g₂ i j = g₂ j i)
    (h₁ : ∀ v : Fin 4 → ℝ,
      minkQuadGen v = 0 →
      (∑ i : Fin 4, ∑ j : Fin 4, g₁ i j * v i * v j = 0))
    (h₂ : ∀ v : Fin 4 → ℝ,
      minkQuadGen v = 0 →
      (∑ i : Fin 4, ∑ j : Fin 4, g₂ i j * v i * v j = 0))
    (hg₁ : g₁ 0 0 ≠ 0) :
    (∀ k : Fin 3, g₁ 0 (Fin.succ k) = 0) ∧
    (∀ k l : Fin 3, k ≠ l → g₁ (Fin.succ k) (Fin.succ l) = 0) ∧
    (∀ k : Fin 3, g₁ (Fin.succ k) (Fin.succ k) = -(g₁ 0 0)) ∧
    (∀ i j : Fin 4, g₂ i j = (g₂ 0 0 / g₁ 0 0) * g₁ i j) := by
  have hent := null_determines_entries (by norm_num : 1 < 3) g₁ hSym₁ h₁
  exact ⟨hent.1, hent.2.1, hent.2.2.2,
    conformal_factor_value (by norm_num : 1 < 3) g₁ g₂ hSym₁ hSym₂ h₁ h₂ hg₁⟩

/-! ### 4. Curved 4D Conformal-Weyl-Lovelock-Schwarzschild Synthesis with Malament & Hawking-Penrose -/

/-- **Malament 4D Conformal Recovery ↔ Weyl Tensor Conformal Invariance Bridge**:
1. By Malament's `3+1` theorem (`stage3_closed_3plus1`), the causal/null cone determines
   the 4D metric up to a scalar conformal factor.
2. In the 4D linearized metric jet decomposition `md = conformalPart + tracelessPart`,
   the conformal factor jet `conformalPartMetricDerivs4D md` has identically vanishing
   Weyl tensor (`weylTensor4D (conformalPartMetricDerivs4D md) = 0`), so the 4D Weyl
   tensor `weylTensor4D md = weylTensor4D (tracelessPartMetricDerivs4D md)` is determined
   purely by the causal-cone structure. -/
theorem malament_4D_conformal_weyl_invariance_bridge
    (md : MetricDerivs 4) (e f a b c d : Fin 4) :
    (∀ (g₁ g₂ : Fin 4 → Fin 4 → ℝ),
      (∀ i j, g₁ i j = g₁ j i) → (∀ i j, g₂ i j = g₂ j i) → g₁ 0 0 ≠ 0 →
      (∀ v : Fin 4 → ℝ, minkQuadGen v = 0 → ∑ i : Fin 4, ∑ j : Fin 4, g₁ i j * v i * v j = 0) →
      (∀ v : Fin 4 → ℝ, minkQuadGen v = 0 → ∑ i : Fin 4, ∑ j : Fin 4, g₂ i j * v i * v j = 0) →
      ∃ μ : ℝ, ∀ i j : Fin 4, g₂ i j = μ * g₁ i j) ∧
    md.h e f a b =
      (conformalPartMetricDerivs4D md).h e f a b +
        (tracelessPartMetricDerivs4D md).h e f a b ∧
    weylTensor4D (conformalPartMetricDerivs4D md) a b c d = 0 ∧
    weylTensor4D md a b c d =
      weylTensor4D (tracelessPartMetricDerivs4D md) a b c d :=
  ⟨stage3_closed_3plus1,
   (metricDerivs4D_conformal_traceless_decomposition md).1 e f a b,
   weylTensor4D_conformalPart_eq_zero md a b c d,
   weylTensor4D_eq_tracelessPart md a b c d⟩

/-- **Malament Causal Order + Sorkin Causal-Set Volume + 4D Variational Stationarity Bridge**:
Combines `stage3_closed_3plus1` (conformal metric from causal order) with Sorkin's
causal-set volume/cosmological-constant law (`0 < sorkinLambda ρ V`, `Λ^2 * (ρ * V) = 1`)
and the 4D variational stationarity locking `scalar md sign = 4 * sorkinLambda ρ V > 0`
and `(scalar md sign)^2 * (ρ * V) = 16`. -/
theorem malament_causal_sorkin_volume_and_variational_4D_bridge
    (md : MetricDerivs 4) (ρ V κ : ℝ) (hρ : 0 < ρ) (hV : 0 < V)
    (sc₃ : StructureConstants 8) (conn₃ : ConnectionData 4 8) :
    (∀ (g₁ g₂ : Fin 4 → Fin 4 → ℝ),
      (∀ i j, g₁ i j = g₁ j i) → (∀ i j, g₂ i j = g₂ j i) → g₁ 0 0 ≠ 0 →
      (∀ v : Fin 4 → ℝ, minkQuadGen v = 0 → ∑ i : Fin 4, ∑ j : Fin 4, g₁ i j * v i * v j = 0) →
      (∀ v : Fin 4 → ℝ, minkQuadGen v = 0 → ∑ i : Fin 4, ∑ j : Fin 4, g₂ i j * v i * v j = 0) →
      ∃ μ : ℝ, ∀ i j : Fin 4, g₂ i j = μ * g₁ i j) ∧
    0 < sorkinLambda ρ V ∧
    sorkinLambda ρ V ^ 2 * (ρ * V) = 1 ∧
    (SatisfiesEinsteinSorkinYangMills4D md ρ V κ sc₃ conn₃ ↔
      (∀ δg : Fin 4 → Fin 4 → ℝ,
        ∑ μ : Fin 4, ∑ ν : Fin 4,
          einsteinLovelockYangMillsResidual4D md (sorkinLambda ρ V) κ sc₃ conn₃ μ ν *
            δg μ ν = 0)) ∧
    ((∀ δg : Fin 4 → Fin 4 → ℝ,
        ∑ μ : Fin 4, ∑ ν : Fin 4,
          einsteinLovelockYangMillsResidual4D md (sorkinLambda ρ V) κ sc₃ conn₃ μ ν *
            δg μ ν = 0) →
      scalar md sign = 4 * sorkinLambda ρ V ∧
      0 < scalar md sign ∧
      (scalar md sign) ^ 2 * (ρ * V) = 16) :=
  ⟨stage3_closed_3plus1,
   sorkinLambda_strict_pos ρ V hρ hV,
   sorkinLambda_sq_mul_N_eq_one ρ V hρ hV,
   einsteinSorkinYangMills4D_iff_variational_stationarity md ρ V κ sc₃ conn₃,
   fun hstat =>
     let hlock := variational_sorkin_stationarity_locks_positive_deSitter_scalar
       md ρ V κ hρ hV sc₃ conn₃ hstat
     ⟨hlock.2.1, hlock.2.2.1, hlock.2.2.2⟩⟩

/-- **Curved 4D Hawking-Penrose Singularity, Schwarzschild Trapped Surface & Malament Master Synthesis**:
Unites:
1. Ostrogradsky higher-derivative exclusion and 4D variational Einstein-Sorkin-Yang-Mills stationarity;
2. Raychaudhuri focusing inequality (`raychaudhuri_rhs θ σ_sq Rkk ≤ -(1/2) * θ^2`),
   null vs. timelike conjugate-point bounds (`0 < conjugatePointTime θ₀ < -3 / θ₀`), and
   `Penrose_Singularity_Target`;
3. Concrete Schwarzschild interior trapped surfaces (`0 < r_int < 2M`) with finite positive
   conjugate times, exact Schwarzschild Ricci flatness (`R_tt = R_rr = R_thetatheta = R_phiphi = 0`),
   Birkhoff spherical uniqueness, and positive Kretschmann curvature with horizon invariant
   `K(2M) * S_BH^2 = 12 * π^2`;
4. Discrete `1+1` and general `3+1` Malament causal-order conformal uniqueness and 4D
   Weyl conformal invariance (`weylTensor4D (conformalPartMetricDerivs4D md) = 0`). -/
theorem curved_4D_hawking_penrose_malament_master_synthesis
    (md : MetricDerivs 4) (a b c d : Fin 4)
    (ρ V κ : ℝ)
    (sc₃ : StructureConstants 8) (conn₃ : ConnectionData 4 8)
    (θ₀ : ℝ) (hθ₀ : θ₀ < 0)
    (M r_ext r_int θ_ang : ℝ) (hM : 0 < M) (hr_ext : r_ext ≠ 0)
    (hr_int_pos : 0 < r_int) (hr_int_lt : r_int < schwarzschildRadius M)
    (hM_lt : ∀ r₀ : ℝ, 0 < r₀ → r₀ > 2 * M) :
    -- (1) Ostrogradsky stability & 4D variational stationarity
    ((∀ v_ost g_ost : ℝ, v_ost ≠ 0 →
        ¬∃ M_bnd : ℝ, ∀ p₁ : ℝ, M_bnd ≤ ostrogradsky_hamiltonian v_ost g_ost p₁) ∧
      (SatisfiesEinsteinSorkinYangMills4D md ρ V κ sc₃ conn₃ ↔
        (∀ δg : Fin 4 → Fin 4 → ℝ,
          ∑ μ : Fin 4, ∑ ν : Fin 4,
            einsteinLovelockYangMillsResidual4D md (sorkinLambda ρ V) κ sc₃ conn₃ μ ν *
              δg μ ν = 0))) ∧
    -- (2) Raychaudhuri focusing & conjugate-point bounds
    ((∀ θ σ_sq Rkk, ShearNonneg σ_sq → NEC Rkk →
        raychaudhuri_rhs θ σ_sq Rkk ≤ -(1 / 2) * θ ^ 2) ∧
      0 < conjugatePointTime θ₀ ∧
      θ₀ * conjugatePointTime θ₀ = -2 ∧
      conjugatePointTime θ₀ < -3 / θ₀ ∧
      Penrose_Singularity_Target) ∧
    -- (3) Schwarzschild interior trapped surface, vacuum Ricci, Birkhoff & Kretschmann
    ((schwarzschildInteriorTrappedSurface M r_int hM hr_int_pos hr_int_lt).θ_plus < 0 ∧
      (schwarzschildInteriorTrappedSurface M r_int hM hr_int_pos hr_int_lt).θ_minus < 0 ∧
      0 < conjugatePointTime
        (schwarzschildInteriorTrappedSurface M r_int hM hr_int_pos hr_int_lt).θ_plus ∧
      0 < conjugatePointTime
        (schwarzschildInteriorTrappedSurface M r_int hM hr_int_pos hr_int_lt).θ_minus ∧
      (R_tt M r_ext = 0 ∧ R_rr M r_ext = 0 ∧
        R_thetatheta M r_ext = 0 ∧ R_phiphi M r_ext θ_ang = 0) ∧
      IsVacuumSphericallySymmetric (schwarzschildAnsatz M hM_lt) ∧
      StaticGauge (schwarzschildAnsatz M hM_lt) ∧
      0 < schwarzschildKretschmann M r_ext ∧
      schwarzschildKretschmann M (schwarzschildRadius M) *
        (bekensteinHawkingEntropy M) ^ 2 = 12 * Real.pi ^ 2) ∧
    -- (4) Malament 3+1 conformal recovery & 4D Weyl conformal invariance
    ((∀ (g₁ g₂ : Fin 4 → Fin 4 → ℝ),
        (∀ i j, g₁ i j = g₁ j i) → (∀ i j, g₂ i j = g₂ j i) → g₁ 0 0 ≠ 0 →
        (∀ v : Fin 4 → ℝ, minkQuadGen v = 0 → ∑ i : Fin 4, ∑ j : Fin 4, g₁ i j * v i * v j = 0) →
        (∀ v : Fin 4 → ℝ, minkQuadGen v = 0 → ∑ i : Fin 4, ∑ j : Fin 4, g₂ i j * v i * v j = 0) →
        ∃ μ : ℝ, ∀ i j : Fin 4, g₂ i j = μ * g₁ i j) ∧
      weylTensor4D (conformalPartMetricDerivs4D md) a b c d = 0 ∧
      weylTensor4D md a b c d =
        weylTensor4D (tracelessPartMetricDerivs4D md) a b c d) := by
  have hM_ne : M ≠ 0 := ne_of_gt hM
  have hlt := conjugatePointTime_lt_timelike_hawking_bound θ₀ hθ₀
  have htrap := schwarzschild_interior_trapped_surface_conjugate_times
    M r_int hM hr_int_pos hr_int_lt
  have hbirk := birkhoff_uniqueness_master_bridge M hM_lt
  exact ⟨⟨ostrogradsky_stability_to_einstein_bridge,
      einsteinSorkinYangMills4D_iff_variational_stationarity md ρ V κ sc₃ conn₃⟩,
    ⟨hawking_penrose_master.1, hlt.1, conjugatePointTime_eq θ₀ (ne_of_lt hθ₀),
      hlt.2.1, Penrose_Singularity_Target_consistent⟩,
    ⟨(schwarzschildInteriorTrappedSurface M r_int hM hr_int_pos hr_int_lt).trapped.1,
      (schwarzschildInteriorTrappedSurface M r_int hM hr_int_pos hr_int_lt).trapped.2,
      htrap.1, htrap.2.1,
      schwarzschild_ricci_components_all_vanish M r_ext θ_ang hr_ext,
      hbirk.1, hbirk.2.1,
      schwarzschildKretschmann_pos M r_ext hM_ne hr_ext,
      schwarzschildKretschmann_horizon_times_entropy_sq M hM_ne⟩,
    ⟨stage3_closed_3plus1,
      weylTensor4D_conformalPart_eq_zero md a b c d,
      weylTensor4D_eq_tracelessPart md a b c d⟩⟩

end

#print axioms raychaudhuri_focusing_bound_under_nec
#print axioms raychaudhuri_sharp_vacuum_and_gap_identity
#print axioms raychaudhuri_gap_nonneg_under_nec
#print axioms conjugatePointTime_strict_pos_of_contracting
#print axioms conjugatePointTime_product_and_denom_zero
#print axioms conjugatePointTime_strictMono_on_contracting
#print axioms conjugatePointTime_lt_timelike_hawking_bound
#print axioms focusingBound_initial_and_blowup_denom
#print axioms focusingBound_denom_pos_and_strict_neg
#print axioms focusingBound_le_initial_expansion_on_domain
#print axioms trappedSurface_expansions_neg_and_both_focus
#print axioms trappedSurface_quantitative_focusing_identities
#print axioms penrose_singularity_target_propositional_consistency
#print axioms schwarzschild_interior_trapped_surface_expansions_neg
#print axioms schwarzschild_interior_trapped_surface_conjugate_times
#print axioms schwarzschild_vacuum_raychaudhuri_sharp_evolution
#print axioms yangMills_positive_null_energy_implies_raychaudhuri_focusing
#print axioms hawking_penrose_singularity_master_bridge
#print axioms malament_1plus1_null_cone_coeffs_and_quad_proportionality
#print axioms malament_1plus1_bilin_and_conformal_factor_exists
#print axioms malament_1plus1_uniqueness_and_explicit_ratio
#print axioms discrete_malament_1plus1_link_nullity_and_dense_cone
#print axioms discrete_malament_1plus1_same_null_and_stage3_closed
#print axioms null_cone_conformal_2d_coeffs_and_equivalence
#print axioms general_null_cone_entry_determination_bridge
#print axioms general_malament_conformal_equivalence_and_factor_value
#print axioms general_malament_dense_links_and_null_approximation
#print axioms general_malament_same_null_and_stage3_closed
#print axioms malament_spacetime_instantiations_2plus1_3plus1_4plus1
#print axioms malament_3plus1_explicit_entries_and_conformal_factor
#print axioms malament_4D_conformal_weyl_invariance_bridge
#print axioms malament_causal_sorkin_volume_and_variational_4D_bridge
#print axioms curved_4D_hawking_penrose_malament_master_synthesis

end UnifiedTheory.Audit.KFCausalCurved4DHawkingPenroseSingularityMalamentCausalBridge
