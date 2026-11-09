/- Quantum Foundations (Wigner, Gleason, Bell, Tsirelson) and Clock-Floor
Higher-Power Second-Order Yosida Graph Convergence Bridge:
1. Establishes the Wigner symmetry easy direction in arbitrary finite dimension n:
   ray inner products, rescaling invariance of transition probabilities, and
   bijective transition-probability-preserving ray actions induced by both
   unitary and antiunitary operators.
2. Establishes the Gleason easy direction on projection lattices: every complex
   density matrix induces an additive, normalized, non-negative Born projection
   measure via the real part of the matrix trace.
3. Establishes the Bell theorem and Tsirelson bound trichotomy: SU(2) spin
   rotations, uniqueness of the antisymmetric singlet state, Born-rule singlet
   correlation -cos(θa - θb), deterministic CHSH bound |S| ≤ 2, quantum violation
   S² = 8 > 4, universal trigonometric Tsirelson bound |S| ≤ 2√2, and exact
   saturation at optimal measurement angles.
4. Synthesizes Wigner, Gleason, Bell, and Tsirelson quantum foundations with
   the clock-floor SO(2) Born-rule unitary evolution conservation, the
   (alpha_unification, gamma_4) two-scale resolvent identities, and the
   second-order Yosida graph convergence of the squared time-dependent
   Hamiltonian H(t)². -/
import UnifiedTheory.Audit.KFCausalClockFloorHigherPowerSecondOrderGraphConvergence
import UnifiedTheory.Audit.KFCausalClockFloorSMFineStructureBornRuleResolventBridge
import UnifiedTheory.LayerB.WignerTheorem
import UnifiedTheory.LayerB.GleasonTheorem
import UnifiedTheory.LayerB.BellTheorem
import UnifiedTheory.LayerB.TsirelsonBound

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorQuantumFoundationsWignerGleasonBellTsirelsonBridge
noncomputable section
open scoped Topology
open Matrix
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open UnifiedTheory.LayerA.FineStructureFromGap (alpha_unification gamma_4)
open UnifiedTheory.LayerA.BornRuleUnique (QuadForm normSqForm)
open UnifiedTheory.LayerB.RobertsonSchrodinger (ComplexDensityMatrix)
open UnifiedTheory.LayerB.WignerTheorem
  (Ray cdot normSq2 normSq2_nonneg normSq2_pos
   transitionProb transitionProb_smul_left
   IsWignerSymmetry cdot_unitary_invariant normSq2_unitary_invariant
   unitaryActionRay unitaryActionRay_bijective unitaryActionRay_preserves_transitionProb
   unitary_induces_wigner conjVec
   antiunitaryActionRay antiunitaryActionRay_bijective
   antiunitaryActionRay_preserves_transitionProb
   antiunitary_induces_wigner wigner_easy_direction_master)
open UnifiedTheory.LayerB.GleasonTheorem
  (IsProjection ProjectionMeasure bornMeasure
   bornMeasure_additive bornMeasure_smul bornMeasure_normalized
   bornMeasure_nonneg bornMeasure_is_projectionMeasure gleason_master)
open UnifiedTheory.LayerB.BellTheorem
  (su2Rotation su2Rotation_det_one spinState spinState_zero spinState_one
   singletState singlet_antisymmetric antisymmetric_unique
   P_upup P_updown P_downup P_downdown
   P_upup_is_sin_sq P_updown_is_cos_sq P_updown_eq_downup P_upup_eq_downdown
   correlation_from_born_rule chshValue tsirelson_value bell_violation
   violation_factor chshDet classical_chsh_bound
   bell_theorem_complete bell_from_derived_gauge)
open UnifiedTheory.LayerB.TsirelsonBound
  (abs_cos_add_abs_sin_le_sqrt_two tsirelsonChshSinglet
   tsirelsonChshSinglet_factored tsirelson_bound
   singlet_saturates_tsirelson singlet_abs_eq_two_sqrt_two
   singlet_value_eq_chshValue tsirelson_master_theorem)
open KFCausalClockFloorPotentialClockApproximation (cutoff)
open KFCausalClockFloorSecondPowerOperatorCores
  (secondPowerDomain secondPowerGraph)
open KFCausalClockFloorHigherPowerYosidaGraphConvergence
  (iteratedIdentityPower)
open KFCausalClockFloorHigherPowerSecondOrderGraphConvergence
  (hamiltonian_iteratedIdentityPower_secondPower_comm_and_bounds
   hamiltonian_iteratedIdentityPower_thirdPower_rate_bounds
   hamiltonian_iteratedIdentityPower_three_tier_tendsto_and_twoTime_diff)
open KFCausalClockFloorSMElectroweakHiggsPotentialBridge
  (evolutionFamily)
open KFCausalClockFloorSMFineStructureBornRuleResolventBridge
  (born_hilbert_eval_conserved_under_evolution
   born_normalized_hilbert_conserved_under_evolution
   hamiltonian_resolvent_alpha_sub_gamma_eq
   hamiltonian_resolvent_alpha_gamma_comm)

/-! ### 1. Wigner's Theorem: Ray Space, Rescaling Invariance, Unitary & Antiunitary Symmetries -/

theorem wigner_normSq2_nonneg {n : ℕ} (ψ : Fin n → ℂ) :
    0 ≤ normSq2 ψ :=
  normSq2_nonneg ψ

theorem wigner_normSq2_pos {n : ℕ} {ψ : Fin n → ℂ} (hψ : ψ ≠ 0) :
    0 < normSq2 ψ :=
  normSq2_pos hψ

theorem wigner_transitionProb_smul_left {n : ℕ} (c : ℂ) (hc : c ≠ 0)
    (ψ φ : Ray n) (hcψ : (fun i => c * ψ.val i) ≠ 0) :
    transitionProb ⟨fun i => c * ψ.val i, hcψ⟩ φ = transitionProb ψ φ :=
  transitionProb_smul_left c hc ψ φ hcψ

theorem wigner_unitary_preserves_cdot_and_normSq2
    {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (ψ φ : Fin n → ℂ) :
    cdot (U *ᵥ ψ) (U *ᵥ φ) = cdot ψ φ ∧
    normSq2 (U *ᵥ ψ) = normSq2 ψ :=
  ⟨cdot_unitary_invariant hU ψ φ, normSq2_unitary_invariant hU ψ⟩

theorem wigner_unitary_action_ray_bijective_and_preserves
    {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Function.Bijective (unitaryActionRay hU) ∧
    ∀ ψ φ : Ray n,
      transitionProb (unitaryActionRay hU ψ) (unitaryActionRay hU φ) =
        transitionProb ψ φ :=
  ⟨unitaryActionRay_bijective hU, unitaryActionRay_preserves_transitionProb hU⟩

theorem wigner_unitary_induces_symmetry
    {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ T : Ray n → Ray n, IsWignerSymmetry T ∧
      ∀ ψ : Ray n, (T ψ).val = U *ᵥ ψ.val :=
  unitary_induces_wigner U hU

theorem wigner_antiunitary_action_ray_bijective_and_preserves
    {n : ℕ} {V : Matrix (Fin n) (Fin n) ℂ}
    (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Function.Bijective (antiunitaryActionRay hV) ∧
    ∀ ψ φ : Ray n,
      transitionProb (antiunitaryActionRay hV ψ) (antiunitaryActionRay hV φ) =
        transitionProb ψ φ :=
  ⟨antiunitaryActionRay_bijective hV,
   antiunitaryActionRay_preserves_transitionProb hV⟩

theorem wigner_antiunitary_induces_symmetry
    {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ T : Ray n → Ray n, IsWignerSymmetry T ∧
      ∀ ψ : Ray n, (T ψ).val = V *ᵥ (conjVec ψ.val) :=
  antiunitary_induces_wigner V hV

theorem wigner_easy_direction_complete (n : ℕ) :
    (∀ (U : Matrix (Fin n) (Fin n) ℂ),
        U ∈ Matrix.unitaryGroup (Fin n) ℂ →
        ∃ T : Ray n → Ray n, IsWignerSymmetry T ∧
          ∀ ψ : Ray n, (T ψ).val = U *ᵥ ψ.val) ∧
    (∀ (V : Matrix (Fin n) (Fin n) ℂ),
        V ∈ Matrix.unitaryGroup (Fin n) ℂ →
        ∃ T : Ray n → Ray n, IsWignerSymmetry T ∧
          ∀ ψ : Ray n, (T ψ).val = V *ᵥ (conjVec ψ.val)) :=
  wigner_easy_direction_master n

/-! ### 2. Gleason's Theorem: Projection Lattice Measures and Born Trace Rule -/

theorem gleason_bornMeasure_additive
    {n : ℕ} (ρ P Q : Matrix (Fin n) (Fin n) ℂ) :
    bornMeasure ρ (P + Q) = bornMeasure ρ P + bornMeasure ρ Q :=
  bornMeasure_additive ρ P Q

theorem gleason_bornMeasure_smul
    {n : ℕ} (c : ℝ) (ρ P : Matrix (Fin n) (Fin n) ℂ) :
    bornMeasure ρ ((c : ℂ) • P) = c * bornMeasure ρ P :=
  bornMeasure_smul c ρ P

theorem gleason_bornMeasure_normalized
    {n : ℕ} (ρ : ComplexDensityMatrix n) :
    bornMeasure ρ.M 1 = 1 :=
  bornMeasure_normalized ρ

theorem gleason_bornMeasure_nonneg
    {n : ℕ} (ρ : ComplexDensityMatrix n)
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsProjection P) :
    0 ≤ bornMeasure ρ.M P :=
  bornMeasure_nonneg ρ P hP

theorem gleason_bornMeasure_projectionMeasure_props
    {n : ℕ} (ρ : ComplexDensityMatrix n) :
    (bornMeasure_is_projectionMeasure ρ).μ 1 = 1 ∧
    (∀ P, IsProjection P → 0 ≤ (bornMeasure_is_projectionMeasure ρ).μ P) ∧
    (∀ P Q,
      (bornMeasure_is_projectionMeasure ρ).μ (P + Q) =
        (bornMeasure_is_projectionMeasure ρ).μ P +
          (bornMeasure_is_projectionMeasure ρ).μ Q) :=
  ⟨bornMeasure_normalized ρ,
   bornMeasure_nonneg ρ,
   fun P Q => bornMeasure_additive ρ.M P Q⟩

theorem gleason_easy_direction_master (n : ℕ) :
    (∀ (ρ : ComplexDensityMatrix n) (P Q : Matrix (Fin n) (Fin n) ℂ),
      bornMeasure ρ.M (P + Q) = bornMeasure ρ.M P + bornMeasure ρ.M Q) ∧
    (∀ (ρ : ComplexDensityMatrix n), bornMeasure ρ.M 1 = 1) ∧
    (∀ (ρ : ComplexDensityMatrix n) (P : Matrix (Fin n) (Fin n) ℂ),
      IsProjection P → 0 ≤ bornMeasure ρ.M P) :=
  gleason_master

/-! ### 3. Bell's Theorem: SU(2) Spin States, Singlet Uniqueness, and CHSH Violation -/

theorem bell_su2_rotation_det_and_spin_components (θ : ℝ) :
    su2Rotation θ 0 0 * su2Rotation θ 1 1 -
      su2Rotation θ 0 1 * su2Rotation θ 1 0 = 1 ∧
    spinState θ 0 = Real.cos (θ / 2) ∧
    spinState θ 1 = Real.sin (θ / 2) :=
  ⟨su2Rotation_det_one θ, spinState_zero θ, spinState_one θ⟩

theorem bell_singlet_antisymmetric_and_unique :
    (∀ i j : Fin 2, singletState j i = -singletState i j) ∧
    (∀ ψ : Fin 2 → Fin 2 → ℝ,
      (∀ i j, ψ j i = -ψ i j) →
      ∀ i j, ψ i j = ψ 0 1 * (singletState i j * Real.sqrt 2)) :=
  ⟨singlet_antisymmetric, antisymmetric_unique⟩

theorem bell_singlet_probabilities_trig (θa θb : ℝ) :
    P_upup θa θb = Real.sin ((θa - θb) / 2) ^ 2 / 2 ∧
    P_updown θa θb = Real.cos ((θa - θb) / 2) ^ 2 / 2 ∧
    P_updown θa θb = P_downup θa θb ∧
    P_upup θa θb = P_downdown θa θb :=
  ⟨P_upup_is_sin_sq θa θb,
   P_updown_is_cos_sq θa θb,
   P_updown_eq_downup θa θb,
   P_upup_eq_downdown θa θb⟩

theorem bell_correlation_from_born_rule (θa θb : ℝ) :
    P_upup θa θb - P_updown θa θb - P_downup θa θb + P_downdown θa θb =
      -Real.cos (θa - θb) :=
  correlation_from_born_rule θa θb

theorem bell_chsh_value_and_tsirelson_sq :
    chshValue ^ 2 = 8 ∧
    chshValue ^ 2 > 4 ∧
    chshValue ^ 2 = 2 * 2 ^ 2 :=
  ⟨tsirelson_value, bell_violation, violation_factor⟩

theorem bell_classical_chsh_bound_int (a a' b b' : Int)
    (ha : a = 1 ∨ a = -1) (ha' : a' = 1 ∨ a' = -1)
    (hb : b = 1 ∨ b = -1) (hb' : b' = 1 ∨ b' = -1) :
    -2 ≤ chshDet a a' b b' ∧ chshDet a a' b b' ≤ 2 :=
  classical_chsh_bound a a' b b' ha ha' hb hb'

theorem bell_theorem_complete_bridge :
    (∀ a a' b b' : Int,
      (a = 1 ∨ a = -1) → (a' = 1 ∨ a' = -1) →
      (b = 1 ∨ b = -1) → (b' = 1 ∨ b' = -1) →
      -2 ≤ chshDet a a' b b' ∧ chshDet a a' b b' ≤ 2) ∧
    chshValue ^ 2 > 4 :=
  bell_theorem_complete

theorem bell_from_derived_weak_gauge_dimension :
    UnifiedTheory.LayerA.GaugeGroupDerived.freeParameters 2 = 1 ∧
    chshValue ^ 2 > 4 ∧
    (∀ a a' b b' : Int,
      (a = 1 ∨ a = -1) → (a' = 1 ∨ a' = -1) →
      (b = 1 ∨ b = -1) → (b' = 1 ∨ b' = -1) →
      -2 ≤ chshDet a a' b b' ∧ chshDet a a' b b' ≤ 2) :=
  bell_from_derived_gauge

/-! ### 4. Tsirelson's Bound: Trigonometric Cauchy–Schwarz, Factorization, and Saturation -/

theorem tsirelson_trig_cauchy_schwarz (β : ℝ) :
    |Real.cos β| + |Real.sin β| ≤ Real.sqrt 2 :=
  abs_cos_add_abs_sin_le_sqrt_two β

theorem tsirelson_chsh_singlet_factored (θa θa' θb θb' : ℝ) :
    tsirelsonChshSinglet θa θa' θb θb' =
      -(2 * Real.cos (θa - (θb + θb') / 2) * Real.cos ((θb' - θb) / 2)) +
        2 * Real.sin (θa' - (θb + θb') / 2) * Real.sin ((θb' - θb) / 2) :=
  tsirelsonChshSinglet_factored θa θa' θb θb'

theorem tsirelson_universal_singlet_bound (θa θa' θb θb' : ℝ) :
    |tsirelsonChshSinglet θa θa' θb θb'| ≤ 2 * Real.sqrt 2 :=
  tsirelson_bound θa θa' θb θb'

theorem tsirelson_optimal_saturation_and_chsh_eq :
    tsirelsonChshSinglet 0 (Real.pi / 2) (Real.pi / 4) (-(Real.pi / 4)) =
      -(2 * Real.sqrt 2) ∧
    |tsirelsonChshSinglet 0 (Real.pi / 2) (Real.pi / 4) (-(Real.pi / 4))| =
      2 * Real.sqrt 2 ∧
    tsirelsonChshSinglet 0 (Real.pi / 2) (Real.pi / 4) (-(Real.pi / 4)) =
      chshValue :=
  ⟨singlet_saturates_tsirelson,
   singlet_abs_eq_two_sqrt_two,
   singlet_value_eq_chshValue⟩

theorem tsirelson_bell_trichotomy_master :
    (∀ f g : Bool → ℝ, (∀ x, |f x| ≤ 1) → (∀ y, |g y| ≤ 1) →
        |UnifiedTheory.LayerB.SeparableCHSH.chshExpr (fun x y => f x * g y)| ≤ 2) ∧
    (∀ θa θa' θb θb' : ℝ,
        |tsirelsonChshSinglet θa θa' θb θb'| ≤ 2 * Real.sqrt 2) ∧
    |tsirelsonChshSinglet 0 (Real.pi / 2) (Real.pi / 4) (-(Real.pi / 4))| =
      2 * Real.sqrt 2 ∧
    tsirelsonChshSinglet 0 (Real.pi / 2) (Real.pi / 4) (-(Real.pi / 4)) =
      chshValue :=
  tsirelson_master_theorem

/-! ### 5. Synthesis with Clock-Floor Born Rule Evolution and Second-Order Graph Convergence -/

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k t : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k

theorem quantum_foundations_born_unitary_evolution_conservation
    (f : QuadForm) (hinv : f.IsSO2Invariant) (s : ℝ) (ψ : Hilbert) :
    f.eval ‖evolutionFamily ε hε h hh hb m g k s t ψ‖ 0 = f.a * ‖ψ‖ ^ 2 ∧
    normSqForm.eval ‖evolutionFamily ε hε h hh hb m g k s t ψ‖ 0 = ‖ψ‖ ^ 2 :=
  ⟨born_hilbert_eval_conserved_under_evolution ε hε h hh hb m g k t f hinv s ψ,
   born_normalized_hilbert_conserved_under_evolution ε hε h hh hb m g k t s ψ⟩

theorem quantum_foundations_alpha_gamma_resolvent_identity (f : Hilbert) :
    RH t alpha_unification f - RH t gamma_4 f =
      ((gamma_4 - alpha_unification : ℝ) : ℂ) •
        RH t alpha_unification (RH t gamma_4 f) ∧
    RH t alpha_unification (RH t gamma_4 f) =
      RH t gamma_4 (RH t alpha_unification f) :=
  ⟨hamiltonian_resolvent_alpha_sub_gamma_eq ε hε h hh hb m g k t f,
   hamiltonian_resolvent_alpha_gamma_comm ε hε h hh hb m g k t f⟩

theorem quantum_foundations_second_order_yosida_hamiltonian_graph_convergence
    (s a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert)
    (xH : (H t).domain) (hHx : H t xH ∈ (H t).domain) :
    iteratedIdentityPower (RH t a) a r (xH : Hilbert) ∈ secondPowerDomain (H t) ∧
    Filter.Tendsto (fun j : ℕ =>
      (iteratedIdentityPower (RH t (cutoff j)) (cutoff j) r (xH : Hilbert),
        (iteratedIdentityPower (RH t (cutoff j)) (cutoff j) r (H t xH),
          iteratedIdentityPower (RH t (cutoff j)) (cutoff j) r (H t ⟨H t xH, hHx⟩))))
      Filter.atTop (nhds ((xH : Hilbert), (H t xH, H t ⟨H t xH, hHx⟩))) :=
  ⟨(hamiltonian_iteratedIdentityPower_secondPower_comm_and_bounds
      ε hε h hh hb m g k t a ha r xH hHx).1,
   (hamiltonian_iteratedIdentityPower_three_tier_tendsto_and_twoTime_diff
      ε hε h hh hb m g k s t a ha r f xH hHx).2.1⟩

theorem quantum_foundations_iterated_alpha_gamma_second_order_yosida_convergence
    (a : ℝ) (ha : 0 < a) (r : ℕ)
    (xH : (H t).domain) (hHx : H t xH ∈ (H t).domain)
    (hHHx : H t ⟨H t xH, hHx⟩ ∈ (H t).domain) :
    ‖iteratedIdentityPower (RH t a) a r (xH : Hilbert) - (xH : Hilbert)‖ ≤
      (r : ℝ) * a⁻¹ * ‖H t xH‖ ∧
    ‖iteratedIdentityPower (RH t a) a r (H t xH) - H t xH‖ ≤
      (r : ℝ) * a⁻¹ * ‖H t ⟨H t xH, hHx⟩‖ ∧
    ‖iteratedIdentityPower (RH t a) a r (H t ⟨H t xH, hHx⟩) - H t ⟨H t xH, hHx⟩‖ ≤
      (r : ℝ) * a⁻¹ * ‖H t ⟨H t ⟨H t xH, hHx⟩, hHHx⟩‖ :=
  hamiltonian_iteratedIdentityPower_thirdPower_rate_bounds
    ε hε h hh hb m g k t a ha r xH hHx hHHx

theorem quantum_foundations_wigner_gleason_bell_tsirelson_clock_floor_master_bridge
    (n : ℕ) (s a : ℝ) (ha : 0 < a) (r : ℕ) (f : Hilbert)
    (xH : (H t).domain) (hHx : H t xH ∈ (H t).domain) :
    ((∀ (U : Matrix (Fin n) (Fin n) ℂ),
        U ∈ Matrix.unitaryGroup (Fin n) ℂ →
        ∃ T : Ray n → Ray n, IsWignerSymmetry T ∧
          ∀ ψ : Ray n, (T ψ).val = U *ᵥ ψ.val) ∧
     (∀ (V : Matrix (Fin n) (Fin n) ℂ),
        V ∈ Matrix.unitaryGroup (Fin n) ℂ →
        ∃ T : Ray n → Ray n, IsWignerSymmetry T ∧
          ∀ ψ : Ray n, (T ψ).val = V *ᵥ (conjVec ψ.val))) ∧
    ((∀ (ρ : ComplexDensityMatrix n) (P Q : Matrix (Fin n) (Fin n) ℂ),
        bornMeasure ρ.M (P + Q) = bornMeasure ρ.M P + bornMeasure ρ.M Q) ∧
     (∀ (ρ : ComplexDensityMatrix n), bornMeasure ρ.M 1 = 1) ∧
     (∀ (ρ : ComplexDensityMatrix n) (P : Matrix (Fin n) (Fin n) ℂ),
        IsProjection P → 0 ≤ bornMeasure ρ.M P)) ∧
    (chshValue ^ 2 = 8 ∧
     chshValue ^ 2 > 4 ∧
     (∀ θa θa' θb θb' : ℝ,
        |tsirelsonChshSinglet θa θa' θb θb'| ≤ 2 * Real.sqrt 2) ∧
     |tsirelsonChshSinglet 0 (Real.pi / 2) (Real.pi / 4) (-(Real.pi / 4))| =
        2 * Real.sqrt 2) ∧
    (normSqForm.eval ‖evolutionFamily ε hε h hh hb m g k s t f‖ 0 = ‖f‖ ^ 2 ∧
     iteratedIdentityPower (RH t a) a r (xH : Hilbert) ∈ secondPowerDomain (H t) ∧
     Filter.Tendsto (fun j : ℕ =>
       (iteratedIdentityPower (RH t (cutoff j)) (cutoff j) r (xH : Hilbert),
         (iteratedIdentityPower (RH t (cutoff j)) (cutoff j) r (H t xH),
           iteratedIdentityPower (RH t (cutoff j)) (cutoff j) r (H t ⟨H t xH, hHx⟩))))
       Filter.atTop (nhds ((xH : Hilbert), (H t xH, H t ⟨H t xH, hHx⟩)))) :=
  ⟨wigner_easy_direction_master n,
   gleason_master,
   ⟨tsirelson_value, bell_violation, tsirelson_bound, singlet_abs_eq_two_sqrt_two⟩,
   ⟨born_normalized_hilbert_conserved_under_evolution ε hε h hh hb m g k t s f,
    (quantum_foundations_second_order_yosida_hamiltonian_graph_convergence
      ε hε h hh hb m g k t s a ha r f xH hHx).1,
    (quantum_foundations_second_order_yosida_hamiltonian_graph_convergence
      ε hε h hh hb m g k t s a ha r f xH hHx).2⟩⟩

#print axioms wigner_normSq2_nonneg
#print axioms wigner_normSq2_pos
#print axioms wigner_transitionProb_smul_left
#print axioms wigner_unitary_preserves_cdot_and_normSq2
#print axioms wigner_unitary_action_ray_bijective_and_preserves
#print axioms wigner_unitary_induces_symmetry
#print axioms wigner_antiunitary_action_ray_bijective_and_preserves
#print axioms wigner_antiunitary_induces_symmetry
#print axioms wigner_easy_direction_complete
#print axioms gleason_bornMeasure_additive
#print axioms gleason_bornMeasure_smul
#print axioms gleason_bornMeasure_normalized
#print axioms gleason_bornMeasure_nonneg
#print axioms gleason_bornMeasure_projectionMeasure_props
#print axioms gleason_easy_direction_master
#print axioms bell_su2_rotation_det_and_spin_components
#print axioms bell_singlet_antisymmetric_and_unique
#print axioms bell_singlet_probabilities_trig
#print axioms bell_correlation_from_born_rule
#print axioms bell_chsh_value_and_tsirelson_sq
#print axioms bell_classical_chsh_bound_int
#print axioms bell_theorem_complete_bridge
#print axioms bell_from_derived_weak_gauge_dimension
#print axioms tsirelson_trig_cauchy_schwarz
#print axioms tsirelson_chsh_singlet_factored
#print axioms tsirelson_universal_singlet_bound
#print axioms tsirelson_optimal_saturation_and_chsh_eq
#print axioms tsirelson_bell_trichotomy_master
#print axioms quantum_foundations_born_unitary_evolution_conservation
#print axioms quantum_foundations_alpha_gamma_resolvent_identity
#print axioms quantum_foundations_second_order_yosida_hamiltonian_graph_convergence
#print axioms quantum_foundations_iterated_alpha_gamma_second_order_yosida_convergence
#print axioms quantum_foundations_wigner_gleason_bell_tsirelson_clock_floor_master_bridge
end
end UnifiedTheory.Audit.KFCausalClockFloorQuantumFoundationsWignerGleasonBellTsirelsonBridge
