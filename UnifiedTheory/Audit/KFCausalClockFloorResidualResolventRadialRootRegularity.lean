/- Unconditional radial square-root and full-energy form regularity of the
residual Hamiltonian resolvent R_{S(t)}(a) = (S(t) + a)⁻¹ for all real couplings
and physical times:
1. Constructs the bounded radial Yosida square-root multiplier
   yosidaRootAction_N = M_N^{1/2} on Hilbert, proves its self-adjointness,
   square identity ⟨M_N^{1/2} u, M_N^{1/2} v⟩ = ⟨u, M_N v⟩, domination by
   K_root on Dom(K_root), and Fatou uniform-bound criterion for membership in
   Dom(K_root).
2. Establishes the unconditional radial Yosida form lower bound on the residual
   form and on the entire residual operator domain Dom(S(t)):
   -(h²/ε²) ‖x‖² ≤ Re ⟨S(t) x, M_N x⟩.
3. Deduces that for every f ∈ Dom(K_root), a > 0, and s, t ∈ ℝ, the residual
   resolvent state R_{S(t)}(a) f lies in Dom(K_root), Dom(T_grow), and the full
   completed energy form domain Dom(E_avg(s)) at every time s, with explicit
   radial square-root and multi-channel form-energy bounds:
   ‖K_root (R_{S(t)}(a) f)‖ ≤ ‖K_root f‖ / a + (|h| / ε) ‖R_{S(t)}(a) f‖ / √a. -/
import UnifiedTheory.Audit.KFCausalClockFloorHamiltonianResolventFormBounds
import UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumTwoTimeOperatorDomain
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaHamiltonianPairing

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorResidualResolventRadialRootRegularity
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint JointHilbert)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalFiniteJointGraph (Output)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalPhysicalEnergyFactors (energyWeight)
open KFCausalPhysicalEnergyTransport (staticOutput)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorOrbitVacuumGraph (physicalOrbit physicalOrbit_coe)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialYosidaSymbol
  (radial radial_nonnegative symbol symbol_continuous symbol_nonnegative
    symbol_le symbol_le_radial action action_coe)
open KFCausalClockFloorRadialYosidaDomain (symbol_tendsto)
open KFCausalClockFloorRadialYosidaOrderedTransport
  (shifted shifted_accretive shift_bound)
open KFCausalClockFloorRadialYosidaOutputAccretivity (action_accretive)
open KFCausalClockFloorRadialYosidaEnergy (factorOutput factorCorrection transformedOutput)
open KFCausalClockFloorRadialYosidaForm (outputAction extra)
open KFCausalClockFloorRadialYosidaHamiltonianPairing (output_static_lower)
open KFCausalClockFloorRadialResolventLeibniz
  (point_static_extra extraSection orbitExtra referenceOutputActionLp)
open KFCausalClockFloorRadialResolventResidual (yosida_graph)
open KFCausalClockFloorGrowingRadialMultiplierForm (rootSymbol rootOperator)
open KFCausalClockFloorRotatedAntiSymbol (chargedWeight_continuous)
open KFCausalUnitaryRealMultiplier (realPullback_domain realPullback_coe)
open KFCausalRealMultiplierSelfAdjoint (realPullback_norm_square)
open KFCausalAveragedEnergyGraph (l2_norm_square)
open KFCausalClockFloorUnconditionalOperatorFormEnergy
  (residual_mem_staticRoot_domain residual_mem_potentialForm_domain
    residual_mem_residualForm_domain)
open KFCausalClockFloorHamiltonianResolventFormBounds
  (residualResolventPoint residual_resolvent_mem_staticRoot_domain
    residual_resolvent_mem_potentialForm_domain
    residual_resolvent_mem_residualForm_domain
    residual_resolvent_two_channel_energy_le
    residual_resolvent_staticRoot_norm_le
    residual_resolvent_potentialForm_norm_le)

/-! ### 1. Bounded Radial Yosida Square-Root Multiplier and Fatou Root-Domain Criterion -/

private theorem rootSymbol_measurable (ε : ℝ) (hε : 0 < ε) (h : ℝ) :
    Measurable (rootSymbol ε h) :=
  (((chargedWeight_continuous ε hε h 0).add
    (chargedWeight_continuous ε hε h 1)).div_const 2).sqrt.measurable

def yosidaRootSymbol (ε h N : ℝ) (x : Joint 2 4) : ℝ :=
  Real.sqrt (symbol ε h N x)

theorem yosidaRootSymbol_nonnegative (ε h N : ℝ) (x : Joint 2 4) :
    0 ≤ yosidaRootSymbol ε h N x :=
  Real.sqrt_nonneg _

theorem yosidaRootSymbol_sq (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (x : Joint 2 4) :
    yosidaRootSymbol ε h N x ^ 2 = symbol ε h N x :=
  Real.sq_sqrt (symbol_nonnegative ε hε h N hN x)

theorem yosidaRootSymbol_le_sqrt (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (x : Joint 2 4) :
    yosidaRootSymbol ε h N x ≤ Real.sqrt N :=
  Real.sqrt_le_sqrt (symbol_le ε hε h N hN x)

theorem yosidaRootSymbol_le_rootSymbol (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (x : Joint 2 4) :
    yosidaRootSymbol ε h N x ≤ rootSymbol ε h x :=
  Real.sqrt_le_sqrt (symbol_le_radial ε hε h N hN x)

theorem yosidaRootSymbol_tendsto (ε : ℝ) (hε : 0 < ε) (h : ℝ) (x : Joint 2 4) :
    Tendsto (fun n : ℕ => yosidaRootSymbol ε h ((n : ℝ) + 1) x)
      atTop (𝓝 (rootSymbol ε h x)) :=
  (Real.continuous_sqrt.tendsto (radial ε h x)).comp (symbol_tendsto ε hε h x)

private theorem yosidaRootSymbol_measurable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N) :
    Measurable (fun x : Joint 2 4 => (yosidaRootSymbol ε h N x : ℂ)) :=
  (Complex.continuous_ofReal.comp
    (symbol_continuous ε hε h N hN).sqrt).measurable

private theorem complex_yosidaRootSymbol_bound (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (x : Joint 2 4) :
    ‖(yosidaRootSymbol ε h N x : ℂ)‖ ≤ Real.sqrt N := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (yosidaRootSymbol_nonnegative ε h N x)]
  exact yosidaRootSymbol_le_sqrt ε hε h N hN x

def yosidaRootAction (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N) :
    Hilbert →L[ℂ] Hilbert :=
  (chargeCoordinates.symm : JointHilbert 2 4 →L[ℂ] Hilbert).comp
    ((KFCausalBoundedLpMultiplier.operator (fun x => (yosidaRootSymbol ε h N x : ℂ))
      (yosidaRootSymbol_measurable ε hε h N hN) (Real.sqrt N) (Real.sqrt_nonneg N)
      (complex_yosidaRootSymbol_bound ε hε h N hN)).comp
        (chargeCoordinates : Hilbert →L[ℂ] JointHilbert 2 4))

private theorem yosidaRootAction_coordinates (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (f : Hilbert) :
    chargeCoordinates (yosidaRootAction ε hε h N hN f) =
      KFCausalBoundedLpMultiplier.operator (fun x => (yosidaRootSymbol ε h N x : ℂ))
        (yosidaRootSymbol_measurable ε hε h N hN) (Real.sqrt N) (Real.sqrt_nonneg N)
        (complex_yosidaRootSymbol_bound ε hε h N hN) (chargeCoordinates f) :=
  chargeCoordinates.apply_symm_apply _

theorem yosidaRootAction_coe (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (f : Hilbert) :
    chargeCoordinates (yosidaRootAction ε hε h N hN f) =ᵐ[volume]
      fun x => (yosidaRootSymbol ε h N x : ℂ) * (chargeCoordinates f) x := by
  rw [yosidaRootAction_coordinates]
  exact KFCausalBoundedLpMultiplier.operator_coe _ _ _ _ _ _

theorem yosidaRootAction_norm (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (f : Hilbert) :
    ‖yosidaRootAction ε hε h N hN f‖ ≤ Real.sqrt N * ‖f‖ := by
  rw [← chargeCoordinates.norm_map (yosidaRootAction ε hε h N hN f),
    yosidaRootAction_coordinates, ← chargeCoordinates.norm_map f]
  exact KFCausalBoundedLpMultiplier.operator_norm _ _ _ _ _ _

theorem yosidaRootAction_selfAdjoint_pairing (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (u v : Hilbert) :
    inner ℂ (yosidaRootAction ε hε h N hN u) v =
      inner ℂ u (yosidaRootAction ε hε h N hN v) := by
  rw [← chargeCoordinates.inner_map_map (yosidaRootAction ε hε h N hN u) v,
    ← chargeCoordinates.inner_map_map u (yosidaRootAction ε hε h N hN v),
    L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [yosidaRootAction_coe ε hε h N hN u,
    yosidaRootAction_coe ε hε h N hN v] with x hu hv
  rw [hu, hv]
  change inner ℂ ((yosidaRootSymbol ε h N x : ℂ) • (chargeCoordinates u) x)
      ((chargeCoordinates v) x) =
    inner ℂ ((chargeCoordinates u) x)
      ((yosidaRootSymbol ε h N x : ℂ) • (chargeCoordinates v) x)
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal]

theorem yosidaRootAction_sq_eq_yosida (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (f : Hilbert) :
    yosidaRootAction ε hε h N hN (yosidaRootAction ε hε h N hN f) =
      action ε hε h N hN f := by
  apply chargeCoordinates.injective
  apply Lp.ext
  filter_upwards [yosidaRootAction_coe ε hε h N hN (yosidaRootAction ε hε h N hN f),
    yosidaRootAction_coe ε hε h N hN f,
    action_coe ε hε h N hN f] with x h1 h2 h3
  rw [h1, h2, h3, ← mul_assoc, ← Complex.ofReal_mul, ← sq,
    yosidaRootSymbol_sq ε hε h N hN x]

theorem yosidaRootAction_sq_inner (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (u v : Hilbert) :
    inner ℂ (yosidaRootAction ε hε h N hN u) (yosidaRootAction ε hε h N hN v) =
      inner ℂ u (action ε hε h N hN v) :=
  (yosidaRootAction_selfAdjoint_pairing ε hε h N hN u
    (yosidaRootAction ε hε h N hN v)).trans
    (congrArg (inner ℂ u) (yosidaRootAction_sq_eq_yosida ε hε h N hN v))

theorem yosidaRootAction_norm_sq_eq_inner (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (u : Hilbert) :
    ‖yosidaRootAction ε hε h N hN u‖ ^ 2 =
      (inner ℂ u (action ε hε h N hN u)).re :=
  (inner_self_eq_norm_sq (𝕜 := ℂ) (yosidaRootAction ε hε h N hN u)).symm.trans
    (congrArg Complex.re (yosidaRootAction_sq_inner ε hε h N hN u u))

theorem yosidaRootAction_norm_le_rootOperator (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (f : Hilbert) (hf : f ∈ (rootOperator ε hε h).domain) :
    ‖yosidaRootAction ε hε h N hN f‖ ≤ ‖rootOperator ε hε h ⟨f, hf⟩‖ := by
  let y := chargeCoordinates (rootOperator ε hε h ⟨f, hf⟩)
  have hy : y =ᵐ[volume] fun x => (rootSymbol ε h x : ℂ) * (chargeCoordinates f) x :=
    realPullback_coe chargeCoordinates (rootSymbol ε h)
      (rootSymbol_measurable ε hε h) ⟨f, hf⟩
  have hle : ‖chargeCoordinates (yosidaRootAction ε hε h N hN f)‖ ≤ 1 * ‖y‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [yosidaRootAction_coe ε hε h N hN f, hy] with x h1 h2
    have hroot : 0 ≤ rootSymbol ε h x := Real.sqrt_nonneg _
    rw [h1, h2, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (yosidaRootSymbol_nonnegative ε h N x),
      abs_of_nonneg hroot, one_mul]
    exact mul_le_mul_of_nonneg_right
      (yosidaRootSymbol_le_rootSymbol ε hε h N hN x) (norm_nonneg _)
  rw [one_mul, chargeCoordinates.norm_map, chargeCoordinates.norm_map] at hle
  exact hle

private def rootDensity (ε h N : ℝ) (f : Hilbert) (x : Joint 2 4) : ℝ :=
  yosidaRootSymbol ε h N x ^ 2 * ‖(chargeCoordinates f) x‖ ^ 2

private theorem rootDensity_eq (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (f : Hilbert) :
    (fun x => ‖(chargeCoordinates (yosidaRootAction ε hε h N hN f)) x‖ ^ 2) =ᵐ[volume]
      rootDensity ε h N f := by
  filter_upwards [yosidaRootAction_coe ε hε h N hN f] with x hx
  rw [hx, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rfl

private theorem rootDensity_integrable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (f : Hilbert) :
    Integrable (rootDensity ε h N f) volume :=
  ((memLp_two_iff_integrable_sq_norm
    (Lp.aestronglyMeasurable (chargeCoordinates (yosidaRootAction ε hε h N hN f)))).mp
      (Lp.memLp _)).congr (rootDensity_eq ε hε h N hN f)

private theorem rootDensity_integral (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (f : Hilbert) :
    (∫ x, rootDensity ε h N f x) = ‖yosidaRootAction ε hε h N hN f‖ ^ 2 := by
  rw [← chargeCoordinates.norm_map (yosidaRootAction ε hε h N hN f), l2_norm_square]
  exact integral_congr_ae (rootDensity_eq ε hε h N hN f).symm

theorem root_domain_of_uniform_bound (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (f : Hilbert) (B : ℝ)
    (hB : ∀ n : ℕ, ‖yosidaRootAction ε hε h ((n : ℝ) + 1) (by positivity) f‖ ≤ B) :
    f ∈ (rootOperator ε hε h).domain := by
  have hi : Integrable (fun x => rootSymbol ε h x ^ 2 * ‖(chargeCoordinates f) x‖ ^ 2) volume := by
    apply KFCausalPureMomentumCutoffDomain.integrable_of_uniform_nonnegative_integrals
      (fun n => rootDensity ε h ((n : ℝ) + 1) f) _
      (fun n => rootDensity_integrable ε hε h _ (by positivity) f)
      (fun n x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (((rootSymbol_measurable ε hε h).pow_const 2).aestronglyMeasurable.mul
        ((Lp.aestronglyMeasurable (chargeCoordinates f)).norm.pow 2))
      (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (fun x => ((yosidaRootSymbol_tendsto ε hε h x).pow 2).mul_const _) (B ^ 2)
    intro n
    rw [rootDensity_integral ε hε h _ (by positivity) f]
    exact pow_le_pow_left₀ (norm_nonneg _) (hB n) 2
  apply (realPullback_domain chargeCoordinates (rootSymbol ε h)
    (rootSymbol_measurable ε hε h) f).mpr
  apply (memLp_two_iff_integrable_sq_norm
    ((Complex.continuous_ofReal.measurable.comp
      (rootSymbol_measurable ε hε h)).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable (chargeCoordinates f)))).mpr
  exact hi.congr (Eventually.of_forall (fun x => by
    change rootSymbol ε h x ^ 2 * ‖(chargeCoordinates f) x‖ ^ 2 =
      ‖(rootSymbol ε h x : ℂ) * (chargeCoordinates f) x‖ ^ 2
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]))

theorem root_norm_of_uniform_bound (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (f : Hilbert) (B : ℝ)
    (hB : ∀ n : ℕ, ‖yosidaRootAction ε hε h ((n : ℝ) + 1) (by positivity) f‖ ≤ B) :
    ‖rootOperator ε hε h ⟨f, root_domain_of_uniform_bound ε hε h f B hB⟩‖ ≤ B := by
  have hBn : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hi := (realPullback_domain chargeCoordinates (rootSymbol ε h)
    (rootSymbol_measurable ε hε h) f).mp
    (root_domain_of_uniform_bound ε hε h f B hB)
  have hi' := (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mp hi
  have hd : Integrable (fun x => rootSymbol ε h x ^ 2 * ‖(chargeCoordinates f) x‖ ^ 2) volume :=
    hi'.congr (Eventually.of_forall (fun x => by
      change ‖(rootSymbol ε h x : ℂ) * (chargeCoordinates f) x‖ ^ 2 =
        rootSymbol ε h x ^ 2 * ‖(chargeCoordinates f) x‖ ^ 2
      rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]))
  have ht : Tendsto (fun n : ℕ => ∫ x, rootDensity ε h ((n : ℝ) + 1) f x) atTop
      (𝓝 (∫ x, rootSymbol ε h x ^ 2 * ‖(chargeCoordinates f) x‖ ^ 2)) := by
    apply tendsto_integral_of_dominated_convergence _
      (fun n => (rootDensity_integrable ε hε h _ (by positivity) f).aestronglyMeasurable) hd
    · intro n
      filter_upwards [] with x
      change ‖yosidaRootSymbol ε h ((n : ℝ) + 1) x ^ 2 * ‖(chargeCoordinates f) x‖ ^ 2‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (yosidaRootSymbol_nonnegative ε h _ x)
          (yosidaRootSymbol_le_rootSymbol ε hε h _ (by positivity) x) 2) (sq_nonneg _)
    · exact Eventually.of_forall (fun x =>
        ((yosidaRootSymbol_tendsto ε hε h x).pow 2).mul_const _)
  have hb : (∫ x, rootSymbol ε h x ^ 2 * ‖(chargeCoordinates f) x‖ ^ 2) ≤ B ^ 2 := by
    apply le_of_tendsto ht
    filter_upwards [] with n
    rw [rootDensity_integral ε hε h _ (by positivity) f]
    exact pow_le_pow_left₀ (norm_nonneg _) (hB n) 2
  apply (sq_le_sq₀ (norm_nonneg _) hBn).mp
  exact (realPullback_norm_square chargeCoordinates (rootSymbol ε h)
    (rootSymbol_measurable ε hε h)
    ⟨f, root_domain_of_uniform_bound ε hε h f B hB⟩).le.trans hb

/-! ### 2. Unconditional Radial Yosida Lower Bound on Residual Form and Dom(S(t)) -/

private theorem output_eight_inner_split (z w : Output (Fin 8) Hilbert) :
    inner ℂ z w =
      inner ℂ (staticOutput z) (staticOutput w) +
        (inner ℂ (z 3) (w 3) + inner ℂ (z 4) (w 4) +
          inner ℂ (z 5) (w 5) + inner ℂ (z 6) (w 6) + inner ℂ (z 7) (w 7)) := by
  simp only [staticOutput, KFCausalFiniteOutputRescaling.selected_apply, PiLp.inner_apply,
    Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Fin.succ_zero_eq_one]
  norm_num only [Nat.reduceLT, if_true, if_false, inner_zero_left, Finset.sum_empty, add_zero]
  abel

private theorem extra_zero_of_ge_three (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (m g k : ℝ) (f : Hilbert) (i : Fin 8) (hi : ¬ i.val < 3) :
    extra ε hε h N hN m g k 0 f i = 0 := by
  have hp := congrArg (fun w : Output (Fin 8) Hilbert => w i)
    (point_static_extra ε hε h N hN m g k f).symm
  simpa only [staticOutput, KFCausalFiniteOutputRescaling.selected_apply, hi, if_false] using hp

theorem output_full_lower (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ) (f : Hilbert)
    (z : Output (Fin 8) Hilbert) :
    -(h ^ 2 / ε ^ 2) * ‖f‖ ^ 2 ≤
      (inner ℂ z (outputAction ε hε h N hN hb z +
        extra ε hε h N hN m g k 0 f)).re := by
  let w := outputAction ε hε h N hN hb z + extra ε hε h N hN m g k 0 f
  have htr : w = transformedOutput ε hε h N hN hb (energyWeight m g k 0) f z := rfl
  have hstat : -(h ^ 2 / ε ^ 2) * ‖f‖ ^ 2 ≤
      (inner ℂ (staticOutput z) (staticOutput w)).re := by
    rw [htr]
    exact output_static_lower ε hε h N hN hb m g k 0 f z
  have hw3 : w 3 = action ε hε h N hN (z 3) := by
    change factorOutput ε hε h N hN hb 3 (z 3) + extra ε hε h N hN m g k 0 f 3 = _
    rw [extra_zero_of_ge_three ε hε h N hN m g k f 3 (by decide), add_zero]
    rfl
  have hw4 : w 4 = action ε hε h N hN (z 4) := by
    change factorOutput ε hε h N hN hb 4 (z 4) + extra ε hε h N hN m g k 0 f 4 = _
    rw [extra_zero_of_ge_three ε hε h N hN m g k f 4 (by decide), add_zero]
    rfl
  have hw5 : w 5 = shifted ε hε h N hN (-h / 2) (shift_bound ε h hb) (z 5) := by
    change factorOutput ε hε h N hN hb 5 (z 5) + extra ε hε h N hN m g k 0 f 5 = _
    rw [extra_zero_of_ge_three ε hε h N hN m g k f 5 (by decide), add_zero]
    rfl
  have hw6 : w 6 = shifted ε hε h N hN (-h / 2) (shift_bound ε h hb) (z 6) := by
    change factorOutput ε hε h N hN hb 6 (z 6) + extra ε hε h N hN m g k 0 f 6 = _
    rw [extra_zero_of_ge_three ε hε h N hN m g k f 6 (by decide), add_zero]
    rfl
  have hw7 : w 7 = shifted ε hε h N hN (-h / 2) (shift_bound ε h hb) (z 7) := by
    change factorOutput ε hε h N hN hb 7 (z 7) + extra ε hε h N hN m g k 0 f 7 = _
    rw [extra_zero_of_ge_three ε hε h N hN m g k f 7 (by decide), add_zero]
    rfl
  have h3 := action_accretive ε hε h N hN (z 3)
  have h4 := action_accretive ε hε h N hN (z 4)
  have h5 := shifted_accretive ε hε h N hN (-h / 2) (shift_bound ε h hb) (z 5)
  have h6 := shifted_accretive ε hε h N hN (-h / 2) (shift_bound ε h hb) (z 6)
  have h7 := shifted_accretive ε hε h N hN (-h / 2) (shift_bound ε h hb) (z 7)
  have hsplit := congrArg Complex.re (output_eight_inner_split z w)
  rw [hw3, hw4, hw5, hw6, hw7] at hsplit
  simp only [Complex.add_re] at hsplit
  linarith

theorem section_full_lower (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (hb : |h| ≤ Real.pi * ε / 3) (hh : h ≠ 0) (m g k : ℝ)
    (f : Hilbert) (z : EnergyOutputSpace) :
    -(h ^ 2 / ε ^ 2) * ‖f‖ ^ 2 ≤
      (inner ℂ z (referenceOutputActionLp ε hε h N hN hb z +
        orbitExtra ε hε h N hN hh m g k f)).re := by
  let φ := physicalOrbit h hh f
  let w1 := referenceOutputActionLp ε hε h N hN hb z
  let w2 := orbitExtra ε hε h N hN hh m g k f
  have hφ : Integrable (fun θ => ‖φ θ‖ ^ 2) angleMeasure :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable φ)).mp (Lp.memLp φ)
  have hz : Integrable (fun θ => inner ℂ (z θ) ((w1 + w2) θ)) angleMeasure :=
    L2.integrable_inner (𝕜 := ℂ) z (w1 + w2)
  have hae : ∀ᵐ θ ∂angleMeasure,
      -(h ^ 2 / ε ^ 2) * ‖φ θ‖ ^ 2 ≤ (inner ℂ (z θ) ((w1 + w2) θ)).re := by
    filter_upwards [Lp.coeFn_add w1 w2,
      (outputAction ε hε h N hN hb).coeFn_compLp z,
      (extra ε hε h N hN m g k 0).coeFn_compLp φ] with θ hadd h1 h2
    have hw1 : w1 θ = outputAction ε hε h N hN hb (z θ) := h1
    have hw2 : w2 θ = extra ε hε h N hN m g k 0 (φ θ) := h2
    have hsum : (w1 + w2) θ =
        outputAction ε hε h N hN hb (z θ) + extra ε hε h N hN m g k 0 (φ θ) :=
      hadd.trans (congrArg₂ (· + ·) hw1 hw2)
    rw [hsum]
    exact output_full_lower ε hε h N hN hb m g k (φ θ) (z θ)
  have hint := integral_mono_ae (hφ.const_mul (-(h ^ 2 / ε ^ 2))) hz.re hae
  rw [integral_const_mul, ← l2_norm_square angleMeasure φ,
    (physicalOrbit h hh).norm_map f, integral_re hz] at hint
  exact hint

private def triangularGraphMap {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (D : H →L[ℂ] H) (R : K →L[ℂ] K) (C : H →L[ℂ] K) :
    WithLp 2 (H × K) →L[ℂ] WithLp 2 (H × K) :=
  let e := WithLp.prodContinuousLinearEquiv 2 ℂ H K
  let b := (D.comp (ContinuousLinearMap.fst ℂ H K)).prod
    (R.comp (ContinuousLinearMap.snd ℂ H K) + C.comp (ContinuousLinearMap.fst ℂ H K))
  e.symm.toContinuousLinearMap.comp (b.comp e.toContinuousLinearMap)

private def triangularAction {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (G : KFCausalClosedGraphForm.Data H K)
    (D : H →L[ℂ] H) (R : K →L[ℂ] K) (C : H →L[ℂ] K)
    (hg : ∀ f g, (f, g) ∈ G.operator.graph → (D f, R g + C f) ∈ G.operator.graph) :
    KFCausalClosedGraphForm.FormSpace G →L[ℂ] KFCausalClosedGraphForm.FormSpace G where
  toFun u := ⟨triangularGraphMap D R C u.val,
    hg (KFCausalClosedGraphForm.embedding G u) (KFCausalClosedGraphForm.energyOutput G u) u.property⟩
  map_add' u v := by apply Subtype.ext; exact (triangularGraphMap D R C).map_add u.val v.val
  map_smul' a u := by apply Subtype.ext; exact (triangularGraphMap D R C).map_smul a u.val
  cont := ((triangularGraphMap D R C).continuous.comp continuous_subtype_val).subtype_mk _

private theorem quadratic_bound (u v z e : ℝ) (hv : 0 ≤ v)
    (hz : 0 ≤ z) (he : 0 < e) (hq : e ^ 2 * u ^ 2 ≤ v * u + z ^ 2) :
    u ≤ v / e ^ 2 + z / e := by
  have hmul : (v / e) * (e * u) = v * u := by rw [← mul_assoc, div_mul_cancel₀ _ he.ne']
  have hs : (e * u) ^ 2 ≤ (v / e) * (e * u) + z ^ 2 := by rw [hmul]; nlinarith only [hq]
  have hn : e * u ≤ v / e + z := by
    have ha : 0 ≤ v / e := div_nonneg hv he.le
    by_contra hbad
    have hb := lt_of_not_ge hbad
    have hc : z < e * u := by linarith
    nlinarith [mul_nonneg ha (show 0 ≤ e * u - z by linarith)]
  have hd : u ≤ (v / e + z) / e := (le_div_iff₀ he).mpr (by simpa only [mul_comm u e] using hn)
  have heq : (v / e + z) / e = v / e ^ 2 + z / e := by ring
  exact hd.trans_eq heq

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "SD" => KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "SV" => KFCausalClockFloorStaticPotentialHamiltonian.ResidualForm ε hε h hh hw m g k
local notation "SJ" => fun t => KFCausalClosedGraphForm.embedding (SD t)
local notation "SB" => fun t => KFCausalClosedGraphForm.energyOutput (SD t)
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RS" => KFCausalClockFloorResidualClockCore.resolvent ε hε h hh hw m g k
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "Kroot" => rootOperator ε hε h
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Tgrow" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hw) hh m g k

def residualYosidaFormAction (N : ℝ) (hN : 0 < N) (t : ℝ) : SV t →L[ℂ] SV t :=
  triangularAction (SD t) (action ε hε h N hN)
    (referenceOutputActionLp ε hε h N hN hb)
    (orbitExtra ε hε h N hN hh m g k)
    (yosida_graph ε hε h N hN hb hh m g k t)

theorem residualYosidaFormAction_embedding (N : ℝ) (hN : 0 < N) (t : ℝ) (w : SV t) :
    SJ t (residualYosidaFormAction ε hε h hh hb m g k N hN t w) =
      action ε hε h N hN (SJ t w) := rfl

theorem residualYosidaFormAction_output (N : ℝ) (hN : 0 < N) (t : ℝ) (w : SV t) :
    SB t (residualYosidaFormAction ε hε h hh hb m g k N hN t w) =
      referenceOutputActionLp ε hε h N hN hb (SB t w) +
        orbitExtra ε hε h N hN hh m g k (SJ t w) := rfl

theorem residual_form_yosida_lower (N : ℝ) (hN : 0 < N) (t : ℝ) (w : SV t) :
    -(h ^ 2 / ε ^ 2) * ‖SJ t w‖ ^ 2 ≤
      (inner ℂ (SB t w)
        (SB t (residualYosidaFormAction ε hε h hh hb m g k N hN t w))).re := by
  rw [residualYosidaFormAction_output]
  exact section_full_lower ε hε h N hN hb hh m g k (SJ t w) (SB t w)

theorem residual_operator_yosida_pairing_lower (N : ℝ) (hN : 0 < N) (t : ℝ)
    (x : (S t).domain) :
    -(h ^ 2 / ε ^ 2) * ‖(x : Hilbert)‖ ^ 2 ≤
      (inner ℂ (S t x) (action ε hε h N hN (x : Hilbert))).re := by
  let w := KFCausalClosedGraphForm.formLift (SD t) x
  have hJ : SJ t w = (x : Hilbert) := KFCausalClosedGraphForm.embedding_formLift (SD t) x
  have hrep : inner ℂ (SB t w)
      (SB t (residualYosidaFormAction ε hε h hh hb m g k N hN t w)) =
      inner ℂ (S t x) (action ε hε h N hN (x : Hilbert)) :=
    (KFCausalClosedGraphForm.hamiltonian_represents_form (SD t) x
      (residualYosidaFormAction ε hε h hh hb m g k N hN t w)).trans
      (congrArg (inner ℂ (S t x)) (congrArg (action ε hε h N hN) hJ))
  have hlow := residual_form_yosida_lower ε hε h hh hb m g k N hN t w
  have hlhs : -(h ^ 2 / ε ^ 2) * ‖(x : Hilbert)‖ ^ 2 =
      -(h ^ 2 / ε ^ 2) * ‖SJ t w‖ ^ 2 :=
    congrArg (fun u : Hilbert => -(h ^ 2 / ε ^ 2) * ‖u‖ ^ 2) hJ.symm
  exact (hlhs.trans_le hlow).trans_eq (congrArg Complex.re hrep)

/-! ### 3. Residual Resolvent Regularity on Dom(K_root) and Dom(E_avg(s)) -/

theorem residual_resolvent_yosida_quadratic_ineq
    (N : ℝ) (hN : 0 < N) (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    a * ‖yosidaRootAction ε hε h N hN (RS t a f)‖ ^ 2 ≤
      (inner ℂ (yosidaRootAction ε hε h N hN f)
        (yosidaRootAction ε hε h N hN (RS t a f))).re +
      (h ^ 2 / ε ^ 2) * ‖RS t a f‖ ^ 2 := by
  let x := residualResolventPoint ε hε h hh hb m g k t a ha f
  have hx : (x : Hilbert) = RS t a f := rfl
  have hval : S t x = f - a • RS t a f :=
    KFCausalPositiveResolventBounds.point_value (S t) (RS t a) a
      (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha) f
  have hlow := residual_operator_yosida_pairing_lower ε hε h hh hb m g k N hN t x
  rw [hx, hval, inner_sub_left, inner_smul_left_eq_smul, Complex.sub_re,
    Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero,
    ← yosidaRootAction_sq_inner ε hε h N hN f (RS t a f),
    ← yosidaRootAction_norm_sq_eq_inner ε hε h N hN (RS t a f)] at hlow
  linarith

theorem residual_resolvent_yosidaRoot_bound
    (N : ℝ) (hN : 0 < N) (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖yosidaRootAction ε hε h N hN (RS t a f)‖ ≤
      ‖yosidaRootAction ε hε h N hN f‖ / a +
        (|h| / ε * ‖RS t a f‖) / Real.sqrt a := by
  have hq0 := residual_resolvent_yosida_quadratic_ineq ε hε h hh hb m g k N hN t a ha f
  have hcs : (inner ℂ (yosidaRootAction ε hε h N hN f)
      (yosidaRootAction ε hε h N hN (RS t a f))).re ≤
      ‖yosidaRootAction ε hε h N hN f‖ * ‖yosidaRootAction ε hε h N hN (RS t a f)‖ :=
    re_inner_le_norm (𝕜 := ℂ)
      (yosidaRootAction ε hε h N hN f) (yosidaRootAction ε hε h N hN (RS t a f))
  have he : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha.le
  have hd : (|h| / ε * ‖RS t a f‖) ^ 2 = (h ^ 2 / ε ^ 2) * ‖RS t a f‖ ^ 2 := by
    rw [mul_pow, div_pow, sq_abs]
  have hq := quadratic_bound
    ‖yosidaRootAction ε hε h N hN (RS t a f)‖
    ‖yosidaRootAction ε hε h N hN f‖
    (|h| / ε * ‖RS t a f‖)
    (Real.sqrt a)
    (norm_nonneg _)
    (by positivity)
    (Real.sqrt_pos.mpr ha)
    (by rw [he, hd]; linarith)
  simpa only [he] using hq

def residualResolventRootBound (t a : ℝ) (f : Hilbert)
    (hf : f ∈ (Kroot).domain) : ℝ :=
  ‖Kroot ⟨f, hf⟩‖ / a + (|h| / ε * ‖RS t a f‖) / Real.sqrt a

def residualResolventRootSourceBound (a : ℝ) (f : Hilbert)
    (hf : f ∈ (Kroot).domain) : ℝ :=
  ‖Kroot ⟨f, hf⟩‖ / a + (|h| / ε * (a⁻¹ * ‖f‖)) / Real.sqrt a

theorem residual_resolvent_norm_le (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖RS t a f‖ ≤ a⁻¹ * ‖f‖ :=
  KFCausalPositiveResolventBounds.resolvent_apply_norm_bound (S t) (RS t a) a ha
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha)
    (KFCausalClosedGraphForm.hamiltonian_positive (SD t)) f

theorem residualResolventRootBound_le_sourceBound (t a : ℝ) (ha : 0 < a)
    (f : Hilbert) (hf : f ∈ (Kroot).domain) :
    residualResolventRootBound ε hε h hh hb m g k t a f hf ≤
      residualResolventRootSourceBound ε hε h a f hf := by
  unfold residualResolventRootBound residualResolventRootSourceBound
  have hn := residual_resolvent_norm_le ε hε h hh hb m g k t a ha f
  have hmul : |h| / ε * ‖RS t a f‖ ≤ |h| / ε * (a⁻¹ * ‖f‖) :=
    mul_le_mul_of_nonneg_left hn (by positivity)
  have hdiv : (|h| / ε * ‖RS t a f‖) / Real.sqrt a ≤
      (|h| / ε * (a⁻¹ * ‖f‖)) / Real.sqrt a :=
    div_le_div_of_nonneg_right hmul (Real.sqrt_nonneg a)
  linarith

theorem residual_resolvent_yosidaRoot_le_rootBound
    (N : ℝ) (hN : 0 < N) (t a : ℝ) (ha : 0 < a)
    (f : Hilbert) (hf : f ∈ (Kroot).domain) :
    ‖yosidaRootAction ε hε h N hN (RS t a f)‖ ≤
      residualResolventRootBound ε hε h hh hb m g k t a f hf := by
  have h1 := residual_resolvent_yosidaRoot_bound ε hε h hh hb m g k N hN t a ha f
  have h2 := div_le_div_of_nonneg_right
    (yosidaRootAction_norm_le_rootOperator ε hε h N hN f hf) ha.le
  unfold residualResolventRootBound
  linarith

theorem residual_resolvent_mem_radialRoot_domain
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kroot).domain) :
    RS t a f ∈ (Kroot).domain :=
  root_domain_of_uniform_bound ε hε h (RS t a f)
    (residualResolventRootBound ε hε h hh hb m g k t a f hf)
    (fun n => residual_resolvent_yosidaRoot_le_rootBound ε hε h hh hb m g k
      ((n : ℝ) + 1) (by positivity) t a ha f hf)

theorem residual_resolvent_radialRoot_norm_le
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kroot).domain) :
    ‖Kroot ⟨RS t a f,
      residual_resolvent_mem_radialRoot_domain ε hε h hh hb m g k t a ha f hf⟩‖ ≤
      residualResolventRootBound ε hε h hh hb m g k t a f hf :=
  root_norm_of_uniform_bound ε hε h (RS t a f)
    (residualResolventRootBound ε hε h hh hb m g k t a f hf)
    (fun n => residual_resolvent_yosidaRoot_le_rootBound ε hε h hh hb m g k
      ((n : ℝ) + 1) (by positivity) t a ha f hf)

theorem residual_resolvent_radialRoot_source_norm_le
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kroot).domain) :
    ‖Kroot ⟨RS t a f,
      residual_resolvent_mem_radialRoot_domain ε hε h hh hb m g k t a ha f hf⟩‖ ≤
      residualResolventRootSourceBound ε hε h a f hf :=
  (residual_resolvent_radialRoot_norm_le ε hε h hh hb m g k t a ha f hf).trans
    (residualResolventRootBound_le_sourceBound ε hε h hh hb m g k t a ha f hf)

theorem residual_resolvent_mem_averaged_domain_of_radialRoot
    (s t a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kroot).domain) :
    RS t a f ∈ (Eavg s).domain := by
  have hK : RS t a f ∈ (Kroot).domain :=
    residual_resolvent_mem_radialRoot_domain ε hε h hh hb m g k t a ha f hf
  have hRt : RS t a f ∈ (Tres t).domain :=
    residual_resolvent_mem_residualForm_domain ε hε h hh hb m g k t a ha f
  have hRs : RS t a f ∈ (Tres s).domain :=
    (KFCausalClockFloorUnconditionalFormDomainSynthesis.residual_domain_time_eq
      ε hε h hh hb m g k t s (RS t a f)).mp hRt
  exact (KFCausalClockFloorResidualFormReconstruction.averaged_domain_eq_root_inter_residual
    ε hε h hh hb m g k s (RS t a f)).mpr ⟨hK, hRs⟩

theorem residual_resolvent_mem_growingForm_domain_of_radialRoot
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kroot).domain) :
    RS t a f ∈ (Tgrow).domain :=
  ((KFCausalClockFloorResidualFormReconstruction.averaged_domain_eq_growing_inter_residual
    ε hε h hh hb m g k t (RS t a f)).mp
    (residual_resolvent_mem_averaged_domain_of_radialRoot ε hε h hh hb m g k t t a ha f hf)).1

theorem residual_resolvent_preserves_averaged_domain
    (s t a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Eavg s).domain) :
    RS t a f ∈ (Eavg s).domain :=
  residual_resolvent_mem_averaged_domain_of_radialRoot ε hε h hh hb m g k s t a ha f
    (KFCausalClockFloorUnconditionalFormDomainSynthesis.averaged_domain_subset_three_forms
      ε hε h hh hb m g k s f hf).2.1

theorem residual_resolvent_preserves_growingForm_domain
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Tgrow).domain) :
    RS t a f ∈ (Tgrow).domain :=
  residual_resolvent_mem_growingForm_domain_of_radialRoot ε hε h hh hb m g k t a ha f
    ((KFCausalClockFloorGrowingFormReconstruction.growing_domain_iff
      ε hε h hh hb m g k f).mp hf).1

theorem residual_resolvent_all_form_domains_of_radialRoot
    (s t a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kroot).domain) :
    RS t a f ∈ (S t).domain ∧
      RS t a f ∈ (Eavg s).domain ∧
      RS t a f ∈ (Tres s).domain ∧
      RS t a f ∈ (Tstat).domain ∧
      RS t a f ∈ (Kroot).domain ∧
      RS t a f ∈ (Tpot).domain ∧
      RS t a f ∈ (Tgrow).domain ∧
      RS t a f ∈ (clockHalf ε).domain := by
  have hS : RS t a f ∈ (S t).domain :=
    (residualResolventPoint ε hε h hh hb m g k t a ha f).property
  have hE : RS t a f ∈ (Eavg s).domain :=
    residual_resolvent_mem_averaged_domain_of_radialRoot ε hε h hh hb m g k s t a ha f hf
  have hRr := (KFCausalClockFloorResidualFormReconstruction.averaged_domain_eq_root_inter_residual
    ε hε h hh hb m g k s (RS t a f)).mp hE
  have hGr := (KFCausalClockFloorResidualFormReconstruction.averaged_domain_eq_growing_inter_residual
    ε hε h hh hb m g k s (RS t a f)).mp hE
  have h3 := KFCausalClockFloorUnconditionalFormDomainSynthesis.averaged_domain_subset_three_forms
    ε hε h hh hb m g k s (RS t a f) hE
  have hC : RS t a f ∈ (clockHalf ε).domain :=
    KFCausalClockFloorPositiveVacuumTwoTimeOperatorDomain.static_root_subset_clockHalf_domain
      ε hε h (RS t a f) h3.1
  exact ⟨hS, hE, hRr.2, h3.1, h3.2.1, h3.2.2, hGr.1, hC⟩

theorem residual_resolvent_three_channel_energy_bound_of_radialRoot
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kroot).domain) :
    ‖Tstat ⟨RS t a f,
      residual_resolvent_mem_staticRoot_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 +
    Real.exp (2 * t) * ‖Kroot ⟨RS t a f,
      residual_resolvent_mem_radialRoot_domain ε hε h hh hb m g k t a ha f hf⟩‖ ^ 2 +
    Real.exp (2 * t) * ‖Tpot ⟨RS t a f,
      residual_resolvent_mem_potentialForm_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 +
    a * ‖RS t a f‖ ^ 2 ≤
      a⁻¹ * ‖f‖ ^ 2 +
        Real.exp (2 * t) *
          (residualResolventRootBound ε hε h hh hb m g k t a f hf) ^ 2 := by
  have hres := residual_resolvent_two_channel_energy_le ε hε h hh hb m g k t a ha f
  have hrad := residual_resolvent_radialRoot_norm_le ε hε h hh hb m g k t a ha f hf
  have hrad_sq : ‖Kroot ⟨RS t a f,
      residual_resolvent_mem_radialRoot_domain ε hε h hh hb m g k t a ha f hf⟩‖ ^ 2 ≤
      (residualResolventRootBound ε hε h hh hb m g k t a f hf) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hrad 2
  have hmul := mul_le_mul_of_nonneg_left hrad_sq (Real.exp_pos (2 * t)).le
  linarith

#print axioms yosidaRootSymbol_nonnegative
#print axioms yosidaRootSymbol_sq
#print axioms yosidaRootSymbol_le_sqrt
#print axioms yosidaRootSymbol_le_rootSymbol
#print axioms yosidaRootSymbol_tendsto
#print axioms yosidaRootAction_coe
#print axioms yosidaRootAction_norm
#print axioms yosidaRootAction_selfAdjoint_pairing
#print axioms yosidaRootAction_sq_eq_yosida
#print axioms yosidaRootAction_sq_inner
#print axioms yosidaRootAction_norm_sq_eq_inner
#print axioms yosidaRootAction_norm_le_rootOperator
#print axioms root_domain_of_uniform_bound
#print axioms root_norm_of_uniform_bound
#print axioms output_full_lower
#print axioms section_full_lower
#print axioms residualYosidaFormAction_embedding
#print axioms residualYosidaFormAction_output
#print axioms residual_form_yosida_lower
#print axioms residual_operator_yosida_pairing_lower
#print axioms residual_resolvent_yosida_quadratic_ineq
#print axioms residual_resolvent_yosidaRoot_bound
#print axioms residual_resolvent_norm_le
#print axioms residualResolventRootBound_le_sourceBound
#print axioms residual_resolvent_yosidaRoot_le_rootBound
#print axioms residual_resolvent_mem_radialRoot_domain
#print axioms residual_resolvent_radialRoot_norm_le
#print axioms residual_resolvent_radialRoot_source_norm_le
#print axioms residual_resolvent_mem_averaged_domain_of_radialRoot
#print axioms residual_resolvent_mem_growingForm_domain_of_radialRoot
#print axioms residual_resolvent_preserves_averaged_domain
#print axioms residual_resolvent_preserves_growingForm_domain
#print axioms residual_resolvent_all_form_domains_of_radialRoot
#print axioms residual_resolvent_three_channel_energy_bound_of_radialRoot
end
end UnifiedTheory.Audit.KFCausalClockFloorResidualResolventRadialRootRegularity
