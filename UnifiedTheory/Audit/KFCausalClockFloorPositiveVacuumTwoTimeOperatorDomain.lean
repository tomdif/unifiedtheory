/- Positive-Vacuum Two-Time Operator Domain Synthesis:
1. Unconditional inclusion of the maximal static square-root domain in the
   unbounded half-clock domain with root-norm bound ‖clockHalf f‖ ≤ √2 ‖Tstat f‖,
   yielding unconditional half-clock domain inclusions for all form and operator
   domains (Tstat, Tres(t), Eavg(t), T, S(t), H(t)), relative bound
   ‖clockHalf x‖² ≤ 2 ‖x‖ ‖T x‖ on Dom T, and absorption of the half-clock
   domain into commonOperatorDomain and Dom T ∩ Dom K ∩ Dom P.
2. Unconditional time-invariance of the completed residual and averaged form
   domains Dom Tres(s) = Dom Tres(t) = Dom Tres(0) and Dom Eavg(s) = Dom Eavg(t).
3. Under positive vacuum (k > 0), exact time-independence and three-operator
   identification of all operator-intersection domains:
   Dom H(t) ∩ Dom G = Dom H(t) ∩ Dom T = Dom H(t) ∩ Dom P = Dom S(t) ∩ Dom G
   = Dom T ∩ Dom G = commonOperatorDomain = Dom T ∩ Dom K ∩ Dom P.
4. Under positive vacuum (k > 0), two-time operator evaluations, differences,
   shifted-resolvent identities, and simultaneous three-operator graph cores
   for T with simultaneous convergence in Hilbert, T, Tstat, and clockHalf
   norms on Dom T ∩ Dom K ∩ Dom P. -/
import UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumThreeOperatorDomain
import UnifiedTheory.Audit.KFCausalClockFloorUnconditionalTwoTimeEvolution
import UnifiedTheory.Audit.KFCausalClockFloorTwoTimeResolventDifference
import UnifiedTheory.Audit.KFCausalClockFloorTwoTimeFormResolventComparison
import UnifiedTheory.Audit.KFCausalClockFloorStaticThreeOperatorCore
import UnifiedTheory.Audit.KFCausalClockFloorHamiltonianResolventFormBounds

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumTwoTimeOperatorDomain
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalChargeTransverseSplit (dualPhysical)
open KFCausalClockFloorFlow (clock)
open KFCausalClockFloorCanonicalDefect (clock_positive)
open KFCausalComplementaryChargeSymbol (complementaryWeight_nonnegative)
open KFCausalClockFloorStaticMultiplierForm (symbol symbol_continuous rootSymbol rootOperator)
open KFCausalUnitaryRealMultiplier (realPullback_coe)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorPureClockClockResponse (half_graph)
open KFCausalClockFloorDualClock (inverseL_dual_coe)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorAveragedOutputTransport (timeOutputLp)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorUnconditionalTwoTimeEvolution (commonOperatorDomain)

private theorem clock_sqrt_le_rootSymbol (ε : ℝ) (hε : 0 < ε) (h : ℝ) (x : Joint 5 1) :
    Real.sqrt (clock ε (x (.inr 0))) ≤ Real.sqrt 2 * rootSymbol ε h x := by
  unfold rootSymbol
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  apply Real.sqrt_le_sqrt
  unfold symbol
  have h0 := complementaryWeight_nonnegative ε hε h 0 x
  have h1 := complementaryWeight_nonnegative ε hε h 1 x
  linarith

private theorem clock_dual_memLp (ε : ℝ) (hε : 0 < ε) (h : ℝ) (f : Hilbert)
    (hf : f ∈ (rootOperator ε hε h).domain) :
    MemLp (fun x : Joint 5 1 =>
      (Real.sqrt (clock ε (x (.inr 0))) : ℂ) * (dualPhysical f) x) 2 volume := by
  let y := dualPhysical (rootOperator ε hε h ⟨f, hf⟩)
  have hy : y =ᵐ[volume] fun x => (rootSymbol ε h x : ℂ) * (dualPhysical f) x :=
    realPullback_coe dualPhysical (rootSymbol ε h)
      ((symbol_continuous ε hε h).sqrt.measurable) ⟨f, hf⟩
  have hclock : Continuous (fun x : Joint 5 1 => clock ε (x (.inr 0))) := by
    unfold clock; fun_prop
  have hm : AEStronglyMeasurable (fun x : Joint 5 1 =>
      (Real.sqrt (clock ε (x (.inr 0))) : ℂ) * (dualPhysical f) x) volume :=
    (Complex.continuous_ofReal.comp hclock.sqrt).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable (dualPhysical f))
  apply ((Lp.memLp y).const_mul ((Real.sqrt 2 : ℝ) : ℂ)).of_le hm
  filter_upwards [hy] with x hx
  rw [hx, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (by unfold rootSymbol; exact Real.sqrt_nonneg _), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (clock_sqrt_le_rootSymbol ε hε h x) (norm_nonneg _)

private theorem clock_dual_graph_vector (ε : ℝ) (hε : 0 < ε) (h : ℝ) (f : Hilbert)
    (hf : f ∈ (rootOperator ε hε h).domain) :
    (f, dualPhysical.symm ((clock_dual_memLp ε hε h f hf).toLp _)) ∈
      (clockHalf ε).graph ∧
    ‖dualPhysical.symm ((clock_dual_memLp ε hε h f hf).toLp _)‖ ≤
      Real.sqrt 2 * ‖rootOperator ε hε h ⟨f, hf⟩‖ := by
  let hm := clock_dual_memLp ε hε h f hf
  let g : Hilbert := dualPhysical.symm (hm.toLp _)
  let y := dualPhysical (rootOperator ε hε h ⟨f, hf⟩)
  have hy : y =ᵐ[volume] fun x => (rootSymbol ε h x : ℂ) * (dualPhysical f) x :=
    realPullback_coe dualPhysical (rootSymbol ε h)
      ((symbol_continuous ε hε h).sqrt.measurable) ⟨f, hf⟩
  have hg_coe : dualPhysical g =ᵐ[volume] fun x : Joint 5 1 =>
      (Real.sqrt (clock ε (x (.inr 0))) : ℂ) * (dualPhysical f) x := by
    rw [show dualPhysical g = hm.toLp _ from dualPhysical.apply_symm_apply _]
    exact hm.coeFn_toLp
  have hfg : (f, g) ∈ (clockHalf ε).graph := by
    apply (half_graph ε hε f g).mpr
    apply dualPhysical.injective
    apply Lp.ext
    filter_upwards [inverseL_dual_coe ε hε g, hg_coe] with x hinv hgx
    have hc : (Real.sqrt (clock ε (x (.inr 0))) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (clock_positive ε _ hε.le)).ne'
    rw [hinv, hgx, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  have hnorm : ‖g‖ ≤ Real.sqrt 2 * ‖rootOperator ε hε h ⟨f, hf⟩‖ := by
    rw [show ‖g‖ = ‖dualPhysical g‖ from (dualPhysical.norm_map g).symm,
      show ‖rootOperator ε hε h ⟨f, hf⟩‖ = ‖y‖ from
        (dualPhysical.norm_map (rootOperator ε hε h ⟨f, hf⟩)).symm]
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hg_coe, hy] with x hgx hx
    rw [hgx, hx, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (by unfold rootSymbol; exact Real.sqrt_nonneg _), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (clock_sqrt_le_rootSymbol ε hε h x) (norm_nonneg _)
  exact ⟨hfg, hnorm⟩

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "Kroot" => KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Tgrow" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (hamiltonian_bound ε h hw) hh m g k
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k
local notation "RS" => KFCausalClockFloorResidualClockCore.resolvent ε hε h hh hw m g k

/-! ### 1. Unconditional Static Root to Half-Clock Domain Inclusion and Norm Bounds -/

theorem static_root_subset_clockHalf_domain (f : Hilbert)
    (hf : f ∈ (Tstat).domain) :
    f ∈ (clockHalf ε).domain :=
  LinearPMap.mem_domain_of_mem_graph (clock_dual_graph_vector ε hε h f hf).1

theorem static_root_clockHalf_norm_le (f : Hilbert)
    (hf : f ∈ (Tstat).domain) :
    ‖clockHalf ε ⟨f, static_root_subset_clockHalf_domain ε hε h f hf⟩‖ ≤
      Real.sqrt 2 * ‖Tstat ⟨f, hf⟩‖ := by
  have hg := clock_dual_graph_vector ε hε h f hf
  have heq : clockHalf ε ⟨f, static_root_subset_clockHalf_domain ε hε h f hf⟩ =
      dualPhysical.symm ((clock_dual_memLp ε hε h f hf).toLp _) :=
    (clockHalf ε).mem_graph_snd_inj'
      ((clockHalf ε).mem_graph ⟨f, static_root_subset_clockHalf_domain ε hε h f hf⟩) hg.1 rfl
  rw [heq]
  exact hg.2

theorem static_root_clockHalf_norm_sq_le (f : Hilbert)
    (hf : f ∈ (Tstat).domain) :
    ‖clockHalf ε ⟨f, static_root_subset_clockHalf_domain ε hε h f hf⟩‖ ^ 2 ≤
      2 * ‖Tstat ⟨f, hf⟩‖ ^ 2 := by
  have hle := static_root_clockHalf_norm_le ε hε h f hf
  have hsq : ‖clockHalf ε ⟨f, static_root_subset_clockHalf_domain ε hε h f hf⟩‖ ^ 2 ≤
      (Real.sqrt 2 * ‖Tstat ⟨f, hf⟩‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hle 2
  calc
    ‖clockHalf ε ⟨f, static_root_subset_clockHalf_domain ε hε h f hf⟩‖ ^ 2 ≤
        (Real.sqrt 2 * ‖Tstat ⟨f, hf⟩‖) ^ 2 := hsq
    _ = (Real.sqrt 2) ^ 2 * ‖Tstat ⟨f, hf⟩‖ ^ 2 := by ring
    _ = 2 * ‖Tstat ⟨f, hf⟩‖ ^ 2 := by
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem static_root_domain_le_clockHalf_domain :
    (Tstat).domain ≤ (clockHalf ε).domain :=
  fun f hf => static_root_subset_clockHalf_domain ε hε h f hf

theorem static_domain_le_clockHalf_domain :
    (T).domain ≤ (clockHalf ε).domain :=
  fun f hf => static_root_subset_clockHalf_domain ε hε h f
    (KFCausalClockFloorStaticOperator.root_domain ε hε h ⟨f, hf⟩)

theorem static_operator_root_norm_sq_eq (x : (T).domain) :
    ‖Tstat ⟨(x : Hilbert), KFCausalClockFloorStaticOperator.root_domain ε hε h x⟩‖ ^ 2 =
      (inner ℂ (x : Hilbert) (T x)).re := by
  have hp := congrArg Complex.re
    (KFCausalClockFloorStaticOperator.root_pairing ε hε h x
      ⟨(x : Hilbert), KFCausalClockFloorStaticOperator.root_domain ε hε h x⟩)
  exact (inner_self_eq_norm_sq (𝕜 := ℂ)
    (Tstat ⟨(x : Hilbert), KFCausalClockFloorStaticOperator.root_domain ε hε h x⟩)).symm.trans hp

theorem static_operator_root_norm_sq_le (x : (T).domain) :
    ‖Tstat ⟨(x : Hilbert), KFCausalClockFloorStaticOperator.root_domain ε hε h x⟩‖ ^ 2 ≤
      ‖(x : Hilbert)‖ * ‖T x‖ := by
  rw [static_operator_root_norm_sq_eq ε hε h x]
  exact re_inner_le_norm (𝕜 := ℂ) (x : Hilbert) (T x)

theorem static_operator_clockHalf_norm_sq_le (x : (T).domain) :
    ‖clockHalf ε ⟨(x : Hilbert), static_domain_le_clockHalf_domain ε hε h x.property⟩‖ ^ 2 ≤
      2 * (‖(x : Hilbert)‖ * ‖T x‖) := by
  have h1 := static_root_clockHalf_norm_sq_le ε hε h (x : Hilbert)
    (KFCausalClockFloorStaticOperator.root_domain ε hε h x)
  have h2 := static_operator_root_norm_sq_le ε hε h x
  linarith

theorem residual_form_domain_le_clockHalf_domain (t : ℝ) :
    (Tres t).domain ≤ (clockHalf ε).domain :=
  fun f hf => static_root_subset_clockHalf_domain ε hε h f
    (KFCausalClockFloorUnconditionalFormDomainSynthesis.residual_domain_subset_static_inter_potential
      ε hε h hh hb m g k t f hf).1

theorem averaged_form_domain_le_clockHalf_domain (t : ℝ) :
    (Eavg t).domain ≤ (clockHalf ε).domain :=
  fun f hf => static_root_subset_clockHalf_domain ε hε h f
    (KFCausalClockFloorUnconditionalFormDomainSynthesis.averaged_domain_subset_three_forms
      ε hε h hh hb m g k t f hf).1

theorem residual_domain_le_clockHalf_domain (t : ℝ) :
    (S t).domain ≤ (clockHalf ε).domain :=
  fun f hf => static_root_subset_clockHalf_domain ε hε h f
    (KFCausalClockFloorUnconditionalOperatorFormEnergy.residual_mem_staticRoot_domain
      ε hε h hh hb m g k t ⟨f, hf⟩)

theorem hamiltonian_domain_le_clockHalf_domain (t : ℝ) :
    (H t).domain ≤ (clockHalf ε).domain :=
  fun f hf => static_root_subset_clockHalf_domain ε hε h f
    (KFCausalClockFloorUnconditionalOperatorFormEnergy.hamiltonian_mem_staticRoot_domain
      ε hε h hh hb m g k t ⟨f, hf⟩)

theorem commonOperatorDomain_le_clockHalf_domain :
    commonOperatorDomain ε hε h hh hb m g k ≤ (clockHalf ε).domain :=
  fun _ hx => static_domain_le_clockHalf_domain ε hε h hx.1.1.1

theorem commonOperatorDomain_inf_clockHalf_eq :
    commonOperatorDomain ε hε h hh hb m g k ⊓ (clockHalf ε).domain =
      commonOperatorDomain ε hε h hh hb m g k :=
  inf_of_le_left (commonOperatorDomain_le_clockHalf_domain ε hε h hh hb m g k)

theorem three_operator_domain_le_clockHalf_domain :
    (T).domain ⊓ (K).domain ⊓ (P).domain ≤ (clockHalf ε).domain :=
  fun _ hx => static_domain_le_clockHalf_domain ε hε h hx.1.1

theorem three_operator_domain_inf_clockHalf_eq :
    ((T).domain ⊓ (K).domain ⊓ (P).domain) ⊓ (clockHalf ε).domain =
      (T).domain ⊓ (K).domain ⊓ (P).domain :=
  inf_of_le_left (three_operator_domain_le_clockHalf_domain ε hε h hh hb m g k)

/-! ### 2. Unconditional Two-Time Residual and Averaged Form Domain Invariance -/

theorem residual_graph_transport (s t : ℝ) (f : Hilbert) (z : EnergyOutputSpace)
    (hz : (f, z) ∈ (Tres s).graph) :
    (f, timeOutputLp s t z) ∈ (Tres t).graph :=
  (KFCausalClockFloorUnconditionalFormDomainSynthesis.residual_graph_time_transfer
    ε hε h hh hb m g k s t f z).mp hz

theorem residual_form_domain_time_iff (s t : ℝ) (f : Hilbert) :
    f ∈ (Tres s).domain ↔ f ∈ (Tres t).domain :=
  KFCausalClockFloorUnconditionalFormDomainSynthesis.residual_domain_time_eq
    ε hε h hh hb m g k s t f

theorem residual_form_domain_time_eq (s t : ℝ) :
    (Tres s).domain = (Tres t).domain := by
  ext f
  exact residual_form_domain_time_iff ε hε h hh hb m g k s t f

theorem residual_form_domain_eq_zero (t : ℝ) :
    (Tres t).domain = (Tres 0).domain :=
  residual_form_domain_time_eq ε hε h hh hb m g k t 0

theorem averaged_form_domain_time_eq (s t : ℝ) :
    (Eavg s).domain = (Eavg t).domain := by
  ext f
  exact KFCausalClockFloorUnconditionalFormDomainSynthesis.averaged_domain_time_eq
    ε hε h hh hb m g k s t f

theorem averaged_form_domain_eq_zero (t : ℝ) :
    (Eavg t).domain = (Eavg 0).domain :=
  averaged_form_domain_time_eq ε hε h hh hb m g k t 0

theorem commonOperatorDomain_eq_time (t : ℝ) :
    ((T).domain ⊓ (K).domain ⊓ (P).domain) ⊓ (Tres t).domain =
      commonOperatorDomain ε hε h hh hb m g k := by
  rw [commonOperatorDomain, residual_form_domain_eq_zero ε hε h hh hb m g k t]

/-! ### 3. Positive-Vacuum (k > 0) Time-Independent Form and Operator Domains -/

theorem positive_vacuum_averaged_form_domain_iff (hk : 0 < k) (t : ℝ) (f : Hilbert) :
    f ∈ (Eavg t).domain ↔
      (f ∈ (Tstat).domain ∧ f ∈ (Kroot).domain) ∧ f ∈ (Tpot).domain := by
  rw [KFCausalClockFloorUnconditionalFormDomainSynthesis.averaged_domain_time_eq
    ε hε h hh hb m g k t 0 f,
    KFCausalClockFloorPositiveVacuumFormReconstruction.root_growing_domain_iff
      ε hε h hh hw m g k hk f,
    KFCausalClockFloorGrowingFormReconstruction.growing_domain_iff
      ε hε h hh hb m g k f,
    and_assoc]

theorem positive_vacuum_averaged_form_domain_eq (hk : 0 < k) (t : ℝ) :
    (Eavg t).domain = (Tstat).domain ⊓ (Kroot).domain ⊓ (Tpot).domain := by
  ext f
  exact positive_vacuum_averaged_form_domain_iff ε hε h hh hb m g k hk t f

theorem positive_vacuum_averaged_form_domain_eq_static_inter_growing (hk : 0 < k) (t : ℝ) :
    (Eavg t).domain = (Tstat).domain ⊓ (Tgrow).domain := by
  ext f
  rw [KFCausalClockFloorUnconditionalFormDomainSynthesis.averaged_domain_time_eq
    ε hε h hh hb m g k t 0 f]
  exact KFCausalClockFloorPositiveVacuumFormReconstruction.root_growing_domain_iff
    ε hε h hh hw m g k hk f

theorem unconditional_two_operator_growing_eval
    {x : Hilbert} (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    ∃ hxG : x ∈ (G).domain,
      G ⟨x, hxG⟩ = K ⟨x, hxK⟩ + P ⟨x, hxP⟩ := by
  have hxG : x ∈ (G).domain :=
    (KFCausalClockFloorGrowingPotentialSum.domain_iff ε hε h hh hb m g k x).mpr ⟨hxK, hxP⟩
  have hsum := KFCausalClockFloorGrowingPotentialSum.operator_sum ε hε h hh hb m g k
  have hg : (x, K ⟨x, hxK⟩ + P ⟨x, hxP⟩) ∈ (G).graph := by
    rw [hsum]
    exact (LinearPMap.mem_graph_iff _).mpr ⟨⟨x, ⟨hxK, hxP⟩⟩, rfl, rfl⟩
  exact ⟨hxG, (G).mem_graph_snd_inj' ((G).mem_graph ⟨x, hxG⟩) hg rfl⟩

theorem positive_vacuum_three_operator_hamiltonian_eval (hk : 0 < k) (t : ℝ)
    {x : Hilbert} (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    ∃ hxt : x ∈ (H t).domain,
      H t ⟨x, hxt⟩ = T ⟨x, hxT⟩ + (Real.exp (2 * t) : ℂ) • (K ⟨x, hxK⟩ + P ⟨x, hxP⟩) := by
  have hg := KFCausalClockFloorPositiveVacuumThreeOperatorDomain.three_operator_hamiltonian_graph
    ε hε h hh hb m g k t hk x (T ⟨x, hxT⟩) (K ⟨x, hxK⟩) (P ⟨x, hxP⟩)
    ((T).mem_graph ⟨x, hxT⟩) ((K).mem_graph ⟨x, hxK⟩) ((P).mem_graph ⟨x, hxP⟩)
  let hxt : x ∈ (H t).domain := LinearPMap.mem_domain_of_mem_graph hg
  exact ⟨hxt, (H t).mem_graph_snd_inj' ((H t).mem_graph ⟨x, hxt⟩) hg rfl⟩

theorem positive_vacuum_three_operator_residual_eval (hk : 0 < k) (t : ℝ)
    {x : Hilbert} (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    ∃ hxt : x ∈ (S t).domain,
      S t ⟨x, hxt⟩ = T ⟨x, hxT⟩ + (Real.exp (2 * t) : ℂ) • P ⟨x, hxP⟩ := by
  have hg := KFCausalClockFloorPositiveVacuumThreeOperatorDomain.three_operator_residual_graph
    ε hε h hh hb m g k t hk x (T ⟨x, hxT⟩) (K ⟨x, hxK⟩) (P ⟨x, hxP⟩)
    ((T).mem_graph ⟨x, hxT⟩) ((K).mem_graph ⟨x, hxK⟩) ((P).mem_graph ⟨x, hxP⟩)
  let hxt : x ∈ (S t).domain := LinearPMap.mem_domain_of_mem_graph hg
  exact ⟨hxt, (S t).mem_graph_snd_inj' ((S t).mem_graph ⟨x, hxt⟩) hg rfl⟩

theorem positive_vacuum_three_operator_in_averaged_domain (hk : 0 < k) (t : ℝ)
    {x : Hilbert} (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    x ∈ (Eavg t).domain := by
  have hxt := (positive_vacuum_three_operator_hamiltonian_eval
    ε hε h hh hb m g k hk t hxT hxK hxP).choose
  exact KFCausalClockFloorUnconditionalOperatorFormEnergy.hamiltonian_mem_averaged_domain
    ε hε h hh hb m g k t ⟨x, hxt⟩

theorem positive_vacuum_three_operator_in_residual_domain (hk : 0 < k) (t : ℝ)
    {x : Hilbert} (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    x ∈ (Tres t).domain := by
  have hxt := (positive_vacuum_three_operator_residual_eval
    ε hε h hh hb m g k hk t hxT hxK hxP).choose
  exact KFCausalClockFloorUnconditionalOperatorFormEnergy.residual_mem_residualForm_domain
    ε hε h hh hb m g k t ⟨x, hxt⟩

theorem positive_vacuum_common_domain_eq_three_operator (hk : 0 < k) :
    commonOperatorDomain ε hε h hh hb m g k =
      (T).domain ⊓ (K).domain ⊓ (P).domain :=
  KFCausalClockFloorUnconditionalTwoTimeEvolution.positive_vacuum_common_domain_eq
    ε hε h hh hb m g k hk

theorem positive_vacuum_common_domain_inf_clockHalf_eq (hk : 0 < k) :
    commonOperatorDomain ε hε h hh hb m g k ⊓ (clockHalf ε).domain =
      (T).domain ⊓ (K).domain ⊓ (P).domain := by
  rw [commonOperatorDomain_inf_clockHalf_eq,
    positive_vacuum_common_domain_eq_three_operator ε hε h hh hb m g k hk]

theorem positive_vacuum_static_inter_growing_domain_eq :
    (T).domain ⊓ (G).domain = (T).domain ⊓ (K).domain ⊓ (P).domain := by
  ext x
  simp only [Submodule.mem_inf]
  rw [KFCausalClockFloorGrowingPotentialSum.domain_iff ε hε h hh hb m g k x]
  tauto

theorem positive_vacuum_hamiltonian_inter_growing_domain_eq (hk : 0 < k) (t : ℝ) :
    (H t).domain ⊓ (G).domain = (T).domain ⊓ (K).domain ⊓ (P).domain :=
  (KFCausalClockFloorUnconditionalThreeOperatorDecomposition.hamiltonian_growing_common_domain_eq
    ε hε h hh hb m g k t).trans
    (positive_vacuum_common_domain_eq_three_operator ε hε h hh hb m g k hk)

theorem positive_vacuum_hamiltonian_inter_static_domain_eq (hk : 0 < k) (t : ℝ) :
    (H t).domain ⊓ (T).domain = (T).domain ⊓ (K).domain ⊓ (P).domain :=
  KFCausalClockFloorPositiveVacuumThreeOperatorDomain.hamiltonian_static_domain_eq
    ε hε h hh hb m g k t hk

theorem positive_vacuum_hamiltonian_inter_potential_domain_eq (hk : 0 < k) (t : ℝ) :
    (H t).domain ⊓ (P).domain = (T).domain ⊓ (K).domain ⊓ (P).domain :=
  KFCausalClockFloorPositiveVacuumThreeOperatorDomain.hamiltonian_potential_domain_eq
    ε hε h hh hb m g k t hk

theorem positive_vacuum_residual_inter_growing_domain_eq (hk : 0 < k) (t : ℝ) :
    (S t).domain ⊓ (G).domain = (T).domain ⊓ (K).domain ⊓ (P).domain :=
  KFCausalClockFloorPositiveVacuumThreeOperatorDomain.residual_growing_domain_eq
    ε hε h hh hb m g k t hk

theorem positive_vacuum_two_time_hamiltonian_growing_domain_eq (hk : 0 < k) (s t : ℝ) :
    (H s).domain ⊓ (G).domain = (H t).domain ⊓ (G).domain := by
  rw [positive_vacuum_hamiltonian_inter_growing_domain_eq ε hε h hh hb m g k hk s,
    positive_vacuum_hamiltonian_inter_growing_domain_eq ε hε h hh hb m g k hk t]

theorem positive_vacuum_two_time_hamiltonian_static_domain_eq (hk : 0 < k) (s t : ℝ) :
    (H s).domain ⊓ (T).domain = (H t).domain ⊓ (T).domain := by
  rw [positive_vacuum_hamiltonian_inter_static_domain_eq ε hε h hh hb m g k hk s,
    positive_vacuum_hamiltonian_inter_static_domain_eq ε hε h hh hb m g k hk t]

theorem positive_vacuum_two_time_hamiltonian_potential_domain_eq (hk : 0 < k) (s t : ℝ) :
    (H s).domain ⊓ (P).domain = (H t).domain ⊓ (P).domain := by
  rw [positive_vacuum_hamiltonian_inter_potential_domain_eq ε hε h hh hb m g k hk s,
    positive_vacuum_hamiltonian_inter_potential_domain_eq ε hε h hh hb m g k hk t]

theorem positive_vacuum_two_time_residual_growing_domain_eq (hk : 0 < k) (s t : ℝ) :
    (S s).domain ⊓ (G).domain = (S t).domain ⊓ (G).domain := by
  rw [positive_vacuum_residual_inter_growing_domain_eq ε hε h hh hb m g k hk s,
    positive_vacuum_residual_inter_growing_domain_eq ε hε h hh hb m g k hk t]

/-! ### 4. Positive-Vacuum Two-Time Operator Evaluations and Second Resolvent Identities -/

theorem positive_vacuum_two_time_residual_eval (hk : 0 < k) (s t : ℝ)
    {x : Hilbert} (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    ∃ (hxs : x ∈ (S s).domain) (hxt : x ∈ (S t).domain),
      S s ⟨x, hxs⟩ = T ⟨x, hxT⟩ + (Real.exp (2 * s) : ℂ) • P ⟨x, hxP⟩ ∧
      S t ⟨x, hxt⟩ = T ⟨x, hxT⟩ + (Real.exp (2 * t) : ℂ) • P ⟨x, hxP⟩ ∧
      S t ⟨x, hxt⟩ - S s ⟨x, hxs⟩ =
        ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) • P ⟨x, hxP⟩ := by
  have hs := positive_vacuum_three_operator_residual_eval ε hε h hh hb m g k hk s hxT hxK hxP
  have ht := positive_vacuum_three_operator_residual_eval ε hε h hh hb m g k hk t hxT hxK hxP
  refine ⟨hs.choose, ht.choose, hs.choose_spec, ht.choose_spec, ?_⟩
  rw [ht.choose_spec, hs.choose_spec, Complex.ofReal_sub, sub_smul]
  abel

theorem positive_vacuum_two_time_hamiltonian_eval (hk : 0 < k) (s t : ℝ)
    {x : Hilbert} (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    ∃ (hxs : x ∈ (H s).domain) (hxt : x ∈ (H t).domain) (hxG : x ∈ (G).domain),
      H s ⟨x, hxs⟩ = T ⟨x, hxT⟩ + (Real.exp (2 * s) : ℂ) • (K ⟨x, hxK⟩ + P ⟨x, hxP⟩) ∧
      H t ⟨x, hxt⟩ = T ⟨x, hxT⟩ + (Real.exp (2 * t) : ℂ) • (K ⟨x, hxK⟩ + P ⟨x, hxP⟩) ∧
      H t ⟨x, hxt⟩ - H s ⟨x, hxs⟩ =
        ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) • G ⟨x, hxG⟩ ∧
      H t ⟨x, hxt⟩ - H s ⟨x, hxs⟩ =
        ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) • (K ⟨x, hxK⟩ + P ⟨x, hxP⟩) := by
  have hs := positive_vacuum_three_operator_hamiltonian_eval ε hε h hh hb m g k hk s hxT hxK hxP
  have ht := positive_vacuum_three_operator_hamiltonian_eval ε hε h hh hb m g k hk t hxT hxK hxP
  have hg := unconditional_two_operator_growing_eval ε hε h hh hb m g k hxK hxP
  have hdiff : H t ⟨x, ht.choose⟩ - H s ⟨x, hs.choose⟩ =
      ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) • (K ⟨x, hxK⟩ + P ⟨x, hxP⟩) := by
    rw [ht.choose_spec, hs.choose_spec, Complex.ofReal_sub, sub_smul]
    abel
  refine ⟨hs.choose, ht.choose, hg.choose, hs.choose_spec, ht.choose_spec, ?_, hdiff⟩
  rw [hdiff, hg.choose_spec]

theorem positive_vacuum_hamiltonian_growing_two_time_transfer (hk : 0 < k) (s t : ℝ)
    {x : Hilbert} (hxs : x ∈ (H s).domain) (hxG : x ∈ (G).domain) :
    x ∈ (T).domain ∧ x ∈ (K).domain ∧ x ∈ (P).domain ∧ x ∈ (clockHalf ε).domain ∧
      ∃ hxt : x ∈ (H t).domain,
        H t ⟨x, hxt⟩ = H s ⟨x, hxs⟩ +
          ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) • G ⟨x, hxG⟩ ∧
        H t ⟨x, hxt⟩ - H s ⟨x, hxs⟩ =
          ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) • G ⟨x, hxG⟩ := by
  have hmem : x ∈ (T).domain ⊓ (K).domain ⊓ (P).domain := by
    rw [← positive_vacuum_hamiltonian_inter_growing_domain_eq ε hε h hh hb m g k hk s]
    exact ⟨hxs, hxG⟩
  have hxT : x ∈ (T).domain := hmem.1.1
  have hxK : x ∈ (K).domain := hmem.1.2
  have hxP : x ∈ (P).domain := hmem.2
  have hxC : x ∈ (clockHalf ε).domain := static_domain_le_clockHalf_domain ε hε h hxT
  have hev := positive_vacuum_two_time_hamiltonian_eval
    ε hε h hh hb m g k hk s t hxT hxK hxP
  let hxt := hev.choose_spec.choose
  have hspec := hev.choose_spec.choose_spec.choose_spec
  have hsub : H t ⟨x, hxt⟩ - H s ⟨x, hxs⟩ =
      ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) • G ⟨x, hxG⟩ := hspec.2.2.1
  refine ⟨hxT, hxK, hxP, hxC, hxt, ?_, hsub⟩
  rw [← hsub]
  abel

theorem positive_vacuum_two_time_shifted_resolvent_identity (hk : 0 < k)
    (s t a : ℝ) (ha : 0 < a) {x : Hilbert}
    (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    ∃ (hxs : x ∈ (H s).domain) (hxG : x ∈ (G).domain),
      (x : Hilbert) - RH t a (H s ⟨x, hxs⟩ + a • x) =
        ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) • RH t a (G ⟨x, hxG⟩) ∧
      (x : Hilbert) - RH t a (H s ⟨x, hxs⟩ + a • x) =
        ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) • RH t a (K ⟨x, hxK⟩ + P ⟨x, hxP⟩) := by
  have hx : x ∈ commonOperatorDomain ε hε h hh hb m g k := by
    rw [positive_vacuum_common_domain_eq_three_operator ε hε h hh hb m g k hk]
    exact ⟨⟨hxT, hxK⟩, hxP⟩
  have hxs : x ∈ (H s).domain :=
    KFCausalClockFloorUnconditionalTwoTimeEvolution.common_domain_subset_hamiltonian
      ε hε h hh hb m g k s hx
  have hxG : x ∈ (G).domain :=
    KFCausalClockFloorUnconditionalTwoTimeEvolution.common_domain_subset_growing
      ε hε h hh hb m g k hx
  have hid1 := KFCausalClockFloorTwoTimeResolventDifference.hamiltonian_resolvent_two_time_action_sub
    ε hε h hh hb m g k t s a ha x hx
  have hid2 := KFCausalClockFloorTwoTimeResolventDifference.hamiltonian_resolvent_two_time_three_operator_sub
    ε hε h hh hb m g k t s a ha x hx
  exact ⟨hxs, hxG, hid1, hid2⟩

theorem positive_vacuum_two_time_residual_shifted_resolvent_identity (hk : 0 < k)
    (s t a : ℝ) (ha : 0 < a) {x : Hilbert}
    (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    ∃ hxs : x ∈ (S s).domain,
      (x : Hilbert) - RS t a (S s ⟨x, hxs⟩ + a • x) =
        ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) • RS t a (P ⟨x, hxP⟩) := by
  have hx : x ∈ commonOperatorDomain ε hε h hh hb m g k := by
    rw [positive_vacuum_common_domain_eq_three_operator ε hε h hh hb m g k hk]
    exact ⟨⟨hxT, hxK⟩, hxP⟩
  have hxs : x ∈ (S s).domain :=
    KFCausalClockFloorUnconditionalTwoTimeEvolution.common_domain_subset_residual
      ε hε h hh hb m g k s hx
  have hid := KFCausalClockFloorTwoTimeResolventDifference.residual_resolvent_two_time_action_sub
    ε hε h hh hb m g k t s a ha x hx
  exact ⟨hxs, hid⟩

theorem two_time_resolvent_all_domains (s t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RH s a f ∈ (H s).domain ∧
    RH s a f ∈ (K).domain ∧
    RH s a f ∈ (S s).domain ∧
    RH s a f ∈ (Eavg t).domain ∧
    RH s a f ∈ (Tres t).domain ∧
    RH s a f ∈ (Tstat).domain ∧
    RH s a f ∈ (Kroot).domain ∧
    RH s a f ∈ (Tpot).domain ∧
    RH s a f ∈ (Tgrow).domain ∧
    RH s a f ∈ (clockHalf ε).domain := by
  have hH : RH s a f ∈ (H s).domain :=
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k s a ha f).1
  have hKS := (KFCausalClockFloorHamiltonianRadialSum.domain_iff
    ε hε h hh hb m g k s (RH s a f)).mp hH
  have hEs : RH s a f ∈ (Eavg s).domain :=
    KFCausalClockFloorUnconditionalOperatorFormEnergy.hamiltonian_mem_averaged_domain
      ε hε h hh hb m g k s ⟨RH s a f, hH⟩
  have hE : RH s a f ∈ (Eavg t).domain :=
    (KFCausalClockFloorUnconditionalFormDomainSynthesis.averaged_domain_time_eq
      ε hε h hh hb m g k s t (RH s a f)).mp hEs
  have hRr := (KFCausalClockFloorResidualFormReconstruction.averaged_domain_eq_root_inter_residual
    ε hε h hh hb m g k t (RH s a f)).mp hE
  have hGr := (KFCausalClockFloorResidualFormReconstruction.averaged_domain_eq_growing_inter_residual
    ε hε h hh hb m g k t (RH s a f)).mp hE
  have h3 := KFCausalClockFloorUnconditionalFormDomainSynthesis.averaged_domain_subset_three_forms
    ε hε h hh hb m g k t (RH s a f) hE
  exact ⟨hH, hKS.1, hKS.2, hE, hRr.2, h3.1, h3.2.1, h3.2.2, hGr.1,
    static_root_subset_clockHalf_domain ε hε h (RH s a f) h3.1⟩

theorem positive_vacuum_two_time_second_resolvent_on_growing_domain (hk : 0 < k)
    (s t a : ℝ) (ha : 0 < a) (f : Hilbert) (hG : RH s a f ∈ (G).domain) :
    RH s a f ∈ (H t).domain ∧
      RH s a f - RH t a f =
        ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) • RH t a (G ⟨RH s a f, hG⟩) := by
  have hHs : RH s a f ∈ (H s).domain :=
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k s a ha f).1
  have htr := positive_vacuum_hamiltonian_growing_two_time_transfer
    ε hε h hh hb m g k hk s t hHs hG
  have hxt : RH s a f ∈ (H t).domain := htr.2.2.2.2.choose
  have hx : RH s a f ∈ commonOperatorDomain ε hε h hh hb m g k := by
    rw [positive_vacuum_common_domain_eq_three_operator ε hε h hh hb m g k hk]
    exact ⟨⟨htr.1, htr.2.1⟩, htr.2.2.1⟩
  have hid := KFCausalClockFloorTwoTimeResolventDifference.hamiltonian_resolvent_two_time_action_sub
    ε hε h hh hb m g k t s a ha (RH s a f) hx
  have hres := (KFCausalClockFloorHamiltonianClockCore.resolves
    ε hε h hh hw m g k s a ha f).2
  have hval : H s ⟨RH s a f,
      KFCausalClockFloorUnconditionalTwoTimeEvolution.common_domain_subset_hamiltonian
        ε hε h hh hb m g k s hx⟩ + a • RH s a f = f := by
    have heq : H s ⟨RH s a f,
        KFCausalClockFloorUnconditionalTwoTimeEvolution.common_domain_subset_hamiltonian
          ε hε h hh hb m g k s hx⟩ = H s ⟨RH s a f, hHs⟩ := rfl
    rw [heq, hres]
    abel
  refine ⟨hxt, ?_⟩
  rw [hval] at hid
  exact hid

/-! ### 5. Positive-Vacuum Three-Operator Graph Cores and Multi-Channel Static Approximations -/

def threeOperatorDomain : Submodule ℂ Hilbert :=
  (T).domain ⊓ (K).domain ⊓ (P).domain

def staticThreeOperatorGraph : Submodule ℂ (Hilbert × Hilbert) :=
  (T).graph ⊓ (threeOperatorDomain ε hε h hh hb m g k).comap
    (LinearMap.fst ℂ Hilbert Hilbert)

def staticHamiltonianThreeOperatorGraph (t : ℝ) : Submodule ℂ (Hilbert × Hilbert) :=
  (KFCausalClockFloorStaticHamiltonian.hamiltonian ε hε h hh hw m g k t).graph ⊓
    (threeOperatorDomain ε hε h hh hb m g k).comap (LinearMap.fst ℂ Hilbert Hilbert)

theorem static_three_operator_graph_core :
    (staticThreeOperatorGraph ε hε h hh hb m g k).topologicalClosure = (T).graph :=
  KFCausalClockFloorStaticThreeOperatorCore.three_operator_static_graph_core
    ε hε h hh hb m g k

theorem static_hamiltonian_three_operator_graph_core (t : ℝ) :
    (staticHamiltonianThreeOperatorGraph ε hε h hh hb m g k t).topologicalClosure =
      (KFCausalClockFloorStaticHamiltonian.hamiltonian ε hε h hh hw m g k t).graph := by
  unfold staticHamiltonianThreeOperatorGraph
  rw [KFCausalClockFloorStaticHamiltonian.hamiltonian_eq_operator ε hε h hh hw m g k t]
  exact static_three_operator_graph_core ε hε h hh hb m g k

theorem positive_vacuum_hamiltonian_growing_static_graph_core (hk : 0 < k) (t : ℝ) :
    ((T).graph ⊓ ((H t).domain ⊓ (G).domain).comap
      (LinearMap.fst ℂ Hilbert Hilbert)).topologicalClosure = (T).graph := by
  rw [positive_vacuum_hamiltonian_inter_growing_domain_eq ε hε h hh hb m g k hk t]
  exact static_three_operator_graph_core ε hε h hh hb m g k

private theorem tendsto_zero_of_sq_le_two_mul_norm {X : Type*} [NormedAddCommGroup X]
    {v : ℕ → X} {a b : ℕ → Hilbert}
    (ha : Tendsto a atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 0))
    (hsq : ∀ n, ‖v n‖ ^ 2 ≤ 2 * (‖a n‖ * ‖b n‖)) :
    Tendsto v atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hprod : Tendsto (fun n => Real.sqrt (2 * (‖a n‖ * ‖b n‖))) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n => 2 * (‖a n‖ * ‖b n‖)) atTop (𝓝 0) := by
      simpa using ((tendsto_zero_iff_norm_tendsto_zero.mp ha).mul
        (tendsto_zero_iff_norm_tendsto_zero.mp hb)).const_mul 2
    simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hprod
    (fun n => norm_nonneg (v n)) (fun n => ?_)
  have h1 := Real.sqrt_le_sqrt (hsq n)
  rwa [Real.sqrt_sq (norm_nonneg (v n))] at h1

theorem exists_three_operator_seq_tendsto_static_and_clockHalf (hk : 0 < k)
    (x : (T).domain) :
    ∃ u : ℕ → Hilbert,
      ∃ (hT : ∀ n, u n ∈ (T).domain) (hK : ∀ n, u n ∈ (K).domain)
        (hP : ∀ n, u n ∈ (P).domain) (hG : ∀ n, u n ∈ (G).domain)
        (hC : ∀ n, u n ∈ (clockHalf ε).domain)
        (hR : ∀ n, u n ∈ (Tstat).domain)
        (hS : ∀ (t : ℝ) (n : ℕ), u n ∈ (S t).domain)
        (hH : ∀ (t : ℝ) (n : ℕ), u n ∈ (H t).domain),
        Tendsto u atTop (𝓝 (x : Hilbert)) ∧
        Tendsto (fun n => T ⟨u n, hT n⟩) atTop (𝓝 (T x)) ∧
        Tendsto (fun n => Tstat ⟨u n, hR n⟩) atTop
          (𝓝 (Tstat ⟨(x : Hilbert), KFCausalClockFloorStaticOperator.root_domain ε hε h x⟩)) ∧
        Tendsto (fun n => clockHalf ε ⟨u n, hC n⟩) atTop
          (𝓝 (clockHalf ε ⟨(x : Hilbert), static_domain_le_clockHalf_domain ε hε h x.property⟩)) ∧
        (∀ n, G ⟨u n, hG n⟩ = K ⟨u n, hK n⟩ + P ⟨u n, hP n⟩) ∧
        (∀ t n, S t ⟨u n, hS t n⟩ = T ⟨u n, hT n⟩ + (Real.exp (2 * t) : ℂ) • P ⟨u n, hP n⟩) ∧
        (∀ t n, H t ⟨u n, hH t n⟩ =
          T ⟨u n, hT n⟩ + (Real.exp (2 * t) : ℂ) • (K ⟨u n, hK n⟩ + P ⟨u n, hP n⟩)) := by
  let hseq := KFCausalClockFloorStaticThreeOperatorCore.exists_common_operator_clock_seq_tendsto_static
    ε hε h hh hb m g k x
  let u := Classical.choose hseq
  have hu_spec := Classical.choose_spec hseq
  let hmem := Classical.choose hu_spec
  have hlim := Classical.choose_spec hu_spec
  have hT : ∀ n, u n ∈ (T).domain := fun n => (hmem n).1.1.1.1
  have hK : ∀ n, u n ∈ (K).domain := fun n => (hmem n).1.1.1.2
  have hP : ∀ n, u n ∈ (P).domain := fun n => (hmem n).1.1.2
  have hG : ∀ n, u n ∈ (G).domain := fun n =>
    (unconditional_two_operator_growing_eval ε hε h hh hb m g k (hK n) (hP n)).choose
  have hC : ∀ n, u n ∈ (clockHalf ε).domain := fun n =>
    static_domain_le_clockHalf_domain ε hε h (hT n)
  have hR : ∀ n, u n ∈ (Tstat).domain := fun n =>
    KFCausalClockFloorStaticOperator.root_domain ε hε h ⟨u n, hT n⟩
  have hS : ∀ (t : ℝ) (n : ℕ), u n ∈ (S t).domain := fun t n =>
    (positive_vacuum_three_operator_residual_eval ε hε h hh hb m g k hk t (hT n) (hK n) (hP n)).choose
  have hH : ∀ (t : ℝ) (n : ℕ), u n ∈ (H t).domain := fun t n =>
    (positive_vacuum_three_operator_hamiltonian_eval ε hε h hh hb m g k hk t (hT n) (hK n) (hP n)).choose
  have ha0 : Tendsto (fun n => u n - (x : Hilbert)) atTop (𝓝 0) :=
    tendsto_sub_nhds_zero_iff.mpr hlim.1
  have hb0 : Tendsto (fun n => T ⟨u n, hT n⟩ - T x) atTop (𝓝 0) :=
    tendsto_sub_nhds_zero_iff.mpr hlim.2
  let xr : (Tstat).domain := ⟨(x : Hilbert), KFCausalClockFloorStaticOperator.root_domain ε hε h x⟩
  let xc : (clockHalf ε).domain :=
    ⟨(x : Hilbert), static_domain_le_clockHalf_domain ε hε h x.property⟩
  have hR_lim : Tendsto (fun n => Tstat ⟨u n, hR n⟩) atTop (𝓝 (Tstat xr)) := by
    apply tendsto_sub_nhds_zero_iff.mp
    refine tendsto_zero_of_sq_le_two_mul_norm ha0 hb0 (fun n => ?_)
    let dT : (T).domain := ⟨u n, hT n⟩ - x
    have hsubR : Tstat ⟨u n, hR n⟩ - Tstat xr =
        Tstat ⟨(dT : Hilbert), KFCausalClockFloorStaticOperator.root_domain ε hε h dT⟩ :=
      ((Tstat).map_sub ⟨u n, hR n⟩ xr).symm
    have hsubT : T dT = T ⟨u n, hT n⟩ - T x := (T).map_sub ⟨u n, hT n⟩ x
    have h1 := static_operator_root_norm_sq_le ε hε h dT
    have h2 : 0 ≤ ‖(dT : Hilbert)‖ * ‖T dT‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    change ‖Tstat ⟨u n, hR n⟩ - Tstat xr‖ ^ 2 ≤ 2 * (‖(dT : Hilbert)‖ * ‖T ⟨u n, hT n⟩ - T x‖)
    rw [hsubR, ← hsubT]
    linarith
  have hC_lim : Tendsto (fun n => clockHalf ε ⟨u n, hC n⟩) atTop (𝓝 (clockHalf ε xc)) := by
    apply tendsto_sub_nhds_zero_iff.mp
    refine tendsto_zero_of_sq_le_two_mul_norm ha0 hb0 (fun n => ?_)
    let dT : (T).domain := ⟨u n, hT n⟩ - x
    have hsubC : clockHalf ε ⟨u n, hC n⟩ - clockHalf ε xc =
        clockHalf ε ⟨(dT : Hilbert), static_domain_le_clockHalf_domain ε hε h dT.property⟩ :=
      ((clockHalf ε).map_sub ⟨u n, hC n⟩ xc).symm
    have hsubT : T dT = T ⟨u n, hT n⟩ - T x := (T).map_sub ⟨u n, hT n⟩ x
    change ‖clockHalf ε ⟨u n, hC n⟩ - clockHalf ε xc‖ ^ 2 ≤
      2 * (‖(dT : Hilbert)‖ * ‖T ⟨u n, hT n⟩ - T x‖)
    rw [hsubC, ← hsubT]
    exact static_operator_clockHalf_norm_sq_le ε hε h dT
  exact ⟨u, hT, hK, hP, hG, hC, hR, hS, hH, hlim.1, hlim.2, hR_lim, hC_lim,
    fun n => (unconditional_two_operator_growing_eval ε hε h hh hb m g k (hK n) (hP n)).choose_spec,
    fun t n => (positive_vacuum_three_operator_residual_eval
      ε hε h hh hb m g k hk t (hT n) (hK n) (hP n)).choose_spec,
    fun t n => (positive_vacuum_three_operator_hamiltonian_eval
      ε hε h hh hb m g k hk t (hT n) (hK n) (hP n)).choose_spec⟩

#print axioms static_root_subset_clockHalf_domain
#print axioms static_root_clockHalf_norm_le
#print axioms static_root_clockHalf_norm_sq_le
#print axioms static_root_domain_le_clockHalf_domain
#print axioms static_domain_le_clockHalf_domain
#print axioms static_operator_root_norm_sq_eq
#print axioms static_operator_root_norm_sq_le
#print axioms static_operator_clockHalf_norm_sq_le
#print axioms residual_form_domain_le_clockHalf_domain
#print axioms averaged_form_domain_le_clockHalf_domain
#print axioms residual_domain_le_clockHalf_domain
#print axioms hamiltonian_domain_le_clockHalf_domain
#print axioms commonOperatorDomain_le_clockHalf_domain
#print axioms commonOperatorDomain_inf_clockHalf_eq
#print axioms three_operator_domain_le_clockHalf_domain
#print axioms three_operator_domain_inf_clockHalf_eq
#print axioms residual_graph_transport
#print axioms residual_form_domain_time_iff
#print axioms residual_form_domain_time_eq
#print axioms residual_form_domain_eq_zero
#print axioms averaged_form_domain_time_eq
#print axioms averaged_form_domain_eq_zero
#print axioms commonOperatorDomain_eq_time
#print axioms positive_vacuum_averaged_form_domain_iff
#print axioms positive_vacuum_averaged_form_domain_eq
#print axioms positive_vacuum_averaged_form_domain_eq_static_inter_growing
#print axioms unconditional_two_operator_growing_eval
#print axioms positive_vacuum_three_operator_hamiltonian_eval
#print axioms positive_vacuum_three_operator_residual_eval
#print axioms positive_vacuum_three_operator_in_averaged_domain
#print axioms positive_vacuum_three_operator_in_residual_domain
#print axioms positive_vacuum_common_domain_eq_three_operator
#print axioms positive_vacuum_common_domain_inf_clockHalf_eq
#print axioms positive_vacuum_static_inter_growing_domain_eq
#print axioms positive_vacuum_hamiltonian_inter_growing_domain_eq
#print axioms positive_vacuum_hamiltonian_inter_static_domain_eq
#print axioms positive_vacuum_hamiltonian_inter_potential_domain_eq
#print axioms positive_vacuum_residual_inter_growing_domain_eq
#print axioms positive_vacuum_two_time_hamiltonian_growing_domain_eq
#print axioms positive_vacuum_two_time_hamiltonian_static_domain_eq
#print axioms positive_vacuum_two_time_hamiltonian_potential_domain_eq
#print axioms positive_vacuum_two_time_residual_growing_domain_eq
#print axioms positive_vacuum_two_time_residual_eval
#print axioms positive_vacuum_two_time_hamiltonian_eval
#print axioms positive_vacuum_hamiltonian_growing_two_time_transfer
#print axioms positive_vacuum_two_time_shifted_resolvent_identity
#print axioms positive_vacuum_two_time_residual_shifted_resolvent_identity
#print axioms two_time_resolvent_all_domains
#print axioms positive_vacuum_two_time_second_resolvent_on_growing_domain
#print axioms static_three_operator_graph_core
#print axioms static_hamiltonian_three_operator_graph_core
#print axioms positive_vacuum_hamiltonian_growing_static_graph_core
#print axioms exists_three_operator_seq_tendsto_static_and_clockHalf
end
end UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumTwoTimeOperatorDomain
