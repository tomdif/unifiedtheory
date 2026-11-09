/- Complex clock-Gaussian multipliers commute with the bounded inverse
half-clock and the bounded clock-defect operator, preserve the unbounded
half-clock and full-clock domains with exact commutation for all nonnegative
widths, and map every L2 vector into both the half-clock and full-clock domains
whenever the Gaussian width is strictly positive. Consequently, on the
intersection of the unconditional multi-operator domain with the half-clock
domain, the centered clock-Gaussian sequence preserves all seven domains and
converges strongly in Hilbert norm, in the half-clock graph, and across all six
static, radial, potential, growing, residual, and full Hamiltonians. -/
import UnifiedTheory.Audit.KFCausalClockFloorGaussianUnconditionalMultiOperatorApproximation
import UnifiedTheory.Audit.KFCausalClockFloorClockOperator
import UnifiedTheory.Audit.KFCausalClockFloorPureClockClockResponse

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGaussianClockCommutation
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalRegularizedLongitudinalChart (chart)
open KFCausalClockFloorFlow (clock)
open KFCausalClockFloorCanonicalDefect (clock_positive defect)
open KFCausalClockFloorClockHalf (halfWeight halfWeight_measurable halfWeight_positive
  clockHalf inverseAction_coe)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorDefectOperator (defectOperator defectOperator_coe)
open KFCausalClockFloorClockOperator (clockWeight_measurable clockOperator
  clock_defect_graph defect_clock)
open KFCausalClockFloorPureClockClockResponse (half_graph)
open KFCausalUnitaryPositiveMultiplier (pullback_domain_iff)
open KFCausalClockFloorGaussianGrowingTransport
  (gaussian centered line gaussian_norm action action_coe)
open KFCausalClockFloorGaussianGrowingApproximation (action_tendsto sequence_tendsto)
open KFCausalClockFloorGaussianMultiOperatorApproximation
  (component_graphs growing_sum_graph multi_operator_tendsto)
open KFCausalClockFloorGaussianUnconditionalMultiOperatorApproximation
  (unconditional_graphs unconditional_sequence_multi_operator_approximation)

private theorem abs_mul_exp_neg_sq_le (a : ℝ) (ha : 0 < a) (q : ℝ) :
    |q| * Real.exp (-a * q ^ 2) ≤ (a + 1) / a := by
  have hq : |q| ≤ 1 + q ^ 2 := by
    nlinarith [sq_nonneg (|q| - 1), sq_abs q]
  have haq : a * |q| ≤ a + a * q ^ 2 := by nlinarith
  have hexp1 : a * q ^ 2 + 1 ≤ Real.exp (a * q ^ 2) :=
    Real.add_one_le_exp (a * q ^ 2)
  have hexp0 : 1 ≤ Real.exp (a * q ^ 2) :=
    Real.one_le_exp (mul_nonneg ha.le (sq_nonneg q))
  have hlin : a * |q| ≤ (a + 1) * Real.exp (a * q ^ 2) := by nlinarith
  have hprod : Real.exp (a * q ^ 2) * Real.exp (-a * q ^ 2) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hpos : 0 ≤ Real.exp (-a * q ^ 2) := (Real.exp_pos _).le
  apply (le_div_iff₀ ha).mpr
  calc
    |q| * Real.exp (-a * q ^ 2) * a = (a * |q|) * Real.exp (-a * q ^ 2) := by ring
    _ ≤ ((a + 1) * Real.exp (a * q ^ 2)) * Real.exp (-a * q ^ 2) :=
      mul_le_mul_of_nonneg_right hlin hpos
    _ = (a + 1) * (Real.exp (a * q ^ 2) * Real.exp (-a * q ^ 2)) := by ring
    _ = a + 1 := by rw [hprod, mul_one]

private theorem clock_le_chart (ε : ℝ) (hε : 0 < ε) (s : ℝ) :
    clock ε s ≤ 1 + ε + |chart ε s| := by
  unfold clock chart
  by_cases hs : s ≤ 0
  · have he : Real.exp s ≤ 1 := Real.exp_le_one_iff.mpr hs
    have ha : 0 ≤ |Real.exp s + ε * s| := abs_nonneg _
    linarith
  · push_neg at hs
    have hm : 0 ≤ ε * s := mul_nonneg hε.le hs.le
    have ha : Real.exp s + ε * s ≤ |Real.exp s + ε * s| := le_abs_self _
    linarith

private theorem line_norm_eq (ε a y s : ℝ) :
    ‖line ε a y s‖ = Real.exp (a * y ^ 2) * Real.exp (-a * (chart ε s) ^ 2) := by
  unfold line centered
  rw [gaussian_norm]
  simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, sub_zero, add_zero, zero_add]
  rw [sub_eq_add_neg, Real.exp_add]
  ring_nf

variable (ε : ℝ) (hε : 0 < ε)

theorem clockOperator_graph_iff_defect (f g : Hilbert) :
    (f, g) ∈ (clockOperator ε hε).graph ↔ defectOperator ε hε g = (ε : ℂ) • f := by
  constructor
  · exact defect_clock ε hε f g
  · intro hd
    have hg := (clockOperator ε hε).graph.smul_mem (ε : ℂ)⁻¹ (clock_defect_graph ε hε g)
    change ((ε : ℂ)⁻¹ • defectOperator ε hε g, (ε : ℂ)⁻¹ • (ε : ℂ) • g) ∈
      (clockOperator ε hε).graph at hg
    have hc : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
    rw [hd, inv_smul_smul₀ hc, inv_smul_smul₀ hc] at hg
    exact hg

theorem gaussian_inverseL_commute (a : ℝ) (ha : 0 ≤ a) (y : ℝ) (f : Hilbert) :
    action ε a ha y (inverseL ε hε f) = inverseL ε hε (action ε a ha y f) := by
  apply Lp.ext
  filter_upwards [action_coe ε a ha y (inverseL ε hε f),
    inverseAction_coe ε hε f,
    inverseAction_coe ε hε (action ε a ha y f),
    action_coe ε a ha y f] with x h1 h2 h3 h4
  change (inverseL ε hε f) x = _ at h2
  change (inverseL ε hε (action ε a ha y f)) x = _ at h3
  rw [h1, h2, h3, h4]
  ring

theorem gaussian_defect_commute (a : ℝ) (ha : 0 ≤ a) (y : ℝ) (f : Hilbert) :
    action ε a ha y (defectOperator ε hε f) = defectOperator ε hε (action ε a ha y f) := by
  apply Lp.ext
  filter_upwards [action_coe ε a ha y (defectOperator ε hε f),
    defectOperator_coe ε hε f,
    defectOperator_coe ε hε (action ε a ha y f),
    action_coe ε a ha y f] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  ring

include hε in
theorem gaussian_clockHalf_graph (a : ℝ) (ha : 0 ≤ a) (y : ℝ) (f g : Hilbert)
    (hfg : (f, g) ∈ (clockHalf ε).graph) :
    (action ε a ha y f, action ε a ha y g) ∈ (clockHalf ε).graph := by
  rw [half_graph ε hε] at hfg ⊢
  rw [hfg, gaussian_inverseL_commute ε hε a ha y g]

include hε in
theorem gaussian_clockHalf_domain (a : ℝ) (ha : 0 ≤ a) (y : ℝ) (f : Hilbert)
    (hf : f ∈ (clockHalf ε).domain) :
    action ε a ha y f ∈ (clockHalf ε).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (gaussian_clockHalf_graph ε hε a ha y f (clockHalf ε ⟨f, hf⟩)
      ((clockHalf ε).mem_graph ⟨f, hf⟩))

include hε in
theorem gaussian_clockHalf_commute (a : ℝ) (ha : 0 ≤ a) (y : ℝ) (f : Hilbert)
    (hf : f ∈ (clockHalf ε).domain) :
    clockHalf ε ⟨action ε a ha y f, gaussian_clockHalf_domain ε hε a ha y f hf⟩ =
      action ε a ha y (clockHalf ε ⟨f, hf⟩) :=
  (clockHalf ε).mem_graph_snd_inj'
    ((clockHalf ε).mem_graph ⟨action ε a ha y f, gaussian_clockHalf_domain ε hε a ha y f hf⟩)
    (gaussian_clockHalf_graph ε hε a ha y f (clockHalf ε ⟨f, hf⟩)
      ((clockHalf ε).mem_graph ⟨f, hf⟩)) rfl

include hε in
theorem gaussian_clockHalf_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (y : ℝ) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hz : Tendsto a l (𝓝 0))
    (f : Hilbert) (hf : f ∈ (clockHalf ε).domain) :
    Tendsto (fun i =>
      clockHalf ε ⟨action ε (a i) (ha i) y f,
        gaussian_clockHalf_domain ε hε (a i) (ha i) y f hf⟩)
      l (𝓝 (clockHalf ε ⟨f, hf⟩)) :=
  (action_tendsto ε y a ha hz (clockHalf ε ⟨f, hf⟩)).congr'
    (Eventually.of_forall (fun i =>
      (gaussian_clockHalf_commute ε hε (a i) (ha i) y f hf).symm))

include hε in
theorem gaussian_clockHalf_sequence_tendsto (y : ℝ) (f : Hilbert)
    (hf : f ∈ (clockHalf ε).domain) :
    Tendsto (fun n : ℕ =>
      clockHalf ε ⟨action ε (((n : ℝ) + 1)⁻¹) (by positivity) y f,
        gaussian_clockHalf_domain ε hε (((n : ℝ) + 1)⁻¹) (by positivity) y f hf⟩)
      atTop (𝓝 (clockHalf ε ⟨f, hf⟩)) :=
  (sequence_tendsto ε y (clockHalf ε ⟨f, hf⟩)).congr'
    (Eventually.of_forall (fun n =>
      (gaussian_clockHalf_commute ε hε (((n : ℝ) + 1)⁻¹) (by positivity) y f hf).symm))

theorem gaussian_clockOperator_graph (a : ℝ) (ha : 0 ≤ a) (y : ℝ) (f g : Hilbert)
    (hfg : (f, g) ∈ (clockOperator ε hε).graph) :
    (action ε a ha y f, action ε a ha y g) ∈ (clockOperator ε hε).graph := by
  rw [clockOperator_graph_iff_defect ε hε] at hfg ⊢
  rw [← gaussian_defect_commute ε hε a ha y g, hfg, map_smul]

theorem gaussian_clockOperator_domain (a : ℝ) (ha : 0 ≤ a) (y : ℝ) (f : Hilbert)
    (hf : f ∈ (clockOperator ε hε).domain) :
    action ε a ha y f ∈ (clockOperator ε hε).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (gaussian_clockOperator_graph ε hε a ha y f (clockOperator ε hε ⟨f, hf⟩)
      ((clockOperator ε hε).mem_graph ⟨f, hf⟩))

theorem gaussian_clockOperator_commute (a : ℝ) (ha : 0 ≤ a) (y : ℝ) (f : Hilbert)
    (hf : f ∈ (clockOperator ε hε).domain) :
    clockOperator ε hε ⟨action ε a ha y f, gaussian_clockOperator_domain ε hε a ha y f hf⟩ =
      action ε a ha y (clockOperator ε hε ⟨f, hf⟩) :=
  (clockOperator ε hε).mem_graph_snd_inj'
    ((clockOperator ε hε).mem_graph
      ⟨action ε a ha y f, gaussian_clockOperator_domain ε hε a ha y f hf⟩)
    (gaussian_clockOperator_graph ε hε a ha y f (clockOperator ε hε ⟨f, hf⟩)
      ((clockOperator ε hε).mem_graph ⟨f, hf⟩)) rfl

theorem gaussian_clockOperator_sequence_tendsto (y : ℝ) (f : Hilbert)
    (hf : f ∈ (clockOperator ε hε).domain) :
    Tendsto (fun n : ℕ =>
      clockOperator ε hε ⟨action ε (((n : ℝ) + 1)⁻¹) (by positivity) y f,
        gaussian_clockOperator_domain ε hε (((n : ℝ) + 1)⁻¹) (by positivity) y f hf⟩)
      atTop (𝓝 (clockOperator ε hε ⟨f, hf⟩)) :=
  (sequence_tendsto ε y (clockOperator ε hε ⟨f, hf⟩)).congr'
    (Eventually.of_forall (fun n =>
      (gaussian_clockOperator_commute ε hε (((n : ℝ) + 1)⁻¹) (by positivity) y f hf).symm))

include hε in
theorem clock_mul_line_bound (a : ℝ) (ha : 0 < a) (y s : ℝ) :
    clock ε s * ‖line ε a y s‖ ≤ (1 + ε + (a + 1) / a) * Real.exp (a * y ^ 2) := by
  rw [line_norm_eq]
  have hc := clock_le_chart ε hε s
  have hq := abs_mul_exp_neg_sq_le a ha (chart ε s)
  have he1 : Real.exp (-a * (chart ε s) ^ 2) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith [sq_nonneg (chart ε s)]
  have hmid : clock ε s * Real.exp (-a * (chart ε s) ^ 2) ≤ 1 + ε + (a + 1) / a := by
    calc
      clock ε s * Real.exp (-a * (chart ε s) ^ 2) ≤
          (1 + ε + |chart ε s|) * Real.exp (-a * (chart ε s) ^ 2) :=
        mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
      _ = (1 + ε) * Real.exp (-a * (chart ε s) ^ 2) +
          |chart ε s| * Real.exp (-a * (chart ε s) ^ 2) := by ring
      _ ≤ (1 + ε) * 1 + (a + 1) / a :=
        add_le_add (mul_le_mul_of_nonneg_left he1 (by positivity)) hq
      _ = 1 + ε + (a + 1) / a := by ring
  calc
    clock ε s * (Real.exp (a * y ^ 2) * Real.exp (-a * (chart ε s) ^ 2)) =
        (clock ε s * Real.exp (-a * (chart ε s) ^ 2)) * Real.exp (a * y ^ 2) := by ring
    _ ≤ (1 + ε + (a + 1) / a) * Real.exp (a * y ^ 2) :=
      mul_le_mul_of_nonneg_right hmid (Real.exp_pos _).le

include hε in
theorem halfWeight_mul_line_bound (a : ℝ) (ha : 0 < a) (y : ℝ) (x : Configuration) :
    halfWeight ε x * ‖line ε a y x.1‖ ≤
      (2 + ε + (a + 1) / a) * Real.exp (a * y ^ 2) := by
  have hc0 : 0 ≤ clock ε x.1 := (clock_positive ε x.1 hε.le).le
  have hsq : halfWeight ε x ^ 2 = clock ε x.1 := Real.sq_sqrt hc0
  have hle : halfWeight ε x ≤ 1 + clock ε x.1 := by
    nlinarith [sq_nonneg (halfWeight ε x - 1), hsq]
  have hline : ‖line ε a y x.1‖ ≤ Real.exp (a * y ^ 2) := by
    rw [line_norm_eq]
    have he1 : Real.exp (-a * (chart ε x.1) ^ 2) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith [sq_nonneg (chart ε x.1)]
    nlinarith [Real.exp_pos (a * y ^ 2)]
  have hclock := clock_mul_line_bound ε hε a ha y x.1
  calc
    halfWeight ε x * ‖line ε a y x.1‖ ≤
        (1 + clock ε x.1) * ‖line ε a y x.1‖ :=
      mul_le_mul_of_nonneg_right hle (norm_nonneg _)
    _ = ‖line ε a y x.1‖ + clock ε x.1 * ‖line ε a y x.1‖ := by ring
    _ ≤ Real.exp (a * y ^ 2) + (1 + ε + (a + 1) / a) * Real.exp (a * y ^ 2) :=
      add_le_add hline hclock
    _ = (2 + ε + (a + 1) / a) * Real.exp (a * y ^ 2) := by ring

theorem gaussian_mem_clockOperator_domain_of_pos (a : ℝ) (ha : 0 < a) (y : ℝ) (f : Hilbert) :
    action ε a ha.le y f ∈ (clockOperator ε hε).domain := by
  apply (pullback_domain_iff (LinearIsometryEquiv.refl ℂ Hilbert)
    (fun x : Configuration => clock ε x.1) (clockWeight_measurable ε)
    (fun x => (clock_positive ε x.1 hε.le).le) (action ε a ha.le y f)).mpr
  let C := (1 + ε + (a + 1) / a) * Real.exp (a * y ^ 2)
  have hC : 0 ≤ C := by positivity
  have hm : AEStronglyMeasurable
      (fun x : Configuration => (clock ε x.1 : ℂ) * (action ε a ha.le y f) x) volume :=
    ((Complex.measurable_ofReal.comp (clockWeight_measurable ε)).aestronglyMeasurable).mul
      (Lp.memLp (action ε a ha.le y f)).aestronglyMeasurable
  apply ((Lp.memLp f).const_mul (C : ℂ)).of_le hm
  filter_upwards [action_coe ε a ha.le y f] with x hx
  change ‖(clock ε x.1 : ℂ) * (action ε a ha.le y f) x‖ ≤ ‖(C : ℂ) * f x‖
  rw [hx, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (clock_positive ε x.1 hε.le).le, abs_of_nonneg hC, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (clock_mul_line_bound ε hε a ha y x.1) (norm_nonneg _)

include hε in
theorem gaussian_mem_clockHalf_domain_of_pos (a : ℝ) (ha : 0 < a) (y : ℝ) (f : Hilbert) :
    action ε a ha.le y f ∈ (clockHalf ε).domain := by
  apply (pullback_domain_iff (LinearIsometryEquiv.refl ℂ Hilbert)
    (halfWeight ε) (halfWeight_measurable ε)
    (fun _ => Real.sqrt_nonneg _) (action ε a ha.le y f)).mpr
  let C := (2 + ε + (a + 1) / a) * Real.exp (a * y ^ 2)
  have hC : 0 ≤ C := by positivity
  have hm : AEStronglyMeasurable
      (fun x : Configuration => (halfWeight ε x : ℂ) * (action ε a ha.le y f) x) volume :=
    ((Complex.measurable_ofReal.comp (halfWeight_measurable ε)).aestronglyMeasurable).mul
      (Lp.memLp (action ε a ha.le y f)).aestronglyMeasurable
  apply ((Lp.memLp f).const_mul (C : ℂ)).of_le hm
  filter_upwards [action_coe ε a ha.le y f] with x hx
  change ‖(halfWeight ε x : ℂ) * (action ε a ha.le y f) x‖ ≤ ‖(C : ℂ) * f x‖
  rw [hx, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (halfWeight_positive ε hε x).le, abs_of_nonneg hC, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (halfWeight_mul_line_bound ε hε a ha y x) (norm_nonneg _)

variable (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k t : ℝ)

local notation "hw" => KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k t
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k t
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k

def unconditionalDomain : Submodule ℂ Hilbert :=
  (T).domain ⊓ (K).domain ⊓ (P).domain ⊓ (Tres 0).domain

theorem unconditional_clock_domain_action (a : ℝ) (ha : 0 ≤ a) (f : Hilbert)
    (hu : f ∈ unconditionalDomain ε hε h hh hb m g k)
    (hc : f ∈ (clockHalf ε).domain) :
    action ε a ha 0 f ∈ unconditionalDomain ε hε h hh hb m g k ∧
      action ε a ha 0 f ∈ (clockHalf ε).domain := by
  have ht : (f, T ⟨f, hu.1.1.1⟩) ∈ (T).graph := (T).mem_graph ⟨f, hu.1.1.1⟩
  have hr : (f, K ⟨f, hu.1.1.2⟩) ∈ (K).graph := (K).mem_graph ⟨f, hu.1.1.2⟩
  have hp : (f, P ⟨f, hu.1.2⟩) ∈ (P).graph := (P).mem_graph ⟨f, hu.1.2⟩
  have hcomp := component_graphs ε hε h hh hb m g k a ha
    f (T ⟨f, hu.1.1.1⟩) (K ⟨f, hu.1.1.2⟩) (P ⟨f, hu.1.2⟩) ht hr hp
  have hres' := KFCausalClockFloorGaussianUnconditionalMultiOperatorApproximation.residual_form_domain_action
    ε hε a ha h hh hw 0 m g k 0 f hu.2
  exact ⟨⟨⟨⟨LinearPMap.mem_domain_of_mem_graph hcomp.1,
    LinearPMap.mem_domain_of_mem_graph hcomp.2.1⟩,
    LinearPMap.mem_domain_of_mem_graph hcomp.2.2⟩, hres'⟩,
    gaussian_clockHalf_domain ε hε a ha 0 f hc⟩

theorem unconditional_clock_sequence_multi_operator_approximation
    (f c y r z : Hilbert)
    (hc : (f, c) ∈ (clockHalf ε).graph)
    (ht : (f, y) ∈ (T).graph)
    (hr : (f, r) ∈ (K).graph)
    (hp : (f, z) ∈ (P).graph)
    (hf : f ∈ (Tres 0).domain) :
    (∀ n : ℕ,
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 c) ∈ (clockHalf ε).graph ∧
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y) ∈ (T).graph ∧
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r) ∈ (K).graph ∧
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z) ∈ (P).graph ∧
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r +
          action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z) ∈ (G).graph ∧
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y +
          (Real.exp (2 * t) : ℂ) • action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z) ∈ (S).graph ∧
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y +
          (Real.exp (2 * t) : ℂ) • (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r +
            action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z)) ∈ (H).graph) ∧
    Tendsto (fun n : ℕ =>
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
        (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 c,
          (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y,
            (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r,
              (action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z,
                (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r +
                  action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z,
                  (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y +
                    (Real.exp (2 * t) : ℂ) • action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z,
                    action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y +
                      (Real.exp (2 * t) : ℂ) • (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r +
                        action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z))))))))) atTop
      (𝓝 (f, (c, (y, (r, (z, (r + z, (y + (Real.exp (2 * t) : ℂ) • z,
        y + (Real.exp (2 * t) : ℂ) • (r + z))))))))) := by
  have hu := unconditional_sequence_multi_operator_approximation
    ε hε h hh m g k hb t f y r z ht hr hp hf
  refine ⟨fun n => ⟨gaussian_clockHalf_graph ε hε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f c hc,
    hu.1 n⟩, ?_⟩
  have hf_lim := sequence_tendsto ε 0 f
  have hc_lim := sequence_tendsto ε 0 c
  have hrest : Tendsto (fun n : ℕ =>
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y,
        (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r,
          (action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z,
            (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r +
              action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z,
              (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y +
                (Real.exp (2 * t) : ℂ) • action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z,
                action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y +
                  (Real.exp (2 * t) : ℂ) • (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r +
                    action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z))))))) atTop
      (𝓝 (y, (r, (z, (r + z, (y + (Real.exp (2 * t) : ℂ) • z,
        y + (Real.exp (2 * t) : ℂ) • (r + z))))))) :=
    (continuous_snd.tendsto _).comp hu.2
  exact hf_lim.prodMk_nhds (hc_lim.prodMk_nhds hrest)

#print axioms clockOperator_graph_iff_defect
#print axioms gaussian_inverseL_commute
#print axioms gaussian_defect_commute
#print axioms gaussian_clockHalf_graph
#print axioms gaussian_clockHalf_domain
#print axioms gaussian_clockHalf_commute
#print axioms gaussian_clockHalf_tendsto
#print axioms gaussian_clockHalf_sequence_tendsto
#print axioms gaussian_clockOperator_graph
#print axioms gaussian_clockOperator_domain
#print axioms gaussian_clockOperator_commute
#print axioms gaussian_clockOperator_sequence_tendsto
#print axioms clock_mul_line_bound
#print axioms halfWeight_mul_line_bound
#print axioms gaussian_mem_clockOperator_domain_of_pos
#print axioms gaussian_mem_clockHalf_domain_of_pos
#print axioms unconditional_clock_domain_action
#print axioms unconditional_clock_sequence_multi_operator_approximation
end
end UnifiedTheory.Audit.KFCausalClockFloorGaussianClockCommutation
