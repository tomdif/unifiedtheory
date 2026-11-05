/- Exact nonnegative physical cell weights and an incidence/Cauchy lower bound.
The denominator retains the full lattice volume. This is not an arbitrary-volume
continuum variance theorem; local occupied-cell counting is a separate task. -/
import UnifiedTheory.Clay.YangMills.WilsonPhysicalCellWeights
import UnifiedTheory.Clay.YangMills.WilsonInfluenceGeometry
import UnifiedTheory.Clay.YangMills.WilsonSingleLinkStaples
import Mathlib.Analysis.Calculus.BumpFunction.Normed

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonCellWeightLower
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 LocalFields
open WilsonIndependentBlocks SingleLinkWilsonOscillation WilsonInfluenceGeometry



/-- One fixed compactly supported smooth nonnegative test, independent of every regulator. -/
def witnessBump : ContDiffBump (0 : Spacetime) := ⟨1, 2, by norm_num, by norm_num⟩

def witnessTest : TestFunction :=
  ((witnessBump.hasCompactSupport_normed (μ := volume)).comp_left
    (show Complex.ofReal 0 = 0 by rfl)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp witnessBump.contDiff_normed)

@[simp] theorem witnessTest_apply (x : Spacetime) :
    witnessTest x = (witnessBump.normed volume x : ℂ) := rfl

theorem witnessTest_nonneg (x : Spacetime) : 0 ≤ (witnessTest x).re :=
  witnessBump.nonneg_normed x

theorem witnessTest_real (x : Spacetime) : (witnessTest x).im = 0 := rfl

theorem witnessTest_integral : (∫ x, witnessTest x) = 1 := by
  simp only [witnessTest_apply, integral_complex_ofReal,
    witnessBump.integral_normed, Complex.ofReal_one]

theorem witnessTest_compact : HasCompactSupport (witnessTest : Spacetime → ℂ) :=
  (witnessBump.hasCompactSupport_normed (μ := volume)).comp_left
    (show Complex.ofReal 0 = 0 by rfl)

/-- The fixed witness vanishes outside the radius-two ball. -/
theorem witnessTest_eq_zero_of_norm_ge (x : Spacetime) (hx : 2 ≤ ‖x‖) : witnessTest x = 0 := by
  have hn : x ∉ Function.support (witnessBump.normed volume) := by
    rw [witnessBump.support_normed_eq]
    simpa only [Metric.mem_ball, dist_zero_right, witnessBump] using not_lt.mpr hx
  simpa only [Function.mem_support, not_not, witnessTest_apply, Complex.ofReal_eq_zero] using hn

variable (n : ℕ) [NeZero n]

/-- Real nonnegative tests give nonnegative actual cell integrals, without a cell-volume premise. -/
theorem weight_nonneg (a : ℝ) (plane : Plane) (f : TestFunction)
    (hf : ∀ x, 0 ≤ (f x).re) (p : PlaquetteIndex n) :
    0 ≤ WilsonPhysicalCellWeights.weight n a plane f p := by
  letI : NormedSpace ℝ ℂ :=
    @InnerProductSpace.toNormedSpace ℝ ℂ _ _ instInnerProductSpaceRealComplex
  let L : ℂ →L[ℝ] ℝ :=
    { toFun := Complex.re
      map_add' := Complex.add_re
      map_smul' := by intro r z; simp
      cont := Complex.continuous_re }
  have hi := FiniteCellSmearing.cellFunction_integrable volume
    (PeriodicCellSampling.sample n a plane)
    (PeriodicCellSampling.sample_measurable n a plane) p f f.integrable
  have hre := L.integral_comp_comm hi
  unfold WilsonPhysicalCellWeights.weight FiniteCellSmearing.coefficient
  change 0 ≤ L (∫ x, FiniteCellSmearing.cellFunction
    (PeriodicCellSampling.sample n a plane) p f x)
  rw [← hre]
  apply integral_nonneg
  intro x
  dsimp only [L, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
    FiniteCellSmearing.cellFunction]
  split_ifs
  · exact hf x
  · norm_num

/-- The source mass incident to one actual link. -/
def linkWeight (w : PlaquetteIndex n → ℝ) (e : Link n) : ℝ :=
  ∑ p ∈ affected n e.1 e.2, w p

omit [NeZero n] in
theorem linkWeight_nonneg (w : PlaquetteIndex n → ℝ) (hw : ∀ p, 0 ≤ w p) (e : Link n) :
    0 ≤ linkWeight n w e := Finset.sum_nonneg (fun p _ => hw p)

theorem linkWeight_eq_sum (w : PlaquetteIndex n → ℝ) (e : Link n) :
    linkWeight n w e = ∑ p, if p ∈ affected n e.1 e.2 then w p else 0 := by
  classical
  unfold linkWeight
  rw [← Finset.sum_filter]
  congr 1
  ext p
  simp

variable [Fact (1 < n)]

omit [NeZero n] in
/-- A nondegenerate periodic plaquette has four distinct link coordinates, also at period two. -/
theorem incidentLinks_card_four (p : PlaquetteIndex n) : (incidentLinks n p).card = 4 := by
  classical
  have hd : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
  have h1 := PeriodicPlaquetteNontriviality.step_ne n p.1 p.2.1.1
  have h2 := PeriodicPlaquetteNontriviality.step_ne n p.1 p.2.1.2
  have hab : (p.1, p.2.1.1) ≠ (step n p.1 p.2.1.1, p.2.1.2) :=
    fun h => hd (congrArg Prod.snd h)
  have hac : (p.1, p.2.1.1) ≠ (step n p.1 p.2.1.2, p.2.1.1) :=
    fun h => h2 (congrArg Prod.fst h).symm
  have had : (p.1, p.2.1.1) ≠ (p.1, p.2.1.2) := fun h => hd (congrArg Prod.snd h)
  have hbc : (step n p.1 p.2.1.1, p.2.1.2) ≠ (step n p.1 p.2.1.2, p.2.1.1) :=
    fun h => hd (congrArg Prod.snd h).symm
  have hbd : (step n p.1 p.2.1.1, p.2.1.2) ≠ (p.1, p.2.1.2) :=
    fun h => h1 (congrArg Prod.fst h)
  have hcd : (step n p.1 p.2.1.2, p.2.1.1) ≠ (p.1, p.2.1.2) :=
    fun h => hd (congrArg Prod.snd h)
  simp [incidentLinks, hab, hac, had, hbc, hbd, hcd]

/-- Exact incidence double counting: every source plaquette contributes four times. -/
theorem sum_linkWeight (w : PlaquetteIndex n → ℝ) :
    (∑ e : Link n, linkWeight n w e) = 4 * ∑ p, w p := by
  classical
  simp_rw [linkWeight_eq_sum]
  rw [Finset.sum_comm]
  have he (p : PlaquetteIndex n) :
      (Finset.univ.filter (fun e : Link n => p ∈ affected n e.1 e.2)) = incidentLinks n p := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      mem_incidentLinks, affected_iff_incident]
  simp_rw [← Finset.sum_filter, he]
  simp only [Finset.sum_const, incidentLinks_card_four, nsmul_eq_mul, Nat.cast_ofNat]
  exact (Finset.mul_sum _ _ _).symm

omit [Fact (1 < n)] in
theorem link_card : Fintype.card (Link n) = 4 * n ^ 4 := by
  simp [Link, Vertex, Nat.mul_comm]

/-- The finite lattice-volume dependence is explicit, not discarded. -/
theorem linkWeight_square_lower (w : PlaquetteIndex n → ℝ) :
    4 * (∑ p, w p)^2 / (n : ℝ)^4 ≤ ∑ e : Link n, (linkWeight n w e)^2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Link n))
    (fun _ => (1 : ℝ)) (linkWeight n w)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  rw [sum_linkWeight, link_card] at h
  push_cast at h
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hn : 0 < (n : ℝ)^4 := pow_pos hn0 4
  apply (div_le_iff₀ hn).mpr
  nlinarith

/-- The same exact incidence bound for the actual Schwartz cell weights. -/
theorem physical_weight_square_lower (a : ℝ) (plane : Plane) (f : TestFunction) :
    4 * ((∫ x, f x).re)^2 / (n : ℝ)^4 ≤
      ∑ e : Link n, (linkWeight n (WilsonPhysicalCellWeights.weight n a plane f) e)^2 := by
  have h := linkWeight_square_lower n (WilsonPhysicalCellWeights.weight n a plane f)
  rw [WilsonPhysicalCellWeights.weight_sum] at h
  exact h


/-- This concrete fixed test discharges the nonempty-test and positive-mass premises. -/
theorem witness_weight_lower (a : ℝ) (plane : Plane) :
    (∀ p, 0 ≤ WilsonPhysicalCellWeights.weight n a plane witnessTest p) ∧
      4 / (n : ℝ)^4 ≤
        ∑ e : Link n,
          (linkWeight n (WilsonPhysicalCellWeights.weight n a plane witnessTest) e)^2 := by
  refine ⟨weight_nonneg n a plane witnessTest witnessTest_nonneg, ?_⟩
  simpa only [witnessTest_integral, Complex.one_re, one_pow, mul_one] using
    physical_weight_square_lower n a plane witnessTest

end
end UnifiedTheory.Clay.YangMills.WilsonCellWeightLower
