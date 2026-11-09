/- The full natural domain of the two charge-averaged symmetric kinetic
factors. The reverse graph implication is proved using maximal momentum
transport. Finite complementary moments construct continuous actual
outputs along the entire charge orbit, including the neutral derivative.
No packet restriction or common operator core is used. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedComplementaryMoment
import UnifiedTheory.Audit.KFCausalSymmetricMomentumGraphEquivalence
import UnifiedTheory.Audit.KFCausalChargeDualMomentumDomain
import UnifiedTheory.Audit.KFCausalMultiplierMomentBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorSymmetricOrbitDomain
noncomputable section
open MeasureTheory
open scoped ENNReal
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates
open KFCausalPhysicalCircleAction (action action_coordinates action_reverse chargeCoordinates)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorChargeClockHalf (inverseL_action)
open KFCausalClockFloorDualClock (inverseL_dual_coe)
open KFCausalClockFloorAntisymmetricGraph (clockMomentum_graph_iff)
open KFCausalClockFloorTrialMomentum (clockMomentum)
open KFCausalSymmetricMomentumCoordinates (symmetricDirection symmetricVector)
open KFCausalSymmetricMomentumGraphEquivalence (symmetric_graph_iff)
open KFCausalClockFloorSymmetricOrbitGraph (rotated_clockMomentum_coe)
open KFCausalComplementaryChargeSymbol
open KFCausalChargeTransverseSplit (dualPhysical dualMixed)
open KFCausalChargeDualMomentum (dualSymbol)
open KFCausalChargeDualMomentumDomain (dualMomentum_graph_iff)
open KFCausalNormalizedChargeFlow
open KFCausalClockFloorComplementaryTonelli
open KFCausalClockFloorAveragedComplementaryMoment (complementaryMoment)
open KFCausalClockFloorFlow (clock)
open KFCausalClockFloorCanonicalDefect (clock_positive)
open KFCausalPairedModeCoordinates (scale)
open KFCausalUnitIntervalOrbit (angleMeasure)

theorem rotated_graph_iff (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (θ : ℝ) (i : Fin 2) (f g : Hilbert) :
    (action h hh θ f,g) ∈ (clockMomentum ε h (symmetricDirection i)).graph ↔
      dualPhysical (action h hh (-θ) g) =ᵐ[volume]
        fun x => (rotatedWeightedSymbol ε h hh θ i x : ℂ)*(dualPhysical f) x := by
  constructor
  · exact rotated_clockMomentum_coe ε hε h hh θ i f g
  · intro hg
    have he : (chargeCoordinates (inverseL ε hε f),chargeCoordinates (action h hh (-θ) g)) ∈
        (KFCausalDirectionalTranslationMomentum.spectralMomentum h (rotatedVector h hh θ i)).graph := by
      apply (dualMomentum_graph_iff h hh _ (rotatedVector_clock h hh θ i) _ _).mpr
      filter_upwards [hg,inverseL_dual_coe ε hε f] with x hx hf
      change (dualPhysical (action h hh (-θ) g)) x =
        (dualSymbol h (rotatedVector h hh θ i) x:ℂ)*(dualPhysical (inverseL ε hε f)) x
      rw [hx,hf,rotatedWeightedSymbol,Complex.ofReal_div,div_eq_mul_inv,mul_assoc]
    have hi : KFCausalMixedCircleAction.action (momentumScale h) (momentumScale_ne_zero h hh) (-θ)
        (chargeCoordinates (inverseL ε hε (action h hh θ f))) = chargeCoordinates (inverseL ε hε f) := by
      rw [inverseL_action,action_coordinates,KFCausalMixedRotationMomentumGraph.action_reverse]
    rw [← hi] at he
    have hr := KFCausalMixedRotationMomentumGraph.momentum_graph_reverse h hh
      (momentumScale h) (momentumScale_ne_zero h hh) (-θ) (rotatedVector h hh θ i)
      (chargeCoordinates (inverseL ε hε (action h hh θ f)))
      (chargeCoordinates (action h hh (-θ) g)) he
    have hv : flowEquiv (momentumScale h) (momentumScale_ne_zero h hh) (-θ)
        (rotatedVector h hh θ i) = symmetricVector i := flow_reverse _ _ θ _
    rw [neg_neg,hv] at hr
    have ho : KFCausalMixedCircleAction.action (momentumScale h) (momentumScale_ne_zero h hh) θ
        (chargeCoordinates (action h hh (-θ) g)) = chargeCoordinates g := by
      rw [← action_coordinates h hh θ (action h hh (-θ) g),
        KFCausalPhysicalCircleAction.action_compose,neg_add_cancel,
        KFCausalPhysicalCircleAction.action_zero]
    rw [ho] at hr
    exact (clockMomentum_graph_iff ε hε h (symmetricDirection i) (action h hh θ f) g).mpr
      ((symmetric_graph_iff h hh i (inverseL ε hε (action h hh θ f)) g).mpr hr)

private def partSymbol (ε h : ℝ) (i : Fin 2) (j : Fin 3) (x : Joint 5 1) : ℝ :=
  ![complementaryMomentum h i x,complementaryPosition i x,neutralTerm h i x] j /
    Real.sqrt (clock ε (x (.inr 0)))

private theorem part_bound (ε : ℝ) (hε : 0 < ε) (h : ℝ) (i : Fin 2)
    (j : Fin 3) (x : Joint 5 1) : partSymbol ε h i j x^2 ≤ complementaryWeight ε h i x := by
  unfold partSymbol complementaryWeight
  rw [div_pow,Real.sq_sqrt (clock_positive ε _ hε.le).le]
  apply div_le_div_of_nonneg_right _ (clock_positive ε _ hε.le).le
  unfold complementarySquare
  fin_cases j
  · change (complementaryMomentum h i x)^2 ≤ _
    nlinarith [sq_nonneg (complementaryPosition i x),sq_nonneg (neutralTerm h i x)]
  · change (complementaryPosition i x)^2 ≤ _
    nlinarith [sq_nonneg (complementaryMomentum h i x),sq_nonneg (neutralTerm h i x)]
  · change (neutralTerm h i x)^2 ≤ _
    nlinarith [sq_nonneg (complementaryMomentum h i x),
    sq_nonneg (complementaryPosition i x),sq_nonneg (neutralTerm h i x)]

private theorem part_measurable (ε h : ℝ) (i : Fin 2) (j : Fin 3) :
    Measurable (partSymbol ε h i j) := by
  fin_cases j
  · change Measurable (fun x : Joint 5 1 => complementaryMomentum h i x / Real.sqrt (clock ε (x (.inr 0))))
    unfold complementaryMomentum clock
    fun_prop
  · change Measurable (fun x : Joint 5 1 => complementaryPosition i x / Real.sqrt (clock ε (x (.inr 0))))
    unfold complementaryPosition clock
    fun_prop
  · change Measurable (fun x : Joint 5 1 => neutralTerm h i x / Real.sqrt (clock ε (x (.inr 0))))
    fin_cases i
    · change Measurable (fun x : Joint 5 1 => 0 / Real.sqrt (clock ε (x (.inr 0)))); simp only [zero_div]; exact measurable_const
    · change Measurable (fun x : Joint 5 1 => neutralMomentum h x / Real.sqrt (clock ε (x (.inr 0))))
      unfold neutralMomentum clock
      fun_prop

private theorem trig_continuous (q : Fin 3 → JointHilbert 5 1) (a : ℝ) :
    Continuous (fun θ : ℝ => ((a*Real.cos θ:ℝ):ℂ) • q 0 +
      ((a*Real.sin θ:ℝ):ℂ) • q 1 + q 2) := by fun_prop

private theorem joint_apply_continuous (F : ℝ → Hilbert → Hilbert)
    (hF : Continuous (fun p : ℝ × Hilbert => F p.1 p.2))
    (z : ℝ → Hilbert) (hz : Continuous z) : Continuous (fun θ => F θ (z θ)) :=
  hF.comp (continuous_id.prodMk hz)

theorem continuous_orbit_output (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (i : Fin 2) (f : Hilbert)
    (hf : Integrable (fun x => complementaryWeight ε h i x*‖(dualPhysical f) x‖^2)) :
    ∃ g : ℝ → Hilbert, Continuous g ∧
      ∀ θ, (action h hh θ f,g θ) ∈ (clockMomentum ε h (symmetricDirection i)).graph := by
  have hp (j : Fin 3) : ∃ q : JointHilbert 5 1,
      q =ᵐ[volume] (fun x => (partSymbol ε h i j x:ℂ)*(dualPhysical f) x) := by
    obtain ⟨q,hq,_⟩ := KFCausalMultiplierMomentBound.multiplier_output (dualPhysical f)
      (partSymbol ε h i j) (part_measurable ε h i j) _ hf
      (Filter.Eventually.of_forall (fun x => mul_le_mul_of_nonneg_right
        (part_bound ε hε h i j x) (sq_nonneg _)))
    exact ⟨q,hq⟩
  choose q hq using hp
  let z (θ : ℝ) : JointHilbert 5 1 :=
    ((2*scale*Real.cos θ:ℝ):ℂ) • q 0 + ((2*scale*Real.sin θ:ℝ):ℂ) • q 1 + q 2
  let g (θ : ℝ) : Hilbert := action h hh θ (dualPhysical.symm (z θ))
  have hz : Continuous z := trig_continuous q (2*scale)
  have hzz : Continuous (fun θ : ℝ => dualPhysical.symm (z θ)) := dualPhysical.symm.continuous.comp hz
  have hg : Continuous (fun θ : ℝ => action h hh θ (dualPhysical.symm (z θ))) :=
    joint_apply_continuous (fun θ v => action h hh θ v)
      (KFCausalPhysicalCircleAction.action_joint_continuous h hh) _ hzz
  refine ⟨g,hg,?_⟩
  intro θ
  apply (rotated_graph_iff ε hε h hh θ i f (g θ)).mpr
  have he : dualPhysical (action h hh (-θ) (g θ)) = z θ := by
    dsimp only [g]
    rw [action_reverse,LinearIsometryEquiv.apply_symm_apply]
  rw [he]
  filter_upwards [hq 0,hq 1,hq 2,
    Lp.coeFn_add (((2*scale*Real.cos θ:ℝ):ℂ) • q 0 + ((2*scale*Real.sin θ:ℝ):ℂ) • q 1) (q 2),
    Lp.coeFn_add (((2*scale*Real.cos θ:ℝ):ℂ) • q 0) (((2*scale*Real.sin θ:ℝ):ℂ) • q 1),
    Lp.coeFn_smul ((2*scale*Real.cos θ:ℝ):ℂ) (q 0),
    Lp.coeFn_smul ((2*scale*Real.sin θ:ℝ):ℂ) (q 1)] with x h0 h1 h2 ha hb hc hd
  change (_ + _ + q 2) x = _
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at ha hb hc hd
  change (q 0) x = ((complementaryMomentum h i x / Real.sqrt (clock ε (x (.inr 0))):ℝ):ℂ)*(dualPhysical f) x at h0
  change (q 1) x = ((complementaryPosition i x / Real.sqrt (clock ε (x (.inr 0))):ℝ):ℂ)*(dualPhysical f) x at h1
  change (q 2) x = ((neutralTerm h i x / Real.sqrt (clock ε (x (.inr 0))):ℝ):ℂ)*(dualPhysical f) x at h2
  rw [ha,hb,hc,hd,h0,h1,h2,rotatedWeightedSymbol,rotatedSymbol_formula]
  simp only [Complex.ofReal_div,Complex.ofReal_add,Complex.ofReal_mul]
  ring

theorem orbit_moment_iff (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (i : Fin 2) (f : Hilbert) :
    Integrable (fun x => complementaryWeight ε h i x*‖(dualPhysical f) x‖^2) ↔
      ∃ g : ℝ → Hilbert, Continuous g ∧
        ∀ θ, (action h hh θ f,g θ) ∈ (clockMomentum ε h (symmetricDirection i)).graph := by
  refine ⟨continuous_orbit_output ε hε h hh i f,?_⟩
  rintro ⟨g,hg,hgraph⟩
  apply (complementaryDensity_integrable_iff ε hε h i f).mpr
  rw [← rotatedMass_angle ε hε h hh i f]
  simp_rw [rotatedMass_graph ε hε h hh _ i f _ (hgraph _)]
  have hi : Integrable (fun θ => ‖g (2*Real.pi*θ)‖^2) angleMeasure :=
    (((hg.comp (by fun_prop)).norm.pow 2).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
  exact ENNReal.ofReal_ne_top

theorem orbit_energy (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (i : Fin 2) (f : Hilbert) (g : ℝ → Hilbert) (hg : Continuous g)
    (hgraph : ∀ θ, (action h hh θ f,g θ) ∈ (clockMomentum ε h (symmetricDirection i)).graph) :
    (∫ θ, ‖g (2*Real.pi*θ)‖^2 ∂angleMeasure) = complementaryMoment ε h i f := by
  have hf := (orbit_moment_iff ε hε h hh i f).mpr ⟨g,hg,hgraph⟩
  have hi : Integrable (fun θ => ‖g (2*Real.pi*θ)‖^2) angleMeasure :=
    (((hg.comp (by fun_prop)).norm.pow 2).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have he := rotatedMass_angle ε hε h hh i f
  simp_rw [rotatedMass_graph ε hε h hh _ i f _ (hgraph _)] at he
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))] at he
  have hm : complementaryMass ε h i f = ENNReal.ofReal (complementaryMoment ε h i f) :=
    (ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall (fun x =>
      mul_nonneg (complementaryWeight_nonnegative ε hε h i x) (sq_nonneg _)))).symm
  rw [hm] at he
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg (fun _ => sq_nonneg _))
    (KFCausalClockFloorAveragedComplementaryMoment.complementaryMoment_nonnegative ε hε h i f)).mp he

#print axioms rotated_graph_iff
#print axioms continuous_orbit_output
#print axioms orbit_moment_iff
#print axioms orbit_energy
end
end UnifiedTheory.Audit.KFCausalClockFloorSymmetricOrbitDomain
