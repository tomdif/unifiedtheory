/- The actual five-dimensional Born law in the complementary transverse
representation. Compact boxes are controlled by the two derived radial
tails, with the neutral coordinate included in the second group. -/
import UnifiedTheory.Audit.KFCausalClockFloorComplementaryTail

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorComplementaryLaw
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalChargeTransverseSplit (dualPhysical)
open UnifiedTheory.Audit.KFCausalComplementaryChargeSymbol
open UnifiedTheory.Audit.KFCausalClockFloorComplementaryTail
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph (l2_norm_square)

abbrev ComplementarySpace := (ℝ × ℝ) × (ℝ × ℝ × ℝ)

def complementaryPoint (h : ℝ) (x : Joint 5 1) : ComplementarySpace :=
  ((complementaryMomentum h 0 x,complementaryPosition 0 x),
    (complementaryMomentum h 1 x,complementaryPosition 1 x,neutralMomentum h x))

theorem complementaryPoint_continuous (h : ℝ) : Continuous (complementaryPoint h) := by
  unfold complementaryPoint complementaryMomentum complementaryPosition neutralMomentum
  fun_prop

def dualLaw (f : Hilbert) : Measure (Joint 5 1) :=
  volume.withDensity (fun x => ENNReal.ofReal (‖(dualPhysical f) x‖^2))

def complementaryLaw (h : ℝ) (f : Hilbert) : Measure ComplementarySpace :=
  (dualLaw f).map (complementaryPoint h)

theorem dualLaw_apply (f : Hilbert) (A : Set (Joint 5 1)) (hA : MeasurableSet A) :
    dualLaw f A = ENNReal.ofReal (∫ x in A, ‖(dualPhysical f) x‖^2) := by
  rw [dualLaw,withDensity_apply _ hA]
  exact (ofReal_integral_eq_lintegral_ofReal
    (((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (dualPhysical f))).mp
      (Lp.memLp (dualPhysical f))).integrableOn)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).symm

theorem complementaryLaw_total (h : ℝ) (f : Hilbert) : complementaryLaw h f Set.univ = ENNReal.ofReal (‖f‖^2) := by
  rw [complementaryLaw,Measure.map_apply (complementaryPoint_continuous h).measurable MeasurableSet.univ,
    Set.preimage_univ,dualLaw_apply f _ MeasurableSet.univ,setIntegral_univ,← l2_norm_square,dualPhysical.norm_map]

theorem complementaryLaw_probability (h : ℝ) (f : Hilbert) (hf : ‖f‖ = 1) :
    IsProbabilityMeasure (complementaryLaw h f) where
  measure_univ := by rw [complementaryLaw_total,hf,one_pow,ENNReal.ofReal_one]

def complementaryBox (R : ℝ) : Set ComplementarySpace :=
  (Set.Icc (-R) R ×ˢ Set.Icc (-R) R) ×ˢ (Set.Icc (-R) R ×ˢ (Set.Icc (-R) R ×ˢ Set.Icc (-R) R))

theorem complementaryBox_compact (R : ℝ) : IsCompact (complementaryBox R) :=
  (isCompact_Icc.prod isCompact_Icc).prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))

theorem complementaryBox_outside_subset (h R : ℝ) (hR : 0 ≤ R) :
    (complementaryPoint h) ⁻¹' (complementaryBox R)ᶜ ⊆
      {x | R^2 ≤ complementarySquare h 0 x} ∪ {x | R^2 ≤ complementarySquare h 1 x} := by
  have hp (u : ℝ) (hu : u^2 < R^2) : u ∈ Set.Icc (-R) R := by
    have hu' := (sq_lt_sq₀ (abs_nonneg u) hR).mp (by simpa only [sq_abs] using hu)
    exact abs_le.mp hu'.le
  intro x hx
  by_contra hn
  have h0 : complementarySquare h 0 x < R^2 := lt_of_not_ge (fun h0 => hn (Or.inl h0))
  have h1 : complementarySquare h 1 x < R^2 := lt_of_not_ge (fun h1 => hn (Or.inr h1))
  change complementaryMomentum h 0 x^2+complementaryPosition 0 x^2+0^2 < R^2 at h0
  change complementaryMomentum h 1 x^2+complementaryPosition 1 x^2+neutralMomentum h x^2 < R^2 at h1
  apply hx
  refine ⟨⟨hp _ ?_,hp _ ?_⟩,hp _ ?_,hp _ ?_,hp _ ?_⟩
  all_goals dsimp only [complementaryPoint]
  all_goals nlinarith [sq_nonneg (complementaryMomentum h 0 x),sq_nonneg (complementaryPosition 0 x),
    sq_nonneg (complementaryMomentum h 1 x),sq_nonneg (complementaryPosition 1 x),sq_nonneg (neutralMomentum h x)]

theorem complementaryLaw_outside_le (h R : ℝ) (hR : 0 ≤ R) (f : Hilbert) :
    complementaryLaw h f (complementaryBox R)ᶜ ≤
      ENNReal.ofReal (complementaryTail h R 0 f+complementaryTail h R 1 f) := by
  have hs (i : Fin 2) : MeasurableSet {x : Joint 5 1 | R^2 ≤ complementarySquare h i x} :=
    measurableSet_le measurable_const (complementarySquare_continuous h i).measurable
  rw [complementaryLaw,Measure.map_apply (complementaryPoint_continuous h).measurable
    (complementaryBox_compact R).isClosed.measurableSet.compl]
  calc
    _ ≤ dualLaw f ({x | R^2 ≤ complementarySquare h 0 x} ∪ {x | R^2 ≤ complementarySquare h 1 x}) :=
      measure_mono (complementaryBox_outside_subset h R hR)
    _ ≤ dualLaw f {x | R^2 ≤ complementarySquare h 0 x}+dualLaw f {x | R^2 ≤ complementarySquare h 1 x} :=
      measure_union_le _ _
    _ = _ := by
      rw [dualLaw_apply f _ (hs 0),dualLaw_apply f _ (hs 1),
        ENNReal.ofReal_add (complementaryTail_nonnegative h R 0 f) (complementaryTail_nonnegative h R 1 f)]
      rfl

#print axioms complementaryPoint_continuous
#print axioms dualLaw_apply
#print axioms complementaryLaw_total
#print axioms complementaryLaw_probability
#print axioms complementaryBox_compact
#print axioms complementaryBox_outside_subset
#print axioms complementaryLaw_outside_le

end
end UnifiedTheory.Audit.KFCausalClockFloorComplementaryLaw
