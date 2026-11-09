/- A four-dimensional Born law for the two antisymmetric momenta and two
symmetric positions, which commute in the actual charge representation.
It is a quantum marginal, not a joint law of all canonical observables. -/
import UnifiedTheory.Audit.KFCausalClockFloorChargedTail

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorChargedLaw
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalClockFloorRotatedAntiSymbol (momentum position)
open UnifiedTheory.Audit.KFCausalClockFloorChargedTail (planeTail planeTail_nonnegative)
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph (l2_norm_square)

abbrev ChargedSpace := (ℝ × ℝ) × (ℝ × ℝ)

def chargedPoint (h : ℝ) (x : Joint 2 4) : ChargedSpace :=
  ((momentum h 0 x,position 0 x),(momentum h 1 x,position 1 x))

theorem chargedPoint_continuous (h : ℝ) : Continuous (chargedPoint h) := by
  unfold chargedPoint momentum position
  fun_prop

def mixedLaw (f : Hilbert) : Measure (Joint 2 4) :=
  volume.withDensity (fun x => ENNReal.ofReal (‖(chargeCoordinates f) x‖^2))

def chargedLaw (h : ℝ) (f : Hilbert) : Measure ChargedSpace := (mixedLaw f).map (chargedPoint h)

theorem mixedLaw_apply (f : Hilbert) (A : Set (Joint 2 4)) (hA : MeasurableSet A) :
    mixedLaw f A = ENNReal.ofReal (∫ x in A, ‖(chargeCoordinates f) x‖^2) := by
  rw [mixedLaw,withDensity_apply _ hA]
  exact (ofReal_integral_eq_lintegral_ofReal
    (((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (chargeCoordinates f))).mp
      (Lp.memLp (chargeCoordinates f))).integrableOn)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).symm

theorem chargedLaw_total (h : ℝ) (f : Hilbert) : chargedLaw h f Set.univ = ENNReal.ofReal (‖f‖^2) := by
  rw [chargedLaw,Measure.map_apply (chargedPoint_continuous h).measurable MeasurableSet.univ,
    Set.preimage_univ,mixedLaw_apply f _ MeasurableSet.univ,setIntegral_univ,← l2_norm_square,
    chargeCoordinates.norm_map]

theorem chargedLaw_probability (h : ℝ) (f : Hilbert) (hf : ‖f‖ = 1) :
    IsProbabilityMeasure (chargedLaw h f) where
  measure_univ := by rw [chargedLaw_total,hf,one_pow,ENNReal.ofReal_one]

def chargedBox (R : ℝ) : Set ChargedSpace :=
  (Set.Icc (-R) R ×ˢ Set.Icc (-R) R) ×ˢ (Set.Icc (-R) R ×ˢ Set.Icc (-R) R)

theorem chargedBox_compact (R : ℝ) : IsCompact (chargedBox R) :=
  (isCompact_Icc.prod isCompact_Icc).prod (isCompact_Icc.prod isCompact_Icc)

theorem chargedBox_outside_subset (h R : ℝ) (hR : 0 ≤ R) :
    (chargedPoint h) ⁻¹' (chargedBox R)ᶜ ⊆
      {x | R^2 ≤ momentum h 0 x^2+position 0 x^2} ∪
      {x | R^2 ≤ momentum h 1 x^2+position 1 x^2} := by
  have hp (u v : ℝ) (he : u^2+v^2 < R^2) :
      (u,v) ∈ Set.Icc (-R) R ×ˢ Set.Icc (-R) R := by
    have hu : u^2 < R^2 := lt_of_le_of_lt (le_add_of_nonneg_right (sq_nonneg v)) he
    have hv : v^2 < R^2 := lt_of_le_of_lt (le_add_of_nonneg_left (sq_nonneg u)) he
    have hu' := (sq_lt_sq₀ (abs_nonneg u) hR).mp (by simpa only [sq_abs] using hu)
    have hv' := (sq_lt_sq₀ (abs_nonneg v) hR).mp (by simpa only [sq_abs] using hv)
    exact ⟨abs_le.mp hu'.le,abs_le.mp hv'.le⟩
  intro x hx
  by_contra hn
  have h0 : momentum h 0 x^2+position 0 x^2 < R^2 :=
    lt_of_not_ge (fun h0 => hn (Or.inl h0))
  have h1 : momentum h 1 x^2+position 1 x^2 < R^2 :=
    lt_of_not_ge (fun h1 => hn (Or.inr h1))
  exact hx ⟨hp _ _ h0,hp _ _ h1⟩

theorem chargedLaw_outside_le (h R : ℝ) (hR : 0 ≤ R) (f : Hilbert) :
    chargedLaw h f (chargedBox R)ᶜ ≤ ENNReal.ofReal (planeTail h R 0 f+planeTail h R 1 f) := by
  have hs (i : Fin 2) : MeasurableSet {x : Joint 2 4 | R^2 ≤ momentum h i x^2+position i x^2} := by
    apply measurableSet_le measurable_const
    unfold momentum position
    fun_prop
  rw [chargedLaw,Measure.map_apply (chargedPoint_continuous h).measurable
    (chargedBox_compact R).isClosed.measurableSet.compl]
  calc
    _ ≤ mixedLaw f ({x | R^2 ≤ momentum h 0 x^2+position 0 x^2} ∪
        {x | R^2 ≤ momentum h 1 x^2+position 1 x^2}) :=
      measure_mono (chargedBox_outside_subset h R hR)
    _ ≤ mixedLaw f {x | R^2 ≤ momentum h 0 x^2+position 0 x^2}+
        mixedLaw f {x | R^2 ≤ momentum h 1 x^2+position 1 x^2} := measure_union_le _ _
    _ = _ := by
      rw [mixedLaw_apply f _ (hs 0),mixedLaw_apply f _ (hs 1),
        ENNReal.ofReal_add (planeTail_nonnegative h R 0 f) (planeTail_nonnegative h R 1 f)]
      rfl

#print axioms chargedPoint_continuous
#print axioms mixedLaw_apply
#print axioms chargedLaw_total
#print axioms chargedLaw_probability
#print axioms chargedBox_compact
#print axioms chargedBox_outside_subset
#print axioms chargedLaw_outside_le

end
end UnifiedTheory.Audit.KFCausalClockFloorChargedLaw
