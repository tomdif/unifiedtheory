/- Actual compact unitary Haar caps, with explicit polynomial mass and
entrywise/trace radii. The group here is U(d), not an arbitrary representation
image or the special unitary group. -/
import UnifiedTheory.Clay.YangMills.UnitaryHaarNeighborhood
import Mathlib.Topology.Algebra.Star.Unitary

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.UnitaryHaarCaps
noncomputable section
open MeasureTheory RegulatedGauge Matrix UnitaryCharacterObservables UnitaryEntryEstimates
open UnitaryHaarNeighborhood

variable (d : Type*) [Fintype d] [DecidableEq d]

instance unitaryMeasurableSpace : MeasurableSpace (Matrix.unitaryGroup d ℂ) :=
  borel (Matrix.unitaryGroup d ℂ)
instance unitaryBorelSpace : BorelSpace (Matrix.unitaryGroup d ℂ) := ⟨rfl⟩
instance unitarySecondCountable : SecondCountableTopology (Matrix.unitaryGroup d ℂ) := by
  letI : SecondCountableTopology (Matrix d d ℂ) := by
    change SecondCountableTopology (d → d → ℂ)
    infer_instance
  exact TopologicalSpace.Subtype.secondCountableTopology
    (Matrix.unitaryGroup d ℂ : Set (Matrix d d ℂ))
instance unitaryCompactSpace : CompactSpace (Matrix.unitaryGroup d ℂ) := by
  apply isCompact_iff_compactSpace.mp
  apply ((isCompact_closedBall (0 : ℂ) 1).matrix (m := d) (n := d)).of_isClosed_subset
    isClosed_unitary
  intro U hU i j
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    unitary_entry_bound (⟨U,hU⟩ : Matrix.unitaryGroup d ℂ) i j

def realTrace (U : Matrix.unitaryGroup d ℂ) : ℂ := ((trace (U : Matrix d d ℂ)).re : ℂ)

theorem realTrace_continuous : Continuous (realTrace d) :=
  Complex.continuous_ofReal.comp (Complex.continuous_re.comp
    (unitaryCharacter_continuous (MonoidHom.id (Matrix.unitaryGroup d ℂ)) continuous_id))

theorem trace_difference_bound (A B : Matrix.unitaryGroup d ℂ) (r : ℝ)
    (h : ∀ i j, ‖A i j-B i j‖ ≤ r) :
    ‖trace (A : Matrix d d ℂ)-trace (B : Matrix d d ℂ)‖ ≤ (Fintype.card d : ℝ)*r := by
  rw [← trace_sub]
  unfold trace
  exact (norm_sum_le _ _).trans (by
    calc
      _ ≤ ∑ _ : d, r := Finset.sum_le_sum (fun i _ => h i i)
      _ = _ := by simp)

theorem realTrace_difference_bound (A B : Matrix.unitaryGroup d ℂ) (r : ℝ)
    (h : ∀ i j, ‖A i j-B i j‖ ≤ r) :
    ‖realTrace d A-realTrace d B‖ ≤ (Fintype.card d : ℝ)*r := by
  change ‖(((trace (A : Matrix d d ℂ)).re : ℂ)-
    ((trace (B : Matrix d d ℂ)).re : ℂ))‖ ≤ _
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm (trace (A : Matrix d d ℂ)-trace (B : Matrix d d ℂ))).trans
    (trace_difference_bound d A B r h)

def cap (A : Matrix.unitaryGroup d ℂ) (K : ℕ) : Set (Matrix.unitaryGroup d ℂ) :=
  (fun U => A⁻¹*U) ⁻¹' nearIdentity (MonoidHom.id (Matrix.unitaryGroup d ℂ)) K

theorem cap_measurable (A : Matrix.unitaryGroup d ℂ) (K : ℕ) : MeasurableSet (cap d A K) :=
  (nearIdentity_measurable (MonoidHom.id (Matrix.unitaryGroup d ℂ)) continuous_id K).preimage
    (continuous_const.mul continuous_id).measurable

theorem cap_mass_lower (A : Matrix.unitaryGroup d ℂ) (K : ℕ) (hK : 0 < K) :
    massLower d K ≤ (compactHaar (Matrix.unitaryGroup d ℂ)).real (cap d A K) := by
  have hm := (measurePreserving_mul_left (compactHaar (Matrix.unitaryGroup d ℂ)) A⁻¹).measure_preimage
      (nearIdentity_measurable (MonoidHom.id (Matrix.unitaryGroup d ℂ)) continuous_id K).nullMeasurableSet
  change massLower d K ≤ ENNReal.toReal ((compactHaar (Matrix.unitaryGroup d ℂ))
    ((fun U => A⁻¹*U) ⁻¹' nearIdentity (MonoidHom.id (Matrix.unitaryGroup d ℂ)) K))
  rw [hm]
  exact nearIdentity_mass_lower (MonoidHom.id (Matrix.unitaryGroup d ℂ)) continuous_id K hK

theorem cap_entry_bound (A U : Matrix.unitaryGroup d ℂ) (K : ℕ) (hU : U ∈ cap d A K)
    (i j : d) : ‖U i j-A i j‖ ≤ (Fintype.card d : ℝ)*entryRadius d K := by
  have he : (U : Matrix d d ℂ)-(A : Matrix d d ℂ) =
      (A : Matrix d d ℂ)*(((A⁻¹*U : Matrix.unitaryGroup d ℂ) : Matrix d d ℂ)-1) := by
    simp only [mul_sub, mul_one, ← UnitaryGroup.mul_val, mul_inv_cancel_left]
  change ‖(((U : Matrix d d ℂ)-(A : Matrix d d ℂ)) i j)‖ ≤ _
  rw [he]
  exact left_mul_entry A _ (entryRadius d K) hU i j

theorem cap_trace_bound (A U : Matrix.unitaryGroup d ℂ) (K : ℕ) (hU : U ∈ cap d A K) :
    ‖realTrace d U-realTrace d A‖ ≤ (Fintype.card d : ℝ)^2*entryRadius d K := by
  simpa only [pow_two, mul_assoc] using
    realTrace_difference_bound d U A ((Fintype.card d : ℝ)*entryRadius d K)
      (cap_entry_bound d A U K hU)

end
end UnifiedTheory.Clay.YangMills.UnitaryHaarCaps
