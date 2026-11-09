/- Unbounded spectator multiplication relations are transported through
the actual partial Fourier unitary. Two bounded regularized multipliers
give the result on all L2 graph pairs, without a smooth core assumption. -/
import UnifiedTheory.Audit.KFCausalChargeSpectatorMultiplier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalChargeSpectatorRelation
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (Space FrequencyHilbert)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (modeIsometry)
open UnifiedTheory.Audit.KFCausalPairedTranslationCoordinates (chargeEuclidean)
open UnifiedTheory.Audit.KFCausalChargeSpectatorMultiplier

def regularizer (z : ℂ) : ℂ := ((1+‖z‖:ℝ):ℂ)⁻¹
def boundedSymbol (z : ℂ) : ℂ := regularizer z*z

theorem regularizer_measurable : Measurable regularizer := by
  unfold regularizer
  fun_prop

theorem boundedSymbol_measurable : Measurable boundedSymbol :=
  regularizer_measurable.mul measurable_id

theorem regularizer_ne_zero (z : ℂ) : regularizer z ≠ 0 := by
  apply inv_ne_zero
  apply Complex.ofReal_ne_zero.mpr
  positivity

theorem regularizer_bound (z : ℂ) : ‖regularizer z‖ ≤ 1 := by
  rw [regularizer,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1+‖z‖)]
  rw [inv_eq_one_div]
  exact (div_le_one (by positivity : 0 < 1+‖z‖)).mpr (by linarith [norm_nonneg z])

theorem boundedSymbol_bound (z : ℂ) : ‖boundedSymbol z‖ ≤ 1 := by
  rw [boundedSymbol,norm_mul,regularizer,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1+‖z‖),← div_eq_inv_mul]
  exact (div_le_one (by positivity : 0 < 1+‖z‖)).mpr (by linarith)

theorem regularized_iff (z f g : ℂ) :
    regularizer z*g = boundedSymbol z*f ↔ g = z*f := by
  rw [boundedSymbol,mul_assoc]
  constructor
  · exact mul_left_cancel₀ (regularizer_ne_zero z)
  · intro he
    rw [he]

variable (a : Block 4 → ℂ) (ha : Measurable a)

theorem euclidean_regularized_iff (f g : FrequencyHilbert) :
    euclideanMultiplier (regularizer ∘ a) (regularizer_measurable.comp ha)
        (fun x => regularizer_bound (a x)) g =
      euclideanMultiplier (boundedSymbol ∘ a) (boundedSymbol_measurable.comp ha)
        (fun x => boundedSymbol_bound (a x)) f ↔
      g =ᵐ[volume] fun x => a (split 2 4 (modeIsometry x)).2*f x := by
  constructor
  · intro he
    filter_upwards [Lp.ext_iff.mp he,
      euclideanMultiplier_coe (regularizer ∘ a) (regularizer_measurable.comp ha)
        (fun x => regularizer_bound (a x)) g,
      euclideanMultiplier_coe (boundedSymbol ∘ a) (boundedSymbol_measurable.comp ha)
        (fun x => boundedSymbol_bound (a x)) f] with x he hg hf
    rw [hg,hf] at he
    exact (regularized_iff _ _ _).mp he
  · intro he
    apply Lp.ext
    filter_upwards [he,
      euclideanMultiplier_coe (regularizer ∘ a) (regularizer_measurable.comp ha)
        (fun x => regularizer_bound (a x)) g,
      euclideanMultiplier_coe (boundedSymbol ∘ a) (boundedSymbol_measurable.comp ha)
        (fun x => boundedSymbol_bound (a x)) f] with x he hg hf
    rw [hg,hf]
    exact (regularized_iff _ _ _).mpr he

theorem joint_regularized_iff (f g : JointHilbert 2 4) :
    jointMultiplier (regularizer ∘ a) (regularizer_measurable.comp ha)
        (fun x => regularizer_bound (a x)) g =
      jointMultiplier (boundedSymbol ∘ a) (boundedSymbol_measurable.comp ha)
        (fun x => boundedSymbol_bound (a x)) f ↔
      g =ᵐ[volume] fun x => a (split 2 4 x).2*f x := by
  constructor
  · intro he
    filter_upwards [Lp.ext_iff.mp he,
      jointMultiplier_coe (regularizer ∘ a) (regularizer_measurable.comp ha)
        (fun x => regularizer_bound (a x)) g,
      jointMultiplier_coe (boundedSymbol ∘ a) (boundedSymbol_measurable.comp ha)
        (fun x => boundedSymbol_bound (a x)) f] with x he hg hf
    rw [hg,hf] at he
    exact (regularized_iff _ _ _).mp he
  · intro he
    apply Lp.ext
    filter_upwards [he,
      jointMultiplier_coe (regularizer ∘ a) (regularizer_measurable.comp ha)
        (fun x => regularizer_bound (a x)) g,
      jointMultiplier_coe (boundedSymbol ∘ a) (boundedSymbol_measurable.comp ha)
        (fun x => boundedSymbol_bound (a x)) f] with x he hg hf
    rw [hg,hf]
    exact (regularized_iff _ _ _).mpr he

include ha in
theorem chargeEuclidean_relation (f g : FrequencyHilbert) :
    (g =ᵐ[volume] fun x => a (split 2 4 (modeIsometry x)).2*f x) ↔
      chargeEuclidean g =ᵐ[volume] fun x => a (split 2 4 x).2*(chargeEuclidean f) x := by
  rw [← euclidean_regularized_iff a ha,← joint_regularized_iff a ha]
  rw [← chargeEuclidean_multiplier,← chargeEuclidean_multiplier]
  exact chargeEuclidean.injective.eq_iff.symm

include ha in
theorem physical_relation (b : KFCausalCoupledLongitudinalFlow.Configuration → ℂ)
    (hab : ∀ x : Space, a (split 2 4 (modeIsometry x)).2 = b (KFCausalEuclideanConfiguration.split x))
    (f g : KFCausalConfigurationTestSpace.Hilbert) :
    (g =ᵐ[volume] fun x => b x*f x) ↔
      KFCausalPhysicalCircleAction.chargeCoordinates g =ᵐ[volume] fun x =>
        a (split 2 4 x).2*(KFCausalPhysicalCircleAction.chargeCoordinates f) x := by
  let U := KFCausalEuclideanConfiguration.euclideanPullback
  have hc := chargeEuclidean_relation a ha (U f) (U g)
  rw [KFCausalPairedTranslationCoordinates.chargeEuclidean_physical,
    KFCausalPairedTranslationCoordinates.chargeEuclidean_physical] at hc
  rw [← hc]
  constructor
  · intro he
    filter_upwards [KFCausalEuclideanConfiguration.split_preserves_volume.quasiMeasurePreserving.ae he,
      KFCausalEuclideanConfiguration.euclideanPullback_coe f,
      KFCausalEuclideanConfiguration.euclideanPullback_coe g] with x he hf hg
    change U g x = a (split 2 4 (modeIsometry x)).2*U f x
    rw [hg,hf,hab]
    exact he
  · intro he
    have hr : ∀ᵐ x : Space ∂volume,
        g (KFCausalEuclideanConfiguration.split x) =
          b (KFCausalEuclideanConfiguration.split x)*f (KFCausalEuclideanConfiguration.split x) := by
      filter_upwards [he,KFCausalEuclideanConfiguration.euclideanPullback_coe f,
        KFCausalEuclideanConfiguration.euclideanPullback_coe g] with x he hf hg
      change U g x = a (split 2 4 (modeIsometry x)).2*U f x at he
      rw [hg,hf,hab] at he
      exact he
    have hb := KFCausalEuclideanConfiguration.split_preserves_volume.symm.quasiMeasurePreserving.ae hr
    simpa only [MeasurableEquiv.apply_symm_apply] using hb

#print axioms regularizer_measurable
#print axioms boundedSymbol_measurable
#print axioms regularizer_ne_zero
#print axioms regularizer_bound
#print axioms boundedSymbol_bound
#print axioms regularized_iff
#print axioms euclidean_regularized_iff
#print axioms joint_regularized_iff
#print axioms chargeEuclidean_relation
#print axioms physical_relation

end
end UnifiedTheory.Audit.KFCausalChargeSpectatorRelation
