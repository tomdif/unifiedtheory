/- The collective entropy estimate in each actual block conditional law.
The exterior remains fixed throughout the ground-normalization argument. -/
import UnifiedTheory.Clay.YangMills.WilsonBlockRotation

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonConditionalEntropy
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundHeatBath
open WilsonStationaryEntropy WilsonBlockRotation CompactDensityEntropy WilsonAveragedResponse
open WilsonPhysicalResponse

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

def rowAt (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (r : Outside n S) (q a : Inside n S) : ℝ :=
  rowEntropy n β hβ (WilsonBlockMarginal.assemble S (r,a))
    (WilsonBlockMarginal.assemble S (r,q*a))

theorem rowAt_continuous (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (r : Outside n S) (q : Inside n S) :
    Continuous (rowAt n β hβ S r q) := by
  have hU : Continuous (fun a : Inside n S => WilsonBlockMarginal.assemble S (r,a)) :=
    (WilsonBlockMarginal.assemble_continuous S).comp (continuous_const.prodMk continuous_id)
  exact (rowEntropy_continuous n β hβ).comp
    (f := fun a : Inside n S => (WilsonBlockMarginal.assemble S (r,a),
      WilsonBlockMarginal.assemble S (r,q*a)))
    (hU.prodMk (hU.comp (continuous_const.mul continuous_id)))

theorem rowAt_pair_bound (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (r : Outside n S) (q a : Inside n S) :
    rowAt n β hβ S r q a + rowAt n β hβ S r q⁻¹ a ≤ 18*β*cost n S q +
      WilsonBlockRotation.logGain n β hβ S r q a +
      WilsonBlockRotation.logGain n β hβ S r q⁻¹ a := by
  have h := WilsonJointEntropy.rowEntropy_pair_bound n β hβ (extend n S q)
    (WilsonBlockMarginal.assemble S (r,a))
  simpa only [extend_cost, extend_inv, extend_assemble, WilsonJointEntropy.logGain,
    rowAt, WilsonBlockRotation.logGain] using h

def meanEntropy (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (r : Outside n S) (q : Inside n S) : ℝ :=
  ∫ a, rowAt n β hβ S r q a ∂conditionalLaw n β hβ S r

theorem meanEntropy_nonneg (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (r : Outside n S) (q : Inside n S) :
    0 ≤ meanEntropy n β hβ S r q :=
  integral_nonneg (fun _a => rowEntropy_nonneg n β hβ _ _)

/-- The bound holds before taking the actual exterior marginal. -/
theorem meanEntropy_pair_bound (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (r : Outside n S) (q : Inside n S) :
    meanEntropy n β hβ S r q + meanEntropy n β hβ S r q⁻¹ ≤ 18*β*cost n S q := by
  letI := conditionalLaw_probability n β hβ S r
  have he (p : Inside n S) := continuous_integrable (conditionalLaw n β hβ S r) _
    (rowAt_continuous n β hβ S r p)
  have hl (p : Inside n S) := continuous_integrable (conditionalLaw n β hβ S r) _
    (WilsonBlockRotation.logGain_continuous n β hβ S r p)
  have hk : Integrable (fun _a : Inside n S => 18*β*cost n S q)
      (conditionalLaw n β hβ S r) := integrable_const _
  have h := integral_mono ((he q).add (he q⁻¹)) ((hk.add (hl q)).add (hl q⁻¹))
    (fun a => rowAt_pair_bound n β hβ S r q a)
  have hsum := integral_add (he q) (he q⁻¹)
  have hout := integral_add (hk.add (hl q)) (hl q⁻¹)
  have hin := integral_add hk (hl q)
  simp only [Pi.add_apply] at h hsum hout hin
  rw [hsum, hout, hin, integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  change meanEntropy n β hβ S r q + meanEntropy n β hβ S r q⁻¹ ≤
    18*β*cost n S q + gain n β hβ S r q + gain n β hβ S r q⁻¹ at h
  linarith [gain_nonpos n β hβ S r q, gain_nonpos n β hβ S r q⁻¹]

theorem meanEntropy_bound (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (r : Outside n S) (q : Inside n S) :
    meanEntropy n β hβ S r q ≤ 18*β*cost n S q := by
  linarith [meanEntropy_pair_bound n β hβ S r q, meanEntropy_nonneg n β hβ S r q⁻¹]

/-- The actual transfer response inside a true conditional block, uniformly in exterior. -/
theorem response_bound (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (r : Outside n S) (q : Inside n S)
    (f : C(Slice n, ℝ)) (lo hi : ℝ) (hf : ∀ v, f v ∈ Set.Icc lo hi) :
    (∫ a, (rowMean n β hβ f (WilsonBlockMarginal.assemble S (r,a)) -
      rowMean n β hβ f (WilsonBlockMarginal.assemble S (r,q*a)))^2
      ∂conditionalLaw n β hβ S r) ≤ 18*β*(hi-lo)^2*cost n S q := by
  letI := conditionalLaw_probability n β hβ S r
  have hU : Continuous (fun a : Inside n S => WilsonBlockMarginal.assemble S (r,a)) :=
    (WilsonBlockMarginal.assemble_continuous S).comp (continuous_const.prodMk continuous_id)
  have hP := (rowMean_continuous n β hβ f).comp hU
  have h := integral_mono
    (continuous_integrable (conditionalLaw n β hβ S r) _
      ((hP.sub (hP.comp (continuous_const.mul continuous_id))).pow 2))
    (continuous_integrable (conditionalLaw n β hβ S r) _
      (continuous_const.mul (rowAt_continuous n β hβ S r q)))
    (fun a => response_sq_le_rowEntropy n β hβ _ _ f lo hi hf)
  simp only [Pi.mul_apply, Function.comp_apply, id_eq] at h
  rw [integral_const_mul] at h
  have hb := mul_le_mul_of_nonneg_left (meanEntropy_bound n β hβ S r q) (sq_nonneg (hi-lo))
  change _ ≤ (hi-lo)^2*meanEntropy n β hβ S r q at h
  nlinarith

end
end UnifiedTheory.Clay.YangMills.WilsonConditionalEntropy
