/- A polynomial removal price for one actual temporal kinetic factor.
Both spatial potentials and every other kinetic link are retained. The
comparison holds for all continuous complex half-sources of the raw kernel;
its ground specialization uses the actual full-transfer eigenfunction and
eigenvalue. It does not remove a spatial plaquette from the ground model. -/
import UnifiedTheory.Clay.YangMills.SU2ReflectionInsertion
import UnifiedTheory.Clay.YangMills.WilsonTemporalGauge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonTemporalCutFloor
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonTemporalGauge
open WilsonGroundLocalComparison WilsonReflectionForm
open WilsonSingleLinkStaples (character character_continuous)

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

def unmarked (β : ℝ) (e : SpatialVertex n × Fin 3) (u v : Slice n) : ℝ :=
  ∏ i : {i : SpatialVertex n × Fin 3 // i ≠ e},
    SU2CrossingHaarFloor.kernel β (u i) (v i)

def cut (β : ℝ) (e : SpatialVertex n × Fin 3) (u v : Slice n) : ℝ :=
  spatialWeight character β 2 u * unmarked n β e u v * spatialWeight character β 2 v

theorem unmarked_continuous (β : ℝ) (e : SpatialVertex n × Fin 3) :
    Continuous (fun z : Slice n × Slice n => unmarked n β e z.1 z.2) := by
  unfold unmarked
  apply continuous_finset_prod
  intro i _
  exact (SU2CrossingHaarFloor.kernel_continuous β).comp
    (f := fun z : Slice n × Slice n => (z.1 i, z.2 i))
    (((continuous_apply i.val).comp continuous_fst).prodMk
      ((continuous_apply i.val).comp continuous_snd))

theorem cut_continuous (β : ℝ) (e : SpatialVertex n × Fin 3) :
    Continuous (fun z : Slice n × Slice n => cut n β e z.1 z.2) := by
  have hw : Continuous (spatialWeight character β 2 : Slice n → ℝ) := by
    have hχ := character_continuous
    unfold spatialWeight potential spatialHolonomy
    fun_prop
  exact ((hw.comp continuous_fst).mul (unmarked_continuous n β e)).mul
    (hw.comp continuous_snd)

theorem kinetic_product (β : ℝ) (u v : Slice n) :
    kineticWeight character β 2 u v =
      ∏ e, SU2CrossingHaarFloor.kernel β (u e) (v e) := by
  simp only [SU2CrossingHaarFloor.kernel, SU2GaussianMass.weight,
    SU2GaussianMass.chord_square, ← Real.exp_sum]
  unfold kineticWeight kineticAction
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [WilsonSingleLinkStaples.character_re]
  ring

theorem unmarked_factor (β : ℝ) (e : SpatialVertex n × Fin 3) (u v : Slice n) :
    unmarked n β e u v * SU2CrossingHaarFloor.kernel β (u e) (v e) =
      kineticWeight character β 2 u v := by
  rw [kinetic_product, unmarked, ← Finset.prod_subtype (Finset.univ.erase e)
    (fun i => by simp) (fun i => SU2CrossingHaarFloor.kernel β (u i) (v i))]
  exact Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ e)

theorem raw_factor (β : ℝ) (e : SpatialVertex n × Fin 3) (u v : Slice n) :
    cut n β e u v * SU2CrossingHaarFloor.kernel β (u e) (v e) =
      rawKernel character β 2 u v := by
  unfold cut rawKernel
  rw [show spatialWeight character β 2 u * unmarked n β e u v *
      spatialWeight character β 2 v * SU2CrossingHaarFloor.kernel β (u e) (v e) =
      spatialWeight character β 2 u *
        (unmarked n β e u v * SU2CrossingHaarFloor.kernel β (u e) (v e)) *
          spatialWeight character β 2 v by ring, unmarked_factor]

/-- No volume factor occurs, and the spatial potentials are not discarded. -/
theorem quadratic_removal (β : ℝ) (hβ : 3 / 4 ≤ β)
    (e : SpatialVertex n × Fin 3) (f : Slice n → ℂ) (hf : Continuous f) :
    (reflectionForm (WilsonSlabOperator.measure n) (cut n β e) f).re ≤ SU2GaussianMass.cap β *
      (reflectionForm (WilsonSlabOperator.measure n) (rawKernel character β 2) f).re := by
  let g : Slice n → ℂ := fun u => (spatialWeight character β 2 u : ℂ) * f u
  have hg : Continuous g := by
    have hw : Continuous (spatialWeight character β 2 : Slice n → ℝ) := by
      have hχ := character_continuous
      unfold spatialWeight potential spatialHolonomy
      fun_prop
    exact (Complex.continuous_ofReal.comp hw).mul hf
  have hi := SU2ReflectionInsertion.crossing_polynomial_removal (WilsonSlabOperator.measure n)
    (fun _ : {i : SpatialVertex n × Fin 3 // i ≠ e} => β) (fun _ => by linarith)
    (fun i u => u i) (fun i => continuous_apply i.val) (fun u => u e)
    (continuous_apply e) β hβ g hg
  change (reflectionForm (WilsonSlabOperator.measure n) (unmarked n β e) g).re ≤
    SU2GaussianMass.cap β * (reflectionForm (WilsonSlabOperator.measure n)
      (fun u v => unmarked n β e u v * SU2CrossingHaarFloor.kernel β (u e) (v e)) g).re at hi
  have he : (fun u v => unmarked n β e u v *
      SU2CrossingHaarFloor.kernel β (u e) (v e)) = kineticWeight character β 2 := by
    funext u v
    exact unmarked_factor n β e u v
  rw [he] at hi
  change (reflectionForm (WilsonSlabOperator.measure n)
    (fun u v => spatialWeight character β 2 u * unmarked n β e u v *
      spatialWeight character β 2 v) f).re ≤ _
  change _ ≤ SU2GaussianMass.cap β * (reflectionForm (WilsonSlabOperator.measure n)
    (fun u v => spatialWeight character β 2 u * kineticWeight character β 2 u v *
      spatialWeight character β 2 v) f).re
  rw [reflectionForm_weights, reflectionForm_weights]
  exact hi

theorem real_reflection (K : Slice n → Slice n → ℝ) (f : Slice n → ℝ) :
    (reflectionForm (WilsonSlabOperator.measure n) K (fun u => (f u : ℂ))).re =
      ∫ z : Slice n × Slice n, f z.1 * K z.1 z.2 * f z.2
        ∂(WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n) := by
  unfold reflectionForm
  simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    integral_complex_ofReal, Complex.ofReal_re]

theorem ground_raw_pairing (β : ℝ) (hβ : 0 ≤ β) :
    (∫ z : Slice n × Slice n, ground n β hβ z.1 * rawKernel character β 2 z.1 z.2 *
      ground n β hβ z.2 ∂(WilsonSlabOperator.measure n).prod
        (WilsonSlabOperator.measure n)) = ‖transfer n β‖ := by
  have hi : Integrable (fun z : Slice n × Slice n => ground n β hβ z.1 *
      rawKernel character β 2 z.1 z.2 * ground n β hβ z.2)
        ((WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n)) := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact (((ground n β hβ).continuous.comp continuous_fst).mul
      (rawKernel_continuous character character_continuous β 2)).mul
        ((ground n β hβ).continuous.comp continuous_snd)
  rw [integral_prod _ hi]
  have he (u : Slice n) :
      (∫ v, ground n β hβ u * rawKernel character β 2 u v * ground n β hβ v
        ∂WilsonSlabOperator.measure n) =
        ‖transfer n β‖ * (ground n β hβ u)^2 := by
    simp_rw [mul_assoc]
    rw [integral_const_mul, ground_raw_equation]
    ring
  simp only [he]
  rw [integral_const_mul, ground_square_integral, mul_one]

/-- The true full-transfer normalization controls this omitted temporal factor
with a polynomial price, without a supplied ground-state reflection premise. -/
theorem ground_removal (β : ℝ) (hβ : 3 / 4 ≤ β) (e : SpatialVertex n × Fin 3) :
    (∫ z : Slice n × Slice n, ground n β (by linarith) z.1 * cut n β e z.1 z.2 *
      ground n β (by linarith) z.2 ∂(WilsonSlabOperator.measure n).prod
        (WilsonSlabOperator.measure n)) ≤
        SU2GaussianMass.cap β * ‖transfer n β‖ := by
  have hi := quadratic_removal n β hβ e (fun u => (ground n β (by linarith) u : ℂ))
    (Complex.continuous_ofReal.comp (ground n β (by linarith)).continuous)
  rwa [real_reflection, real_reflection, ground_raw_pairing] at hi

end
end UnifiedTheory.Clay.YangMills.WilsonTemporalCutFloor
