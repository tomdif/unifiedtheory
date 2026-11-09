/- Configuration concatenation preserves Lebesgue volume. Pulling the actual
external Schwartz product through this coordinate equivalence gives the
multi-point tensor test used by products of smeared observables. -/
import UnifiedTheory.Clay.YangMills.SchwartzProductTensor
import UnifiedTheory.Clay.YangMills.ContinuumControl
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SchwartzConfigurationTensor
noncomputable section
open MeasureTheory ContinuumControl
open scoped NNReal ENNReal

def indexEquiv (m n : ℕ) : (Fin m × Fin 4) ⊕ (Fin n × Fin 4) ≃ Fin (m+n) × Fin 4 :=
  (Equiv.sumProdDistrib (Fin m) (Fin n) (Fin 4)).symm.trans
    (Equiv.prodCongr finSumFinEquiv (Equiv.refl (Fin 4)))

def split (m n : ℕ) : Configuration (m+n) ≃L[ℝ] Configuration m × Configuration n :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (indexEquiv m n).symm).toContinuousLinearEquiv.trans
    EuclideanSpace.sumEquivProd

def concat (m n : ℕ) : (Configuration m × Configuration n) ≃L[ℝ] Configuration (m+n) :=
  (split m n).symm

@[simp] theorem split_fst (m n : ℕ) (x : Configuration (m+n)) (i : Fin m) (μ : Fin 4) :
    (split m n x).1 (i, μ) = x (Fin.castAdd n i, μ) := rfl

@[simp] theorem split_snd (m n : ℕ) (x : Configuration (m+n)) (i : Fin n) (μ : Fin 4) :
    (split m n x).2 (i, μ) = x (Fin.natAdd m i, μ) := rfl

@[simp] theorem split_concat (m n : ℕ) (x : Configuration m × Configuration n) :
    split m n (concat m n x) = x := (split m n).apply_symm_apply x

@[simp] theorem concat_split (m n : ℕ) (x : Configuration (m+n)) :
    concat m n (split m n x) = x := (split m n).symm_apply_apply x

@[simp] theorem concat_left (m n : ℕ) (x : Configuration m × Configuration n)
    (i : Fin m) (μ : Fin 4) : concat m n x (Fin.castAdd n i, μ) = x.1 (i, μ) := by
  rw [← split_fst, split_concat]

@[simp] theorem concat_right (m n : ℕ) (x : Configuration m × Configuration n)
    (i : Fin n) (μ : Fin 4) : concat m n x (Fin.natAdd m i, μ) = x.2 (i, μ) := by
  rw [← split_snd, split_concat]

theorem split_preserves_volume (m n : ℕ) : MeasurePreserving (split m n) := by
  have hp := ((PiLp.volume_preserving_toLp (Fin m × Fin 4)).prod
    (PiLp.volume_preserving_toLp (Fin n × Fin 4))).comp
      ((volume_measurePreserving_sumPiEquivProdPi
        (fun _ : (Fin m × Fin 4) ⊕ (Fin n × Fin 4) => ℝ)).comp
          ((volume_measurePreserving_piCongrLeft
            (fun _ : (Fin m × Fin 4) ⊕ (Fin n × Fin 4) => ℝ) (indexEquiv m n).symm).comp
              (PiLp.volume_preserving_ofLp (Fin (m+n) × Fin 4))))
  convert hp using 1
  ext x i <;>
    simp [split, EuclideanSpace.sumEquivProd, PiLp.sumPiLpEquivProdLpPiLp,
      MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, MeasurableEquiv.sumPiEquivProdPi,
      Equiv.piCongrLeft']

theorem concat_preserves_volume (m n : ℕ) : MeasurePreserving (concat m n) :=
  MeasurePreserving.symm (split m n).toHomeomorph.toMeasurableEquiv (split_preserves_volume m n)

theorem integral_concat (m n : ℕ) (h : Configuration (m+n) → ℂ) :
    (∫ x, h (concat m n x)) = ∫ x, h x :=
  (concat_preserves_volume m n).integral_comp (concat m n).toHomeomorph.measurableEmbedding h

def tensorLeftCLM (m n : ℕ) (g : CorrelationTest n) :
    CorrelationTest m →L[ℂ] CorrelationTest (m+n) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (split m n)).comp
    (SchwartzProductTensor.tensorLeftCLM g)

def tensor (m n : ℕ) (f : CorrelationTest m) (g : CorrelationTest n) : CorrelationTest (m+n) :=
  tensorLeftCLM m n g f

@[simp] theorem tensor_apply (m n : ℕ) (f : CorrelationTest m) (g : CorrelationTest n)
    (x : Configuration (m+n)) : tensor m n f g x = f (split m n x).1 * g (split m n x).2 := rfl

@[simp] theorem tensor_concat (m n : ℕ) (f : CorrelationTest m) (g : CorrelationTest n)
    (x : Configuration m) (y : Configuration n) : tensor m n f g (concat m n (x,y)) = f x * g y := by
  rw [tensor_apply, split_concat]

theorem continuous_tensor_left (m n : ℕ) (g : CorrelationTest n) :
    Continuous (fun f : CorrelationTest m => tensor m n f g) := (tensorLeftCLM m n g).continuous

end
end UnifiedTheory.Clay.YangMills.SchwartzConfigurationTensor
