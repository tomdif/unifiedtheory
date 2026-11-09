/- Exact position marginal of the existing positive windowed law: the
difference of independent configuration Born variables. This follows
from spectator projections and the actual partial Fourier unitary. -/
import UnifiedTheory.Audit.KFCausalBornLocalization
import UnifiedTheory.Audit.KFCausalWindowedPhaseSpaceLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalWindowedPositionMarginal
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalWindowedPhaseSpaceState
open UnifiedTheory.Audit.KFCausalWindowedPhaseSpaceLaw
open UnifiedTheory.Audit.KFCausalPartialFourier
open UnifiedTheory.Audit.KFCausalPartialFourierMultiplier
open UnifiedTheory.Audit.KFCausalBornLocalization

theorem leftFourier_marginal (n m : ℕ) (f : ProductHilbert n m)
    (A : Set (Block m)) (hA : MeasurableSet A) :
    KFCausalL2BornLaw.law volume (leftFourier n m f) (Prod.snd ⁻¹' A) =
      KFCausalL2BornLaw.law volume f (Prod.snd ⁻¹' A) := by
  classical
  let w : Block m → ℂ := A.indicator (fun _ => 1)
  have hw : Measurable w := measurable_const.indicator hA
  have hb (x : Block m) : ‖w x‖ ≤ 1 := by by_cases hx : x ∈ A <;> simp [w,hx]
  have he (g : ProductHilbert n m) : mask volume (Prod.snd ⁻¹' A)
      (hA.preimage measurable_snd) g = rightMultiplier n m w hw hb g := by
    rfl
  rw [law_mask volume _ (hA.preimage measurable_snd),law_mask volume _ (hA.preimage measurable_snd),
    he,he,← leftFourier_commutes n m w hw hb,LinearIsometryEquiv.norm_map]

theorem position_marginal (n : ℕ) (h : ℝ) (f g : BlockHilbert n)
    (A : Set (Block n)) (hA : MeasurableSet A) :
    law n h f g (Prod.fst ⁻¹' A) =
      ((KFCausalL2BornLaw.law volume f).prod (KFCausalL2BornLaw.law volume g))
        {z : Block n × Block n | z.1-z.2 ∈ A} := by
  rw [law,Measure.map_apply (phaseCoordinates_measurable n h) (hA.preimage measurable_fst)]
  change KFCausalL2BornLaw.law volume
    (leftFourier n n (shearUnitary n (KFCausalL2TensorEmbedding.productState volume volume f g)))
      (Prod.snd ⁻¹' A) = _
  rw [leftFourier_marginal n n _ A hA]
  change KFCausalL2BornLaw.law volume
    (KFCausalMeasureUnitaryPullback.unitaryPullback (shear n) (shear_preserves n)
      (KFCausalL2TensorEmbedding.productState volume volume f g)) (Prod.snd ⁻¹' A) = _
  rw [law_pullback volume volume,Measure.map_apply (shear n).symm.measurable
    (hA.preimage measurable_snd)]
  change KFCausalL2BornLaw.law (volume.prod volume)
    (KFCausalL2TensorEmbedding.productState volume volume f g)
      ((shear n).symm ⁻¹' (Prod.snd ⁻¹' A)) = _
  rw [law_product]
  rfl

def positionLaw (n : ℕ) (i : Fin n) (f : BlockHilbert n) : Measure ℝ :=
  (KFCausalL2BornLaw.law volume f).map (fun x : Block n => x i)

def marginal (n : ℕ) (i : Fin n) (h : ℝ) (f g : BlockHilbert n) : Measure ℝ :=
  (law n h f g).map (fun z : Block n × Block n => z.1 i)

theorem marginal_product (n : ℕ) (i : Fin n) (h : ℝ) (f g : BlockHilbert n) :
    marginal n i h f g =
      ((KFCausalL2BornLaw.law volume f).prod (KFCausalL2BornLaw.law volume g)).map
        (fun z : Block n × Block n => z.1 i-z.2 i) := by
  ext A hA
  rw [marginal,Measure.map_apply (by fun_prop) hA,Measure.map_apply (by fun_prop) hA]
  have he := position_marginal n h f g ((fun x : Block n => x i) ⁻¹' A)
    (hA.preimage (by fun_prop))
  simpa only [Set.preimage_preimage,Function.comp_def,PiLp.sub_apply] using he

#print axioms leftFourier_marginal
#print axioms position_marginal
#print axioms marginal_product

end
end UnifiedTheory.Audit.KFCausalWindowedPositionMarginal
