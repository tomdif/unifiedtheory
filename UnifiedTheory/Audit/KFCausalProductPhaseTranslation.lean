/- Phase-translation observables factor exactly on product L2 states.
The maps are unitaries on the entire product Hilbert space. -/
import UnifiedTheory.Audit.KFCausalLpPhaseTranslation
import UnifiedTheory.Audit.KFCausalL2TensorEmbedding

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalProductPhaseTranslation
noncomputable section
open MeasureTheory MeasureTheory.Measure
open UnifiedTheory.Audit.KFCausalL2TensorEmbedding
open UnifiedTheory.Audit.KFCausalLpPhaseTranslation

variable {X Y : Type*} [NormedAddCommGroup X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup Y] [MeasurableSpace Y] [BorelSpace Y]
  (μ : Measure X) (ν : Measure Y) [Measure.IsAddHaarMeasure μ] [Measure.IsAddHaarMeasure ν]
  [SFinite μ] [SFinite ν]

local instance prodHaar : Measure.IsAddHaarMeasure (μ.prod ν) := Measure.prod.instIsAddHaarMeasure _ _

omit [NormedAddCommGroup X] [BorelSpace X] [NormedAddCommGroup Y] [BorelSpace Y]
  [Measure.IsAddHaarMeasure μ] [Measure.IsAddHaarMeasure ν] in
theorem product_norm (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    ‖productState μ ν f g‖ = ‖f‖*‖g‖ := by
  have he := congrArg Complex.re (productState_inner μ ν f f g g)
  simp only [inner_self_eq_norm_sq_to_K] at he
  change ((‖productState μ ν f g‖:ℂ)^2).re = (((‖f‖:ℂ)^2)*((‖g‖:ℂ)^2)).re at he
  norm_cast at he
  nlinarith only [he,norm_nonneg (productState μ ν f g),mul_nonneg (norm_nonneg f) (norm_nonneg g)]

omit [NormedAddCommGroup X] [BorelSpace X] [NormedAddCommGroup Y] [BorelSpace Y]
  [Measure.IsAddHaarMeasure μ] [Measure.IsAddHaarMeasure ν] [SFinite μ] [SFinite ν] in
theorem product_real_smul_left (r : ℝ) (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    productState μ ν (r • f) g = r • productState μ ν f g :=
  productState_smul_left μ ν (r:ℂ) f g

omit [NormedAddCommGroup X] [BorelSpace X] [NormedAddCommGroup Y] [BorelSpace Y]
  [Measure.IsAddHaarMeasure μ] [Measure.IsAddHaarMeasure ν] [SFinite μ] [SFinite ν] in
theorem product_real_smul_right (r : ℝ) (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    productState μ ν f (r • g) = r • productState μ ν f g :=
  productState_smul_right μ ν (r:ℂ) f g

variable [BorelSpace (X × Y)]

theorem product_phaseTranslation (l : X → ℝ) (hl : Measurable l) (m : Y → ℝ) (hm : Measurable m)
    (v : X) (w : Y) (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    phaseTranslation (μ.prod ν) (fun z : X × Y => l z.1+m z.2)
      ((hl.comp measurable_fst).add (hm.comp measurable_snd)) (v,w) (productState μ ν f g) =
      productState μ ν (phaseTranslation μ l hl v f) (phaseTranslation ν m hm w g) := by
  apply Lp.ext
  filter_upwards [phaseTranslation_coe (μ.prod ν) (fun z : X × Y => l z.1+m z.2)
      ((hl.comp measurable_fst).add (hm.comp measurable_snd)) (v,w) (productState μ ν f g),
    (shift_preserves (μ.prod ν) (v,w)).quasiMeasurePreserving.ae (productState_coe μ ν f g),
    productState_coe μ ν (phaseTranslation μ l hl v f) (phaseTranslation ν m hm w g),
    quasiMeasurePreserving_fst.ae (phaseTranslation_coe μ l hl v f),
    quasiMeasurePreserving_snd.ae (phaseTranslation_coe ν m hm w g)] with z hz hp ho hf hg
  change productState μ ν f g (z+(v,w)) = f (z.1+v)*g (z.2+w) at hp
  rw [hz,hp,ho,hf,hg]
  simp only [phase,Complex.ofReal_add,mul_add,Complex.exp_add]
  ring

theorem product_characteristic (l : X → ℝ) (hl : Measurable l) (m : Y → ℝ) (hm : Measurable m)
    (v : X) (w : Y) (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    inner ℂ (productState μ ν f g)
      (phaseTranslation (μ.prod ν) (fun z : X × Y => l z.1+m z.2)
        ((hl.comp measurable_fst).add (hm.comp measurable_snd)) (v,w) (productState μ ν f g)) =
      inner ℂ f (phaseTranslation μ l hl v f)*inner ℂ g (phaseTranslation ν m hm w g) := by
  rw [product_phaseTranslation,productState_inner]

#print axioms product_norm
#print axioms product_real_smul_left
#print axioms product_real_smul_right
#print axioms product_phaseTranslation
#print axioms product_characteristic

end
end UnifiedTheory.Audit.KFCausalProductPhaseTranslation
