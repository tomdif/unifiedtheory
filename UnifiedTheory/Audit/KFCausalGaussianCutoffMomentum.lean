/- Gaussian multiplication preserves the entire natural spectral momentum
graph. The product rule follows from the actual operator-norm derivative
and translation generator, with no smooth-state or core premise. -/
import UnifiedTheory.Audit.KFCausalGaussianCutoffOperator
import UnifiedTheory.Audit.KFCausalDirectionalTranslationMomentum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalGaussianCutoffMomentum
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalFourierTranslation (Hilbert translation translation_coe shift_preserves_volume)
open UnifiedTheory.Audit.KFCausalDirectionalTranslationMomentum
open UnifiedTheory.Audit.KFCausalGaussianCutoffOperator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (δ : ℝ) (hδ : 0 < δ) (l : E →L[ℝ] ℝ) (v : E)

theorem translation_cutoff (t : ℝ) (f : Hilbert (E := E)) :
    translation (t • v) (cutoff δ hδ l l.continuous.measurable (l v) 0 f) =
      cutoff δ hδ l l.continuous.measurable (l v) t (translation (t • v) f) := by
  apply Lp.ext
  filter_upwards [translation_coe (t • v) (cutoff δ hδ l l.continuous.measurable (l v) 0 f),
    (shift_preserves_volume (t • v)).quasiMeasurePreserving.ae
      (cutoff_coe δ hδ l l.continuous.measurable (l v) 0 f),
    cutoff_coe δ hδ l l.continuous.measurable (l v) t (translation (t • v) f),
    translation_coe (t • v) f] with x ht hs hc hf
  change cutoff δ hδ l l.continuous.measurable (l v) 0 f (x+t • v) =
    symbol δ l (l v) 0 (x+t • v)*f (x+t • v) at hs
  rw [ht,hs,hc,hf]
  simp only [symbol,map_add,map_smul,smul_eq_mul,zero_mul,add_zero]

theorem momentum_graph_cutoff (h : ℝ) (hh : h ≠ 0) (f g : Hilbert (E := E))
    (hfg : (f,g) ∈ (spectralMomentum h v).graph) :
    (cutoff δ hδ l l.continuous.measurable (l v) 0 f,
      cutoff δ hδ l l.continuous.measurable (l v) 0 g+
        (-Complex.I*(h:ℂ)) • derivativeOperator δ hδ l l.continuous.measurable (l v) f) ∈
      (spectralMomentum h v).graph := by
  let R := ContinuousLinearMap.restrictScalarsL ℂ (Hilbert (E := E)) (Hilbert (E := E)) ℝ ℝ
  have hB := R.hasFDerivAt.comp_hasDerivAt 0
    (cutoff_derivative (μ := volume) δ hδ l l.continuous.measurable (l v))
  have hd := hB.clm_apply ((spectralMomentum_graph_derivative h hh v f g).mp hfg)
  change HasDerivAt (fun t : ℝ => cutoff δ hδ l l.continuous.measurable (l v) t (translation (t • v) f))
    (derivativeOperator δ hδ l l.continuous.measurable (l v) (translation ((0:ℝ) • v) f)+
      cutoff δ hδ l l.continuous.measurable (l v) 0 ((Complex.I/(h:ℂ)) • g)) 0 at hd
  simp only [zero_smul,translation_initial,map_smul] at hd
  apply (spectralMomentum_graph_derivative h hh v _ _).mpr
  simp_rw [translation_cutoff]
  convert hd using 1
  rw [smul_add,smul_smul,KFCausalUnitaryMomentumEvolution.inverse_coefficient h hh,one_smul,add_comm]

theorem correction_norm (h : ℝ) (f : Hilbert (E := E)) :
    ‖(-Complex.I*(h:ℂ)) • derivativeOperator δ hδ l l.continuous.measurable (l v) f‖ ≤
      |h| *(2*Real.sqrt δ)*|l v| *‖f‖ := by
  rw [norm_smul,norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left
    (derivativeOperator_norm δ hδ l l.continuous.measurable (l v) f) (abs_nonneg h)).trans_eq (by ring)

#print axioms translation_cutoff
#print axioms momentum_graph_cutoff
#print axioms correction_norm

end
end UnifiedTheory.Audit.KFCausalGaussianCutoffMomentum
