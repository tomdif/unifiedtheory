/- Physical Gaussian multiplication has an exact bounded product correction
on every natural transverse momentum graph. The result is transported
through the actual measure-preserving Euclidean coordinates. -/
import UnifiedTheory.Audit.KFCausalGaussianCutoffMomentum
import UnifiedTheory.Audit.KFCausalClockFloorKineticModulation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalPhysicalGaussianCutoff
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalPhysicalTransverseMomentum
open UnifiedTheory.Audit.KFCausalClockFloorKineticDefect (transverse_graph_iff)
open UnifiedTheory.Audit.KFCausalGaussianCutoffTaylor (amplitude slope)

variable (δ : ℝ) (hδ : 0 < δ) (l : Configuration →L[ℝ] ℝ)

def cutoff : Hilbert →L[ℂ] Hilbert :=
  KFCausalGaussianCutoffOperator.cutoff δ hδ l l.continuous.measurable 0 0

def derivativeOperator (v : Transverse) : Hilbert →L[ℂ] Hilbert :=
  KFCausalGaussianCutoffOperator.derivativeOperator δ hδ l l.continuous.measurable (l (0,v))

def euclideanLinear : Space →L[ℝ] ℝ where
  toFun x := l (split x)
  map_add' x y := l.map_add (split x) (split y)
  map_smul' c x := l.map_smul c (split x)
  cont := by
    change Continuous (fun x : Space => l (x 0,fun i : Fin 5 => x i.succ))
    fun_prop

theorem euclideanLinear_direction (v : Transverse) : euclideanLinear l (transverseVector v) = l (0,v) := rfl

theorem cutoff_coe (f : Hilbert) : cutoff δ hδ l f =ᵐ[volume] fun x => (amplitude δ (l x):ℂ)*f x := by
  simpa only [KFCausalGaussianCutoffOperator.symbol,zero_mul,add_zero] using
    KFCausalGaussianCutoffOperator.cutoff_coe δ hδ l l.continuous.measurable 0 0 f

theorem derivativeOperator_coe (v : Transverse) (f : Hilbert) :
    derivativeOperator δ hδ l v f =ᵐ[volume] fun x => ((l (0,v)*slope δ (l x):ℝ):ℂ)*f x :=
  KFCausalGaussianCutoffOperator.derivativeOperator_coe δ hδ l l.continuous.measurable (l (0,v)) f

theorem cutoff_norm (f : Hilbert) : ‖cutoff δ hδ l f‖ ≤ ‖f‖ :=
  KFCausalContractiveMultiplier.multiply_norm_le _
    (KFCausalGaussianCutoffOperator.symbol_measurable δ l l.continuous.measurable 0 0)
    (KFCausalGaussianCutoffOperator.symbol_bound δ hδ l 0 0) f

theorem derivativeOperator_norm (v : Transverse) (f : Hilbert) :
    ‖derivativeOperator δ hδ l v f‖ ≤ |l (0,v)| * (2*Real.sqrt δ)*‖f‖ :=
  KFCausalGaussianCutoffOperator.derivativeOperator_norm δ hδ l l.continuous.measurable (l (0,v)) f

theorem euclidean_cutoff (v : Transverse) (f : Hilbert) :
    euclideanPullback (cutoff δ hδ l f) =
      KFCausalGaussianCutoffOperator.cutoff δ hδ (euclideanLinear l) (euclideanLinear l).continuous.measurable
        (euclideanLinear l (transverseVector v)) 0 (euclideanPullback f) := by
  apply Lp.ext
  filter_upwards [euclideanPullback_coe (cutoff δ hδ l f),euclideanPullback_coe f,
    split_preserves_volume.quasiMeasurePreserving.ae (cutoff_coe δ hδ l f),
    KFCausalGaussianCutoffOperator.cutoff_coe δ hδ (euclideanLinear l) (euclideanLinear l).continuous.measurable
      (euclideanLinear l (transverseVector v)) 0 (euclideanPullback f)] with x he hf hc hg
  simp only [Function.comp_apply] at he hf
  change cutoff δ hδ l f (split x) = _ at hc
  rw [he,hc,hg,hf]
  simp only [KFCausalGaussianCutoffOperator.symbol,zero_mul,add_zero]
  rfl

theorem euclidean_derivativeOperator (v : Transverse) (f : Hilbert) :
    euclideanPullback (derivativeOperator δ hδ l v f) =
      KFCausalGaussianCutoffOperator.derivativeOperator δ hδ (euclideanLinear l) (euclideanLinear l).continuous.measurable
        (euclideanLinear l (transverseVector v)) (euclideanPullback f) := by
  apply Lp.ext
  filter_upwards [euclideanPullback_coe (derivativeOperator δ hδ l v f),euclideanPullback_coe f,
    split_preserves_volume.quasiMeasurePreserving.ae (derivativeOperator_coe δ hδ l v f),
    KFCausalGaussianCutoffOperator.derivativeOperator_coe δ hδ (euclideanLinear l) (euclideanLinear l).continuous.measurable
      (euclideanLinear l (transverseVector v)) (euclideanPullback f)] with x he hf hc hg
  simp only [Function.comp_apply] at he hf
  change derivativeOperator δ hδ l v f (split x) = _ at hc
  rw [he,hc,hg,hf]
  rfl

theorem momentum_graph_cutoff (h : ℝ) (hh : h ≠ 0) (v : Transverse) (f g : Hilbert)
    (hfg : (f,g) ∈ (transverseMomentum h v).graph) :
    (cutoff δ hδ l f,cutoff δ hδ l g+(-Complex.I*(h:ℂ)) • derivativeOperator δ hδ l v f) ∈
      (transverseMomentum h v).graph := by
  have he := KFCausalGaussianCutoffMomentum.momentum_graph_cutoff δ hδ (euclideanLinear l)
    (transverseVector v) h hh _ _ ((transverse_graph_iff h v f g).mp hfg)
  apply (transverse_graph_iff h v _ _).mpr
  rw [euclidean_cutoff δ hδ l v,map_add,map_smul,euclidean_cutoff δ hδ l v,euclidean_derivativeOperator]
  exact he

#print axioms euclideanLinear_direction
#print axioms cutoff_coe
#print axioms derivativeOperator_coe
#print axioms cutoff_norm
#print axioms derivativeOperator_norm
#print axioms euclidean_cutoff
#print axioms euclidean_derivativeOperator
#print axioms momentum_graph_cutoff

end
end UnifiedTheory.Audit.KFCausalPhysicalGaussianCutoff
