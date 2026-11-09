/- The actual shear is a linear coordinate change in Euclidean variables.
Its inverse-adjoint Fourier map fixes the clock frequency exactly. -/
import UnifiedTheory.Audit.KFCausalTransverseShearTransport
import UnifiedTheory.Audit.KFCausalFourierLinearChange

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalTransverseShearEuclidean
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalTransverseShearTransport
open UnifiedTheory.Audit.KFCausalFourierLinearChange

def splitLinear : Space ≃ₗ[ℝ] Configuration :=
  { split.toEquiv with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

def linearFlow (t : ℝ) : Space ≃L[ℝ] Space :=
  (splitLinear.trans (((LinearEquiv.refl ℝ ℝ).prodCongr (flowEquiv t)).trans splitLinear.symm)).toContinuousLinearEquiv

theorem split_linearFlow (t : ℝ) (x : Space) :
    split (linearFlow t x) = shearFlow t (split x) := by
  change splitLinear (splitLinear.symm ((splitLinear x).1,flow t (splitLinear x).2)) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem linearFlow_clock (t : ℝ) : linearFlow t clockVector = clockVector := by
  apply split.injective
  rw [split_linearFlow]
  change (clockVector 0,flow t (fun i : Fin 5 => clockVector i.succ)) =
    (clockVector 0,fun i : Fin 5 => clockVector i.succ)
  have he : (fun i : Fin 5 => clockVector i.succ) = 0 := by
    funext i
    simp [clockVector,Fin.succ_ne_zero]
  rw [he]
  change (clockVector 0,flowEquiv t 0) = _
  rw [map_zero]

theorem inverse_linearFlow_clock (t : ℝ) : (linearFlow t).symm clockVector = clockVector := by
  apply (linearFlow t).injective
  rw [ContinuousLinearEquiv.apply_symm_apply,linearFlow_clock]

theorem dual_clock (t : ℝ) (k : Space) : dualEquiv (linearFlow t) k 0 = k 0 := by
  rw [← clockVector_inner,dual_inner,inverse_linearFlow_clock,clockVector_inner]

def euclideanTransport (t : ℝ) : FrequencyHilbert ≃ₗᵢ[ℂ] FrequencyHilbert :=
  euclideanPullback.symm.trans ((transport t).trans euclideanPullback)

theorem euclideanTransport_coe (t : ℝ) (f : FrequencyHilbert) :
    euclideanTransport t f =ᵐ[volume] fun x => (Real.exp t:ℂ)*f (linearFlow t x) := by
  have hi : euclideanPullback.symm f =ᵐ[volume] f ∘ split.symm :=
    KFCausalMeasureUnitaryPullback.unitaryPullback_symm_coe split split_preserves_volume f
  filter_upwards [euclideanPullback_coe (transport t (euclideanPullback.symm f)),
    split_preserves_volume.quasiMeasurePreserving.ae (transport_coe t (euclideanPullback.symm f)),
    ((shearFlow_quasiMeasurePreserving t).comp split_preserves_volume.quasiMeasurePreserving).ae hi]
    with x he ht hf
  dsimp only [Function.comp_apply] at he ht hf
  change euclideanPullback (transport t (euclideanPullback.symm f)) x = _
  rw [he,ht,hf,← split_linearFlow,MeasurableEquiv.symm_apply_apply]

theorem euclideanTransport_coordinates (t : ℝ) (f : Hilbert) :
    euclideanTransport t (euclideanPullback f) = euclideanPullback (transport t f) := by
  change euclideanPullback (transport t (euclideanPullback.symm (euclideanPullback f))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

#print axioms split_linearFlow
#print axioms linearFlow_clock
#print axioms inverse_linearFlow_clock
#print axioms dual_clock
#print axioms euclideanTransport_coe
#print axioms euclideanTransport_coordinates
end
end UnifiedTheory.Audit.KFCausalTransverseShearEuclidean
