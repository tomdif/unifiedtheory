/- The actual coupled Fourier map on noncompact L2 functions is the
ordinary L2 Fourier transform of the explicit straightened function.
This identifies the exponential-domain condition without assuming it. -/
import UnifiedTheory.Audit.KFCausalCoupledLpCoordinates
import UnifiedTheory.Audit.KFCausalLongitudinalExponential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalNoncompactFourierCoordinates
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalCoupledUnitaryCoordinates
open UnifiedTheory.Audit.KFCausalCoupledLpCoordinates
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalClockFourierDiagonalization
open UnifiedTheory.Audit.KFCausalLongitudinalFourierMultiplier
open UnifiedTheory.Audit.KFCausalLongitudinalExponential

theorem flatten_memLp (f : Configuration → ℂ) (hf : MemLp f 2) :
    MemLp (f ∘ split) 2 := hf.comp_measurePreserving split_preserves_volume

theorem flatten_toLp (f : Configuration → ℂ) (hf : MemLp f 2) :
    euclideanPullback (hf.toLp f) = (flatten_memLp f hf).toLp (f ∘ split) := by
  apply Lp.ext
  filter_upwards [euclideanPullback_coe (hf.toLp f),
    split_preserves_volume.quasiMeasurePreserving.ae hf.coeFn_toLp,
    (flatten_memLp f hf).coeFn_toLp] with x hx hf' hg
  simp only [Function.comp_apply] at hx hg
  rw [hx,hf',hg]

theorem fourier_toLp (f : Configuration → ℂ) (hf : MemLp f 2) :
    fourierCoordinates (hf.toLp f) =
      (Lp.fourierTransformₗᵢ Space ℂ) ((flatten_memLp f hf).toLp (f ∘ split)) := by
  change (Lp.fourierTransformₗᵢ Space ℂ) (euclideanPullback (hf.toLp f)) = _
  rw [flatten_toLp]

theorem coupledFourier_coordinates (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    coupledFourier ε hε (coordinates ε hε f) = fourierCoordinates f := by
  rw [coupledFourier_apply,LinearIsometryEquiv.symm_apply_apply]

theorem coupledFourier_weighted_toLp (ε : ℝ) (hε : 0 < ε)
    (f : Configuration → ℂ) (hf : MemLp f 2) :
    coupledFourier ε hε ((weighted_memLp ε hε f hf).toLp (weightedFunction ε hε f)) =
      (Lp.fourierTransformₗᵢ Space ℂ) ((flatten_memLp f hf).toLp (f ∘ split)) := by
  rw [← coordinates_toLp ε hε f hf,coupledFourier_coordinates,fourier_toLp f hf]

def spectralInput (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ) : Space → ℂ :=
  inverseFunction ε hε f ∘ split

theorem spectralInput_memLp (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ) (hf : MemLp f 2) :
    MemLp (spectralInput ε hε f) 2 := flatten_memLp _ (inverse_memLp ε hε f hf)

theorem coupledFourier_toLp (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ) (hf : MemLp f 2) :
    coupledFourier ε hε (hf.toLp f) =
      (Lp.fourierTransformₗᵢ Space ℂ) ((spectralInput_memLp ε hε f hf).toLp (spectralInput ε hε f)) := by
  rw [coupledFourier_apply,coordinates_inverse_toLp ε hε f hf,
    fourier_toLp _ (inverse_memLp ε hε f hf)]
  rfl

theorem weighted_half_domain (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
    (f : Configuration → ℂ) (hf : MemLp f 2) :
    (weighted_memLp ε hε f hf).toLp (weightedFunction ε hε f) ∈
      (longitudinalExponential ε hε hbar (1/2)).domain ↔
    Integrable (fun k => Real.exp (symbol hbar k)*
      ‖((Lp.fourierTransformₗᵢ Space ℂ) ((flatten_memLp f hf).toLp (f ∘ split))) k‖^2) := by
  rw [half_exponential_domain,coupledFourier_weighted_toLp ε hε f hf]

theorem function_half_domain (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
    (f : Configuration → ℂ) (hf : MemLp f 2 (volume : Measure Configuration)) :
    hf.toLp f ∈ (longitudinalExponential ε hε hbar (1/2)).domain ↔
    Integrable (fun k => Real.exp (symbol hbar k)*
      ‖((Lp.fourierTransformₗᵢ Space ℂ) ((spectralInput_memLp ε hε f hf).toLp (spectralInput ε hε f))) k‖^2) := by
  rw [half_exponential_domain,coupledFourier_toLp ε hε f hf]

theorem weighted_half_energy (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
    (f : Configuration → ℂ) (hf : MemLp f 2)
    (hd : (weighted_memLp ε hε f hf).toLp (weightedFunction ε hε f) ∈
      (longitudinalExponential ε hε hbar (1/2)).domain) :
    ‖longitudinalExponential ε hε hbar (1/2)
      ⟨(weighted_memLp ε hε f hf).toLp (weightedFunction ε hε f),hd⟩‖^2 =
    ∫ k, Real.exp (symbol hbar k)*
      ‖((Lp.fourierTransformₗᵢ Space ℂ) ((flatten_memLp f hf).toLp (f ∘ split))) k‖^2 := by
  rw [half_exponential_energy,coupledFourier_weighted_toLp ε hε f hf]

#print axioms flatten_memLp
#print axioms flatten_toLp
#print axioms fourier_toLp
#print axioms coupledFourier_coordinates
#print axioms coupledFourier_weighted_toLp
#print axioms spectralInput_memLp
#print axioms coupledFourier_toLp
#print axioms weighted_half_domain
#print axioms function_half_domain
#print axioms weighted_half_energy

end
end UnifiedTheory.Audit.KFCausalNoncompactFourierCoordinates
