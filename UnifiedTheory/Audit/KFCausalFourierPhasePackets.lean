/- Fourier signs for translated, phase-modulated functions. These identities
connect physical momentum phases to displacements of Fourier coordinates. -/
import UnifiedTheory.Audit.KFCausalFourierTranslation
import UnifiedTheory.Audit.KFCausalL2FourierIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalFourierPhasePackets
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalFourierTranslation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def modulated (u : E) (f : E → ℂ) (x : E) : ℂ := phase u x*f x

theorem modulated_integrable (u : E) (f : E → ℂ) (hf : Integrable f) :
    Integrable (modulated u f) := by
  apply hf.norm.mono' ((phase_continuous u).aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖phase u x*f x‖ ≤ ‖f x‖
  simp only [norm_mul,phase_norm,one_mul,le_refl]

theorem modulated_memLp (u : E) (f : E → ℂ) (hf : MemLp f 2) : MemLp (modulated u f) 2 := by
  apply hf.of_le ((phase_continuous u).aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖phase u x*f x‖ ≤ ‖f x‖
  simp only [norm_mul,phase_norm,one_mul,le_refl]

theorem fourier_modulated (u : E) (f : E → ℂ) (ξ : E) :
    (𝓕 (modulated u f)) ξ = (𝓕 f) (ξ-u) := by
  simp only [Real.fourier_eq,Circle.smul_def,smul_eq_mul,modulated,phase]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← mul_assoc,← Circle.coe_mul,← AddChar.map_add_eq_mul]
  have he : -inner ℝ x ξ+inner ℝ u x = -inner ℝ x (ξ-u) := by
    rw [inner_sub_right]
    have hc : inner ℝ u x = inner ℝ x u := real_inner_comm _ _
    rw [hc]
    ring
  rw [he]

def packet (u v : E) (f : E → ℂ) (x : E) : ℂ := modulated u f (x+v)

theorem packet_integrable (u v : E) (f : E → ℂ) (hf : Integrable f) :
    Integrable (packet u v f) :=
  (shift_preserves_volume v).integrable_comp_of_integrable (modulated_integrable u f hf)

theorem packet_memLp (u v : E) (f : E → ℂ) (hf : MemLp f 2) : MemLp (packet u v f) 2 :=
  (modulated_memLp u f hf).comp_measurePreserving (shift_preserves_volume v)

theorem fourier_packet (u v : E) (f : E → ℂ) (ξ : E) :
    (𝓕 (packet u v f)) ξ = phase v ξ*(𝓕 f) (ξ-u) := by
  have he := congrFun (VectorFourier.fourierIntegral_comp_add_right
    Real.fourierChar volume (innerₗ E) (modulated u f) v) ξ
  change (𝓕 (packet u v f)) ξ = phase v ξ*(𝓕 (modulated u f)) ξ at he
  exact he.trans (congrArg (fun z : ℂ => phase v ξ*z) (fourier_modulated u f ξ))

def phaseShift (r w : E) (g : E → ℂ) (x : E) : ℂ := phase r x*g (x+w)

theorem phaseShift_memLp (r w : E) (g : E → ℂ) (hg : MemLp g 2) :
    MemLp (phaseShift r w g) 2 :=
  modulated_memLp r (fun x => g (x+w)) (hg.comp_measurePreserving (shift_preserves_volume w))

#print axioms modulated_integrable
#print axioms modulated_memLp
#print axioms fourier_modulated
#print axioms packet_integrable
#print axioms packet_memLp
#print axioms fourier_packet
#print axioms phaseShift_memLp

end
end UnifiedTheory.Audit.KFCausalFourierPhasePackets
