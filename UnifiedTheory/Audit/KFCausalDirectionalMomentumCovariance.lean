/- Exact covariance of the maximal spectral momentum, derived by strong
differentiation of a proved bounded translation covariance identity. -/
import UnifiedTheory.Audit.KFCausalDirectionalTranslationMomentum
import UnifiedTheory.Audit.KFCausalCanonicalWeylDirac

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalDirectionalMomentumCovariance
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalFourierTranslation (Hilbert translation)
open UnifiedTheory.Audit.KFCausalDirectionalTranslationMomentum
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (scalar)
open UnifiedTheory.Audit.KFCausalCanonicalWeylDirac (scalar_derivative)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem spectral_graph_covariance (h : ℝ) (hh : h ≠ 0) (v : E)
    (B : Hilbert (E := E) →L[ℂ] Hilbert (E := E)) (c : ℝ)
    (hB : ∀ (t : ℝ) f, translation (t • v) (B f) = scalar (t*c) • B (translation (t • v) f))
    (f g : Hilbert (E := E)) (hfg : (f,g) ∈ (spectralMomentum h v).graph) :
    (B f,B (g+((h*c:ℝ):ℂ) • f)) ∈ (spectralMomentum h v).graph := by
  have hd := (B.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    ((spectralMomentum_graph_derivative h hh v f g).mp hfg)
  change HasDerivAt (fun t : ℝ => B (translation (t • v) f))
    (B ((Complex.I/(h:ℂ)) • g)) 0 at hd
  have hp := (scalar_derivative c).smul hd
  simp only [zero_smul,translation_initial,scalar,zero_mul,Complex.ofReal_zero,
    mul_zero,Complex.exp_zero,one_smul,map_smul] at hp
  apply (spectralMomentum_graph_derivative h hh v _ _).mpr
  simp_rw [hB]
  convert hp using 1
  rw [map_add,map_smul,smul_add,smul_smul]
  have he : (Complex.I/(h:ℂ))*((h*c:ℝ):ℂ) = Complex.I*(c:ℂ) := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hh]
  rw [he,add_comm]

#print axioms spectral_graph_covariance

end
end UnifiedTheory.Audit.KFCausalDirectionalMomentumCovariance
