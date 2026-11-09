/- Linear phase modulation preserves the full natural domains of the
actual physical transverse momenta. The momentum shift is derived from
strong translations, without smooth representatives or a core assumption. -/
import UnifiedTheory.Audit.KFCausalDirectionalMomentumCovariance
import UnifiedTheory.Audit.KFCausalClockFloorKineticDefect
import UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalPhysicalMomentumModulation
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalPhysicalTransverseMomentum
open UnifiedTheory.Audit.KFCausalClockFloorKineticDefect (transverse_graph_iff)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (scalar scalar_add)

def modulation (l : Configuration →L[ℝ] ℝ) : Hilbert ≃ₗᵢ[ℂ] Hilbert :=
  KFCausalLpPhaseTranslation.modulation volume l l.continuous.measurable

theorem modulation_coe (l : Configuration →L[ℝ] ℝ) (f : Hilbert) :
    modulation l f =ᵐ[volume] fun x => scalar (l x)*f x :=
  KFCausalLpPhaseTranslation.modulation_coe volume l l.continuous.measurable f

theorem modulation_inverse (l : Configuration →L[ℝ] ℝ) (f : Hilbert) :
    modulation (-l) (modulation l f) = f := by
  apply Lp.ext
  filter_upwards [modulation_coe (-l) (modulation l f),modulation_coe l f] with x hx hy
  rw [hx,hy,← mul_assoc,ContinuousLinearMap.neg_apply,← scalar_add,neg_add_cancel]
  simp only [scalar,Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_mul]

def euclideanModulation (l : Configuration →L[ℝ] ℝ) : FrequencyHilbert →L[ℂ] FrequencyHilbert :=
  (euclideanPullback : Hilbert →L[ℂ] FrequencyHilbert).comp
    ((modulation l : Hilbert →L[ℂ] Hilbert).comp (euclideanPullback.symm : FrequencyHilbert →L[ℂ] Hilbert))

theorem euclideanModulation_coe (l : Configuration →L[ℝ] ℝ) (f : FrequencyHilbert) :
    euclideanModulation l f =ᵐ[volume] fun x => scalar (l (split x))*f x := by
  have he : euclideanPullback (euclideanPullback.symm f) = f := euclideanPullback.apply_symm_apply f
  filter_upwards [euclideanPullback_coe (modulation l (euclideanPullback.symm f)),
    euclideanPullback_coe (euclideanPullback.symm f),
    split_preserves_volume.quasiMeasurePreserving.ae (modulation_coe l (euclideanPullback.symm f))]
    with x hx hy hz
  change euclideanPullback (modulation l (euclideanPullback.symm f)) x = _
  simp only [Function.comp_def] at hx hy
  rw [hx,hz]
  rw [he] at hy
  rw [hy]

theorem euclideanModulation_covariance (l : Configuration →L[ℝ] ℝ)
    (v : Transverse) (t : ℝ) (f : FrequencyHilbert) :
    KFCausalFourierTranslation.translation (t • transverseVector v) (euclideanModulation l f) =
      scalar (t*l (0,v)) • euclideanModulation l
        (KFCausalFourierTranslation.translation (t • transverseVector v) f) := by
  apply Lp.ext
  filter_upwards [KFCausalFourierTranslation.translation_coe (t • transverseVector v) (euclideanModulation l f),
    (KFCausalFourierTranslation.shift_preserves_volume (t • transverseVector v)).quasiMeasurePreserving.ae
      (euclideanModulation_coe l f),
    euclideanModulation_coe l (KFCausalFourierTranslation.translation (t • transverseVector v) f),
    KFCausalFourierTranslation.translation_coe (t • transverseVector v) f,
    Lp.coeFn_smul (scalar (t*l (0,v)))
      (euclideanModulation l (KFCausalFourierTranslation.translation (t • transverseVector v) f))]
    with x hx hy hz ht hc
  change euclideanModulation l f (x+t • transverseVector v) =
    scalar (l (split (x+t • transverseVector v)))*f (x+t • transverseVector v) at hy
  rw [hx,hy,hc]
  simp only [Pi.smul_apply,smul_eq_mul,hz,ht]
  have hs : split (x+t • transverseVector v) = split x+t • (0,v) := by
    rw [split_transverse_add]
    apply Prod.ext <;> simp
  rw [hs,map_add,map_smul,smul_eq_mul,scalar_add]
  ring

theorem momentum_graph_modulation (h : ℝ) (hh : h ≠ 0) (v : Transverse)
    (l : Configuration →L[ℝ] ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (transverseMomentum h v).graph) :
    (modulation l f,modulation l (g+((h*l (0,v):ℝ):ℂ) • f)) ∈ (transverseMomentum h v).graph := by
  have he := KFCausalDirectionalMomentumCovariance.spectral_graph_covariance h hh (transverseVector v)
    (euclideanModulation l) (l (0,v)) (euclideanModulation_covariance l v)
    _ _ ((transverse_graph_iff h v f g).mp hfg)
  apply (transverse_graph_iff h v _ _).mpr
  change (euclideanPullback (modulation l (euclideanPullback.symm (euclideanPullback f))),
    euclideanPullback (modulation l (euclideanPullback.symm
      (euclideanPullback g+((h*l (0,v):ℝ):ℂ) • euclideanPullback f)))) ∈ _ at he
  rw [show euclideanPullback g+((h*l (0,v):ℝ):ℂ) • euclideanPullback f =
    euclideanPullback (g+((h*l (0,v):ℝ):ℂ) • f) by rw [map_add,map_smul]] at he
  simpa only [LinearIsometryEquiv.symm_apply_apply] using he

theorem momentum_domain_modulation (h : ℝ) (hh : h ≠ 0) (v : Transverse)
    (l : Configuration →L[ℝ] ℝ) (f : Hilbert) :
    modulation l f ∈ (transverseMomentum h v).domain ↔ f ∈ (transverseMomentum h v).domain := by
  constructor
  · intro hf
    have he := momentum_graph_modulation h hh v (-l) _ _ ((transverseMomentum h v).mem_graph ⟨_,hf⟩)
    rw [modulation_inverse] at he
    exact LinearPMap.mem_domain_of_mem_graph he
  · intro hf
    exact LinearPMap.mem_domain_of_mem_graph
      (momentum_graph_modulation h hh v l f _ ((transverseMomentum h v).mem_graph ⟨f,hf⟩))

theorem momentum_graph_boost (h : ℝ) (hh : h ≠ 0) (v : Transverse)
    (l : Configuration →L[ℝ] ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (transverseMomentum h v).graph) :
    (modulation (h⁻¹ • l) f,modulation (h⁻¹ • l) (g+(l (0,v):ℂ) • f)) ∈
      (transverseMomentum h v).graph := by
  have he := momentum_graph_modulation h hh v (h⁻¹ • l) f g hfg
  simpa only [ContinuousLinearMap.smul_apply,smul_eq_mul,← mul_assoc,mul_inv_cancel₀ hh,one_mul] using he

#print axioms modulation_coe
#print axioms modulation_inverse
#print axioms euclideanModulation_coe
#print axioms euclideanModulation_covariance
#print axioms momentum_graph_modulation
#print axioms momentum_domain_modulation
#print axioms momentum_graph_boost

end
end UnifiedTheory.Audit.KFCausalPhysicalMomentumModulation
