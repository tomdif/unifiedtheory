/- Pointwise fixed-probe representation of the actual windowed L2 state.
The window and state are arbitrary L2 vectors, without moment hypotheses. -/
import UnifiedTheory.Audit.KFCausalPartialFourierIntegrableSlices
import UnifiedTheory.Audit.KFCausalWindowedPhaseSpaceState
import UnifiedTheory.Audit.KFCausalFourierTranslation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalWindowedPhaseSpaceProbe
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalL2TensorEmbedding
open UnifiedTheory.Audit.KFCausalWindowedPhaseSpaceState
open UnifiedTheory.Audit.KFCausalPartialFourierSlices
open UnifiedTheory.Audit.KFCausalFourierTranslation

variable (n : ℕ)

def probe (g : BlockHilbert n) (z : Block n × Block n) : BlockHilbert n :=
  (translation z.2).symm (phaseAction z.1 (star g))

def amplitude (f g : BlockHilbert n) (z : Block n × Block n) : ℂ :=
  inner ℂ (probe n g z) f

theorem probe_norm (g : BlockHilbert n) (z : Block n × Block n) :
    ‖probe n g z‖ = ‖g‖ := by
  simp only [probe,LinearIsometryEquiv.norm_map]
  apply le_antisymm
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_star g] with x hx
    simp only [hx,Pi.star_apply,norm_star,le_refl]
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_star g] with x hx
    simp only [hx,Pi.star_apply,norm_star,le_refl]

theorem amplitude_bound (f g : BlockHilbert n) (z : Block n × Block n) :
    ‖amplitude n f g z‖ ≤ ‖f‖ * ‖g‖ := by
  simpa only [amplitude,probe_norm,mul_comm] using
    (norm_inner_le_norm (𝕜 := ℂ) (probe n g z) f)

private theorem sheared_measurable (f g : BlockHilbert n) :
    Measurable (fun z : Block n × Block n => f (z.1+z.2)*g z.1) :=
  ((Lp.stronglyMeasurable f).measurable.comp (measurable_fst.add measurable_snd)).mul
    ((Lp.stronglyMeasurable g).measurable.comp measurable_fst)

private theorem sheared_slice_integrable (f g : BlockHilbert n) (q : Block n) :
    Integrable (fun x : Block n => f (x+q)*g x) := by
  apply (L2.integrable_inner (𝕜 := ℂ) (star g) (translation q f)).congr
  filter_upwards [Lp.coeFn_star g,translation_coe q f] with x hg hf
  rw [hg,hf,RCLike.inner_apply']
  simp only [Pi.star_apply,starRingEnd_apply,star_star]
  exact mul_comm _ _

theorem amplitude_integral (f g : BlockHilbert n) (z : Block n × Block n) :
    amplitude n f g z =
      leftIntegral n n (fun w : Block n × Block n => f (w.1+w.2)*g w.1) z := by
  have hi := (translation z.2).inner_map_map (probe n g z) f
  rw [probe,LinearIsometryEquiv.apply_symm_apply] at hi
  rw [amplitude,probe,← hi,L2.inner_def]
  change (∫ x, inner ℂ ((phaseAction z.1 (star g)) x) ((translation z.2 f) x)) =
    ∫ x, (Real.fourierChar (-inner ℝ x z.1) : ℂ) * (f (x+z.2)*g x)
  apply integral_congr_ae
  filter_upwards [phaseAction_coe z.1 (star g),Lp.coeFn_star g,
    translation_coe z.2 f] with x hp hg hf
  rw [hp,hg,hf,RCLike.inner_apply',map_mul]
  simp only [Pi.star_apply,starRingEnd_apply,star_star]
  have he : star (phase z.1 x) = (Real.fourierChar (-inner ℝ x z.1) : ℂ) := by
    rw [phase,real_inner_comm,AddChar.map_neg_eq_inv,Circle.coe_inv_eq_conj]
    rfl
  rw [he]
  ring

theorem amplitude_measurable (f g : BlockHilbert n) :
    AEStronglyMeasurable (amplitude n f g) volume := by
  have he : amplitude n f g =
      leftIntegral n n (fun w : Block n × Block n => f (w.1+w.2)*g w.1) :=
    funext (amplitude_integral n f g)
  rw [he]
  exact KFCausalPartialFourierIntegrableSlices.integral_measurable n n _
    (sheared_measurable n f g)

theorem state_coe (f g : BlockHilbert n) :
    state n f g =ᵐ[volume] amplitude n f g := by
  let F : Block n × Block n → ℂ := fun w => f (w.1+w.2)*g w.1
  have h2 : MemLp F 2 :=
    (Lp.memLp (shearUnitary n (productState volume volume f g))).ae_eq
      (shear_product_coe n f g)
  have he : shearUnitary n (productState volume volume f g) = h2.toLp F := by
    apply Lp.ext
    exact (shear_product_coe n f g).trans h2.coeFn_toLp.symm
  change KFCausalPartialFourier.leftFourier n n
    (shearUnitary n (productState volume volume f g)) =ᵐ[volume] _
  rw [he]
  have ht := KFCausalPartialFourierIntegrableSlices.unitary_toLp_coe n n F
    (sheared_measurable n f g)
    (Filter.Eventually.of_forall (sheared_slice_integrable n f g)) h2
  exact ht.trans (Filter.Eventually.of_forall (fun z => (amplitude_integral n f g z).symm))

#print axioms probe_norm
#print axioms amplitude_bound
#print axioms amplitude_integral
#print axioms amplitude_measurable
#print axioms state_coe

end
end UnifiedTheory.Audit.KFCausalWindowedPhaseSpaceProbe
