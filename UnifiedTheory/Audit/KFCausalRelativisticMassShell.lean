/- Four-dimensional positive-frequency mass-shell measure and its actual
one-particle Hilbert space and self-adjoint energy operator. Lorentz
invariance of the measure and spacelike commutator support are separate
statements and are not assumed here. Spatial Fourier factors use unit
normalization; an overall (2*pi)^(-3) can be absorbed by a Hilbert isometry. -/
import UnifiedTheory.Audit.KFCausalRealMultiplierSelfAdjoint
import UnifiedTheory.Audit.KFCausalMassEuclideanKernel
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option Elab.async false

namespace UnifiedTheory.Audit.KFCausalRelativisticMassShell
noncomputable section
open MeasureTheory
open KFCausalUnitaryRealMultiplier KFCausalRealMultiplierSelfAdjoint

abbrev Momentum := EuclideanSpace ℝ (Fin 3)
abbrev ShellPoint := ℝ × Momentum

def frequency (δ : ℝ) (x : ShellPoint) : ℝ :=
  Real.sqrt (‖x.2‖^2 + max (δ^2) x.1)

theorem frequency_continuous (δ : ℝ) : Continuous (frequency δ) := by
  unfold frequency
  fun_prop

theorem frequency_lower (δ : ℝ) (hδ : 0 < δ) (x : ShellPoint) : δ ≤ frequency δ x :=
  KFCausalMassEuclideanKernel.energy_lower δ hδ ‖x.2‖ x.1

theorem frequency_pos (δ : ℝ) (hδ : 0 < δ) (x : ShellPoint) : 0 < frequency δ x :=
  hδ.trans_le (frequency_lower δ hδ x)

def shellMeasure (ρ : Measure ℝ) (δ : ℝ) : Measure ShellPoint :=
  (ρ.prod (volume : Measure Momentum)).withDensity
    (fun x => ENNReal.ofReal ((2*frequency δ x)⁻¹))

abbrev OneParticle (ρ : Measure ℝ) (δ : ℝ) := Lp ℂ 2 (shellMeasure ρ δ)

theorem shell_equation (ρ : Measure ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ᵐ s ∂ρ, δ^2 ≤ s) :
    ∀ᵐ x ∂shellMeasure ρ δ, (frequency δ x)^2 - ‖x.2‖^2 = x.1 := by
  rw [shellMeasure, ae_withDensity_iff (by unfold frequency; fun_prop)]
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hρ] with x hx
  intro _
  unfold frequency
  rw [max_eq_right hx, Real.sq_sqrt (by nlinarith [sq_nonneg ‖x.2‖, sq_nonneg δ])]
  ring

def energyOperator (ρ : Measure ℝ) (δ : ℝ) : OneParticle ρ δ →ₗ.[ℂ] OneParticle ρ δ :=
  realPullback (LinearIsometryEquiv.refl ℂ (OneParticle ρ δ)) (frequency δ)
    (frequency_continuous δ).measurable

theorem energy_selfAdjoint (ρ : Measure ℝ) (δ : ℝ) : IsSelfAdjoint (energyOperator ρ δ) :=
  realPullback_selfAdjoint _ _ _

theorem energy_domain (ρ : Measure ℝ) (δ : ℝ) (f : OneParticle ρ δ) :
    f ∈ (energyOperator ρ δ).domain ↔
      MemLp (fun x => (frequency δ x : ℂ)*f x) 2 (shellMeasure ρ δ) :=
  realPullback_domain _ _ _ f

theorem energy_graph (ρ : Measure ℝ) (δ : ℝ) (f g : OneParticle ρ δ) :
    (f,g) ∈ (energyOperator ρ δ).graph ↔
      g =ᵐ[shellMeasure ρ δ] fun x => (frequency δ x : ℂ)*f x :=
  realPullback_graph _ _ _ f g

theorem energy_floor (ρ : Measure ℝ) (δ : ℝ) (hδ : 0 < δ)
    (f : (energyOperator ρ δ).domain) :
    δ*‖(f : OneParticle ρ δ)‖^2 ≤ (inner ℂ (energyOperator ρ δ f) (f : OneParticle ρ δ)).re := by
  have he := (energy_graph ρ δ f (energyOperator ρ δ f)).mp ((energyOperator ρ δ).mem_graph f)
  have hsq : Integrable (fun x => ‖(f : OneParticle ρ δ) x‖^2) (shellMeasure ρ δ) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  have hi := (L2.integrable_inner (𝕜 := ℂ) (energyOperator ρ δ f) (f : OneParticle ρ δ)).re
  have hn := KFCausalPositiveMultiplierEnergy.l2_norm_square (f : OneParticle ρ δ)
  rw [hn, ← integral_const_mul, L2.inner_def]
  have hr : (∫ x, inner ℂ (energyOperator ρ δ f x) ((f : OneParticle ρ δ) x)
      ∂shellMeasure ρ δ).re =
      ∫ x, (inner ℂ (energyOperator ρ δ f x) ((f : OneParticle ρ δ) x)).re
        ∂shellMeasure ρ δ :=
    (integral_re (L2.integrable_inner (𝕜 := ℂ) (energyOperator ρ δ f)
      (f : OneParticle ρ δ))).symm
  rw [hr]
  apply integral_mono_ae (hsq.const_mul δ) hi
  filter_upwards [he] with x hx
  rw [hx]
  change δ*‖(f : OneParticle ρ δ) x‖^2 ≤
    (inner ℂ ((frequency δ x : ℂ) • (f : OneParticle ρ δ) x) ((f : OneParticle ρ δ) x)).re
  rw [inner_smul_left, Complex.conj_ofReal]
  have hinner : (inner ℂ ((f : OneParticle ρ δ) x) ((f : OneParticle ρ δ) x)).re =
      ‖(f : OneParticle ρ δ) x‖^2 :=
        inner_self_eq_norm_sq (𝕜 := ℂ) ((f : OneParticle ρ δ) x)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hinner]
  exact mul_le_mul_of_nonneg_right (frequency_lower δ hδ x) (sq_nonneg _)

end
end UnifiedTheory.Audit.KFCausalRelativisticMassShell
