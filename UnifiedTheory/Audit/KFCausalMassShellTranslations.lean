/- Explicit unitary spacetime translations on the continuous-mass
one-particle space. No boost invariance or locality is presumed. -/
import UnifiedTheory.Audit.KFCausalRelativisticMassShell
import UnifiedTheory.Audit.KFCausalUnitModulusMultiplier
import Mathlib.Analysis.Complex.Trigonometric

set_option autoImplicit false
set_option Elab.async false

namespace UnifiedTheory.Audit.KFCausalMassShellTranslations
noncomputable section
open MeasureTheory
open KFCausalRelativisticMassShell

abbrev Spacetime := ℝ × Momentum

def phase (δ : ℝ) (a : Spacetime) (x : ShellPoint) : ℂ :=
  Complex.exp (((a.1 * frequency δ x - inner ℝ a.2 x.2 : ℝ) : ℂ) * Complex.I)

theorem phase_measurable (δ : ℝ) (a : Spacetime) : Measurable (phase δ a) := by
  apply Continuous.measurable
  unfold phase
  have hf := frequency_continuous δ
  fun_prop

theorem phase_continuous (δ : ℝ) (x : ShellPoint) : Continuous (fun a => phase δ a x) := by
  unfold phase
  fun_prop

theorem phase_norm (δ : ℝ) (a : Spacetime) (x : ShellPoint) : ‖phase δ a x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem phase_zero (δ : ℝ) (x : ShellPoint) : phase δ 0 x = 1 := by simp [phase]

theorem phase_add (δ : ℝ) (a b : Spacetime) (x : ShellPoint) :
    phase δ (a+b) x = phase δ a x * phase δ b x := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add, inner_add_left,
    Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul]
  ring

def translation (ρ : Measure ℝ) (δ : ℝ) (a : Spacetime) :
    OneParticle ρ δ ≃ₗᵢ[ℂ] OneParticle ρ δ :=
  KFCausalUnitModulusMultiplier.unitary (phase δ a) (phase_measurable δ a) (phase_norm δ a)

theorem translation_coe (ρ : Measure ℝ) (δ : ℝ) (a : Spacetime) (f : OneParticle ρ δ) :
    translation ρ δ a f =ᵐ[shellMeasure ρ δ] fun x => phase δ a x * f x :=
  KFCausalUnitModulusMultiplier.unitary_coe _ _ _ _

theorem translation_zero (ρ : Measure ℝ) (δ : ℝ) (f : OneParticle ρ δ) :
    translation ρ δ 0 f = f := by
  apply Lp.ext
  filter_upwards [translation_coe ρ δ 0 f] with x hx
  simpa only [phase_zero, one_mul] using hx

theorem translation_add (ρ : Measure ℝ) (δ : ℝ) (a b : Spacetime)
    (f : OneParticle ρ δ) : translation ρ δ (a+b) f = translation ρ δ a (translation ρ δ b f) := by
  apply Lp.ext
  filter_upwards [translation_coe ρ δ (a+b) f,
    translation_coe ρ δ a (translation ρ δ b f), translation_coe ρ δ b f] with x hab ha hb
  rw [hab, ha, hb, phase_add, mul_assoc]

theorem translation_energy_graph (ρ : Measure ℝ) (δ : ℝ) (a : Spacetime)
    (f g : OneParticle ρ δ) (hfg : (f,g) ∈ (energyOperator ρ δ).graph) :
    (translation ρ δ a f, translation ρ δ a g) ∈ (energyOperator ρ δ).graph := by
  apply (energy_graph ρ δ _ _).mpr
  filter_upwards [(energy_graph ρ δ f g).mp hfg,
    translation_coe ρ δ a f, translation_coe ρ δ a g] with x hx hf hg
  rw [hg, hf, hx]
  ring

end
end UnifiedTheory.Audit.KFCausalMassShellTranslations
