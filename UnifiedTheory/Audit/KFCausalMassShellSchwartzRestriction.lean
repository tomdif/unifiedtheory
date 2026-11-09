/- Restricting four-momentum Schwartz test functions to the positive mass
shell gives actual L2 vectors. The estimate is uniform in the mass variable,
so a finite mass law requires no higher mass moments. -/
import UnifiedTheory.Audit.KFCausalRelativisticMassShell
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

set_option autoImplicit false
set_option Elab.async false

namespace UnifiedTheory.Audit.KFCausalMassShellSchwartzRestriction
noncomputable section
open MeasureTheory
open KFCausalRelativisticMassShell
open scoped BigOperators

abbrev Test := SchwartzMap (ℝ × Momentum) ℂ

def decayConstant (F : Test) : ℝ :=
  4 * (Finset.Iic (2,0)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) F

def waveFunction (δ : ℝ) (F : Test) (x : ShellPoint) : ℂ := F (frequency δ x, x.2)

theorem waveFunction_measurable (δ : ℝ) (F : Test) : Measurable (waveFunction δ F) := by
  exact F.continuous.measurable.comp
    ((frequency_continuous δ).measurable.prodMk measurable_snd)

theorem waveFunction_bound (δ : ℝ) (F : Test) (x : ShellPoint) :
    ‖waveFunction δ F x‖ ≤ decayConstant F * (1+‖x.2‖)^(-2 : ℝ) := by
  have hF : (1+‖(frequency δ x, x.2)‖)^2 * ‖F (frequency δ x, x.2)‖ ≤ decayConstant F := by
    simpa [decayConstant, show (2 : ℝ)^2 = 4 by norm_num] using SchwartzMap.one_add_le_sup_seminorm_apply
      (𝕜 := ℂ) (m := (2,0)) (k := 2) (n := 0) le_rfl le_rfl F (frequency δ x, x.2)
  have hb : (1+‖x.2‖)^2 * ‖waveFunction δ F x‖ ≤ decayConstant F := by
    apply le_trans _ hF
    unfold waveFunction
    gcongr
    exact norm_snd_le (frequency δ x, x.2)
  rw [Real.rpow_neg (by positivity), Real.rpow_two, ← div_eq_mul_inv,
    le_div_iff₀ (by positivity : 0 < (1+‖x.2‖)^2)]
  nlinarith

theorem spatialDecay_memLp :
    MemLp (fun p : Momentum => (1+‖p‖)^(-2 : ℝ)) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (by apply Measurable.aestronglyMeasurable; fun_prop)).mpr
  have hi : Integrable (fun p : Momentum => (1+‖p‖)^(-4 : ℝ)) volume :=
    integrable_one_add_norm (by norm_num)
  convert hi using 1
  funext p
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _),
    ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

theorem shellMeasure_le (ρ : Measure ℝ) (δ : ℝ) (hδ : 0 < δ) :
    shellMeasure ρ δ ≤ ENNReal.ofReal ((2*δ)⁻¹) • ρ.prod (volume : Measure Momentum) := by
  rw [shellMeasure, ← withDensity_const]
  apply withDensity_mono
  apply Filter.Eventually.of_forall
  intro x
  apply ENNReal.ofReal_le_ofReal
  exact inv_anti₀ (by positivity) (by linarith [frequency_lower δ hδ x])

theorem waveFunction_memLp (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (δ : ℝ) (hδ : 0 < δ) (F : Test) :
    MemLp (waveFunction δ F) 2 (shellMeasure ρ δ) := by
  have hd : MemLp (fun x : ShellPoint => decayConstant F * (1+‖x.2‖)^(-2 : ℝ))
      2 (ρ.prod (volume : Measure Momentum)) :=
    (spatialDecay_memLp.comp_snd ρ).const_smul (decayConstant F)
  have hp : MemLp (waveFunction δ F) 2 (ρ.prod (volume : Measure Momentum)) :=
    hd.mono' (waveFunction_measurable δ F).aestronglyMeasurable
      (Filter.Eventually.of_forall (waveFunction_bound δ F))
  exact (hp.smul_measure ENNReal.ofReal_ne_top).mono_measure (shellMeasure_le ρ δ hδ)

def restriction (ρ : Measure ℝ) [IsFiniteMeasure ρ] (δ : ℝ) (hδ : 0 < δ) :
    Test →ₗ[ℂ] OneParticle ρ δ where
  toFun F := (waveFunction_memLp ρ δ hδ F).toLp (waveFunction δ F)
  map_add' F G := by
    apply Lp.ext
    filter_upwards [(waveFunction_memLp ρ δ hδ (F+G)).coeFn_toLp,
      (waveFunction_memLp ρ δ hδ F).coeFn_toLp,
      (waveFunction_memLp ρ δ hδ G).coeFn_toLp,
      Lp.coeFn_add ((waveFunction_memLp ρ δ hδ F).toLp _)
        ((waveFunction_memLp ρ δ hδ G).toLp _)] with x hfg hf hg ha
    rw [hfg, ha]
    simp only [Pi.add_apply, hf, hg, waveFunction, SchwartzMap.add_apply]
  map_smul' c F := by
    apply Lp.ext
    filter_upwards [(waveFunction_memLp ρ δ hδ (c • F)).coeFn_toLp,
      (waveFunction_memLp ρ δ hδ F).coeFn_toLp,
      Lp.coeFn_smul c ((waveFunction_memLp ρ δ hδ F).toLp _)] with x hcf hf hs
    simp only [RingHom.id_apply]
    rw [hcf, hs]
    simp only [Pi.smul_apply, hf, waveFunction, SchwartzMap.smul_apply]

theorem restriction_coe (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (δ : ℝ) (hδ : 0 < δ) (F : Test) :
    restriction ρ δ hδ F =ᵐ[shellMeasure ρ δ] waveFunction δ F :=
  (waveFunction_memLp ρ δ hδ F).coeFn_toLp

end
end UnifiedTheory.Audit.KFCausalMassShellSchwartzRestriction
