/- Actual phase and translation unitaries on L2. These are bounded tests
of joint canonical position and momentum, not Hamiltonian evolution. -/
import UnifiedTheory.Audit.KFCausalMeasureUnitaryPullback
import UnifiedTheory.Audit.KFCausalUnitModulusMultiplier
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalLpPhaseTranslation
noncomputable section
open MeasureTheory
open scoped ENNReal
open UnifiedTheory.Audit.KFCausalMeasureUnitaryPullback

variable {X : Type*} [NormedAddCommGroup X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [Measure.IsAddHaarMeasure μ]

abbrev Hilbert := Lp ℂ 2 μ

def shift (v : X) : X ≃ᵐ X := (Homeomorph.addRight v).toMeasurableEquiv

theorem shift_preserves (v : X) : MeasurePreserving (shift v) μ μ :=
  measurePreserving_add_right μ v

def translation (v : X) : Hilbert μ ≃ₗᵢ[ℂ] Hilbert μ :=
  unitaryPullback (shift v) (shift_preserves μ v)

theorem translation_coe (v : X) (f : Hilbert μ) :
    translation μ v f =ᵐ[μ] fun x => f (x+v) :=
  unitaryPullback_coe (shift v) (shift_preserves μ v) f

theorem translation_zero (f : Hilbert μ) : translation μ 0 f = f := by
  apply Lp.ext
  simpa only [add_zero] using translation_coe μ 0 f

theorem translation_continuous [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ] (f : Hilbert μ) : Continuous (fun v : X => translation μ v f) := by
  have hc : Continuous (fun v : X => (Homeomorph.addRight v : C(X,X))) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : X × X => p.2+p.1)
    fun_prop
  have h := (continuous_const : Continuous (fun _ : X => f)).compMeasurePreservingLp
    hc (shift_preserves μ) (by norm_num : (2:ℝ≥0∞) ≠ ∞)
  exact h

omit [Measure.IsAddHaarMeasure μ] in
def phase (l : X → ℝ) (x : X) : ℂ := Complex.exp (Complex.I*(l x:ℂ))

omit [Measure.IsAddHaarMeasure μ] [NormedAddCommGroup X] [MeasurableSpace X] [BorelSpace X] in
theorem phase_norm (l : X → ℝ) (x : X) : ‖phase l x‖ = 1 := by
  simp [phase,Complex.norm_exp,Complex.mul_re]

omit [Measure.IsAddHaarMeasure μ] in
def modulation (l : X → ℝ) (hl : Measurable l) : Hilbert μ ≃ₗᵢ[ℂ] Hilbert μ :=
  KFCausalUnitModulusMultiplier.unitary (phase l)
    (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp hl))) (phase_norm l)

omit [Measure.IsAddHaarMeasure μ] [NormedAddCommGroup X] [BorelSpace X] in
theorem modulation_coe (l : X → ℝ) (hl : Measurable l) (f : Hilbert μ) :
    modulation μ l hl f =ᵐ[μ] fun x => phase l x*f x :=
  KFCausalUnitModulusMultiplier.unitary_coe _ _ _ f

omit [Measure.IsAddHaarMeasure μ] [NormedAddCommGroup X] [BorelSpace X] in
theorem modulation_difference (l : X → ℝ) (hl : Measurable l) (f g : Hilbert μ)
    (hg : g =ᵐ[μ] fun x => (l x:ℂ)*f x) :
    ‖modulation μ l hl f-f‖ ≤ ‖g‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub (modulation μ l hl f) f,modulation_coe μ l hl f,hg] with x hx hm hq
  simp only [Pi.sub_apply] at hx
  rw [hx,hm,hq,show phase l x*f x-f x = (phase l x-1)*f x by ring,
    norm_mul,norm_mul,Complex.norm_real]
  exact mul_le_mul_of_nonneg_right Real.norm_exp_I_mul_ofReal_sub_one_le (norm_nonneg _)

def phaseTranslation (l : X → ℝ) (hl : Measurable l) (v : X) : Hilbert μ ≃ₗᵢ[ℂ] Hilbert μ :=
  (translation μ v).trans (modulation μ l hl)

theorem phaseTranslation_coe (l : X → ℝ) (hl : Measurable l) (v : X) (f : Hilbert μ) :
    phaseTranslation μ l hl v f =ᵐ[μ] fun x => phase l x*f (x+v) := by
  filter_upwards [modulation_coe μ l hl (translation μ v f),translation_coe μ v f] with x hx ht
  exact hx.trans (congrArg (fun z : ℂ => phase l x*z) ht)

theorem phaseTranslation_difference (l : X → ℝ) (hl : Measurable l) (v : X) (f : Hilbert μ) :
    ‖phaseTranslation μ l hl v f-f‖ ≤ ‖translation μ v f-f‖+‖modulation μ l hl f-f‖ := by
  have h := norm_sub_le_norm_sub_add_norm_sub (modulation μ l hl (translation μ v f)) (modulation μ l hl f) f
  have he : ‖modulation μ l hl (translation μ v f)-modulation μ l hl f‖ = ‖translation μ v f-f‖ :=
    (congrArg norm ((modulation μ l hl).map_sub _ _).symm).trans ((modulation μ l hl).norm_map _)
  exact h.trans_eq (congrArg (fun r : ℝ => r+‖modulation μ l hl f-f‖) he)

#print axioms shift_preserves
#print axioms translation_coe
#print axioms translation_zero
#print axioms translation_continuous
#print axioms phase_norm
#print axioms modulation_coe
#print axioms modulation_difference
#print axioms phaseTranslation_coe
#print axioms phaseTranslation_difference

end
end UnifiedTheory.Audit.KFCausalLpPhaseTranslation
