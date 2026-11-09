/- The exact bounded triangular change of all eight energy outputs under
neutral translation. Weight conjugation retains the actual energy factors
and permits passage to their closed joint graph. -/
import UnifiedTheory.Audit.KFCausalNeutralTranslationMatter
import UnifiedTheory.Audit.KFCausalFiniteJointGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalNeutralTranslationOutput
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalNeutralTranslationCoordinates (action)

abbrev Outputs := Output (Fin 8) Hilbert

def mixValues (c : ℂ) (g : Outputs) : Fin 8 → Hilbert :=
  ![g 0,g 1,g 2,g 3,g 4,g 5-c • g 7,g 6-(2*c) • g 5+c^2 • g 7,g 7]

def mix (c : ℂ) : Outputs →L[ℂ] Outputs where
  toFun g := WithLp.toLp 2 (mixValues c g)
  map_add' f g := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [mixValues,smul_add] <;> module
  map_smul' z g := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [mixValues,smul_add,smul_sub,smul_smul,mul_comm]
  cont := (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i => by
    fin_cases i <;> simp only [mixValues,Matrix.cons_val_zero',Matrix.cons_val_succ']
    all_goals fun_prop))

def scaleOutput (w : Fin 8 → ℂ) : Outputs →L[ℂ] Outputs where
  toFun g := WithLp.toLp 2 (fun i => w i • g i)
  map_add' f g := by ext i; simp [smul_add]
  map_smul' z g := by ext i; simp [smul_smul,mul_comm]
  cont := (PiLp.continuous_toLp 2 _).comp
    (continuous_pi (fun i => continuous_const.smul (PiLp.continuous_apply 2 _ i)))

def translateOutput (r : ℝ) : Outputs →L[ℂ] Outputs where
  toFun g := WithLp.toLp 2 (fun i => action r (g i))
  map_add' f g := by ext i; simp [map_add]
  map_smul' z g := by ext i; simp [map_smul]
  cont := (PiLp.continuous_toLp 2 _).comp
    (continuous_pi (fun i => (action r).continuous.comp (PiLp.continuous_apply 2 _ i)))

def weightedMix (w : Fin 8 → ℂ) (c : ℂ) : Outputs →L[ℂ] Outputs :=
  (scaleOutput w).comp ((mix c).comp (scaleOutput (fun i => (w i)⁻¹)))

def outputAction (w : Fin 8 → ℂ) (c : ℂ) (r : ℝ) : Outputs →L[ℂ] Outputs :=
  (translateOutput r).comp (weightedMix w c)

theorem outputAction_apply (w : Fin 8 → ℂ) (c : ℂ) (r : ℝ) (g : Outputs) (i : Fin 8) :
    outputAction w c r g i = action r (w i • mixValues c (scaleOutput (fun j => (w j)⁻¹) g) i) := rfl

theorem weightedMix_zero (w : Fin 8 → ℂ) (hw : ∀ i, w i ≠ 0) (g : Outputs) :
    weightedMix w 0 g = g := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [weightedMix,scaleOutput,mix,mixValues,smul_smul,hw]

theorem translateOutput_norm (r : ℝ) (g : Outputs) : ‖translateOutput r g‖ = ‖g‖ := by
  have he : ‖translateOutput r g‖^2 = ‖g‖^2 := by
    simp only [PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro i _
    change ‖action r (g i)‖^2 = ‖g i‖^2
    rw [(action r).norm_map]
  nlinarith [norm_nonneg (translateOutput r g),norm_nonneg g]

#print axioms outputAction_apply
#print axioms weightedMix_zero
#print axioms translateOutput_norm

end
end UnifiedTheory.Audit.KFCausalNeutralTranslationOutput
