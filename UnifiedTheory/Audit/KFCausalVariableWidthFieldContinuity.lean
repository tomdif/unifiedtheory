/- Continuity of actual sourced spectral and field outputs at arbitrary
positive Gaussian widths with 32*beta<=alpha. The half-width majorants
are proved here, so no extra integrability premise is introduced. -/
import UnifiedTheory.Audit.KFCausalClockFloorSourcedMultiplierContinuity
import UnifiedTheory.Audit.KFCausalClockFloorSourcedCommonDomain
import UnifiedTheory.Audit.KFCausalClockFloorCoherentMatterOrbit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalVariableWidthFieldContinuity
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedMultiplierContinuity
open UnifiedTheory.Audit.KFCausalClockFloorSourcedSpectral (shiftedOutput)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedCommonDomain
open UnifiedTheory.Audit.KFCausalClockFloorCoherentMatterOrbit
  (pulledField pulledField_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral (gaussianState gaussianState_coe)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds (sourceSize)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (coordinateHomeomorph)
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates (weightedFunction)
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates (coordinates)
open UnifiedTheory.Audit.KFCausalPhysicalField
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare

variable (ε a α β h : ℝ) (hε : 0 < ε) (ha : 0 < a)
  (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "hy" => shift_bound ε h hb
local notation "Y" => shiftedOutput ε a α β hε ha hα hβ hw
local notation "L" => linearOutput ε a α β hε ha hα hβ hw
local notation "Q" => quadraticOutput ε a α β hε ha hα hβ hw
local notation "O" => outputState ε a α β (-h/2) hε ha hα hβ hw hy

theorem outputState_mul_coe (m : Configuration → ℂ) (hm : AEStronglyMeasurable m volume)
    (hbase : MemLp (fun x => m x*baseLine ε a α β (-h/2) x) 2) (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) :
    O m hm hbase C p b =ᵐ[volume] fun x => m (coordinateHomeomorph ε hε x)*(Y C p b h hb) x := by
  filter_upwards [outputState_coe ε a α β (-h/2) hε ha hα hβ hw hy m hm hbase C p b,
    Lp.coeFn_smul C (gaussianState ε a α β p b (-h/2) hε ha hα hβ hw hy),
    gaussianState_coe ε a α β p b (-h/2) hε ha hα hβ hw hy] with x ho hs hg
  change (Y C p b h hb) x = C*(gaussianState ε a α β p b (-h/2) hε ha hα hβ hw hy) x at hs
  rw [ho,hs,hg]
  simp only [weightedFunction,modifiedLine]
  ring

include hε ha hα hβ hw in
theorem base_memLp (y : ℝ) (hy₁ : |y| ≤ Real.pi*ε/3) :
    MemLp (baseLine ε a α β y) 2 volume :=
  KFCausalClockFloorShiftedOutput.configurationLine_memLp ε a (α/2) (β/2) y hε ha
    (by positivity) (by positivity) (by linarith) hy₁

include hε ha hα hβ hw in
theorem quadratic_base_memLp (y : ℝ) (hy₁ : |y| ≤ Real.pi*ε/3) (l : Transverse →L[ℝ] ℝ) :
    MemLp (fun x => (pulledField ε hε l x:ℂ)^2*baseLine ε a α β y x) 2 volume :=
  KFCausalClockFloorTrialMatter.quadratic_configuration_memLp ε a (α/2) (β/2) y hε ha
    (by positivity) (by positivity) (by linarith) hy₁ l

include hε ha hα hβ hw in
theorem linear_base_memLp (y : ℝ) (hy₁ : |y| ≤ Real.pi*ε/3) (l : Transverse →L[ℝ] ℝ) :
    MemLp (fun x => (pulledField ε hε l x:ℂ)*baseLine ε a α β y x) 2 volume := by
  have hf := base_memLp ε a α β hε ha hα hβ hw y hy₁
  have hq := quadratic_base_memLp ε a α β hε ha hα hβ hw y hy₁ l
  have hm := (Complex.continuous_ofReal.comp (pulledField_continuous ε hε l)).aestronglyMeasurable.mul
    hf.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have h₀ := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have h₄ := (memLp_two_iff_integrable_sq_norm hq.aestronglyMeasurable).mp hq
  apply (h₀.add h₄).mono' (hm.norm.pow 2)
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  dsimp only [Pi.add_apply,Pi.pow_apply,Pi.mul_apply]
  simp only [Function.comp_apply,norm_mul,norm_pow,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have hd : (pulledField ε hε l x)^2 ≤ 1+((pulledField ε hε l x)^2)^2 := by
    nlinarith [sq_nonneg ((pulledField ε hε l x)^2-1/2)]
  nlinarith [mul_le_mul_of_nonneg_right hd (sq_nonneg ‖baseLine ε a α β y x‖)]

def scalarBase : MemLp (fun x => (1:ℂ)*baseLine ε a α β (-h/2) x) 2 :=
  by simpa only [one_mul] using base_memLp ε a α β hε ha hα hβ hw (-h/2) hy

theorem scalarOutput_eq (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) :
    O (fun _ => 1) aestronglyMeasurable_const (scalarBase ε a α β h hε ha hα hβ hw hb) C p b = Y C p b h hb := by
  apply Lp.ext
  filter_upwards [outputState_mul_coe ε a α β h hε ha hα hβ hw hb (fun _ => 1) aestronglyMeasurable_const
    (scalarBase ε a α β h hε ha hα hβ hw hb) C p b] with x hx
  simpa only [one_mul] using hx

theorem linearOutput_eq (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) (l : Transverse →L[ℝ] ℝ) :
    O (fun x => (pulledField ε hε l x:ℂ))
      (Complex.continuous_ofReal.comp (pulledField_continuous ε hε l)).aestronglyMeasurable
      (linear_base_memLp ε a α β hε ha hα hβ hw (-h/2) hy l) C p b = L C p b h hb l := by
  refine (physicalField l).mem_graph_snd_inj ?_
    ((physicalField l).mem_graph ⟨Y C p b h hb,
      shiftedOutput_physicalField_domain ε a α β hε ha hα hβ hw C p b h hb l⟩) rfl
  apply (physicalField_graph l _ _).mpr
  filter_upwards [outputState_mul_coe ε a α β h hε ha hα hβ hw hb _
    (Complex.continuous_ofReal.comp (pulledField_continuous ε hε l)).aestronglyMeasurable
    (linear_base_memLp ε a α β hε ha hα hβ hw (-h/2) hy l) C p b] with x hx
  simpa only [Function.comp_apply,pulledField,Homeomorph.symm_apply_apply] using hx

theorem quadraticOutput_eq (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) (l : Transverse →L[ℝ] ℝ) :
    O (fun x => (pulledField ε hε l x:ℂ)^2)
      ((Complex.continuous_ofReal.comp (pulledField_continuous ε hε l)).pow 2).aestronglyMeasurable
      (quadratic_base_memLp ε a α β hε ha hα hβ hw (-h/2) hy l) C p b = Q C p b h hb l := by
  refine (fieldSquare l).mem_graph_snd_inj ?_
    ((fieldSquare l).mem_graph ⟨Y C p b h hb,
      shiftedOutput_fieldSquare_domain ε a α β hε ha hα hβ hw C p b h hb l⟩) rfl
  apply (fieldSquare_graph l _ _).mpr
  filter_upwards [outputState_mul_coe ε a α β h hε ha hα hβ hw hb _
    ((Complex.continuous_ofReal.comp (pulledField_continuous ε hε l)).pow 2).aestronglyMeasurable
    (quadratic_base_memLp ε a α β hε ha hα hβ hw (-h/2) hy l) C p b] with x hx
  simpa only [Function.comp_apply,pulledField,Homeomorph.symm_apply_apply] using hx

theorem outputs_curve_continuous (P B : ℝ) (C : ℝ → ℂ) (p : ℝ → ℝ) (b : ℝ → Fin 5 → ℂ)
    (hCc : Continuous C) (hpc : Continuous p) (hbc : Continuous b)
    (hC : ∀ θ, ‖C θ‖ ≤ 1) (hp : ∀ θ, |p θ| ≤ P) (hB : ∀ θ, sourceSize (b θ) ≤ B) :
    Continuous (fun θ => Y (C θ) (p θ) (b θ) h hb) ∧
      (∀ l, Continuous (fun θ => L (C θ) (p θ) (b θ) h hb l)) ∧
      (∀ l, Continuous (fun θ => Q (C θ) (p θ) (b θ) h hb l)) := by
  have hc (m : Configuration → ℂ) (hm : AEStronglyMeasurable m volume)
      (hbase : MemLp (fun x => m x*baseLine ε a α β (-h/2) x) 2) :
      Continuous (fun θ => O m hm hbase (C θ) (p θ) (b θ)) :=
    (coordinates ε hε).continuous.comp
      (modifiedLine_curve_continuous ε a α β (-h/2) P B hε ha hα hβ hw hy m hm hbase
        C p b hCc hpc hbc hC hp hB)
  refine ⟨?_,?_,?_⟩
  · have he := funext (fun θ => scalarOutput_eq ε a α β h hε ha hα hβ hw hb (C θ) (p θ) (b θ))
    rw [← he]
    exact hc _ _ _
  · intro l
    have he := funext (fun θ => linearOutput_eq ε a α β h hε ha hα hβ hw hb (C θ) (p θ) (b θ) l)
    rw [← he]
    exact hc _ _ _
  · intro l
    have he := funext (fun θ => quadraticOutput_eq ε a α β h hε ha hα hβ hw hb (C θ) (p θ) (b θ) l)
    rw [← he]
    exact hc _ _ _

#print axioms base_memLp
#print axioms quadratic_base_memLp
#print axioms linear_base_memLp
#print axioms outputState_mul_coe
#print axioms scalarOutput_eq
#print axioms linearOutput_eq
#print axioms quadraticOutput_eq
#print axioms outputs_curve_continuous

end
end UnifiedTheory.Audit.KFCausalVariableWidthFieldContinuity
