/- The actual linear and quadratic matter outputs have continuous L2
orbits. Their fixed pulled-back field multipliers are controlled by the
half-width Gaussian majorant, including the exact longitudinal shift. -/
import UnifiedTheory.Audit.KFCausalClockFloorCoherentShiftedOrbit
import UnifiedTheory.Audit.KFCausalClockFloorCoherentMatter

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorCoherentMatterOrbit
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentMultiplierOrbit
open UnifiedTheory.Audit.KFCausalClockFloorCoherentShiftedOrbit
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral (shiftedOutput state_ordered_graph)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (coordinateHomeomorph)
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates (weightedFunction)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalChargeModulationFlow
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMatter (matterFactor)
open UnifiedTheory.Audit.KFCausalPhysicalField
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition

def pulledField (ε : ℝ) (hε : 0 < ε) (l : Transverse →L[ℝ] ℝ) (x : Configuration) : ℝ :=
  l ((coordinateHomeomorph ε hε).symm x).2

theorem pulledField_continuous (ε : ℝ) (hε : 0 < ε) (l : Transverse →L[ℝ] ℝ) :
    Continuous (pulledField ε hε l) :=
  l.continuous.comp (continuous_snd.comp (coordinateHomeomorph ε hε).symm.continuous)

theorem quadratic_base_memLp (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) (l : Transverse →L[ℝ] ℝ) :
    MemLp (fun x => (pulledField ε hε l x:ℂ)^2*baseLine ε a hbar y x) 2 volume :=
  KFCausalClockFloorTrialMatter.quadratic_configuration_memLp ε a _ _ y hε ha
    (by have := groundWidth_positive hbar hh; positivity)
    (by have := neutralWidth_positive hbar hh; positivity)
    (by have := neutralWidth_bound hbar; linarith) hy l

theorem linear_base_memLp (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) (l : Transverse →L[ℝ] ℝ) :
    MemLp (fun x => (pulledField ε hε l x:ℂ)*baseLine ε a hbar y x) 2 volume := by
  have hf := baseLine_memLp ε a hbar hε ha hh y hy
  have hq := quadratic_base_memLp ε a hbar hε ha hh y hy l
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
  have hb : (pulledField ε hε l x)^2 ≤ 1+((pulledField ε hε l x)^2)^2 := by
    nlinarith [sq_nonneg ((pulledField ε hε l x)^2-1/2)]
  nlinarith [mul_le_mul_of_nonneg_right hb (sq_nonneg ‖baseLine ε a hbar y x‖)]

def linearOutput (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) (k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) : Hilbert :=
  outputState ε a hbar hε ha hh y hy (fun x => (pulledField ε hε l x:ℂ))
    (Complex.continuous_ofReal.comp (pulledField_continuous ε hε l)).aestronglyMeasurable
    (linear_base_memLp ε a hbar hε ha hh y hy l) k

def quadraticOutput (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) (k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) : Hilbert :=
  outputState ε a hbar hε ha hh y hy (fun x => (pulledField ε hε l x:ℂ)^2)
    ((Complex.continuous_ofReal.comp (pulledField_continuous ε hε l)).pow 2).aestronglyMeasurable
    (quadratic_base_memLp ε a hbar hε ha hh y hy l) k

theorem linearOutput_graph (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) (k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) :
    (scalarOutput ε a hbar hε ha hh y hy k, linearOutput ε a hbar hε ha hh y hy k l) ∈
      (physicalField l).graph := by
  apply (physicalField_graph l _ _).mpr
  filter_upwards [scalarOutput_coe ε a hbar hε ha hh y hy k,
    outputState_coe ε a hbar hε ha hh y hy _ _ (linear_base_memLp ε a hbar hε ha hh y hy l) k] with x hs hl
  change linearOutput ε a hbar hε ha hh y hy k l x = _ at hl
  rw [hl,hs]
  simp only [weightedFunction,modifiedLine,pulledField,Homeomorph.symm_apply_apply,one_mul]
  ring

theorem quadraticOutput_graph (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) (k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) :
    (scalarOutput ε a hbar hε ha hh y hy k, quadraticOutput ε a hbar hε ha hh y hy k l) ∈
      (fieldSquare l).graph := by
  apply (fieldSquare_graph l _ _).mpr
  filter_upwards [scalarOutput_coe ε a hbar hε ha hh y hy k,
    outputState_coe ε a hbar hε ha hh y hy _ _ (quadratic_base_memLp ε a hbar hε ha hh y hy l) k] with x hs hq
  change quadraticOutput ε a hbar hε ha hh y hy k l x = _ at hq
  rw [hq,hs]
  simp only [weightedFunction,modifiedLine,pulledField,Homeomorph.symm_apply_apply,one_mul]
  ring

theorem linearOutput_matter_graph (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (hbound : |hbar| ≤ 2*Real.pi*ε/3) (k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) :
    (KFCausalClockFloorCoherentStates.state ε a hbar hε ha hh k,
      linearOutput ε a hbar hε ha hh (-hbar/2) (shift_bound ε hbar hbound) k l) ∈
        (matterFactor ε hε hbar (physicalField l)).graph := by
  apply (composition_graph _ _ _ _).mpr
  refine ⟨_,state_ordered_graph ε a hbar hε ha hh hbound k,?_⟩
  rw [shiftedOutput_eq_scalarOutput]
  exact linearOutput_graph ε a hbar hε ha hh _ _ k l

theorem quadraticOutput_matter_graph (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (hbound : |hbar| ≤ 2*Real.pi*ε/3) (k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) :
    (KFCausalClockFloorCoherentStates.state ε a hbar hε ha hh k,
      quadraticOutput ε a hbar hε ha hh (-hbar/2) (shift_bound ε hbar hbound) k l) ∈
        (matterFactor ε hε hbar (fieldSquare l)).graph := by
  apply (composition_graph _ _ _ _).mpr
  refine ⟨_,state_ordered_graph ε a hbar hε ha hh hbound k,?_⟩
  rw [shiftedOutput_eq_scalarOutput]
  exact quadraticOutput_graph ε a hbar hε ha hh _ _ k l

theorem linearOutput_orbit_continuous (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) (k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) :
    Continuous (fun θ => linearOutput ε a hbar hε ha hh y hy (parameter θ k) l) :=
  outputState_orbit_continuous ε a hbar hε ha hh y hy _ _ _ k

theorem quadraticOutput_orbit_continuous (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) (k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) :
    Continuous (fun θ => quadraticOutput ε a hbar hε ha hh y hy (parameter θ k) l) :=
  outputState_orbit_continuous ε a hbar hε ha hh y hy _ _ _ k

#print axioms pulledField_continuous
#print axioms quadratic_base_memLp
#print axioms linear_base_memLp
#print axioms linearOutput_graph
#print axioms quadraticOutput_graph
#print axioms linearOutput_matter_graph
#print axioms quadraticOutput_matter_graph
#print axioms linearOutput_orbit_continuous
#print axioms quadraticOutput_orbit_continuous

end
end UnifiedTheory.Audit.KFCausalClockFloorCoherentMatterOrbit
