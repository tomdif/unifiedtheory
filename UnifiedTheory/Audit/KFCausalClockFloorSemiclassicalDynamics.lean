/- A non-vacuous uniform small-Planck estimate for the actual evolved
normalized Gaussian family. The comparator is the previously derived
classical clock coefficient evaluated on the quantum energy outputs;
this is not a classical phase-space transport theorem. -/
import UnifiedTheory.Audit.KFCausalClockFloorSemiclassicalStates
import UnifiedTheory.Audit.KFCausalClockFloorExactEhrenfest

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorSemiclassicalDynamics
noncomputable section
open UnifiedTheory.Audit.KFCausalClockFloorSemiclassicalStates
open UnifiedTheory.Audit.KFCausalClockFloorExactEhrenfest

def windowConstant (ε a mass2 quartic vacuum s T : ℝ) : ℝ :=
  (20/ε^2)*Real.exp (2*T)*uniformEnergy ε a mass2 quartic vacuum s

theorem windowConstant_nonnegative (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (mass2 quartic vacuum s T : ℝ) (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    0 ≤ windowConstant ε a mass2 quartic vacuum s T :=
  mul_nonneg (by positivity) (uniformEnergy_nonnegative ε a hε ha mass2 quartic vacuum s hm hq hv)

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
  (mass2 quartic vacuum s : ℝ) (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum)

def rateError (hbar : ℝ) (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3) (hh1 : |hbar| ≤ 1)
    (t : ℝ) : ℝ :=
  |exactRate ε hε hbar hh hb mass2 quartic vacuum s t
      (state ε a hε ha hbar hh hb hh1 mass2 quartic vacuum s hm hq hv)-
    classicalRate ε hε hbar hh hb mass2 quartic vacuum s t
      (state ε a hε ha hbar hh hb hh1 mass2 quartic vacuum s hm hq hv)|

theorem rateError_uniform_bound (hbar : ℝ) (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3)
    (hh1 : |hbar| ≤ 1) (T t : ℝ) (ht : |t-s| ≤ T) :
    rateError ε a hε ha mass2 quartic vacuum s hm hq hv hbar hh hb hh1 t ≤
      windowConstant ε a mass2 quartic vacuum s T*|hbar| := by
  have hbase := rate_error_initial_energy ε hε hbar hh hb mass2 quartic vacuum s t
    (state ε a hε ha hbar hh hb hh1 mass2 quartic vacuum s hm hq hv)
  have hE := state_energy ε a hε ha hbar hh hb hh1 mass2 quartic vacuum s hm hq hv
  have hK := uniformEnergy_nonnegative ε a hε ha mass2 quartic vacuum s hm hq hv
  have he : Real.exp (2*|t-s|) ≤ Real.exp (2*T) := Real.exp_le_exp.mpr (by linarith only [ht])
  calc
    _ ≤ (20*|hbar|/ε^2)*Real.exp (2*|t-s|)*
        UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl.timeEnergy ε hε hbar hh hb mass2 quartic vacuum s
          (state ε a hε ha hbar hh hb hh1 mass2 quartic vacuum s hm hq hv) := hbase
    _ ≤ (20*|hbar|/ε^2)*Real.exp (2*|t-s|)*uniformEnergy ε a mass2 quartic vacuum s :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    _ ≤ (20*|hbar|/ε^2)*Real.exp (2*T)*uniformEnergy ε a mass2 quartic vacuum s :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by positivity)) hK
    _ = _ := by unfold windowConstant; ring

private theorem small_product (L η x : ℝ) (hL : 0 ≤ L)
    (hx : 0 ≤ x) (hsmall : x < η/(L+1)) : L*x < η := by
  have hp : 0 < L+1 := by positivity
  have h := (lt_div_iff₀ hp).mp hsmall
  nlinarith only [h,hx]

theorem rateError_uniform_small (T η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (hbar : ℝ) (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3)
      (hh1 : |hbar| ≤ 1), |hbar| < δ → ∀ t : ℝ, |t-s| ≤ T →
        rateError ε a hε ha mass2 quartic vacuum s hm hq hv hbar hh hb hh1 t < η := by
  let L := windowConstant ε a mass2 quartic vacuum s T
  have hL : 0 ≤ L := windowConstant_nonnegative ε a hε ha mass2 quartic vacuum s T hm hq hv
  refine ⟨η/(L+1),by positivity,?_⟩
  intro hbar hh hb hh1 hsmall t ht
  exact (rateError_uniform_bound ε a hε ha mass2 quartic vacuum s hm hq hv hbar hh hb hh1 T t ht).trans_lt
    (small_product L η |hbar| hL (abs_nonneg hbar) hsmall)

include hε in
theorem exists_parameter_below (δ : ℝ) (hδ : 0 < δ) :
    ∃ hbar : ℝ, 0 < hbar ∧ hbar < δ ∧ |hbar| ≤ 1 ∧ |hbar| ≤ 2*Real.pi*ε/3 := by
  let b := min δ (min 1 (2*Real.pi*ε/3))
  have hb : 0 < b := lt_min hδ (lt_min zero_lt_one (by positivity))
  have h1 : b ≤ δ := min_le_left _ _
  have h2 : b ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : b ≤ 2*Real.pi*ε/3 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨b/2,by positivity,by linarith only [hb,h1],?_,?_⟩
  · rw [abs_of_pos (by positivity : 0 < b/2)]
    linarith only [hb,h2]
  · rw [abs_of_pos (by positivity : 0 < b/2)]
    linarith only [hb,h3]

#print axioms windowConstant_nonnegative
#print axioms rateError_uniform_bound
#print axioms rateError_uniform_small
#print axioms exists_parameter_below

end
end UnifiedTheory.Audit.KFCausalClockFloorSemiclassicalDynamics
