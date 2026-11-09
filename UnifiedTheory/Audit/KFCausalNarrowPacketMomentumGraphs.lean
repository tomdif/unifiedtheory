/- Identify the explicitly constructed first moment states with the
actual maximal physical transverse momentum outputs of every packet. -/
import UnifiedTheory.Audit.KFCausalNarrowFourierMomentStates
import UnifiedTheory.Audit.KFCausalNarrowPacketDifferential
import UnifiedTheory.Audit.KFCausalTransverseMomentumDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000

namespace UnifiedTheory.Audit.KFCausalNarrowPacketMomentumGraphs
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalPairedModeCoordinates (scale scale_square)
open KFCausalNarrowFourierMomentStates
open KFCausalNarrowFourierCoordinates (mixedCoordinates)
open KFCausalNarrowFourierPackets (state state_configuration_coe state_coordinates_coe configurationDensity coordinateDensity)
open KFCausalNarrowPacketDifferential (density_derivative quadratic_model_slope modelSlope density_transverse_differentiable)
open KFCausalNeutralLinePackets (step)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalTransverseTrialDerivative (derivative)
open KFCausalPhysicalTransverseMomentum (transverseMomentum)

def narrowCoefficient (α w : ℝ) : ℂ := -4*(scale:ℂ)*(α/w:ℝ)
def broadCoefficient (α w : ℝ) : ℂ := -4*(scale:ℂ)*(α*w:ℝ)

def differentialProfile (α β w : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (j : Fin 4) (x : Configuration) : ℂ :=
  ![narrowCoefficient α w*(leftPositions x.2 0:ℂ)*configurationDensity α β w b P g x,
    broadCoefficient α w*(rightPositions x.2 1:ℂ)*configurationDensity α β w b P g x+
      configurationDensity α β w b (step β b P) g x,
    broadCoefficient α w*(rightPositions x.2 0:ℂ)*configurationDensity α β w b P g x,
    narrowCoefficient α w*(leftPositions x.2 1:ℂ)*configurationDensity α β w b P g x] j

theorem differentialProfile_derivative (α β w : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (j : Fin 4) (x : Configuration) :
    derivative (modelDirections j) (configurationDensity α β w b P g) x = differentialProfile α β w b P g j x := by
  rw [density_derivative,quadratic_model_slope]
  have hs : (scale:ℂ)^2=(1/2:ℂ) := by rw [← Complex.ofReal_pow,scale_square]; norm_num
  fin_cases j <;> simp [differentialProfile,modelSlope,modelDirections,narrowCoefficient,broadCoefficient,
    leftPositions,rightPositions]
  all_goals ring_nf; rw [hs]; left; ring

def differentialCoordinates (α β w : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (j : Fin 4) (z : Block 2 × Block 4) : ℂ :=
  ![(4*(Real.pi:ℂ)*Complex.I*scale)*(z.1 0:ℂ)*coordinateDensity α β w b P g z,
    broadCoefficient α w*(z.2 2:ℂ)*coordinateDensity α β w b P g z+
      coordinateDensity α β w b (step β b P) g z,
    broadCoefficient α w*(z.2 1:ℂ)*coordinateDensity α β w b P g z,
    (4*(Real.pi:ℂ)*Complex.I*scale)*(z.1 1:ℂ)*coordinateDensity α β w b P g z] j

variable (α β w : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 0 < w)
  (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume)
local notation "L" => leftState α β w hα hβ hw b P g hc hg
local notation "R" => rightState α β w hα hβ hw b P g hc hg
local notation "N" => state α β w hα hβ hw b (step β b P) g hc hg

def differentialState (j : Fin 4) : Hilbert :=
  ![narrowCoefficient α w • L 0,broadCoefficient α w • R 1+N,
    broadCoefficient α w • R 0,narrowCoefficient α w • L 1] j

theorem differentialState_coe (j : Fin 4) :
    differentialState α β w hα hβ hw b P g hc hg j =ᵐ[volume] differentialProfile α β w b P g j := by
  have hL (i : Fin 2) : (narrowCoefficient α w • L i : Hilbert) =ᵐ[volume]
      fun x => narrowCoefficient α w*(leftPositions x.2 i:ℂ)*configurationDensity α β w b P g x := by
    filter_upwards [Lp.coeFn_smul (narrowCoefficient α w) (L i),leftState_coe α β w hα hβ hw b P g hc hg i] with x hx hl
    simp only [hx,Pi.smul_apply,smul_eq_mul,hl,mul_assoc]
  have hR (i : Fin 2) : (broadCoefficient α w • R i : Hilbert) =ᵐ[volume]
      fun x => broadCoefficient α w*(rightPositions x.2 i:ℂ)*configurationDensity α β w b P g x := by
    filter_upwards [Lp.coeFn_smul (broadCoefficient α w) (R i),rightState_coe α β w hα hβ hw b P g hc hg i] with x hx hr
    simp only [hx,Pi.smul_apply,smul_eq_mul,hr,mul_assoc]
  have hA : (broadCoefficient α w • R 1+N : Hilbert) =ᵐ[volume]
      fun x => broadCoefficient α w*(rightPositions x.2 1:ℂ)*configurationDensity α β w b P g x+
        configurationDensity α β w b (step β b P) g x := by
    filter_upwards [Lp.coeFn_add (broadCoefficient α w • R 1) N,hR 1,
      state_configuration_coe α β w hα hβ hw b (step β b P) g hc hg] with x hx hr hn
    simp only [hx,Pi.add_apply,hr,hn]
  fin_cases j
  · exact hL 0
  · exact hA
  · exact hR 0
  · exact hL 1

theorem differentialState_coordinates_coe (j : Fin 4) :
    mixedCoordinates (differentialState α β w hα hβ hw b P g hc hg j) =ᵐ[volume]
      differentialCoordinates α β w b P g j := by
  have hL (i : Fin 2) : mixedCoordinates (narrowCoefficient α w • L i) =ᵐ[volume]
      fun z => (4*(Real.pi:ℂ)*Complex.I*scale)*(z.1 i:ℂ)*coordinateDensity α β w b P g z := by
    rw [map_smul]
    filter_upwards [Lp.coeFn_smul (narrowCoefficient α w) (mixedCoordinates (L i)),
      leftState_coordinates_coe α β w hα hβ hw b P g hc hg i] with z hz hl
    simp only [hz,Pi.smul_apply,smul_eq_mul,hl]
    have hA : (α:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα.ne'
    have hW : (w:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
    unfold narrowCoefficient
    push_cast
    field_simp [hA,hW]
  have hR (i : Fin 2) : mixedCoordinates (broadCoefficient α w • R i) =ᵐ[volume]
      fun z => broadCoefficient α w*(z.2 i.castSucc.succ:ℂ)*coordinateDensity α β w b P g z := by
    rw [map_smul]
    filter_upwards [Lp.coeFn_smul (broadCoefficient α w) (mixedCoordinates (R i)),
      rightState_coordinates_coe α β w hα hβ hw b P g hc hg i] with z hz hr
    simp only [hz,Pi.smul_apply,smul_eq_mul,hr,mul_assoc]
  have hA : mixedCoordinates (broadCoefficient α w • R 1+N) =ᵐ[volume]
      fun z => broadCoefficient α w*(z.2 2:ℂ)*coordinateDensity α β w b P g z+
        coordinateDensity α β w b (step β b P) g z := by
    rw [map_add]
    filter_upwards [Lp.coeFn_add (mixedCoordinates (broadCoefficient α w • R 1)) (mixedCoordinates N),hR 1,
      state_coordinates_coe α β w hα hβ hw b (step β b P) g hc hg] with z hz hr hn
    simp only [hz,Pi.add_apply,hr,hn]
    rfl
  fin_cases j
  · exact hL 0
  · exact hA
  · exact hR 0
  · exact hL 1

def momentumOutput (h : ℝ) (j : Fin 4) : Hilbert :=
  (-Complex.I*(h:ℂ)) • differentialState α β w hα hβ hw b P g hc hg j

theorem momentum_graph (h : ℝ) (j : Fin 4) :
    (state α β w hα hβ hw b P g hc hg,momentumOutput α β w hα hβ hw b P g hc hg h j) ∈
      (transverseMomentum h (modelDirections j)).graph := by
  let F := configurationDensity α β w b P g
  have hF : MemLp F 2 volume := (Lp.memLp (state α β w hα hβ hw b P g hc hg)).ae_eq
    (state_configuration_coe α β w hα hβ hw b P g hc hg)
  have hD : differentialState α β w hα hβ hw b P g hc hg j =ᵐ[volume] derivative (modelDirections j) F := by
    filter_upwards [differentialState_coe α β w hα hβ hw b P g hc hg j] with x hx
    exact hx.trans (differentialProfile_derivative α β w b P g j x).symm
  have hd : MemLp (derivative (modelDirections j) F) 2 volume := (Lp.memLp _).ae_eq hD
  have he : state α β w hα hβ hw b P g hc hg = hF.toLp F :=
    Lp.ext ((state_configuration_coe α β w hα hβ hw b P g hc hg).trans hF.coeFn_toLp.symm)
  have heD : differentialState α β w hα hβ hw b P g hc hg j = hd.toLp (derivative (modelDirections j) F) :=
    Lp.ext (hD.trans hd.coeFn_toLp.symm)
  rw [momentumOutput,he,heD]
  exact KFCausalTransverseMomentumDerivative.derivative_momentum_graph h F (modelDirections j) hF hd
    (density_transverse_differentiable α β w b P g)

theorem momentum_coordinates_coe (h : ℝ) (j : Fin 4) :
    mixedCoordinates (momentumOutput α β w hα hβ hw b P g hc hg h j) =ᵐ[volume]
      fun z => (-Complex.I*(h:ℂ))*differentialCoordinates α β w b P g j z := by
  rw [momentumOutput,map_smul]
  filter_upwards [Lp.coeFn_smul (-Complex.I*(h:ℂ))
    (mixedCoordinates (differentialState α β w hα hβ hw b P g hc hg j)),
    differentialState_coordinates_coe α β w hα hβ hw b P g hc hg j] with z hz hd
  simp only [hz,Pi.smul_apply,smul_eq_mul,hd]

#print axioms differentialProfile_derivative
#print axioms differentialState_coe
#print axioms differentialState_coordinates_coe
#print axioms momentum_graph
#print axioms momentum_coordinates_coe
end
end UnifiedTheory.Audit.KFCausalNarrowPacketMomentumGraphs
