/- Construct the complete second physical derivative vector and identify
its actual narrow Fourier representative, including mixed neutral terms. -/
import UnifiedTheory.Audit.KFCausalNarrowFourierSecondMomentStates
import UnifiedTheory.Audit.KFCausalNarrowPacketSecondDifferential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

namespace UnifiedTheory.Audit.KFCausalNarrowPacketSecondStates
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalNarrowFourierCoordinates (mixedCoordinates)
open KFCausalNarrowFourierPackets (state configurationDensity coordinateDensity state_configuration_coe state_coordinates_coe)
open KFCausalNarrowFourierMomentStates (leftState rightState leftState_coe rightState_coe leftState_coordinates_coe rightState_coordinates_coe)
open KFCausalNarrowFourierSecondMomentStates
open KFCausalNarrowPacketSecondDifferential (position coefficient neutral secondProfile)
open KFCausalNeutralLinePackets (step)
open KFCausalPairedModeCoordinates (scale scale_square)

variable (α β w : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 0 < w)
  (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume)

def positionState (j : Fin 4) : Hilbert :=
  ![leftState α β w hα hβ hw b P g hc hg 0,rightState α β w hα hβ hw b P g hc hg 1,
    rightState α β w hα hβ hw b P g hc hg 0,leftState α β w hα hβ hw b P g hc hg 1] j

def squareState (j : Fin 4) : Hilbert :=
  ![leftSquareState α β w hα hβ hw b P g hc hg 0,rightSquareState α β w hα hβ hw b P g hc hg 1,
    rightSquareState α β w hα hβ hw b P g hc hg 0,leftSquareState α β w hα hβ hw b P g hc hg 1] j

theorem positionState_coe (j : Fin 4) : positionState α β w hα hβ hw b P g hc hg j =ᵐ[volume]
    fun x => (position j x.2:ℂ)*configurationDensity α β w b P g x := by
  fin_cases j
  · exact leftState_coe α β w hα hβ hw b P g hc hg 0
  · exact rightState_coe α β w hα hβ hw b P g hc hg 1
  · exact rightState_coe α β w hα hβ hw b P g hc hg 0
  · exact leftState_coe α β w hα hβ hw b P g hc hg 1

theorem squareState_coe (j : Fin 4) : squareState α β w hα hβ hw b P g hc hg j =ᵐ[volume]
    fun x => (position j x.2:ℂ)^2*configurationDensity α β w b P g x := by
  fin_cases j
  · exact leftSquareState_coe α β w hα hβ hw b P g hc hg 0
  · exact rightSquareState_coe α β w hα hβ hw b P g hc hg 1
  · exact rightSquareState_coe α β w hα hβ hw b P g hc hg 0
  · exact leftSquareState_coe α β w hα hβ hw b P g hc hg 1

def firstMultiplier (j : Fin 4) (z : Block 2 × Block 4) : ℂ :=
  ![-(Real.pi:ℂ)*Complex.I*(z.1 0:ℂ)/(α/w:ℝ),(z.2 2:ℂ),(z.2 1:ℂ),
    -(Real.pi:ℂ)*Complex.I*(z.1 1:ℂ)/(α/w:ℝ)] j
def secondMultiplier (j : Fin 4) (z : Block 2 × Block 4) : ℂ :=
  ![1/(2*(α/w:ℝ))-(Real.pi:ℂ)^2*(z.1 0:ℂ)^2/(α/w:ℝ)^2,(z.2 2:ℂ)^2,(z.2 1:ℂ)^2,
    1/(2*(α/w:ℝ))-(Real.pi:ℂ)^2*(z.1 1:ℂ)^2/(α/w:ℝ)^2] j

theorem positionState_coordinates (j : Fin 4) : mixedCoordinates (positionState α β w hα hβ hw b P g hc hg j) =ᵐ[volume]
    fun z => firstMultiplier α w j z*coordinateDensity α β w b P g z := by
  fin_cases j
  · exact leftState_coordinates_coe α β w hα hβ hw b P g hc hg 0
  · exact rightState_coordinates_coe α β w hα hβ hw b P g hc hg 1
  · exact rightState_coordinates_coe α β w hα hβ hw b P g hc hg 0
  · exact leftState_coordinates_coe α β w hα hβ hw b P g hc hg 1

theorem squareState_coordinates (j : Fin 4) : mixedCoordinates (squareState α β w hα hβ hw b P g hc hg j) =ᵐ[volume]
    fun z => secondMultiplier α w j z*coordinateDensity α β w b P g z := by
  fin_cases j
  · exact leftSquareState_coordinates_coe α β w hα hβ hw b P g hc hg 0
  · exact rightSquareState_coordinates_coe α β w hα hβ hw b P g hc hg 1
  · exact rightSquareState_coordinates_coe α β w hα hβ hw b P g hc hg 0
  · exact leftSquareState_coordinates_coe α β w hα hβ hw b P g hc hg 1

def termStates (j : Fin 4) : Fin 4 → Hilbert :=
  ![state α β w hα hβ hw b P g hc hg,squareState α β w hα hβ hw b P g hc hg j,
    positionState α β w hα hβ hw b (step β b P) g hc hg j,
    state α β w hα hβ hw b (step β b (step β b P)) g hc hg]
def termCoefficients (j : Fin 4) : Fin 4 → ℂ :=
  ![coefficient α w j*(2*(scale:ℂ)),coefficient α w j^2,2*coefficient α w j*neutral j,neutral j^2]
def secondState (j : Fin 4) : Hilbert :=
  ∑ k, termCoefficients α w j k • termStates α β w hα hβ hw b P g hc hg j k

theorem secondState_coe (j : Fin 4) : secondState α β w hα hβ hw b P g hc hg j =ᵐ[volume]
    secondProfile α β w b P g j := by
  let F : Fin 4 → Configuration → ℂ := ![configurationDensity α β w b P g,
    (fun x => (position j x.2:ℂ)^2*configurationDensity α β w b P g x),
    (fun x => (position j x.2:ℂ)*configurationDensity α β w b (step β b P) g x),
    configurationDensity α β w b (step β b (step β b P)) g]
  have hf (k : Fin 4) : termStates α β w hα hβ hw b P g hc hg j k =ᵐ[volume] F k := by
    fin_cases k
    · exact state_configuration_coe α β w hα hβ hw b P g hc hg
    · exact squareState_coe α β w hα hβ hw b P g hc hg j
    · exact positionState_coe α β w hα hβ hw b (step β b P) g hc hg j
    · exact state_configuration_coe α β w hα hβ hw b (step β b (step β b P)) g hc hg
  filter_upwards [KFCausalFiniteLpRepresentatives.weighted_sum_coe volume (termCoefficients α w j)
    (termStates α β w hα hβ hw b P g hc hg j) F hf] with x hx
  rw [secondState,hx]
  simp [F,termCoefficients,Fin.sum_univ_succ,secondProfile,mul_assoc,add_assoc]

def secondCoordinates (j : Fin 4) (z : Block 2 × Block 4) : ℂ :=
  ![-8*(Real.pi:ℂ)^2*(z.1 0:ℂ)^2*coordinateDensity α β w b P g z,
    (-4*(α*w:ℝ)+8*(α*w:ℝ)^2*(z.2 2:ℂ)^2)*coordinateDensity α β w b P g z+
      (-8*(scale:ℂ)*(α*w:ℝ)*(z.2 2:ℂ))*coordinateDensity α β w b (step β b P) g z+
      coordinateDensity α β w b (step β b (step β b P)) g z,
    (-4*(α*w:ℝ)+8*(α*w:ℝ)^2*(z.2 1:ℂ)^2)*coordinateDensity α β w b P g z,
    -8*(Real.pi:ℂ)^2*(z.1 1:ℂ)^2*coordinateDensity α β w b P g z] j

theorem secondState_coordinates (j : Fin 4) : mixedCoordinates (secondState α β w hα hβ hw b P g hc hg j) =ᵐ[volume]
    secondCoordinates α β w b P g j := by
  let F : Fin 4 → Block 2 × Block 4 → ℂ := ![coordinateDensity α β w b P g,
    (fun z => secondMultiplier α w j z*coordinateDensity α β w b P g z),
    (fun z => firstMultiplier α w j z*coordinateDensity α β w b (step β b P) g z),
    coordinateDensity α β w b (step β b (step β b P)) g]
  have hf (k : Fin 4) : mixedCoordinates (termStates α β w hα hβ hw b P g hc hg j k) =ᵐ[volume] F k := by
    fin_cases k
    · exact state_coordinates_coe α β w hα hβ hw b P g hc hg
    · exact squareState_coordinates α β w hα hβ hw b P g hc hg j
    · exact positionState_coordinates α β w hα hβ hw b (step β b P) g hc hg j
    · exact state_coordinates_coe α β w hα hβ hw b (step β b (step β b P)) g hc hg
  rw [secondState,map_sum]
  simp only [map_smul]
  filter_upwards [KFCausalFiniteLpRepresentatives.weighted_sum_coe volume (termCoefficients α w j)
    (fun k => mixedCoordinates (termStates α β w hα hβ hw b P g hc hg j k)) F hf] with z hz
  rw [hz]
  have hs : (scale:ℂ)^2=(1/2:ℂ) := by rw [← Complex.ofReal_pow,scale_square]; norm_num
  have hA : (α:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα.ne'
  have hW : (w:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
  fin_cases j <;> simp [F,Fin.sum_univ_succ,termCoefficients,coefficient,neutral,firstMultiplier,secondMultiplier,
    secondCoordinates,KFCausalNarrowPacketMomentumGraphs.narrowCoefficient,KFCausalNarrowPacketMomentumGraphs.broadCoefficient]
  all_goals field_simp [hA,hW]; ring_nf; rw [hs]; ring

#print axioms positionState_coe
#print axioms squareState_coe
#print axioms positionState_coordinates
#print axioms squareState_coordinates
#print axioms secondState_coe
#print axioms secondState_coordinates
end
end UnifiedTheory.Audit.KFCausalNarrowPacketSecondStates
