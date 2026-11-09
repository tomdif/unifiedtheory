/- Actual second physical directional derivatives, retaining the mixed
broad/neutral cross term. Clock coefficients are arbitrary spectators. -/
import UnifiedTheory.Audit.KFCausalNarrowPacketMomentumGraphs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalNarrowPacketSecondDifferential
noncomputable section
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalNarrowFourierPackets (configurationDensity)
open KFCausalNeutralLinePackets (step)
open KFCausalNarrowFourierMomentStates (leftPositions rightPositions)
open KFCausalNarrowPacketMomentumGraphs (narrowCoefficient broadCoefficient differentialProfile differentialProfile_derivative)
open KFCausalNarrowPacketDifferential (density_line_derivative density_derivative density_transverse_differentiable)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalPairedModeCoordinates (scale)
open KFCausalTransverseTrialDerivative (derivative)

def position (j : Fin 4) (q : Transverse) : ℝ :=
  ![leftPositions q 0,rightPositions q 1,rightPositions q 0,leftPositions q 1] j
def coefficient (α w : ℝ) (j : Fin 4) : ℂ :=
  ![narrowCoefficient α w,broadCoefficient α w,broadCoefficient α w,narrowCoefficient α w] j
def neutral (j : Fin 4) : ℂ := ![0,1,0,0] j

def firstProfile (α β w : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (j : Fin 4) (x : Configuration) : ℂ :=
  coefficient α w j*(position j x.2:ℂ)*configurationDensity α β w b P g x+
    neutral j*configurationDensity α β w b (step β b P) g x

def secondProfile (α β w : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (j : Fin 4) (x : Configuration) : ℂ :=
  (coefficient α w j*(2*(scale:ℂ)))*configurationDensity α β w b P g x+
    coefficient α w j^2*(position j x.2:ℂ)^2*configurationDensity α β w b P g x+
    (2*coefficient α w j*neutral j)*(position j x.2:ℂ)*configurationDensity α β w b (step β b P) g x+
    neutral j^2*configurationDensity α β w b (step β b (step β b P)) g x

theorem firstProfile_eq (α β w : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (j : Fin 4) (x : Configuration) : firstProfile α β w b P g j x = differentialProfile α β w b P g j x := by
  fin_cases j <;> simp [firstProfile,differentialProfile,coefficient,position,neutral]

theorem position_line (j : Fin 4) (q : Transverse) :
    HasDerivAt (fun t : ℝ => position j (q+t • modelDirections j)) (2*scale) 0 := by
  have he : (fun t : ℝ => position j (q+t • modelDirections j)) =
      (fun t => position j q+t*(2*scale)) := by
    funext t
    fin_cases j <;> simp [position,leftPositions,rightPositions,modelDirections] <;> ring
  rw [he]
  simpa only [id_eq,one_mul] using ((hasDerivAt_id (0:ℝ)).mul_const (2*scale)).const_add (position j q)

theorem density_line_first (α β w : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (s : ℝ) (q : Transverse) (j : Fin 4) :
    HasLineDerivAt ℝ (fun y => configurationDensity α β w b P g (s,y))
      (firstProfile α β w b P g j (s,q)) q (modelDirections j) := by
  have he := (differentialProfile_derivative α β w b P g j (s,q)).symm
  rw [density_derivative] at he
  rw [firstProfile_eq,he]
  exact density_line_derivative α β w b P g s q (modelDirections j)

theorem firstProfile_line (α β w : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (s : ℝ) (q : Transverse) (j : Fin 4) :
    HasLineDerivAt ℝ (fun y => firstProfile α β w b P g j (s,y))
      (secondProfile α β w b P g j (s,q)) q (modelDirections j) := by
  have hF : HasDerivAt (fun t : ℝ => configurationDensity α β w b P g (s,q+t • modelDirections j))
      (firstProfile α β w b P g j (s,q)) 0 := density_line_first α β w b P g s q j
  have hN : HasDerivAt (fun t : ℝ => configurationDensity α β w b (step β b P) g (s,q+t • modelDirections j))
      (firstProfile α β w b (step β b P) g j (s,q)) 0 := density_line_first α β w b (step β b P) g s q j
  have hd := (((position_line j q).ofReal_comp.mul hF).const_mul (coefficient α w j)).add
    (hN.const_mul (neutral j))
  change HasDerivAt (fun t : ℝ => firstProfile α β w b P g j (s,q+t • modelDirections j)) _ 0
  convert hd using 1
  · funext t
    simp only [firstProfile,Pi.add_apply,Pi.mul_apply]
    ring
  · simp only [firstProfile,secondProfile,zero_smul,add_zero,Complex.ofReal_mul,Complex.ofReal_ofNat]
    ring

theorem second_derivative (α β w : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (j : Fin 4) (x : Configuration) :
    derivative (modelDirections j) (firstProfile α β w b P g j) x = secondProfile α β w b P g j x :=
  (firstProfile_line α β w b P g x.1 x.2 j).lineDeriv

theorem firstProfile_transverse_differentiable (α β w : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (g : ℝ → ℂ) (j : Fin 4) (s : ℝ) :
    Differentiable ℝ (fun q : Transverse => firstProfile α β w b P g j (s,q)) := by
  have hp : Differentiable ℝ (fun q : Transverse => (position j q:ℂ)) := by
    apply Complex.ofRealCLM.differentiable.comp
    fin_cases j
    · change Differentiable ℝ (fun q : Transverse => scale*(q 0+q 1))
      fun_prop
    · change Differentiable ℝ (fun q : Transverse => scale*(q 2+q 3))
      fun_prop
    · change Differentiable ℝ (fun q : Transverse => scale*(q 0-q 1))
      fun_prop
    · change Differentiable ℝ (fun q : Transverse => scale*(q 2-q 3))
      fun_prop
  simpa only [firstProfile,Pi.mul_apply,Pi.add_apply,mul_assoc] using
    ((hp.mul (density_transverse_differentiable α β w b P g s)).const_mul (coefficient α w j)).add
    ((density_transverse_differentiable α β w b (step β b P) g s).const_mul (neutral j))

#print axioms firstProfile_eq
#print axioms position_line
#print axioms density_line_first
#print axioms firstProfile_line
#print axioms second_derivative
#print axioms firstProfile_transverse_differentiable
end
end UnifiedTheory.Audit.KFCausalNarrowPacketSecondDifferential
