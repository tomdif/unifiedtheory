/- The two actual antisymmetric maximal momenta are multiplication by
physical momenta in the existing charge coordinates. This is derived from
strong translation generators on the full natural operator graphs. -/
import UnifiedTheory.Audit.KFCausalPairedTranslationCoordinates
import UnifiedTheory.Audit.KFCausalClockFloorKineticDefect
import UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalAntisymmetricMomentumCoordinates
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (Space FrequencyHilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates
open UnifiedTheory.Audit.KFCausalPairedTranslationCoordinates
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalPhysicalTransverseMomentum (transverseMomentum transverseVector)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalClockFloorKineticDefect (transverse_graph_iff)
open UnifiedTheory.Audit.KFCausalDirectionalTranslationMomentum

theorem spectral_graph_charge_coe (h : ℝ) (hh : h ≠ 0) (v : Space) (a : Block 2)
    (hv : modeIsometry v = leftVector a) (f g : FrequencyHilbert)
    (hfg : (f,g) ∈ (spectralMomentum h v).graph) :
    chargeEuclidean g =ᵐ[volume]
      fun x => (2*Real.pi*h*inner ℝ (split 2 4 x).1 a : ℝ)*(chargeEuclidean f) x := by
  have hd := ((chargeEuclidean : FrequencyHilbert →L[ℂ] JointHilbert 2 4).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    ((spectralMomentum_graph_derivative h hh v f g).mp hfg)
  change HasDerivAt (fun t => chargeEuclidean (KFCausalFourierTranslation.translation (t • v) f))
    (chargeEuclidean ((Complex.I/(h:ℂ)) • g)) 0 at hd
  rw [map_smul] at hd
  have hr := KFCausalLpDerivativeRepresentative.derivative_representative _ _ _ _
    (fun t => chargeEuclidean_directional_coe v a hv t f) hd
    (fun x => phase_derivative a (split 2 4 x).1 ((chargeEuclidean f) x))
  filter_upwards [hr,Lp.coeFn_smul (Complex.I/(h:ℂ)) (chargeEuclidean g)] with x hx hs
  rw [hs] at hx
  simp only [Pi.smul_apply,smul_eq_mul] at hx
  have he := congrArg (fun z : ℂ => (-Complex.I*(h:ℂ))*z) hx
  dsimp only at he
  have hi : (-Complex.I*(h:ℂ))*(Complex.I/(h:ℂ)) = 1 := by
    rw [mul_comm,KFCausalUnitaryMomentumEvolution.inverse_coefficient h hh]
  rw [← mul_assoc,hi,one_mul] at he
  rw [he]
  push_cast
  ring_nf
  norm_num [Complex.I_sq]

def antiDirection (i : Fin 2) : Transverse := ![modelDirections 2,modelDirections 3] i

def antiFrequency (i : Fin 2) : Block 2 := WithLp.toLp 2 (Pi.single i (2*scale))

theorem transverseVector_explicit (v : Transverse) :
    transverseVector v = WithLp.toLp 2 ![0,v 0,v 1,v 2,v 3,v 4] := by
  ext i
  fin_cases i <;> rfl

theorem antiDirection_mode (i : Fin 2) :
    modeIsometry (transverseVector (antiDirection i)) = leftVector (antiFrequency i) := by
  rw [transverseVector_explicit]
  fin_cases i <;> ext j <;> rcases j with j | j <;> fin_cases j <;>
    simp [modeIsometry,modeEquiv,forward,antiDirection,modelDirections,antiFrequency,leftVector]
  all_goals ring

def antiSymbol (h : ℝ) (i : Fin 2) (x : Joint 2 4) : ℝ :=
  2*Real.pi*h*(2*scale)*x (.inl i)

theorem antiSymbol_eq (h : ℝ) (i : Fin 2) (x : Joint 2 4) :
    2*Real.pi*h*inner ℝ (split 2 4 x).1 (antiFrequency i) = antiSymbol h i x := by
  fin_cases i <;> simp [antiFrequency,antiSymbol,PiLp.inner_apply,RCLike.inner_apply,split_fst]
  all_goals ring

theorem antisymmetric_graph_coe (h : ℝ) (hh : h ≠ 0) (i : Fin 2) (f g : Hilbert)
    (hfg : (f,g) ∈ (transverseMomentum h (antiDirection i)).graph) :
    chargeCoordinates g =ᵐ[volume] fun x => (antiSymbol h i x : ℂ)*(chargeCoordinates f) x := by
  have he := spectral_graph_charge_coe h hh (transverseVector (antiDirection i))
    (antiFrequency i) (antiDirection_mode i) _ _ ((transverse_graph_iff h (antiDirection i) f g).mp hfg)
  simpa only [chargeEuclidean_physical,antiSymbol_eq] using he

#print axioms spectral_graph_charge_coe
#print axioms transverseVector_explicit
#print axioms antiDirection_mode
#print axioms antiSymbol_eq
#print axioms antisymmetric_graph_coe

end
end UnifiedTheory.Audit.KFCausalAntisymmetricMomentumCoordinates
