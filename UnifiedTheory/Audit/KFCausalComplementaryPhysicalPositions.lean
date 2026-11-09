/- Identify the two complementary position coordinates with maximal
multiplication by the original normalized antisymmetric physical positions.
The equality includes the complete natural domains of both operators. -/
import UnifiedTheory.Audit.KFCausalChargePositionGraph
import UnifiedTheory.Audit.KFCausalComplementaryPhysicalMomenta

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalComplementaryPhysicalPositions
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (Space euclideanPullback)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates
open UnifiedTheory.Audit.KFCausalPairedTranslationCoordinates
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalChargeTransverseSplit
open UnifiedTheory.Audit.KFCausalChargeDualMomentum
open UnifiedTheory.Audit.KFCausalComplementaryChargeSymbol
open UnifiedTheory.Audit.KFCausalChargePositionGraph
open UnifiedTheory.Audit.KFCausalDirectionalTranslationMomentum
open UnifiedTheory.Audit.KFCausalUnitaryRealMultiplier
open UnifiedTheory.Audit.KFCausalRealMultiplierSelfAdjoint
open UnifiedTheory.Audit.KFCausalSelfAdjointMultiplierIdentification

def positionBasis (i : Fin 2) : Block 2 := WithLp.toLp 2 (Pi.single i 1)

def positionSymbol (i : Fin 2) (x : Space) : ℝ :=
  ![scale*(x 1-x 2),scale*(x 3-x 4)] i

theorem positionSymbol_continuous (i : Fin 2) : Continuous (positionSymbol i) := by
  unfold positionSymbol
  fin_cases i <;> simp only [Matrix.cons_val_zero',Matrix.cons_val_succ'] <;> fun_prop

def positionScale : ℝ := -1/(2*Real.pi)

theorem positionScale_ne_zero : positionScale ≠ 0 := by
  exact div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) Real.pi_ne_zero)

theorem positionScale_mul : 2*Real.pi*positionScale = -1 := by
  unfold positionScale
  field_simp

theorem position_basis_symbol (i : Fin 2) (x : Space) :
    2*Real.pi*positionScale*inner ℝ (split 2 4 (modeIsometry x)).1 (-positionBasis i) =
      positionSymbol i x := by
  rw [positionScale_mul]
  fin_cases i <;> simp [positionBasis,positionSymbol,PiLp.inner_apply,RCLike.inner_apply,
    split_fst,modeIsometry,modeEquiv,forward]

theorem position_dual_symbol (i : Fin 2) (x : Joint 5 1) :
    dualSymbol positionScale (leftVector (positionBasis i)) x = complementaryPosition i x := by
  unfold dualSymbol
  rw [positionScale_mul]
  fin_cases i <;> simp [transverseBlock,split_fst,repackIsometry,repackEquiv,repack,
    leftVector,positionBasis,PiLp.inner_apply,RCLike.inner_apply,Fin.sum_univ_succ,
    complementaryPosition,antiDualIndex]

def physicalPosition (i : Fin 2) : Hilbert →ₗ.[ℂ] Hilbert :=
  realPullback euclideanPullback (positionSymbol i) (positionSymbol_continuous i).measurable

def dualPosition (i : Fin 2) : Hilbert →ₗ.[ℂ] Hilbert :=
  realPullback dualPhysical (complementaryPosition i) (by
    unfold complementaryPosition
    fun_prop)

def chargePosition (i : Fin 2) : Hilbert →ₗ.[ℂ] Hilbert :=
  realPullback (chargeCoordinates.trans (Lp.fourierTransformₗᵢ (Joint 2 4) ℂ))
    (multiplier positionScale (leftVector (positionBasis i))) (multiplier_measurable _ _)

theorem chargePosition_graph (i : Fin 2) (f g : Hilbert) :
    (f,g) ∈ (chargePosition i).graph ↔
      (chargeCoordinates f,chargeCoordinates g) ∈ (spectralMomentum positionScale (leftVector (positionBasis i))).graph := by
  unfold chargePosition spectralMomentum
  rw [realPullback_graph,realPullback_graph]
  rfl

theorem chargePosition_physical_coe (i : Fin 2) (f g : Hilbert)
    (hfg : (f,g) ∈ (chargePosition i).graph) :
    euclideanPullback g =ᵐ[volume] fun x => (positionSymbol i x:ℂ)*(euclideanPullback f) x := by
  have he := inverse_momentum_graph_coe positionScale positionScale_ne_zero (positionBasis i)
    _ _ ((chargePosition_graph i f g).mp hfg)
  have hi (u : Hilbert) : chargeEuclidean.symm (chargeCoordinates u) = euclideanPullback u := by
    rw [← chargeEuclidean_physical,LinearIsometryEquiv.symm_apply_apply]
  simpa only [hi,position_basis_symbol] using he

theorem chargePosition_dual_coe (i : Fin 2) (f g : Hilbert)
    (hfg : (f,g) ∈ (chargePosition i).graph) :
    dualPhysical g =ᵐ[volume] fun x => (complementaryPosition i x:ℂ)*(dualPhysical f) x := by
  have he := dualMomentum_graph_coe positionScale positionScale_ne_zero (leftVector (positionBasis i))
    rfl _ _ ((chargePosition_graph i f g).mp hfg)
  simpa only [position_dual_symbol] using he

theorem physicalPosition_eq_dual (i : Fin 2) : physicalPosition i = dualPosition i := by
  have hs : IsSelfAdjoint (chargePosition i) := realPullback_selfAdjoint _ _ _
  have hp : chargePosition i = physicalPosition i :=
    selfAdjoint_eq_realPullback _ hs _ _ _ (chargePosition_physical_coe i)
  have hd : chargePosition i = dualPosition i :=
    selfAdjoint_eq_realPullback _ hs _ _ _ (chargePosition_dual_coe i)
  exact hp.symm.trans hd

theorem physicalPosition_dual_graph (i : Fin 2) (f g : Hilbert) :
    (f,g) ∈ (physicalPosition i).graph ↔
      dualPhysical g =ᵐ[volume] fun x => (complementaryPosition i x:ℂ)*(dualPhysical f) x := by
  rw [physicalPosition_eq_dual]
  exact realPullback_graph _ _ _ f g

#print axioms positionSymbol_continuous
#print axioms positionScale_ne_zero
#print axioms positionScale_mul
#print axioms position_basis_symbol
#print axioms position_dual_symbol
#print axioms chargePosition_graph
#print axioms chargePosition_physical_coe
#print axioms chargePosition_dual_coe
#print axioms physicalPosition_eq_dual
#print axioms physicalPosition_dual_graph

end
end UnifiedTheory.Audit.KFCausalComplementaryPhysicalPositions
