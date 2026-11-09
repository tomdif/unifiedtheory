/- The explicit pure-clock output construction preserves second kinetic
graphs. All inverse-clock and transverse commutations are on actual graphs. -/
import UnifiedTheory.Audit.KFCausalGaussianKineticSquare
import UnifiedTheory.Audit.KFCausalPureClockOutputMultipliers
import UnifiedTheory.Audit.KFCausalSourcedMomentumFactors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalKineticSquareClockOutput
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalClockFloorClockHalf (inverseClockHalf)
open KFCausalClockFloorBoundedInverse (inverseL inverseL_graph inverseL_defect)
open KFCausalPhysicalTransverseMomentum (transverseMomentum)
open KFCausalClockFloorPureClockCommonDomain (clockInverse)
open KFCausalClockFloorDefectOperator (defectOperator)
open KFCausalPureClockOutputMultipliers (outputMap rateOperator)
open KFCausalShiftedClockMomentOperator (momentOperator)
open KFCausalClockFloorKineticSquare (square square_graph)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a)

theorem outputMap_inverse_graph (p : ℝ) (f f' g g' : Hilbert)
    (hf : (f,f') ∈ (inverseClockHalf ε).graph)
    (hg : (g,g') ∈ (inverseClockHalf ε).graph) :
    (outputMap ε a h hε ha p f g,outputMap ε a h hε ha p f' g') ∈
      (inverseClockHalf ε).graph := by
  have hd : (defectOperator ε hε f,defectOperator ε hε f') ∈ (inverseClockHalf ε).graph := by
    apply (inverseL_graph ε hε _ _).mpr
    rw [(inverseL_graph ε hε f f').mp hf,← inverseL_defect]
  have hi : (clockInverse ε hε f,clockInverse ε hε f') ∈ (inverseClockHalf ε).graph :=
    (inverseClockHalf ε).graph.smul_mem (1/(ε:ℂ)) hd
  have hr : (rateOperator ε hε f,rateOperator ε hε f') ∈ (inverseClockHalf ε).graph :=
    KFCausalBoundedClockFactorGraphs.inverse_half_graph _ _ _ _ _ ε f f' hf
  have hm : (momentOperator ε a 0 ha g,momentOperator ε a 0 ha g') ∈ (inverseClockHalf ε).graph :=
    KFCausalBoundedClockFactorGraphs.inverse_half_graph _ _ _ _ _ ε g g' hg
  exact (inverseClockHalf ε).graph.smul_mem _ ((inverseClockHalf ε).graph.sub_mem
    ((inverseClockHalf ε).graph.sub_mem ((inverseClockHalf ε).graph.smul_mem _ hi) hr)
    ((inverseClockHalf ε).graph.smul_mem _ hm))

theorem outputMap_transverse_graph (hh : h ≠ 0) (v : Transverse) (p : ℝ) (f f' g g' : Hilbert)
    (hf : (f,f') ∈ (transverseMomentum h v).graph)
    (hg : (g,g') ∈ (transverseMomentum h v).graph) :
    (outputMap ε a h hε ha p f g,outputMap ε a h hε ha p f' g') ∈
      (transverseMomentum h v).graph := by
  have hi : (clockInverse ε hε f,clockInverse ε hε f') ∈ (transverseMomentum h v).graph :=
    (transverseMomentum h v).graph.smul_mem (1/(ε:ℂ))
      (KFCausalClockFloorKineticDefect.transverse_graph_defect ε hε h v f f' hf)
  have hr : (rateOperator ε hε f,rateOperator ε hε f') ∈ (transverseMomentum h v).graph :=
    KFCausalBoundedClockFactorGraphs.transverse_graph _ _ _ _ _ h hh v f f' hf
  have hm : (momentOperator ε a 0 ha g,momentOperator ε a 0 ha g') ∈ (transverseMomentum h v).graph :=
    KFCausalBoundedClockFactorGraphs.transverse_graph _ _ _ _ _ h hh v g g' hg
  exact (transverseMomentum h v).graph.smul_mem _ ((transverseMomentum h v).graph.sub_mem
    ((transverseMomentum h v).graph.sub_mem ((transverseMomentum h v).graph.smul_mem _ hi) hr)
    ((transverseMomentum h v).graph.smul_mem _ hm))

theorem outputMap_square_graph (hh : h ≠ 0) (v : Transverse) (p : ℝ) (f f' g g' : Hilbert)
    (hf : (f,f') ∈ (square ε h v).graph)
    (hg : (g,g') ∈ (square ε h v).graph) :
    (outputMap ε a h hε ha p f g,outputMap ε a h hε ha p f' g') ∈ (square ε h v).graph := by
  obtain ⟨u,q,hfu,huq,hq⟩ := (square_graph ε hε h v f f').mp hf
  obtain ⟨u',q',hgu',hu'q',hq'⟩ := (square_graph ε hε h v g g').mp hg
  have hd := outputMap_inverse_graph ε a h hε ha p f (inverseL ε hε f) g (inverseL ε hε g)
    ((inverseL_graph ε hε _ _).mpr rfl) ((inverseL_graph ε hε _ _).mpr rfl)
  have h1 := outputMap_transverse_graph ε a h hε ha hh v p _ _ _ _ hfu hgu'
  rw [(inverseL_graph ε hε _ _).mp hd] at h1
  apply (square_graph ε hε h v _ _).mpr
  refine ⟨_,_,h1,outputMap_transverse_graph ε a h hε ha hh v p _ _ _ _ huq hu'q',?_⟩
  exact (inverseL_graph ε hε _ _).mp
    (outputMap_inverse_graph ε a h hε ha p q f' q' g'
      ((inverseL_graph ε hε _ _).mpr hq) ((inverseL_graph ε hε _ _).mpr hq'))

variable (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)

def momentumOutput (v : Transverse) : Hilbert := outputMap ε a h hε ha 0
  (KFCausalGaussianKineticSquare.squareOutput ε a α β hε ha hα hβ h v)
  (KFCausalGaussianKineticSquare.squareOutput ε (a/2) α β hε (by positivity) hα hβ h v)

theorem momentum_graph (hh : h ≠ 0) (v : Transverse) :
    (KFCausalSourcedMomentumFactors.pureOutput ε a α β hε ha hα hβ hw 1 0 0 h,
      momentumOutput ε a h hε ha α β hα hβ v) ∈ (square ε h v).graph :=
  outputMap_square_graph ε a h hε ha hh v 0 _ _ _ _
    (KFCausalGaussianKineticSquare.squareOutput_graph ε a α β hε ha hα hβ hw h v)
    (KFCausalGaussianKineticSquare.squareOutput_graph ε (a/2) α β hε (by positivity) hα hβ hw h v)

#print axioms outputMap_inverse_graph
#print axioms outputMap_transverse_graph
#print axioms outputMap_square_graph
#print axioms momentum_graph
end
end UnifiedTheory.Audit.KFCausalKineticSquareClockOutput
