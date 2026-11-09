/- Identify the three momentum coordinates of the complementary Born law
with the original maximal physical momenta: two normalized symmetric
directions and the neutral direction. This is an operator-graph identity. -/
import UnifiedTheory.Audit.KFCausalComplementaryChargeSymbol

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalComplementaryPhysicalMomenta
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalPhysicalTransverseMomentum (transverseMomentum transverseVector)
open UnifiedTheory.Audit.KFCausalAntisymmetricMomentumCoordinates (transverseVector_explicit)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalSymmetricMomentumCoordinates
open UnifiedTheory.Audit.KFCausalChargeDualMomentum
open UnifiedTheory.Audit.KFCausalChargeTransverseSplit
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow (momentumScale)
open UnifiedTheory.Audit.KFCausalComplementaryChargeSymbol
open UnifiedTheory.Audit.KFCausalUnitaryRealMultiplier (realPullback realPullback_graph realPullback_coe)

def physicalDirection (j : Fin 3) : Transverse :=
  ![![scale,scale,0,0,0],![0,0,scale,scale,0],![0,0,0,0,1]] j

def directionBlock (j : Fin 3) : Block 4 :=
  WithLp.toLp 2 (![![0,1,0,0],![0,0,1,0],![0,0,0,1]] j)

def momentumIndex (j : Fin 3) : Fin 5 := ![2,3,4] j

theorem physicalDirection_mode (j : Fin 3) :
    modeIsometry (transverseVector (physicalDirection j)) = rightVector (directionBlock j) := by
  rw [transverseVector_explicit]
  fin_cases j <;> ext k <;> rcases k with k | k <;> fin_cases k <;>
    simp [modeIsometry,modeEquiv,forward,physicalDirection,rightVector,directionBlock]
  all_goals ring_nf; rw [scale_square]; norm_num

theorem direction_clock (j : Fin 3) : rightVector (directionBlock j) (.inr 0) = 0 := by
  fin_cases j <;> rfl

theorem direction_symbol (h : ℝ) (j : Fin 3) (x : Joint 5 1) :
    dualSymbol h (rightVector (directionBlock j)) x = momentumScale h*x (.inl (momentumIndex j)) := by
  fin_cases j <;>
    simp [dualSymbol,transverseBlock,split_fst,repackIsometry,repackEquiv,repack,
      rightVector,directionBlock,PiLp.inner_apply,RCLike.inner_apply,Fin.sum_univ_succ,momentumIndex,momentumScale]

theorem physicalMomentum_dual_coe (h : ℝ) (hh : h ≠ 0) (j : Fin 3) (f g : Hilbert)
    (hfg : (f,g) ∈ (transverseMomentum h (physicalDirection j)).graph) :
    dualPhysical g =ᵐ[volume] fun x =>
      (momentumScale h*x (.inl (momentumIndex j)) : ℝ)*(dualPhysical f) x := by
  have hg := transverse_charge_graph h hh _ _ (physicalDirection_mode j) f g hfg
  have he := dualMomentum_graph_coe h hh _ (direction_clock j) _ _ hg
  simpa only [direction_symbol] using he

def dualMomentum (h : ℝ) (j : Fin 3) : Hilbert →ₗ.[ℂ] Hilbert :=
  realPullback dualPhysical (fun x => momentumScale h*x (.inl (momentumIndex j))) (by fun_prop)

theorem physicalMomentum_eq_dual (h : ℝ) (hh : h ≠ 0) (j : Fin 3) :
    transverseMomentum h (physicalDirection j) = dualMomentum h j := by
  let A := transverseMomentum h (physicalDirection j)
  have hle : A ≤ dualMomentum h j := by
    apply LinearPMap.le_graph_iff.mp
    rintro ⟨f,g⟩ hfg
    exact (realPullback_graph _ _ _ f g).mpr (physicalMomentum_dual_coe h hh j f g hfg)
  have hf : A.IsFormalAdjoint (dualMomentum h j) := by
    intro f g
    rw [← dualPhysical.inner_map_map (A f) (g:Hilbert),
      ← dualPhysical.inner_map_map (f:Hilbert) (dualMomentum h j g),L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [physicalMomentum_dual_coe h hh j f (A f) (A.mem_graph f),
      realPullback_coe dualPhysical (fun x => momentumScale h*x (.inl (momentumIndex j))) (by fun_prop) g] with x ha hb
    change (dualPhysical (dualMomentum h j g)) x = _ at hb
    rw [ha,hb]
    change inner ℂ (((momentumScale h*x (.inl (momentumIndex j)):ℝ):ℂ) • (dualPhysical (f:Hilbert)) x)
      ((dualPhysical (g:Hilbert)) x) = inner ℂ ((dualPhysical (f:Hilbert)) x)
        ((((momentumScale h*x (.inl (momentumIndex j)):ℝ):ℂ) • (dualPhysical (g:Hilbert)) x))
    simp [mul_assoc,mul_left_comm]
  have hr := hf.le_adjoint (KFCausalPhysicalTransverseMomentum.transverseMomentum_dense h (physicalDirection j))
  have hs : A.adjoint = A := LinearPMap.isSelfAdjoint_def.mp
    (KFCausalPhysicalTransverseMomentum.transverseMomentum_selfAdjoint h (physicalDirection j))
  rw [hs] at hr
  exact le_antisymm hle hr

#print axioms physicalDirection_mode
#print axioms direction_clock
#print axioms direction_symbol
#print axioms physicalMomentum_dual_coe
#print axioms physicalMomentum_eq_dual

end
end UnifiedTheory.Audit.KFCausalComplementaryPhysicalMomenta
