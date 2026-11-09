/- The two physical antisymmetric momenta in the actual straightened mixed
chart, with their maximal natural graphs in both directions. -/
import UnifiedTheory.Audit.KFCausalAntisymmetricMomentumGraphEquivalence
import UnifiedTheory.Audit.KFCausalClockFloorMixedRadial

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClockMixedAntisymmetricGraph
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Block split)
open KFCausalClockFloorMixedRadial (clockMixed clockMixed_relation)
open KFCausalClockFloorMixedChart (mixedMap)
open KFCausalClockFloorPairedStraightening (dilation dilation_continuous)
open KFCausalPhysicalTransverseMomentum (transverseMomentum transverseMomentum_selfAdjoint)
open KFCausalAntisymmetricMomentumCoordinates (antiDirection antiSymbol antisymmetric_graph_coe)
open KFCausalPairedModeCoordinates (scale)
open KFCausalUnitaryRealMultiplier (realPullback realPullback_graph realPullback_domain)
open KFCausalRealMultiplierSelfAdjoint (realPullback_symmetric)

def mixedSymbol (ε : ℝ) (hε : 0 < ε) (h : ℝ) (i : Fin 2)
    (x : Block 2 × Block 4) : ℝ :=
  antiSymbol h i ((split 2 4).symm (mixedMap ε hε x))

theorem mixedSymbol_eq (ε : ℝ) (hε : 0 < ε) (h : ℝ) (i : Fin 2)
    (x : Block 2 × Block 4) :
    mixedSymbol ε hε h i x=2*Real.pi*h*(2*scale)*(dilation ε hε x.2)⁻¹*x.1 i := by
  change 2*Real.pi*h*(2*scale)*((dilation ε hε x.2)⁻¹*x.1 i)=_
  ring

theorem mixedSymbol_continuous (ε : ℝ) (hε : 0 < ε) (h : ℝ) (i : Fin 2) :
    Continuous (mixedSymbol ε hε h i) := by
  change Continuous (fun x => mixedSymbol ε hε h i x)
  simp_rw [mixedSymbol_eq]
  have hd : Continuous (fun x : Block 2 × Block 4 => dilation ε hε x.2) :=
    (dilation_continuous ε hε).comp continuous_snd
  have hn : ∀ x : Block 2 × Block 4, dilation ε hε x.2 ≠ 0 :=
    fun _ => Real.exp_ne_zero _
  exact (continuous_const.mul (hd.inv₀ hn)).mul ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) i).comp continuous_fst)

theorem momentum_graph_coe (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (i : Fin 2) (f g : Hilbert) (hfg : (f,g) ∈ (transverseMomentum h (antiDirection i)).graph) :
    clockMixed ε hε g =ᵐ[volume] fun x =>
      (mixedSymbol ε hε h i x:ℂ)*(clockMixed ε hε f) x :=
  clockMixed_relation ε hε _ f g (antisymmetric_graph_coe h hh i f g hfg)

theorem momentum_eq_multiplier (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (i : Fin 2) :
    transverseMomentum h (antiDirection i) =
      realPullback (clockMixed ε hε) (mixedSymbol ε hε h i)
        (mixedSymbol_continuous ε hε h i).measurable := by
  let A := transverseMomentum h (antiDirection i)
  let B := realPullback (clockMixed ε hε) (mixedSymbol ε hε h i)
    (mixedSymbol_continuous ε hε h i).measurable
  have hle : A ≤ B := by
    apply LinearPMap.le_graph_iff.mp
    rintro ⟨f,g⟩ hfg
    exact (realPullback_graph (clockMixed ε hε) (mixedSymbol ε hε h i) _ f g).mpr
      (momentum_graph_coe ε hε h hh i f g hfg)
  have hsa : IsSelfAdjoint A := transverseMomentum_selfAdjoint h (antiDirection i)
  have hsym : A.IsFormalAdjoint B := by
    intro f g
    have he : A f=B ⟨f,hle.1 f.property⟩ := hle.2 rfl
    rw [he]
    exact realPullback_symmetric (clockMixed ε hε) (mixedSymbol ε hε h i) _
      ⟨f,hle.1 f.property⟩ g
  have hrev := hsym.le_adjoint hsa.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hsa] at hrev
  exact le_antisymm hle hrev

theorem momentum_graph_iff (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (i : Fin 2) (f g : Hilbert) :
    (f,g) ∈ (transverseMomentum h (antiDirection i)).graph ↔
      clockMixed ε hε g =ᵐ[volume] fun x =>
        (mixedSymbol ε hε h i x:ℂ)*(clockMixed ε hε f) x := by
  rw [momentum_eq_multiplier ε hε h hh i]
  exact realPullback_graph _ _ _ f g

theorem momentum_domain_iff (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (i : Fin 2) (f : Hilbert) :
    f ∈ (transverseMomentum h (antiDirection i)).domain ↔
      MemLp (fun x => (mixedSymbol ε hε h i x:ℂ)*(clockMixed ε hε f) x) 2 := by
  rw [momentum_eq_multiplier ε hε h hh i]
  exact realPullback_domain _ _ _ f

#print axioms mixedSymbol_eq
#print axioms mixedSymbol_continuous
#print axioms momentum_graph_coe
#print axioms momentum_eq_multiplier
#print axioms momentum_graph_iff
#print axioms momentum_domain_iff
end
end UnifiedTheory.Audit.KFCausalClockMixedAntisymmetricGraph
