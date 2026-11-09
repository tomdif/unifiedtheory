/- A proved graph core for every clock/neutral energy fiber, built from
explicit separable modulated packets. -/
import UnifiedTheory.Audit.KFCausalSpectatorCoreWeights

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalSpectatorEnergyCore
noncomputable section
open MeasureTheory
open KFCausalEuclideanProductCoordinates
open KFCausalPhysicalSpectatorPackets (one)
open KFCausalModulatedLpTotality (state state_coe)
open KFCausalEuclideanFourierUniqueness (modulate)
open KFCausalSpectatorEnergyPackets (energy output output_coe)
open KFCausalSpectatorCoreWeights
open KFCausalEuclideanGaussianCore (gaussian gaussian_memLp)

variable (ε : ℝ) (hε : 0 < ε)

def weight : Block 2 → ℂ :=
  KFCausalJoinedModulatedWeights.weight (clockWeight ε) neutralWeight

include hε
theorem weight_memLp : MemLp (weight ε) 2 :=
  KFCausalJoinedModulatedWeights.weight_memLp (clockWeight ε) neutralWeight
    (clock_memLp ε hε) neutral_memLp

def input (k : Block 2) : BlockHilbert 2 := state (weight ε) (weight_memLp ε hε) k

def coreOutput (c a : ℝ) (k : Block 2) : BlockHilbert 2 :=
  output c a
    (state gaussian gaussian_memLp (one (k 0)))
    (state (clockInverseWeight ε) (clockInverse_memLp ε hε) (one (k 0)))
    (state neutralWeight neutral_memLp (one (k 1)))
    (state neutralSquareWeight neutralSquare_memLp (one (k 1)))

theorem input_join (k : Block 2) : input ε hε k =
    KFCausalJoinedMultiplierSum.joinProduct 1 1
      (state (clockWeight ε) (clock_memLp ε hε) (one (k 0)))
      (state neutralWeight neutral_memLp (one (k 1))) :=
  KFCausalJoinedModulatedWeights.state_join _ _ _ _ k

theorem output_relation (c a : ℝ) (k : Block 2) :
    coreOutput ε hε c a k =ᵐ[volume] fun x => (energy ε c a x:ℂ)*(input ε hε k) x := by
  rw [input_join]
  exact output_coe ε c a _ _ _ _ _ (clock_state ε hε (one (k 0)))
    (clockInverse_state ε hε (one (k 0))) (neutralSquare_state (one (k 1)))

theorem weighted_memLp (c a : ℝ) :
    MemLp (fun x => (energy ε c a x:ℂ)*weight ε x) 2 := by
  apply (Lp.memLp (coreOutput ε hε c a 0)).ae_eq
  filter_upwards [output_relation ε hε c a 0,
    state_coe (weight ε) (weight_memLp ε hε) 0] with x h1 h2
  change (input ε hε 0) x = _ at h2
  rw [h1,h2]
  simp [modulate]

theorem output_state (c a : ℝ) (k : Block 2) :
    coreOutput ε hε c a k =
      state (fun x => (energy ε c a x:ℂ)*weight ε x) (weighted_memLp ε hε c a) k := by
  apply Lp.ext
  filter_upwards [output_relation ε hε c a k,
    state_coe (weight ε) (weight_memLp ε hε) k,
    state_coe (fun x => (energy ε c a x:ℂ)*weight ε x) (weighted_memLp ε hε c a) k]
      with x h1 h2 h3
  change (input ε hε k) x = _ at h2
  rw [h1,h2,h3]
  unfold modulate
  ring

theorem graph_core (c a : ℝ) :
    (Submodule.span ℂ (Set.range (fun k => (input ε hε k,coreOutput ε hε c a k)))).topologicalClosure =
      KFCausalMultiplierGraphCoordinates.graph (energy ε c a)
        (KFCausalSpectatorEnergyPackets.energy_continuous ε hε c a).measurable := by
  have hn (x : Block 2) : weight ε x ≠ 0 :=
    mul_ne_zero (clock_nonzero ε hε _) (neutral_nonzero _)
  have he := KFCausalModulatedGraphCore.graph_core (energy ε c a)
    (KFCausalSpectatorEnergyPackets.energy_continuous ε hε c a).measurable
    (weight ε) (weight_memLp ε hε) (weighted_memLp ε hε c a) hn
  have hp : (fun k => (input ε hε k,coreOutput ε hε c a k)) =
      KFCausalModulatedGraphCore.packet (energy ε c a) (weight ε)
        (weight_memLp ε hε) (weighted_memLp ε hε c a) := by
    funext k
    rw [output_state]
    rfl
  rw [hp]
  exact he

#print axioms weighted_memLp
#print axioms graph_core
end
end UnifiedTheory.Audit.KFCausalSpectatorEnergyCore
