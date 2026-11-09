/- Actual second matter actions for the reciprocal Gaussian clock momentum.
Both reverse graphs are constructed by analytic coefficient transport. -/
import UnifiedTheory.Audit.KFCausalGaussianMomentumMatterSquare
import UnifiedTheory.Audit.KFCausalReciprocalSqueezeMatterSquare
import UnifiedTheory.Audit.KFCausalReciprocalGaussianMomentum
import UnifiedTheory.Audit.KFCausalEnergyReverseFactors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalReciprocalGaussianMomentumMatterSquare
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalReciprocalSqueezeTransport (transport)
open KFCausalReciprocalGaussianDomain
open KFCausalReciprocalGaussianMomentum (momentumOutput_graph)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorTrialMatter (matterFactor)
open KFCausalClockFloorMatterClosure (reversedMatterFactor)
open KFCausalOrderedOperatorComposition (composition composition_graph)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalPhysicalField (physicalField)
open KFCausalTransverseFieldSquare (fieldSquare)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalGaussianVacuumSquare (original_strip)

private theorem reverse_of_composition (T R : Hilbert →ₗ.[ℂ] Hilbert) (f u z : Hilbert)
    (hfu : (f,u) ∈ T.graph) (hfz : (f,z) ∈ (composition R T).graph) : (u,z) ∈ R.graph := by
  obtain ⟨u',hu',hz⟩ := (composition_graph R T f z).mp hfz
  have he := T.mem_graph_snd_inj' hu' hfu rfl
  dsimp only at he
  rwa [he] at hz

variable (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hw : 1 ≤ w)
  (hb : |h| ≤ Real.pi*ε/3)
local notation "t" => Real.log w/2
local notation "ht" => div_nonneg (Real.log_nonneg hw) (by norm_num : (0:ℝ) ≤ 2)
local notation "α" => groundWidth h
local notation "β" => baseWidth h t
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => baseWidth_positive h hh t
local notation "hbw" => baseWidth_bound h hh t ht
local notation "ψ" => KFCausalReciprocalGaussianMomentum.momentum ε a h w hε ha hh hw
local notation "c" => (Real.exp (-t/2):ℂ)
local notation "hb₀" => original_strip ε h hε hb

def linearOutput : Hilbert := c •
  (((Real.exp (-t):ℂ)*(Real.exp (-t):ℂ)) • transport (-t)
    (KFCausalGaussianMomentumMatterSquare.output ε a α β hε ha hα hβ hbw h hb 0))

def quadraticOutput : Hilbert := c •
  (((Real.exp (2*(-t)):ℂ)*(Real.exp (2*(-t)):ℂ)) • transport (-t)
    (KFCausalGaussianMomentumMatterSquare.output ε a α β hε ha hα hβ hbw h hb 1))

theorem linear_square_graph : (ψ,linearOutput ε a h w hε ha hh hw hb) ∈
    (composition (reversedMatterFactor ε hε h (physicalField pointField))
      (matterFactor ε hε h (physicalField pointField))).graph := by
  exact (composition (reversedMatterFactor ε hε h (physicalField pointField))
    (matterFactor ε hε h (physicalField pointField))).graph.smul_mem c
      (KFCausalReciprocalSqueezeMatterSquare.linear_square_graph ε hε h (-t) _ _
        (KFCausalGaussianMomentumMatterSquare.linear_square_graph ε a α β hε ha hα hβ hbw h hb hh))

theorem quadratic_square_graph : (ψ,quadraticOutput ε a h w hε ha hh hw hb) ∈
    (composition (reversedMatterFactor ε hε h (fieldSquare pointField))
      (matterFactor ε hε h (fieldSquare pointField))).graph := by
  exact (composition (reversedMatterFactor ε hε h (fieldSquare pointField))
    (matterFactor ε hε h (fieldSquare pointField))).graph.smul_mem c
      (KFCausalReciprocalSqueezeMatterSquare.quadratic_square_graph ε hε h (-t) _ _
        (KFCausalGaussianMomentumMatterSquare.quadratic_square_graph ε a α β hε ha hα hβ hbw h hb hh))

theorem linear_reverse_graph :
    (KFCausalReciprocalGaussianMomentum.momentumOutput ε a h w hε ha hh hw hb₀ 5,
      linearOutput ε a h w hε ha hh hw hb) ∈
        (reverseFactor ε hε h modelDirections pointField 5).graph :=
  reverse_of_composition _ _ _ _ _ (momentumOutput_graph ε a h w hε ha hh hw hb₀ 5)
    (linear_square_graph ε a h w hε ha hh hw hb)

theorem quadratic_reverse_graph :
    (KFCausalReciprocalGaussianMomentum.momentumOutput ε a h w hε ha hh hw hb₀ 6,
      quadraticOutput ε a h w hε ha hh hw hb) ∈
        (reverseFactor ε hε h modelDirections pointField 6).graph :=
  reverse_of_composition _ _ _ _ _ (momentumOutput_graph ε a h w hε ha hh hw hb₀ 6)
    (quadratic_square_graph ε a h w hε ha hh hw hb)

#print axioms linear_square_graph
#print axioms quadratic_square_graph
#print axioms linear_reverse_graph
#print axioms quadratic_reverse_graph
end
end UnifiedTheory.Audit.KFCausalReciprocalGaussianMomentumMatterSquare
