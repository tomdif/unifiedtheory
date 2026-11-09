/- Actual second matter actions for the reciprocal neutral exponential-polynomial state.
Both reverse graphs are constructed; they are not domain premises. -/
import UnifiedTheory.Audit.KFCausalPolynomialMatterSquare
import UnifiedTheory.Audit.KFCausalReciprocalSqueezeMatterSquare
import UnifiedTheory.Audit.KFCausalReciprocalNeutralPackets
import UnifiedTheory.Audit.KFCausalEnergyReverseFactors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralMatterSquare
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalReciprocalSqueezeTransport (transport)
open KFCausalReciprocalGaussianDomain
open KFCausalReciprocalNeutralPackets (output_graph rescaledPolynomial)
open KFCausalNeutralExponentialProfiles (neutralSource)
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
  (hb : |h| ≤ Real.pi*ε/3) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
local notation "t" => Real.log w/2
local notation "ht" => div_nonneg (Real.log_nonneg hw) (by norm_num : (0:ℝ) ≤ 2)
local notation "α" => groundWidth h
local notation "β" => baseWidth h t
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => baseWidth_positive h hh t
local notation "hbw" => baseWidth_bound h hh t ht
local notation "ψ" => KFCausalReciprocalNeutralPackets.state ε a h w hε ha hh hw C p b P
local notation "d" => neutralSource ((Real.exp (-t):ℂ)*b)
local notation "Q" => rescaledPolynomial t P
local notation "c" => (Real.exp (-t/2):ℂ)
local notation "hb₀" => original_strip ε h hε hb

def linearOutput : Hilbert := c •
  (((Real.exp (-t):ℂ)*(Real.exp (-t):ℂ)) • transport (-t)
    (KFCausalPolynomialMatterSquare.second ε a α β hε ha hα hβ hbw h hb C p d 4 Q 0))

def quadraticOutput : Hilbert := c •
  (((Real.exp (2*(-t)):ℂ)*(Real.exp (2*(-t)):ℂ)) • transport (-t)
    (KFCausalPolynomialMatterSquare.second ε a α β hε ha hα hβ hbw h hb C p d 4 Q 1))

theorem linear_square_graph : (ψ,linearOutput ε a h w hε ha hh hw hb C p b P) ∈
    (composition (reversedMatterFactor ε hε h (physicalField pointField))
      (matterFactor ε hε h (physicalField pointField))).graph := by
  exact (composition (reversedMatterFactor ε hε h (physicalField pointField))
    (matterFactor ε hε h (physicalField pointField))).graph.smul_mem c
      (KFCausalReciprocalSqueezeMatterSquare.linear_square_graph ε hε h (-t) _ _
        (KFCausalPolynomialMatterSquare.linear_square_graph ε a α β hε ha hα hβ hbw h hb C p d 4 Q))

theorem quadratic_square_graph : (ψ,quadraticOutput ε a h w hε ha hh hw hb C p b P) ∈
    (composition (reversedMatterFactor ε hε h (fieldSquare pointField))
      (matterFactor ε hε h (fieldSquare pointField))).graph := by
  exact (composition (reversedMatterFactor ε hε h (fieldSquare pointField))
    (matterFactor ε hε h (fieldSquare pointField))).graph.smul_mem c
      (KFCausalReciprocalSqueezeMatterSquare.quadratic_square_graph ε hε h (-t) _ _
        (KFCausalPolynomialMatterSquare.quadratic_square_graph ε a α β hε ha hα hβ hbw h hb C p d 4 Q))

theorem linear_reverse_graph :
    (KFCausalReciprocalNeutralPackets.output ε a h w hε ha hh hw C p b P hb₀ 5,
      linearOutput ε a h w hε ha hh hw hb C p b P) ∈
        (reverseFactor ε hε h modelDirections pointField 5).graph :=
  reverse_of_composition _ _ _ _ _ (output_graph ε a h w hε ha hh hw C p b P hb₀ 5)
    (linear_square_graph ε a h w hε ha hh hw hb C p b P)

theorem quadratic_reverse_graph :
    (KFCausalReciprocalNeutralPackets.output ε a h w hε ha hh hw C p b P hb₀ 6,
      quadraticOutput ε a h w hε ha hh hw hb C p b P) ∈
        (reverseFactor ε hε h modelDirections pointField 6).graph :=
  reverse_of_composition _ _ _ _ _ (output_graph ε a h w hε ha hh hw C p b P hb₀ 6)
    (quadratic_square_graph ε a h w hε ha hh hw hb C p b P)

#print axioms linear_square_graph
#print axioms quadratic_square_graph
#print axioms linear_reverse_graph
#print axioms quadratic_reverse_graph
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralMatterSquare
