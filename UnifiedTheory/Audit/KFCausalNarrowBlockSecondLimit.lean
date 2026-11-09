/- Strong L2 limits for all four complete second-derivative blocks,
including the broad/neutral cross term and second neutral derivative. -/
import UnifiedTheory.Audit.KFCausalClusteredPacketSecondCoordinates
import UnifiedTheory.Audit.KFCausalNarrowFourierQuadraticWeights
import UnifiedTheory.Audit.KFCausalNarrowBlockDerivativeLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000

namespace UnifiedTheory.Audit.KFCausalNarrowBlockSecondLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalEuclideanProductCoordinates (Block ProductHilbert)
open KFCausalPairedModeCoordinates (scale)
open KFCausalNarrowFourierChargedBounds (charged slope)
open KFCausalNarrowFourierWeightedLimit
open KFCausalNarrowFourierSecondJetLimit (secondSlope secondVector secondVector_coe secondVector_tendsto)
open KFCausalNarrowFourierQuadraticWeights
open KFCausalClusteredPacketSecondCoordinates (blockSecond)
open KFCausalNarrowBlockDerivativeLimit (rightVector rightVector_coe rightVector_exists_limit neutralVector neutralVector_coe neutralVector_exists_limit)
open KFCausalNeutralLinePackets (step)

variable (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
  (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume) (n : ℕ)

def leftSquareVector (i : Fin 2) (δ : ℝ) : ProductHilbert 2 4 :=
  chargedVector α β hα hβ b P g hc hg (fun z => (z.1 i:ℂ)^2) (by fun_prop)
    (1/(Real.pi^2/α)) (by positivity) (fun z => left_square_bound α hα z i) n δ

def rightSquareVector (i : Fin 2) (δ : ℝ) : ProductHilbert 2 4 :=
  secondVector α β hα hβ b P g hc hg (fun z => (z.2 i.castSucc.succ:ℂ)^2) (by fun_prop)
    (1/α) (by positivity) (fun z => right_square_bound α hα z i) n δ

def plainSlopeVector (δ : ℝ) : ProductHilbert 2 4 :=
  slopeVector α β hα hβ b P g hc hg (fun _ => 1) continuous_const 1 zero_le_one (one_bound α hα) n δ

def components (δ : ℝ) : Fin 7 → ProductHilbert 2 4 :=
  ![leftSquareVector α β hα hβ b P g hc hg n 0 δ,leftSquareVector α β hα hβ b P g hc hg n 1 δ,
    plainSlopeVector α β hα hβ b P g hc hg n δ,
    rightSquareVector α β hα hβ b P g hc hg n 0 δ,rightSquareVector α β hα hβ b P g hc hg n 1 δ,
    rightVector α β hα hβ b (step β b P) g hc hg n 1 δ,
    neutralVector α β hα hβ b (step β b P) g hc hg n δ]

def componentProfiles (δ : ℝ) : Fin 7 → Block 2 × Block 4 → ℂ :=
  ![(fun z => (z.1 0:ℂ)^2*charged n δ α β b P g z),
    (fun z => (z.1 1:ℂ)^2*charged n δ α β b P g z),
    slope n δ α β b P g,
    (fun z => (z.2 1:ℂ)^2*secondSlope n δ α β b P g z),
    (fun z => (z.2 2:ℂ)^2*secondSlope n δ α β b P g z),
    (fun z => (z.2 2:ℂ)*slope n δ α β b (step β b P) g z),
    charged n δ α β b (step β b (step β b P)) g]

theorem components_coe (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (k : Fin 7) :
    components α β hα hβ b P g hc hg n δ k =ᵐ[volume] componentProfiles α β b P g n δ k := by
  fin_cases k
  · exact chargedVector_coe α β hα hβ b P g hc hg (fun z => (z.1 0:ℂ)^2) (by fun_prop)
      (1/(Real.pi^2/α)) (by positivity) (fun z => left_square_bound α hα z 0) n δ hδ
  · exact chargedVector_coe α β hα hβ b P g hc hg (fun z => (z.1 1:ℂ)^2) (by fun_prop)
      (1/(Real.pi^2/α)) (by positivity) (fun z => left_square_bound α hα z 1) n δ hδ
  · simpa only [one_mul] using slopeVector_coe α β hα hβ b P g hc hg (fun _ => 1) continuous_const
      1 zero_le_one (one_bound α hα) n δ hδ
  · exact secondVector_coe α β hα hβ b P g hc hg (fun z => (z.2 1:ℂ)^2) (by fun_prop)
      (1/α) (by positivity) (fun z => right_square_bound α hα z 0) n δ hδ hδ1
  · exact secondVector_coe α β hα hβ b P g hc hg (fun z => (z.2 2:ℂ)^2) (by fun_prop)
      (1/α) (by positivity) (fun z => right_square_bound α hα z 1) n δ hδ hδ1
  · exact rightVector_coe α β hα hβ b (step β b P) g hc hg n 1 δ hδ
  · exact neutralVector_coe α β hα hβ b (step β b P) g hc hg n δ hδ

theorem components_exists_limit (k : Fin 7) : ∃ v : ProductHilbert 2 4,
    Tendsto (fun δ => components α β hα hβ b P g hc hg n δ k) (𝓝[>] 0) (𝓝 v) := by
  fin_cases k
  · exact ⟨_,chargedVector_tendsto α β hα hβ b P g hc hg (fun z => (z.1 0:ℂ)^2) (by fun_prop)
      (1/(Real.pi^2/α)) (by positivity) (fun z => left_square_bound α hα z 0) n⟩
  · exact ⟨_,chargedVector_tendsto α β hα hβ b P g hc hg (fun z => (z.1 1:ℂ)^2) (by fun_prop)
      (1/(Real.pi^2/α)) (by positivity) (fun z => left_square_bound α hα z 1) n⟩
  · exact ⟨_,slopeVector_tendsto α β hα hβ b P g hc hg (fun _ => 1) continuous_const
      1 zero_le_one (one_bound α hα) n⟩
  · exact ⟨_,secondVector_tendsto α β hα hβ b P g hc hg (fun z => (z.2 1:ℂ)^2) (by fun_prop)
      (1/α) (by positivity) (fun z => right_square_bound α hα z 0) n⟩
  · exact ⟨_,secondVector_tendsto α β hα hβ b P g hc hg (fun z => (z.2 2:ℂ)^2) (by fun_prop)
      (1/α) (by positivity) (fun z => right_square_bound α hα z 1) n⟩
  · exact rightVector_exists_limit α β hα hβ b (step β b P) g hc hg n 1
  · exact neutralVector_exists_limit α β hα hβ b (step β b P) g hc hg n

def blockCoefficients (j : Fin 4) : Fin 7 → ℂ :=
  ![![-8*(Real.pi:ℂ)^2*(Real.pi/α:ℝ),0,0,0,0,0,0],
    ![0,0,4*(α:ℂ)*(Real.pi/α:ℝ),0,8*(α:ℂ)^2*(Real.pi/α:ℝ),8*(scale:ℂ)*α*(Real.pi/α:ℝ),(Real.pi/α:ℝ)],
    ![0,0,4*(α:ℂ)*(Real.pi/α:ℝ),8*(α:ℂ)^2*(Real.pi/α:ℝ),0,0,0],
    ![0,-8*(Real.pi:ℂ)^2*(Real.pi/α:ℝ),0,0,0,0,0]] j

def blockVector (j : Fin 4) (δ : ℝ) : ProductHilbert 2 4 :=
  ∑ k, blockCoefficients α j k • components α β hα hβ b P g hc hg n δ k

theorem blockVector_coe (j : Fin 4) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    blockVector α β hα hβ b P g hc hg n j δ =ᵐ[volume] blockSecond n δ α β b P g j := by
  filter_upwards [KFCausalFiniteLpRepresentatives.weighted_sum_coe volume (blockCoefficients α j)
    (components α β hα hβ b P g hc hg n δ) (componentProfiles α β b P g n δ)
    (components_coe α β hα hβ b P g hc hg n δ hδ hδ1)] with z hz
  rw [blockVector,hz]
  fin_cases j <;> simp [blockCoefficients,componentProfiles,blockSecond,Fin.sum_univ_succ,mul_assoc,add_assoc]

theorem blockVector_exists_limit (j : Fin 4) : ∃ v : ProductHilbert 2 4,
    Tendsto (blockVector α β hα hβ b P g hc hg n j) (𝓝[>] 0) (𝓝 v) := by
  choose v hv using components_exists_limit α β hα hβ b P g hc hg n
  exact ⟨_,tendsto_finset_sum Finset.univ (fun k _ => (hv k).const_smul (blockCoefficients α j k))⟩

#print axioms components_coe
#print axioms components_exists_limit
#print axioms blockVector_coe
#print axioms blockVector_exists_limit
end
end UnifiedTheory.Audit.KFCausalNarrowBlockSecondLimit
