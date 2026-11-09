/- Strong limits for every transformed clustered block derivative,
including the broad-coordinate and neutral pieces of direction one. -/
import UnifiedTheory.Audit.KFCausalClusteredPacketDerivativeCoordinates
import UnifiedTheory.Audit.KFCausalNarrowFourierWeightedLimit
import UnifiedTheory.Audit.KFCausalNarrowFourierModelDirections

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalNarrowBlockDerivativeLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalEuclideanProductCoordinates (Block ProductHilbert)
open KFCausalPairedModeCoordinates (scale)
open KFCausalNarrowFourierPackets (chargedRadius)
open KFCausalNarrowFourierChargedBounds (charged slope)
open KFCausalNarrowFourierWeightedLimit
open KFCausalNarrowFourierModelDirections (left_coordinate_bound right_coordinate_bound)
open KFCausalClusteredPacketDerivativeCoordinates (blockDifferential)
open KFCausalNeutralLinePackets (step)

variable (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
  (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume) (n : ℕ)

def leftVector (i : Fin 2) (δ : ℝ) : ProductHilbert 2 4 :=
  chargedVector α β hα hβ b P g hc hg (fun z => (z.1 i:ℂ)) (by fun_prop)
    (1+1/(Real.pi^2/α)) (by positivity) (fun z => left_coordinate_bound α hα z i) n δ

def rightVector (i : Fin 2) (δ : ℝ) : ProductHilbert 2 4 :=
  slopeVector α β hα hβ b P g hc hg (fun z => (z.2 i.castSucc.succ:ℂ)) (by fun_prop)
    (1+1/α) (by positivity) (fun z => right_coordinate_bound α hα z i) n δ

include hα in
private theorem one_bound (z : Block 2 × Block 4) : ‖(1:ℂ)‖ ≤ 1*(1+chargedRadius α z) := by
  have hz := KFCausalNarrowFourierPackets.chargedRadius_nonnegative α hα z
  simp only [norm_one,one_mul]
  linarith

def neutralVector (δ : ℝ) : ProductHilbert 2 4 :=
  chargedVector α β hα hβ b (step β b P) g hc hg (fun _ => 1) continuous_const
    1 zero_le_one (one_bound α hα) n δ

theorem leftVector_coe (i : Fin 2) (δ : ℝ) (hδ : 0 < δ) :
    leftVector α β hα hβ b P g hc hg n i δ =ᵐ[volume]
      fun z => (z.1 i:ℂ)*charged n δ α β b P g z :=
  chargedVector_coe α β hα hβ b P g hc hg (fun z => (z.1 i:ℂ)) (by fun_prop)
    (1+1/(Real.pi^2/α)) (by positivity) (fun z => left_coordinate_bound α hα z i) n δ hδ

theorem rightVector_coe (i : Fin 2) (δ : ℝ) (hδ : 0 < δ) :
    rightVector α β hα hβ b P g hc hg n i δ =ᵐ[volume]
      fun z => (z.2 i.castSucc.succ:ℂ)*slope n δ α β b P g z :=
  slopeVector_coe α β hα hβ b P g hc hg (fun z => (z.2 i.castSucc.succ:ℂ)) (by fun_prop)
    (1+1/α) (by positivity) (fun z => right_coordinate_bound α hα z i) n δ hδ

theorem neutralVector_coe (δ : ℝ) (hδ : 0 < δ) :
    neutralVector α β hα hβ b P g hc hg n δ =ᵐ[volume] charged n δ α β b (step β b P) g := by
  simpa only [one_mul] using chargedVector_coe α β hα hβ b (step β b P) g hc hg (fun _ => 1) continuous_const
    1 zero_le_one (one_bound α hα) n δ hδ

theorem leftVector_exists_limit (i : Fin 2) : ∃ v : ProductHilbert 2 4,
    Tendsto (leftVector α β hα hβ b P g hc hg n i) (𝓝[>] 0) (𝓝 v) :=
  ⟨_,chargedVector_tendsto α β hα hβ b P g hc hg (fun z => (z.1 i:ℂ)) (by fun_prop)
    (1+1/(Real.pi^2/α)) (by positivity) (fun z => left_coordinate_bound α hα z i) n⟩

theorem rightVector_exists_limit (i : Fin 2) : ∃ v : ProductHilbert 2 4,
    Tendsto (rightVector α β hα hβ b P g hc hg n i) (𝓝[>] 0) (𝓝 v) :=
  ⟨_,slopeVector_tendsto α β hα hβ b P g hc hg (fun z => (z.2 i.castSucc.succ:ℂ)) (by fun_prop)
    (1+1/α) (by positivity) (fun z => right_coordinate_bound α hα z i) n⟩

theorem neutralVector_exists_limit : ∃ v : ProductHilbert 2 4,
    Tendsto (neutralVector α β hα hβ b P g hc hg n) (𝓝[>] 0) (𝓝 v) :=
  ⟨_,chargedVector_tendsto α β hα hβ b (step β b P) g hc hg (fun _ => 1) continuous_const
    1 zero_le_one (one_bound α hα) n⟩

local notation "L" => leftVector α β hα hβ b P g hc hg n
local notation "R" => rightVector α β hα hβ b P g hc hg n
local notation "N" => neutralVector α β hα hβ b P g hc hg n
local notation "cL" => (4*(Real.pi:ℂ)*Complex.I*scale)*(Real.pi/α:ℝ)
local notation "cR" => (4*(scale:ℂ)*α)*(Real.pi/α:ℝ)

def blockVector (j : Fin 4) (δ : ℝ) : ProductHilbert 2 4 :=
  ![cL • L 0 δ,cR • R 1 δ+(Real.pi/α:ℝ) • N δ,cR • R 0 δ,cL • L 1 δ] j

theorem blockVector_coe (j : Fin 4) (δ : ℝ) (hδ : 0 < δ) :
    blockVector α β hα hβ b P g hc hg n j δ =ᵐ[volume] blockDifferential n δ α β b P g j := by
  have hL (i : Fin 2) : (cL • L i δ : ProductHilbert 2 4) =ᵐ[volume]
      fun z => cL*(z.1 i:ℂ)*charged n δ α β b P g z := by
    filter_upwards [Lp.coeFn_smul cL (L i δ),leftVector_coe α β hα hβ b P g hc hg n i δ hδ] with z hz hl
    rw [hz]
    simp only [Pi.smul_apply,smul_eq_mul,hl,mul_assoc]
  have hR (i : Fin 2) : (cR • R i δ : ProductHilbert 2 4) =ᵐ[volume]
      fun z => cR*(z.2 i.castSucc.succ:ℂ)*slope n δ α β b P g z := by
    filter_upwards [Lp.coeFn_smul cR (R i δ),rightVector_coe α β hα hβ b P g hc hg n i δ hδ] with z hz hr
    rw [hz]
    simp only [Pi.smul_apply,smul_eq_mul,hr,mul_assoc]
  have hA : (cR • R 1 δ+(Real.pi/α:ℝ) • N δ : ProductHilbert 2 4) =ᵐ[volume]
      fun z => cR*(z.2 2:ℂ)*slope n δ α β b P g z+(Real.pi/α:ℝ)*charged n δ α β b (step β b P) g z := by
    filter_upwards [Lp.coeFn_add (cR • R 1 δ) ((Real.pi/α:ℝ) • N δ),hR 1,
      Lp.coeFn_smul (Real.pi/α:ℝ) (N δ),neutralVector_coe α β hα hβ b P g hc hg n δ hδ] with z hz hr hn hn'
    simp only [hz,Pi.add_apply,hr,hn,Pi.smul_apply,Complex.real_smul,hn']
    rfl
  fin_cases j
  · exact hL 0
  · exact hA
  · exact hR 0
  · exact hL 1

theorem blockVector_exists_limit (j : Fin 4) : ∃ v : ProductHilbert 2 4,
    Tendsto (blockVector α β hα hβ b P g hc hg n j) (𝓝[>] 0) (𝓝 v) := by
  obtain ⟨l0,hl0⟩ := leftVector_exists_limit α β hα hβ b P g hc hg n 0
  obtain ⟨l1,hl1⟩ := leftVector_exists_limit α β hα hβ b P g hc hg n 1
  obtain ⟨r0,hr0⟩ := rightVector_exists_limit α β hα hβ b P g hc hg n 0
  obtain ⟨r1,hr1⟩ := rightVector_exists_limit α β hα hβ b P g hc hg n 1
  obtain ⟨nn,hn⟩ := neutralVector_exists_limit α β hα hβ b P g hc hg n
  fin_cases j
  · exact ⟨_,hl0.const_smul cL⟩
  · exact ⟨_,(hr1.const_smul cR).add (hn.const_smul (Real.pi/α:ℝ))⟩
  · exact ⟨_,hr0.const_smul cR⟩
  · exact ⟨_,hl1.const_smul cL⟩

#print axioms leftVector_coe
#print axioms rightVector_coe
#print axioms neutralVector_coe
#print axioms leftVector_exists_limit
#print axioms rightVector_exists_limit
#print axioms neutralVector_exists_limit
#print axioms blockVector_coe
#print axioms blockVector_exists_limit
end
end UnifiedTheory.Audit.KFCausalNarrowBlockDerivativeLimit
