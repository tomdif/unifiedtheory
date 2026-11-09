/- The bounded inverse half-clock preserves the independent L2 clock
coefficients. Its actual maximal multiplier graph passes to the limit. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredClockVectors
import UnifiedTheory.Audit.KFCausalClockFloorClockHalf

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredInverseHalfLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredClockVectors
open KFCausalClockFloorClockHalf

variable {m : ℕ} (ε : ℝ) (c : ℝ → Fin m → ℂ)

def damped (s : ℝ) (i : Fin m) : ℂ := (Real.sqrt (Real.exp s+ε):ℂ)⁻¹*c s i

theorem damped_continuous (hε : 0 < ε) (hc : ∀ i, Continuous (fun s => c s i)) (i : Fin m) :
    Continuous (fun s => damped ε c s i) := by
  have hn (s : ℝ) : (Real.sqrt (Real.exp s+ε):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  exact (Continuous.inv₀ (by fun_prop) hn).mul (hc i)

theorem damped_memLp (hε : 0 < ε) (hc : ∀ i, Continuous (fun s => c s i))
    (hc2 : ∀ i, MemLp (fun s => c s i) 2 volume) (i : Fin m) :
    MemLp (fun s => damped ε c s i) 2 volume := by
  apply ((hc2 i).const_mul (((Real.sqrt ε)⁻¹:ℝ):ℂ)).of_le
    (damped_continuous ε c hε hc i).aestronglyMeasurable
  filter_upwards [] with s
  simp only [damped,← Complex.ofReal_inv,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  exact mul_le_mul_of_nonneg_right (inverseWeight_bound ε hε (s,0)) (norm_nonneg _)

variable (f : Family m) (α β : ℝ)

theorem profile_damped (δ : ℝ) (x : Configuration) :
    profile f (damped ε c) α β δ x = (inverseWeight ε x:ℂ)*profile f c α β δ x := by
  rw [profile_sum,profile_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [damped,inverseWeight,halfWeight,Complex.ofReal_inv]
  ring

variable (hε : 0 < ε) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
  (hc : ∀ i, Continuous (fun s => c s i)) (hc2 : ∀ i, MemLp (fun s => c s i) 2 volume)

local notation "dc" => damped_continuous ε c hε hc
local notation "dc2" => damped_memLp ε c hε hc hc2

theorem finite_graph (δ : ℝ) (hδ : 0 < δ) :
    (vector f c α β hα hβ hw hc2 δ,vector f (damped ε c) α β hα hβ hw dc2 δ) ∈
      (inverseClockHalf ε).graph := by
  rw [inverseClockHalf_graph]
  filter_upwards [vector_coe f c α β hα hβ hw hc2 δ hδ,
    vector_coe f (damped ε c) α β hα hβ hw dc2 δ hδ] with x hx hd
  rw [hd,hx,profile_damped]

theorem limiting_graph :
    (limitingVector f c α β hα hβ hw hc2 hc,limitingVector f (damped ε c) α β hα hβ hw dc2 dc) ∈
      (inverseClockHalf ε).graph := by
  apply (inverseClockHalf_selfAdjoint ε).isClosed.mem_of_tendsto
    ((vector_tendsto f c α β hα hβ hw hc2 hc).prodMk_nhds
      (vector_tendsto f (damped ε c) α β hα hβ hw dc2 dc))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact finite_graph ε c f α β hε hα hβ hw hc hc2 δ hδ

theorem inverseAction_eq : inverseAction ε hε (limitingVector f c α β hα hβ hw hc2 hc) =
    limitingVector f (damped ε c) α β hα hβ hw dc2 dc :=
  (inverseClockHalf ε).mem_graph_snd_inj'
    ((inverseClockHalf ε).mem_graph ⟨_,inverseClockHalf_domain ε hε _⟩)
    (limiting_graph ε c f α β hε hα hβ hw hc hc2) rfl

#print axioms damped_continuous
#print axioms damped_memLp
#print axioms profile_damped
#print axioms finite_graph
#print axioms limiting_graph
#print axioms inverseAction_eq
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredInverseHalfLimit
