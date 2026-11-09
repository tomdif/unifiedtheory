/- Exact actions of the actual clock operators on the dressed states.
The inverse half-clock recovers the previously proved joint-domain trial. -/
import UnifiedTheory.Audit.KFCausalClockDressedProducts
import UnifiedTheory.Audit.KFCausalPhysicalClockPowers
import UnifiedTheory.Audit.KFCausalCoupledJointDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockDressedActions
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalClockTrialWeights
open UnifiedTheory.Audit.KFCausalDampedProductDomain
open UnifiedTheory.Audit.KFCausalClockDressedProducts
open UnifiedTheory.Audit.KFCausalPhysicalClockPowers
open UnifiedTheory.Audit.KFCausalCoupledJointDomain

theorem trial_to_dressed_graph (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : TailSpace → ℂ) (hψ : MemLp ψ 2) :
    (trialState ε a p hε ha ψ hψ,dressedState ε a p hε ha ψ hψ) ∈ (clockPower (1/2)).graph := by
  apply (clockPower_graph _ _ _).mpr
  filter_upwards [trialState_coe ε a p hε ha ψ hψ,
    clockProduct_coe ε a p (1/2) hε ψ (clockTrial_half_memLp ε a hε ha p) hψ] with z ht hd
  rw [show (dressedState ε a p hε ha ψ hψ) z=clockFunction ε a p (1/2) ψ z from hd,ht]
  rfl

theorem dressed_inverse_graph (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : TailSpace → ℂ) (hψ : MemLp ψ 2) :
    (dressedState ε a p hε ha ψ hψ,trialState ε a p hε ha ψ hψ) ∈ (clockPower (-(1/2))).graph :=
  (clockPower_inverse_graph _ _ _).mp (trial_to_dressed_graph ε a p hε ha ψ hψ)

theorem dressed_clock_graph (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : TailSpace → ℂ) (hψ : MemLp ψ 2) :
    (dressedState ε a p hε ha ψ hψ,clockEnergyState ε a p hε ha ψ hψ) ∈ (clockPower (1/2)).graph := by
  apply (clockPower_graph _ _ _).mpr
  filter_upwards [clockProduct_coe ε a p (1/2) hε ψ (clockTrial_half_memLp ε a hε ha p) hψ,
    clockProduct_coe ε a p 1 hε ψ (clockTrial_one_memLp ε a hε ha p) hψ] with z hd hc
  rw [show (clockEnergyState ε a p hε ha ψ hψ) z=clockFunction ε a p 1 ψ z from hc,
    show (dressedState ε a p hε ha ψ hψ) z=clockFunction ε a p (1/2) ψ z from hd]
  simp only [clockFunction]
  rw [← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
  rw [show (1/2:ℝ)*z.1+(1/2:ℝ)*z.1=1*z.1 by ring]

theorem dressed_inverse_domain (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : TailSpace → ℂ) (hψ : MemLp ψ 2) :
    dressedState ε a p hε ha ψ hψ ∈ (clockPower (-(1/2))).domain :=
  LinearPMap.mem_domain_of_mem_graph (dressed_inverse_graph ε a p hε ha ψ hψ)

theorem dressed_clock_domain (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : TailSpace → ℂ) (hψ : MemLp ψ 2) :
    dressedState ε a p hε ha ψ hψ ∈ (clockPower (1/2)).domain :=
  LinearPMap.mem_domain_of_mem_graph (dressed_clock_graph ε a p hε ha ψ hψ)

theorem inverseHalf_dressed (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : TailSpace → ℂ) (hψ : MemLp ψ 2) :
    clockPower (-(1/2)) ⟨dressedState ε a p hε ha ψ hψ,dressed_inverse_domain ε a p hε ha ψ hψ⟩ =
      trialState ε a p hε ha ψ hψ :=
  (clockPower (-(1/2))).mem_graph_snd_inj ((clockPower (-(1/2))).mem_graph _)
    (dressed_inverse_graph ε a p hε ha ψ hψ) rfl

theorem halfClock_dressed (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : TailSpace → ℂ) (hψ : MemLp ψ 2) :
    clockPower (1/2) ⟨dressedState ε a p hε ha ψ hψ,dressed_clock_domain ε a p hε ha ψ hψ⟩ =
      clockEnergyState ε a p hε ha ψ hψ :=
  (clockPower (1/2)).mem_graph_snd_inj ((clockPower (1/2)).mem_graph _)
    (dressed_clock_graph ε a p hε ha ψ hψ) rfl

theorem inverseHalf_joint (ε a p hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : |hbar| < Real.pi*ε) (ψ : SchwartzMap TailSpace ℂ) :
    clockPower (-(1/2))
      ⟨dressedState ε a p hε ha ψ (ψ.memLp 2 volume),dressed_inverse_domain ε a p hε ha ψ (ψ.memLp 2 volume)⟩
      ∈ jointSpace ε hε hbar := by
  rw [inverseHalf_dressed]
  exact trialFamily_mem_jointSpace ε a hbar hε ha hh (p,ψ)

#print axioms trial_to_dressed_graph
#print axioms dressed_inverse_graph
#print axioms dressed_clock_graph
#print axioms dressed_inverse_domain
#print axioms dressed_clock_domain
#print axioms inverseHalf_dressed
#print axioms halfClock_dressed
#print axioms inverseHalf_joint

end
end UnifiedTheory.Audit.KFCausalClockDressedActions
