/- The constructed trial family is nontrivial: every nonzero Schwartz
transverse packet yields a nonzero actual coupled Hilbert-space state. -/
import UnifiedTheory.Audit.KFCausalDampedProductDomain
import UnifiedTheory.Audit.KFCausalSchwartzTransversePacket

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalDampedProductNonzero
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalCoupledProductDomain
open UnifiedTheory.Audit.KFCausalCoupledFunctionEnergy
open UnifiedTheory.Audit.KFCausalDampedGaussianMomentum
open UnifiedTheory.Audit.KFCausalDampedGaussianTotality
open UnifiedTheory.Audit.KFCausalRegularizedGaussianTotality
open UnifiedTheory.Audit.KFCausalDampedProductDomain

theorem modulatedClock_nonzero (ε a p : ℝ) (hε : 0 ≤ ε) (ha : 0 < a) :
    (modulated_memLp ε a p hε ha).toLp (modulate p (realTrial ε a)) ≠ 0 := by
  intro hz
  have he : modulate p (realTrial ε a) = (fun _ => (0:ℂ)) :=
    ((modulate_continuous p _ (realTrial_continuous ε a)).ae_eq_iff_eq volume continuous_const).mp
      ((modulated_memLp ε a p hε ha).coeFn_toLp.symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp hz))
  have hn : ‖realTrial ε a 0‖ = 0 := by
    rw [← modulate_norm p (realTrial ε a) 0,congrFun he 0,norm_zero]
  exact realTrial_ne_zero ε a 0 (norm_eq_zero.mp hn)

theorem productState_nonzero (ε : ℝ) (hε : 0 < ε) (g : ℝ → ℂ) (ψ : TailSpace → ℂ)
    (hg : MemLp g 2) (hψ : MemLp ψ 2) (hgn : hg.toLp g ≠ 0) (hψn : hψ.toLp ψ ≠ 0) :
    productState ε hε g ψ hg hψ ≠ 0 := by
  have hn : 0 < ‖productState ε hε g ψ hg hψ‖^2 := by
    rw [productState_norm_square,← toLp_square_integral g hg,← toLp_square_integral ψ hψ]
    exact mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hgn)) (sq_pos_of_pos (norm_pos_iff.mpr hψn))
  intro hz
  simp only [hz,norm_zero,zero_pow (by decide : 2 ≠ 0),lt_self_iff_false] at hn

theorem trialState_nonzero (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : SchwartzMap TailSpace ℂ) (hψ : ψ ≠ 0) :
    trialState ε a p hε ha ψ (ψ.memLp 2 volume) ≠ 0 := by
  have hp : (ψ.memLp 2 volume).toLp ψ ≠ 0 := by
    intro hz
    apply hψ
    apply SchwartzMap.injective_toLp 2 volume
    change (ψ.memLp 2 volume).toLp ψ = (0 : SchwartzMap TailSpace ℂ).toLp 2 volume
    rw [hz]
    simp [SchwartzMap.toLp]
  exact productState_nonzero ε hε _ ψ (modulated_memLp ε a p hε.le ha) (ψ.memLp 2 volume)
    (modulatedClock_nonzero ε a p hε.le ha) hp

#print axioms modulatedClock_nonzero
#print axioms productState_nonzero
#print axioms trialState_nonzero

end
end UnifiedTheory.Audit.KFCausalDampedProductNonzero
