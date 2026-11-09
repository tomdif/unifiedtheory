/- The exact finite width-squared sum is the negative charged jet.
This follows from differentiating the finite sum, not only its limit. -/
import UnifiedTheory.Audit.KFCausalClusteredWidthChargedJet

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalClusteredChargedJetIdentity
noncomputable section
open KFCausalClusteredWidthProfiles (widths coefficients)
open KFCausalClusteredWidthChargedJet (jet)

def widthSquareSum (n : ℕ) (δ : ℝ) (z : ℂ) : ℂ :=
  ∑ i, coefficients n δ i*(widths n δ i:ℂ)^2*Complex.exp (-(widths n δ i:ℂ)*z)

theorem widthSquareSum_eq (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (z : ℂ) :
    widthSquareSum n δ z = -jet n δ z := by
  have hd := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin (n+1))))
    (fun i _ => (((hasDerivAt_id z).const_mul (-(widths n δ i:ℂ))).cexp).const_mul
      (coefficients n δ i*(widths n δ i:ℂ)))
  have he := (KFCausalClusteredWidthChargedJet.laplaceSum_derivative n δ hδ z).unique hd
  calc
    widthSquareSum n δ z = -(∑ i, (coefficients n δ i*(widths n δ i:ℂ))*
      (Complex.exp (-(widths n δ i:ℂ)*z)*(-(widths n δ i:ℂ)*1))) := by
        rw [← Finset.sum_neg_distrib]
        unfold widthSquareSum
        exact Finset.sum_congr rfl (fun i _ => by ring)
    _ = -jet n δ z := congrArg Neg.neg he.symm

#print axioms widthSquareSum_eq
end
end UnifiedTheory.Audit.KFCausalClusteredChargedJetIdentity
