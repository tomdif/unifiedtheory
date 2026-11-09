/- The existing second energy outputs of every finite neutral polynomial
belong to the actual pure-clock domain. The source-circle graph outputs
are derived before taking coefficients and finite sums. -/
import UnifiedTheory.Audit.KFCausalCoherentSecondPureDomains
import UnifiedTheory.Audit.KFCausalPolynomialSecondFactors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalPolynomialSecondPureDomain
noncomputable section
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalPolynomialSecondFactors (powerSecond second)
open KFCausalPolynomialGaussianStates
  (circleSource sourceBound circleSource_continuous circleSource_bound)
open KFCausalSourceCircleCoefficients (weight weight_continuous weight_norm normalization)

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi*ε/3)
  (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) (i : Fin 5)
include hh

theorem power_domain (n : ℕ) (j : Fin 8) :
    powerSecond ε a α β hε ha hα hβ hw h hb C p b i n j ∈ (pureMomentum ε hε h).domain :=
  (pureMomentum ε hε h).domain.smul_mem (C*normalization n)
    (KFCausalCoherentSecondPureDomains.meanSecond_domain ε a α β hε ha hα hβ hw h hh hb p
      (sourceBound b) (weight n) (circleSource b i) (weight_continuous n) (circleSource_continuous b i)
      (fun θ => (weight_norm n θ).le) (circleSource_bound b i) j)

theorem second_domain (P : Polynomial ℂ) (j : Fin 8) :
    second ε a α β hε ha hα hβ hw h hb C p b i P j ∈ (pureMomentum ε hε h).domain :=
  (pureMomentum ε hε h).domain.sum_mem (fun n (_ : n ∈ P.support) =>
    (pureMomentum ε hε h).domain.smul_mem (P.coeff n)
      (power_domain ε a α β hε ha hα hβ hw h hh hb C p b i n j))

#print axioms power_domain
#print axioms second_domain
end
end UnifiedTheory.Audit.KFCausalPolynomialSecondPureDomain
