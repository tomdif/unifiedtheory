/- Exact zero-charge projected neutral polynomial and Hermite packets,
with the actual maximal pure-clock momentum graph. Energy-form
membership after projection still requires control of the factor orbit. -/
import UnifiedTheory.Audit.KFCausalUnboundedNeutralCharge
import UnifiedTheory.Audit.KFCausalPolynomialMomentumDomain
import UnifiedTheory.Audit.KFCausalNeutralHermiteDomain
import UnifiedTheory.Audit.KFCausalPureClockZeroProjection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalNeutralPolynomialProjection
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalPolynomialGaussianDomain (input input_coe)
open UnifiedTheory.Audit.KFCausalUnboundedNeutralCharge (relation relation_projection)
open UnifiedTheory.Audit.KFCausalStandingChargeOperator (zeroProjection)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedClockMomentum (state state_coe)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
  (neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalPolynomialMomentumDomain (momentum momentum_graph)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)

theorem weight_measurable (P : Polynomial ℂ) : Measurable (fun s : ℝ => P.eval (s:ℂ)) :=
  (P.continuous.comp Complex.continuous_ofReal).measurable

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => neutralWidth_positive h hh
local notation "hw" => neutralWidth_bound h
local notation "S" => state ε a α β hε ha hα hβ hw C p b

theorem input_relation (P : Polynomial ℂ) :
    relation (fun s : ℝ => P.eval (s:ℂ)) S (input ε a h hε ha hh C p b 4 P) := by
  filter_upwards [input_coe ε a h hε ha hh C p b 4 P,
    state_coe ε a α β hε ha hα hβ hw C p b] with x hp hs
  exact hp.trans (congrArg (fun z : ℂ => P.eval (x.2 4:ℂ)*z) hs.symm)

theorem projected_input_coe (P : Polynomial ℂ) :
    zeroProjection h hh (input ε a h hε ha hh C p b 4 P) =ᵐ[volume]
      fun x : Configuration => P.eval (x.2 4:ℂ)*zeroProjection h hh S x :=
  relation_projection _ (weight_measurable P) h hh S _
    (input_relation ε a h hε ha hh C p b P)

theorem projected_weight_memLp (P : Polynomial ℂ) :
    MemLp (fun x : Configuration => P.eval (x.2 4:ℂ)*zeroProjection h hh S x) 2 volume :=
  (Lp.memLp (zeroProjection h hh (input ε a h hε ha hh C p b 4 P))).ae_eq
    (projected_input_coe ε a h hε ha hh C p b P)

theorem projected_momentum_graph (P : Polynomial ℂ) :
    (zeroProjection h hh (input ε a h hε ha hh C p b 4 P),
      zeroProjection h hh (momentum ε a h hε ha hh p b 4 C P)) ∈
        (pureMomentum ε hε h).graph :=
  KFCausalPureClockZeroProjection.projected_graph ε hε h hh _ _
    (momentum_graph ε a h hε ha hh p b 4 C P)

theorem projected_momentum_domain (P : Polynomial ℂ) :
    zeroProjection h hh (input ε a h hε ha hh C p b 4 P) ∈ (pureMomentum ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph (projected_momentum_graph ε a h hε ha hh C p b P)

theorem projected_hermite_coe (B : ℝ) (n : ℕ) :
    zeroProjection h hh (KFCausalNeutralHermiteDomain.state ε a h hε ha hh C p b B n) =ᵐ[volume]
      fun x : Configuration =>
        ((KFCausalNeutralHermiteDomain.physicistsHermite n).eval
          ((Real.sqrt (2*β):ℂ)*((x.2 4:ℂ)-(B:ℂ)))/
            (Real.sqrt ((2:ℝ)^n*n.factorial):ℂ))*zeroProjection h hh S x := by
  filter_upwards [projected_input_coe ε a h hε ha hh C p b
    (KFCausalNeutralHermiteDomain.multiplier β B n)] with x hx
  exact hx.trans (congrArg (fun z : ℂ => z*zeroProjection h hh S x)
    (KFCausalNeutralHermiteDomain.multiplier_eval β B n (x.2 4:ℂ)))

#print axioms weight_measurable
#print axioms input_relation
#print axioms projected_input_coe
#print axioms projected_weight_memLp
#print axioms projected_momentum_graph
#print axioms projected_momentum_domain
#print axioms projected_hermite_coe
end
end UnifiedTheory.Audit.KFCausalNeutralPolynomialProjection
