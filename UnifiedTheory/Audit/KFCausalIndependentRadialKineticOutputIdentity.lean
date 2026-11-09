/- Original natural kinetic outputs have exact projected radial-moment
identities. Both inverse half-clock factors and the second neutral
polynomial derivative are retained. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialProjectedKinetic
import UnifiedTheory.Audit.KFCausalIndependentRadialMomentKinetic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalIndependentRadialKineticOutputIdentity
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalStandingChargeOperator (zeroProjection)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive groundWidth_matching)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive)
open KFCausalNormalizedChargeFlow (momentumScale)
open KFCausalIndependentRadialPackets (state state_charge_coe clock clock_continuous clock_memLp)
open KFCausalIndependentRadialPacketMoments (momentState)
open KFCausalIndependentRadialKineticRepresentatives
  (baseState base_coe secondState singleState antiFactor symmetric_square antisymmetric_square)
open KFCausalIndependentRadialProjectedKinetic
  (radialState averageSecond projected_symmetric projected_antisymmetric)
open KFCausalIndependentRadialPolynomialKinetic (kineticIndex kinetic_component)
open KFCausalIndependentRadialHamiltonian (componentOutput component_graph)
open KFCausalNaturalSecondHamiltonianGraph (component)
open KFCausalNeutralLinePackets (step)

variable (ε a h wL wR : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
  (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hL : 1 ≤ wL) (hR : 1 ≤ wR)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "c" => momentumScale h
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => neutralWidth_positive h hh
local notation "hl" => zero_lt_one.trans_le hL
local notation "hr" => zero_lt_one.trans_le hR
local notation "hm" => groundWidth_matching h hh
local notation "g" => clock ε a C p
local notation "hc" => clock_continuous ε a C p
local notation "hg" => clock_memLp ε a C p hε ha

theorem base_equals :
    baseState α β wL wR c hα hβ hl hr hm b P g hc hg=
      state ε a h wL wR C p b P hε ha hh hL hR := by
  apply chargeCoordinates.injective
  exact Lp.ext ((base_coe α β wL wR c hα hβ hl hr hm b P g hc hg).trans
    (state_charge_coe ε a h wL wR C p b P hε ha hh hL hR).symm)

def rawOutput (i : Fin 4) : Hilbert :=
  ![(-(h:ℂ)^2) • secondState α β wL wR c hα hβ hl hr hm b P g hc hg 0,
    (-(h:ℂ)^2) • secondState α β wL wR c hα hβ hl hr hm b P g hc hg 1,
    (antiFactor h c)^2 • singleState α β wL wR c hα hβ hl hr hm b P g hc hg 0 2,
    (antiFactor h c)^2 • singleState α β wL wR c hα hβ hl hr hm b P g hc hg 1 2] i

def kineticCombination (i : Fin 4) : Hilbert :=
  ![(4*(h:ℂ)^2*(α:ℂ)*(1/wL:ℝ)) • state ε a h wL wR C p b P hε ha hh hL hR+
      (-4*(h:ℂ)^2*((α:ℂ)*(1/wL:ℝ))^2) • momentState ε a h wL wR C p b P hε ha hh hL hR 1 0,
    (4*(h:ℂ)^2*(α:ℂ)*(wR:ℂ)) • state ε a h wL wR C p b P hε ha hh hL hR+
      (-4*(h:ℂ)^2*((α:ℂ)*(wR:ℂ))^2) • momentState ε a h wL wR C p b P hε ha hh hL hR 0 1+
      (-(h:ℂ)^2) • state ε a h wL wR C p b (step β b (step β b P)) hε ha hh hL hR,
    momentState ε a h wL wR C p b P hε ha hh hL hR 1 0,
    momentState ε a h wL wR C p b P hε ha hh hL hR 0 1] i

theorem raw_graph (i : Fin 4) :
    (state ε a h wL wR C p b P hε ha hh hL hR,
      inverseL ε hε (inverseL ε hε (rawOutput ε a h wL wR C p b P hε ha hh hL hR i))) ∈
        (component ε hε h (kineticIndex i)).graph := by
  rw [kinetic_component]
  have h0 := symmetric_square α β wL wR c hα hβ hl hr hm b P g hc hg ε hε h hh 0
  have h1 := symmetric_square α β wL wR c hα hβ hl hr hm b P g hc hg ε hε h hh 1
  have h2 := antisymmetric_square α β wL wR c hα hβ hl hr hm b P g hc hg ε hε h hh 0
  have h3 := antisymmetric_square α β wL wR c hα hβ hl hr hm b P g hc hg ε hε h hh 1
  rw [base_equals] at h0 h1 h2 h3
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem projected_raw (i : Fin 4) :
    zeroProjection h hh (inverseL ε hε (inverseL ε hε (rawOutput ε a h wL wR C p b P hε ha hh hL hR i)))=
      inverseL ε hε (inverseL ε hε (kineticCombination ε a h wL wR C p b P hε ha hh hL hR i)) := by
  fin_cases i
  · have he := projected_symmetric α β wL wR h hα hβ hl hr hh hm b P g hc hg ε hε 0
    change zeroProjection h hh (inverseL ε hε (inverseL ε hε ((-(h:ℂ)^2) •
      secondState α β wL wR c hα hβ hl hr hm b P g hc hg 0)))=_
    rw [he]
    congr 2
    change (-(h:ℂ)^2) •
      ((-4*(α:ℂ)*(1/wL:ℝ)) • baseState α β wL wR c hα hβ hl hr hm b P g hc hg+
        (4*((α:ℂ)*(1/wL:ℝ))^2) • momentState ε a h wL wR C p b P hε ha hh hL hR 1 0+
        (0:ℂ) • baseState α β wL wR c hα hβ hl hr hm b (step β b (step β b P)) g hc hg)=
      (4*(h:ℂ)^2*(α:ℂ)*(1/wL:ℝ)) • state ε a h wL wR C p b P hε ha hh hL hR+
        (-4*(h:ℂ)^2*((α:ℂ)*(1/wL:ℝ))^2) • momentState ε a h wL wR C p b P hε ha hh hL hR 1 0
    rw [base_equals ε a h wL wR C p b P hε ha hh hL hR]
    simp only [zero_smul,add_zero,smul_add,smul_smul]
    module
  · have he := projected_symmetric α β wL wR h hα hβ hl hr hh hm b P g hc hg ε hε 1
    change zeroProjection h hh (inverseL ε hε (inverseL ε hε ((-(h:ℂ)^2) •
      secondState α β wL wR c hα hβ hl hr hm b P g hc hg 1)))=_
    rw [he]
    congr 2
    change (-(h:ℂ)^2) •
      ((-4*(α:ℂ)*(wR:ℂ)) • baseState α β wL wR c hα hβ hl hr hm b P g hc hg+
        (4*((α:ℂ)*(wR:ℂ))^2) • momentState ε a h wL wR C p b P hε ha hh hL hR 0 1+
        (1:ℂ) • baseState α β wL wR c hα hβ hl hr hm b (step β b (step β b P)) g hc hg)=
      (4*(h:ℂ)^2*(α:ℂ)*(wR:ℂ)) • state ε a h wL wR C p b P hε ha hh hL hR+
        (-4*(h:ℂ)^2*((α:ℂ)*(wR:ℂ))^2) • momentState ε a h wL wR C p b P hε ha hh hL hR 0 1+
        (-(h:ℂ)^2) • state ε a h wL wR C p b (step β b (step β b P)) hε ha hh hL hR
    rw [base_equals ε a h wL wR C p b P hε ha hh hL hR,
      base_equals ε a h wL wR C p b (step β b (step β b P)) hε ha hh hL hR]
    simp only [one_smul,smul_add,smul_smul]
    module
  · exact projected_antisymmetric α β wL wR h hα hβ hl hr hh hm b P g hc hg ε hε 0
  · exact projected_antisymmetric α β wL wR h hα hβ hl hr hh hm b P g hc hg ε hε 1

theorem projected_component_output (hb : |h| ≤ Real.pi*ε/3) (i : Fin 4) :
    zeroProjection h hh (componentOutput ε a h wL wR C p b P hε ha hh hR hb (kineticIndex i))=
      inverseL ε hε (inverseL ε hε (kineticCombination ε a h wL wR C p b P hε ha hh hL hR i)) := by
  have he := (component ε hε h (kineticIndex i)).mem_graph_snd_inj'
    (component_graph ε a h wL wR C p b P hε ha hh hL hR hb (kineticIndex i))
    (raw_graph ε a h wL wR C p b P hε ha hh hL hR i) rfl
  dsimp only at he
  rw [he]
  exact projected_raw ε a h wL wR C p b P hε ha hh hL hR i

#print axioms base_equals
#print axioms raw_graph
#print axioms projected_raw
#print axioms projected_component_output
end
end UnifiedTheory.Audit.KFCausalIndependentRadialKineticOutputIdentity
