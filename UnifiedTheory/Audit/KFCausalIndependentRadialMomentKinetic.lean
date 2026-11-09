/- The two actual degree-one radial moment states lie in the invariant
charged polynomial space. Their four natural kinetic second graphs
follow from two constructed primitive momentum steps. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialPolynomialKinetic
import UnifiedTheory.Audit.KFCausalIndependentRadialPacketMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalIndependentRadialMomentKinetic
noncomputable section
open MeasureTheory
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalIndependentRadialPolynomialMomentum (state space state_mem state_charge_coe)
open KFCausalIndependentRadialPacketMoments (genericMomentState generic_charge_coe momentState)
open KFCausalIndependentRadialCoordinateMoments (coordinate monomial profile)
open KFCausalIndependentRadialPacketDerivatives (momentProfile leftRadius rightRadius)
open KFCausalIndependentRadialPolynomialKinetic (kineticIndex kinetic_graph_exists)
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalNaturalSecondHamiltonianGraph (component)

def squareExponent (j : Fin 4) : Fin 4 → ℕ := Function.update 0 j 2

variable (α β wL wR c : ℝ) (hα : 0 < α) (hβ : 0 < β) (hL : 0 < wL) (hR : 0 < wR)
  (hmatch : Real.pi^2/α=α*c^2) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume)

theorem left_state_eq :
    genericMomentState α β wL wR c hα hβ hL hR hmatch b P g hc hg 1 0=
      state α β wL wR c hα hβ hL hR hmatch b g hc hg P (squareExponent 0)+
      state α β wL wR c hα hβ hL hR hmatch b g hc hg P (squareExponent 2) := by
  apply chargeCoordinates.injective
  rw [map_add]
  apply Lp.ext
  filter_upwards [generic_charge_coe α β wL wR c hα hβ hL hR hmatch b P g hc hg 1 0,
    Lp.coeFn_add (chargeCoordinates (state α β wL wR c hα hβ hL hR hmatch b g hc hg P (squareExponent 0)))
      (chargeCoordinates (state α β wL wR c hα hβ hL hR hmatch b g hc hg P (squareExponent 2))),
    state_charge_coe α β wL wR c hα hβ hL hR hmatch b g hc hg P (squareExponent 0),
    state_charge_coe α β wL wR c hα hβ hL hR hmatch b g hc hg P (squareExponent 2)] with x hm hs h0 h2
  rw [hm,hs]
  simp only [Pi.add_apply,h0,h2]
  simp [momentProfile,profile,monomial,coordinate,squareExponent,leftRadius,Fin.prod_univ_succ]
  ring

theorem right_state_eq :
    genericMomentState α β wL wR c hα hβ hL hR hmatch b P g hc hg 0 1=
      state α β wL wR c hα hβ hL hR hmatch b g hc hg P (squareExponent 1)+
      state α β wL wR c hα hβ hL hR hmatch b g hc hg P (squareExponent 3) := by
  apply chargeCoordinates.injective
  rw [map_add]
  apply Lp.ext
  filter_upwards [generic_charge_coe α β wL wR c hα hβ hL hR hmatch b P g hc hg 0 1,
    Lp.coeFn_add (chargeCoordinates (state α β wL wR c hα hβ hL hR hmatch b g hc hg P (squareExponent 1)))
      (chargeCoordinates (state α β wL wR c hα hβ hL hR hmatch b g hc hg P (squareExponent 3))),
    state_charge_coe α β wL wR c hα hβ hL hR hmatch b g hc hg P (squareExponent 1),
    state_charge_coe α β wL wR c hα hβ hL hR hmatch b g hc hg P (squareExponent 3)] with x hm hs h1 h3
  rw [hm,hs]
  simp only [Pi.add_apply,h1,h3]
  simp [momentProfile,profile,monomial,coordinate,squareExponent,rightRadius,Fin.prod_univ_succ]
  ring

theorem left_mem : genericMomentState α β wL wR c hα hβ hL hR hmatch b P g hc hg 1 0 ∈
    space α β wL wR c hα hβ hL hR hmatch b g hc hg := by
  rw [left_state_eq]
  exact Submodule.add_mem _ (state_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (state_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)

theorem right_mem : genericMomentState α β wL wR c hα hβ hL hR hmatch b P g hc hg 0 1 ∈
    space α β wL wR c hα hβ hL hR hmatch b g hc hg := by
  rw [right_state_eq]
  exact Submodule.add_mem _ (state_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (state_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)

theorem left_kinetic_graph (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (i : Fin 4) :
    ∃ z : Hilbert, (genericMomentState α β wL wR c hα hβ hL hR hmatch b P g hc hg 1 0,z) ∈
      (component ε hε h (kineticIndex i)).graph :=
  kinetic_graph_exists α β wL wR c hα hβ hL hR hmatch b g hc hg ε hε h hh i _
    (left_mem α β wL wR c hα hβ hL hR hmatch b P g hc hg)

theorem right_kinetic_graph (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (i : Fin 4) :
    ∃ z : Hilbert, (genericMomentState α β wL wR c hα hβ hL hR hmatch b P g hc hg 0 1,z) ∈
      (component ε hε h (kineticIndex i)).graph :=
  kinetic_graph_exists α β wL wR c hα hβ hL hR hmatch b g hc hg ε hε h hh i _
    (right_mem α β wL wR c hα hβ hL hR hmatch b P g hc hg)

end

noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalIndependentRadialPacketMoments (momentState)
open KFCausalIndependentRadialPolynomialKinetic (kineticIndex)
open KFCausalNaturalSecondHamiltonianGraph (component)

theorem moment_left_kinetic_graph (ε a h wL wR : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hL : 1 ≤ wL) (hR : 1 ≤ wR) (i : Fin 4) :
    ∃ z : Hilbert, (momentState ε a h wL wR C p b P hε ha hh hL hR 1 0,z) ∈
      (component ε hε h (kineticIndex i)).graph :=
  left_kinetic_graph _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ε h hε hh i

theorem moment_right_kinetic_graph (ε a h wL wR : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hL : 1 ≤ wL) (hR : 1 ≤ wR) (i : Fin 4) :
    ∃ z : Hilbert, (momentState ε a h wL wR C p b P hε ha hh hL hR 0 1,z) ∈
      (component ε hε h (kineticIndex i)).graph :=
  right_kinetic_graph _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ε h hε hh i

#print axioms left_state_eq
#print axioms right_state_eq
#print axioms left_mem
#print axioms right_mem
#print axioms left_kinetic_graph
#print axioms right_kinetic_graph
#print axioms moment_left_kinetic_graph
#print axioms moment_right_kinetic_graph
end
end UnifiedTheory.Audit.KFCausalIndependentRadialMomentKinetic
