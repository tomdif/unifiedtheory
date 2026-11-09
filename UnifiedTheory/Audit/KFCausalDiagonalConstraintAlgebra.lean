/-
  All three deformation-bracket types in the diagonal, one-coordinate
  classical target. Exact jet identities include the boundary terms.
  General three-dimensional fields, spatial integration, quantum brackets,
  and a microscopic origin remain separate obligations.
-/
import UnifiedTheory.Audit.KFCausalDiagonalClockDynamics

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalDiagonalClockDynamics
noncomputable section
open MvPolynomial
open scoped BigOperators

@[simp] theorem jet_pderiv_two (i : Fin 20) : pderiv i (2 : P) = 0 := by
  change pderiv i ((2 : ℕ) : P) = 0
  rw [← map_natCast C 2]
  exact pderiv_C

/-- Canonical variational bracket for densities with no momentum derivatives. -/
def variationalBracket (F G : P) : P :=
  ∑ i : Fin 3,
    (euler i F * pderiv (![8,9,10] i) G - pderiv (![8,9,10] i) F * euler i G)

/-- Integration-by-parts form of the spatial generator D[N]. -/
def spatialSmearing (N dN : P) : P :=
  N*(X 8*X 2+X 9*X 3+X 10*X 4)+2*dN*X 9

theorem spatialSmearing_boundary (N : P) :
    spatialSmearing N (spatialD N) = N*spatialConstraint + spatialD (2*N*X 9) := by
  simp [spatialSmearing, spatialConstraint, Derivation.leibniz, smul_eq_mul, velocity]
  ring

/-- Log-metric Lie derivative: the longitudinal component has the extra 2 N'. -/
theorem spatial_metric_action (i : Fin 3) :
    pderiv (![8,9,10] i) (spatialSmearing (X 14) (X 15)) =
      X 14 * (![X 2,X 3,X 4] i) + if i = 1 then 2*X 15 else 0 := by
  fin_cases i <;>
    simp [spatialSmearing, Derivation.leibniz, smul_eq_mul]

/-- Each canonical log-metric momentum transforms as a spatial density. -/
theorem spatial_momentum_action (i : Fin 3) :
    -euler i (spatialSmearing (X 14) (X 15)) =
      X 14 * (![X 11,X 12,X 13] i) + X 15 * (![X 8,X 9,X 10] i) := by
  fin_cases i <;>
    simp [euler, logPartial, spatialSmearing, Derivation.leibniz,
      smul_eq_mul, velocity] <;> ring

theorem spatial_spatial_bracket :
    variationalBracket (spatialSmearing (X 14) (X 15))
      (spatialSmearing (X 17) (X 18)) = lapseW * spatialConstraint := by
  simp [variationalBracket, euler, logPartial, spatialSmearing, lapseW,
    spatialConstraint, Fin.sum_univ_succ, Derivation.leibniz, smul_eq_mul, velocity]
  ring

/-- Boundary current for {D[N],H[M]}, containing only first field jets. -/
def mixedBoundary (a b lam : ℝ) : P :=
  -X 14*X 17*C a*X 0*(X 8^2+X 9^2+X 10^2-C lam*(X 8+X 9+X 10)^2) -
    C (1/2)*X 14*X 17*C b*X 1*X 2*X 4 -
    X 14*X 18*C b*X 1*(X 2+X 4)

set_option maxHeartbeats 2000000 in
/-- Spatial covariance holds for every kinetic trace coefficient. The normal
    bracket is what further selects the DeWitt coefficient. -/
theorem spatial_normal_bracket (a b lam : ℝ) :
    variationalBracket (spatialSmearing (X 14) (X 15)) (X 17*density a b lam) =
      X 14*X 18*density a b lam + spatialD (mixedBoundary a b lam) := by
  apply MvPolynomial.funext
  intro values
  simp [variationalBracket, euler, logPartial, spatialSmearing, density,
    mixedBoundary, Fin.sum_univ_succ, Derivation.leibniz, Derivation.leibniz_pow,
    smul_eq_mul, velocity]
  ring

theorem normal_normal_bracket (a b : ℝ) :
    variationalBracket (X 14*density a b (1/2)) (X 17*density a b (1/2)) =
      (C a*C b*X 0*X 1*spatialConstraint)*lapseW +
        spatialD (secondLapseCoefficient a b (1/2)*lapseW) := by
  change clockBracket a b (1/2) = _
  rw [clockBracket_divergence_identity, corrected_clock_current]

/-- The same structure function e*f transforms as an inverse spatial metric. -/
theorem inverse_metric_spatial_action :
    (∑ i : Fin 3, logPartial i (X 0*X 1) *
      pderiv (![8,9,10] i) (spatialSmearing (X 14) (X 15))) =
        X 14*spatialD (X 0*X 1)-2*X 15*(X 0*X 1) := by
  apply MvPolynomial.funext
  intro values
  simp [logPartial, spatialSmearing, Fin.sum_univ_succ, Derivation.leibniz,
    smul_eq_mul, velocity]
  ring

#print axioms spatialSmearing_boundary
#print axioms spatial_metric_action
#print axioms spatial_momentum_action
#print axioms spatial_spatial_bracket
#print axioms spatial_normal_bracket
#print axioms normal_normal_bracket
#print axioms inverse_metric_spatial_action

end
end UnifiedTheory.Audit.KFCausalDiagonalClockDynamics
