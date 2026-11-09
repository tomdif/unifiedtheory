/-
  Gravity plus a scalar field in the diagonal one-coordinate target.
  Actual variational-jet brackets select the DeWitt trace coefficient
  and a common gravity/matter characteristic cone. A volume-weighted
  scalar potential passes the spatial covariance test; a bare potential
  has a nonzero density-weight anomaly.

  This is a proposed classical continuum constraint model. It is not a
  microscopic spin derivation, an integrated functional Poisson theorem,
  a full 3D constraint algebra, a quantum theory, or Standard Model matter.
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalMatterConstraintAlgebra
noncomputable section
open MvPolynomial
open scoped BigOperators

/- e,f, dx,dy,dz, ddx,ddy,ddz, px,py,pz, dpx,dpy,dpz,
   N,dN,ddN, M,dM,ddM, volume, phi,dphi,ddphi, pi,dpi.
   e=1/sqrt(det q), f=sqrt(det q)*q^yy, volume=sqrt(det q).
   The polynomial identities implement their chain rules explicitly. -/
abbrev P := MvPolynomial (Fin 26) ℝ

def velocity : Fin 26 → P :=
  ![-C (1/2)*X 0*(X 2+X 3+X 4), C (1/2)*X 1*(X 2-X 3+X 4),
    X 5,X 6,X 7,0,0,0,X 11,X 12,X 13,0,0,0,X 15,X 16,0,X 18,X 19,0,
    C (1/2)*X 20*(X 2+X 3+X 4),X 22,X 23,0,X 25,0]

def spatialD : Derivation ℝ P P := mkDerivation ℝ velocity
@[simp] theorem spatialD_X (j : Fin 26) : spatialD (X j) = velocity j := mkDerivation_X _ _ _
@[simp] theorem spatialD_C (a : ℝ) : spatialD (C a) = 0 := derivation_C _ _
@[simp] theorem spatialD_nat (n : ℕ) : spatialD (n : P) = 0 := by
  rw [← map_natCast C n]; exact spatialD_C n
@[simp] theorem spatialD_two : spatialD (2 : P) = 0 := spatialD_nat 2
@[simp] theorem pderiv_two (i : Fin 26) : pderiv i (2 : P) = 0 := by
  change pderiv i ((2 : ℕ) : P) = 0
  rw [← map_natCast C 2]; exact pderiv_C

def logPartial (i : Fin 3) (F : P) : P :=
  -C (1/2)*X 0*pderiv 0 F +
    (if i = 1 then -C (1/2) else C (1/2))*X 1*pderiv 1 F +
    C (1/2)*X 20*pderiv 20 F

def eulerMetric (i : Fin 3) (F : P) : P :=
  logPartial i F-spatialD (pderiv (![2,3,4] i) F)+
    spatialD (spatialD (pderiv (![5,6,7] i) F))
def eulerScalar (F : P) : P := pderiv 21 F-spatialD (pderiv 22 F)

def bracket (F G : P) : P :=
  (∑ i : Fin 3, (eulerMetric i F*pderiv (![8,9,10] i) G-
    pderiv (![8,9,10] i) F*eulerMetric i G)) +
      eulerScalar F*pderiv 24 G-pderiv 24 F*eulerScalar G

theorem eulerMetric_add (i : Fin 3) (F G : P) :
    eulerMetric i (F+G) = eulerMetric i F+eulerMetric i G := by
  simp [eulerMetric, logPartial, map_add, mul_add]
  ring

theorem eulerScalar_add (F G : P) : eulerScalar (F+G) = eulerScalar F+eulerScalar G := by
  simp [eulerScalar, map_add]
  ring

theorem bracket_add_left (F G H : P) : bracket (F+G) H = bracket F H+bracket G H := by
  simp [bracket, eulerMetric_add, eulerScalar_add, map_add, add_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

theorem bracket_add_right (F G H : P) : bracket F (G+H) = bracket F G+bracket F H := by
  simp [bracket, eulerMetric_add, eulerScalar_add, map_add, mul_add,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

def gravityDensity (a b lam : ℝ) : P :=
  C a*X 0*(X 8^2+X 9^2+X 10^2-C lam*(X 8+X 9+X 10)^2)+
    C b*X 1*(X 5+X 7+C (1/2)*(X 2^2+X 4^2+X 2*X 4-X 3*(X 2+X 4)))
def potential (mass2 quartic vacuum : ℝ) : P :=
  C (mass2/2)*X 21^2+C (quartic/4)*X 21^4+C vacuum
def matterDensity (κ γ mass2 quartic vacuum : ℝ) : P :=
  C (κ/2)*X 0*X 24^2+C (γ/2)*X 1*X 22^2+X 20*potential mass2 quartic vacuum
def totalDensity (a b lam κ γ mass2 quartic vacuum : ℝ) : P :=
  gravityDensity a b lam+matterDensity κ γ mass2 quartic vacuum

def gravitySpatial : P := X 8*X 2+X 9*X 3+X 10*X 4-2*X 12
def matterSpatial : P := X 24*X 22
def totalSpatial : P := gravitySpatial+matterSpatial
def traceAnomaly : P := 2*(X 11+X 12+X 13)-(X 2+X 3+X 4)*(X 8+X 9+X 10)
def lapseW : P := X 14*X 18-X 17*X 15
def normalBoundary (a b lam : ℝ) : P :=
  2*C a*C b*X 0*X 1*(2*C lam*(X 8+X 9+X 10)-X 8-X 10)*lapseW
def normalCurrent (a b lam κ γ : ℝ) : P :=
  X 0*X 1*(C a*C b*(gravitySpatial-(2*C lam-1)*traceAnomaly)+C κ*C γ*matterSpatial)

set_option maxHeartbeats 2000000 in
theorem gravity_normal_bracket (a b lam : ℝ) :
    bracket (X 14*gravityDensity a b lam) (X 17*gravityDensity a b lam) =
      normalCurrent a b lam 0 0*lapseW+spatialD (normalBoundary a b lam) := by
  apply MvPolynomial.funext
  intro values
  simp [bracket, eulerMetric, eulerScalar, logPartial,
    gravityDensity, normalCurrent, normalBoundary,
    gravitySpatial, matterSpatial, traceAnomaly, lapseW, Fin.sum_univ_succ,
    Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, velocity]
  ring

theorem matter_normal_bracket (κ γ mass2 quartic vacuum : ℝ) :
    bracket (X 14*matterDensity κ γ mass2 quartic vacuum)
      (X 17*matterDensity κ γ mass2 quartic vacuum) =
        C κ*C γ*X 0*X 1*matterSpatial*lapseW := by
  apply MvPolynomial.funext
  intro values
  simp [bracket, eulerMetric, eulerScalar, logPartial, matterDensity, potential,
    matterSpatial, lapseW, Fin.sum_univ_succ, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, velocity]
  ring

set_option maxHeartbeats 2000000 in
theorem normal_cross_terms_cancel (a b lam κ γ mass2 quartic vacuum : ℝ) :
    bracket (X 14*gravityDensity a b lam) (X 17*matterDensity κ γ mass2 quartic vacuum)+
      bracket (X 14*matterDensity κ γ mass2 quartic vacuum) (X 17*gravityDensity a b lam) = 0 := by
  apply MvPolynomial.funext
  intro values
  simp [bracket, eulerMetric, eulerScalar, logPartial, gravityDensity,
    matterDensity, potential, Fin.sum_univ_succ, Derivation.leibniz,
    Derivation.leibniz_pow, smul_eq_mul, velocity]
  ring

/-- Computed from the coupled canonical Euler bracket, including all
gravity/matter cross terms and the exact spatial divergence. -/
theorem coupled_normal_bracket (a b lam κ γ mass2 quartic vacuum : ℝ) :
    bracket (X 14*totalDensity a b lam κ γ mass2 quartic vacuum)
      (X 17*totalDensity a b lam κ γ mass2 quartic vacuum) =
        normalCurrent a b lam κ γ*lapseW+spatialD (normalBoundary a b lam) := by
  simp only [totalDensity, mul_add, bracket_add_left, bracket_add_right]
  have hc := normal_cross_terms_cancel a b lam κ γ mass2 quartic vacuum
  rw [gravity_normal_bracket, matter_normal_bracket]
  have he : normalCurrent a b lam κ γ = normalCurrent a b lam 0 0+
      C κ*C γ*X 0*X 1*matterSpatial := by
    simp [normalCurrent]
    ring
  rw [he]
  linear_combination hc

def traceWitness : Fin 26 → ℝ :=
  ![1,1,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0]
def matterWitness : Fin 26 → ℝ :=
  ![1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,1,0]

/-- The same inverse-metric current for gravity and scalar matter forces
lambda=1/2 and kappa*gamma=a*b. The potential parameters remain free. -/
theorem common_metric_current_iff (a b lam κ γ : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∀ values : Fin 26 → ℝ, eval values (normalCurrent a b lam κ γ) =
      a*b*values 0*values 1*eval values totalSpatial) ↔ lam=1/2 ∧ κ*γ=a*b := by
  constructor
  · intro h
    have ht := h traceWitness
    have hm := h matterWitness
    simp [normalCurrent, traceWitness, totalSpatial, gravitySpatial,
      matterSpatial, traceAnomaly] at ht
    simp [normalCurrent, matterWitness, totalSpatial, gravitySpatial,
      matterSpatial, traceAnomaly] at hm
    have hz : 2*lam-1 = 0 := ht.resolve_left (by simp [ha, hb])
    exact ⟨by linarith, hm⟩
  · rintro ⟨rfl, hκγ⟩ values
    simp [normalCurrent, totalSpatial, hκγ]
    ring

theorem coupled_current_closed (a b κ γ : ℝ) (hκγ : κ*γ=a*b) :
    normalCurrent a b (1/2) κ γ = C a*C b*X 0*X 1*totalSpatial := by
  apply MvPolynomial.funext
  intro values
  simp [normalCurrent, totalSpatial, hκγ]
  ring

def spatialSmearing (N dN : P) : P :=
  N*(X 8*X 2+X 9*X 3+X 10*X 4+X 24*X 22)+2*dN*X 9

theorem spatial_smearing_boundary (N : P) :
    spatialSmearing N (spatialD N) = N*totalSpatial+spatialD (2*N*X 9) := by
  simp [spatialSmearing, totalSpatial, gravitySpatial, matterSpatial,
    Derivation.leibniz, smul_eq_mul, velocity]
  ring

theorem coupled_spatial_bracket :
    bracket (spatialSmearing (X 14) (X 15)) (spatialSmearing (X 17) (X 18)) =
      lapseW*totalSpatial := by
  simp [bracket, eulerMetric, eulerScalar, logPartial, spatialSmearing,
    lapseW, totalSpatial, gravitySpatial, matterSpatial, Fin.sum_univ_succ,
    Derivation.leibniz, smul_eq_mul, velocity]
  ring

def mixedBoundary (a b lam κ γ mass2 quartic vacuum : ℝ) : P :=
  -X 14*X 17*C a*X 0*(X 8^2+X 9^2+X 10^2-C lam*(X 8+X 9+X 10)^2)-
    C (1/2)*X 14*X 17*C b*X 1*X 2*X 4-
    X 14*X 18*C b*X 1*(X 2+X 4)+
    X 14*X 17*(-C (κ/2)*X 0*X 24^2+C (γ/2)*X 1*X 22^2-
      X 20*potential mass2 quartic vacuum)

set_option maxHeartbeats 4000000 in
theorem coupled_spatial_normal_bracket (a b lam κ γ mass2 quartic vacuum : ℝ) :
    bracket (spatialSmearing (X 14) (X 15))
      (X 17*totalDensity a b lam κ γ mass2 quartic vacuum) =
        X 14*X 18*totalDensity a b lam κ γ mass2 quartic vacuum+
          spatialD (mixedBoundary a b lam κ γ mass2 quartic vacuum) := by
  apply MvPolynomial.funext
  intro values
  simp [bracket, eulerMetric, eulerScalar, logPartial, spatialSmearing,
    totalDensity, gravityDensity, matterDensity, potential, mixedBoundary,
    Fin.sum_univ_succ, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, velocity]
  ring

/-- A bare scalar potential is a scalar, whereas the Hamiltonian integrand
must be a density. Its missing volume factor has this exact anomaly. -/
theorem bare_potential_covariance_defect (mass2 quartic vacuum : ℝ) :
    bracket (spatialSmearing (X 14) (X 15)) (X 17*potential mass2 quartic vacuum) =
      X 14*X 18*potential mass2 quartic vacuum+
        spatialD (-X 14*X 17*potential mass2 quartic vacuum)+
          X 15*X 17*potential mass2 quartic vacuum := by
  apply MvPolynomial.funext
  intro values
  simp [bracket, eulerMetric, eulerScalar, logPartial, spatialSmearing,
    potential, Fin.sum_univ_succ, Derivation.leibniz, Derivation.leibniz_pow,
    smul_eq_mul, velocity]
  ring

/-- Closure fixes the principal characteristic coefficient, not masses
or scalar self-couplings. Here e*f is the inverse spatial metric. -/
theorem common_characteristic_cone (a b κ γ e f : ℝ) (hκγ : κ*γ=a*b) :
    (κ*e)*(γ*f) = (a*b)*(e*f) := by
  calc
    _ = (κ*γ)*(e*f) := by ring
    _ = _ := by rw [hκγ]

#print axioms coupled_normal_bracket
#print axioms common_metric_current_iff
#print axioms coupled_current_closed
#print axioms spatial_smearing_boundary
#print axioms coupled_spatial_bracket
#print axioms coupled_spatial_normal_bracket
#print axioms bare_potential_covariance_defect
#print axioms common_characteristic_cone

end
end UnifiedTheory.Audit.KFCausalMatterConstraintAlgebra
