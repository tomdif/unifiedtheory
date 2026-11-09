/- Actual ordered outputs and the stronger momentum domain of every
neutral Hermite packet, before physical charge projection. -/
import UnifiedTheory.Audit.KFCausalPolynomialOrderedProfile
import UnifiedTheory.Audit.KFCausalPolynomialMomentumDomain
import UnifiedTheory.Audit.KFCausalNeutralHermiteDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalNeutralHermiteOutputs
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (scale)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor commonEnergyDomain)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalNeutralHermiteDomain (state multiplier multiplier_eval physicistsHermite)
open UnifiedTheory.Audit.KFCausalPolynomialOrderedProfile (gaussianProfile orderedProfile)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) (B : ℝ) (n : ℕ)

def factorOutput (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) : Hilbert :=
  KFCausalPolynomialGaussianDomain.output ε a h hε ha hh C p b 4 hb (multiplier (neutralWidth h) B n) v l j

def shiftedProfile (x : Configuration) : ℂ :=
  ((physicistsHermite n).eval ((Real.sqrt (2*neutralWidth h):ℂ)*
    ((x.2 4:ℂ)+2*(scale ε (-h/2) x.1-1)*((x.2 2:ℂ)+(x.2 3:ℂ))-(B:ℂ)))/
      (Real.sqrt ((2:ℝ)^n*n.factorial):ℂ))*gaussianProfile ε a h C p b x

theorem orderedProfile_eq :
    orderedProfile ε a h C p b 4 (multiplier (neutralWidth h) B n) = shiftedProfile ε a h C p b B n := by
  funext x
  unfold orderedProfile shiftedProfile
  rw [multiplier_eval]
  rfl

theorem factorOutput_graph (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) :
    (state ε a h hε ha hh C p b B n,factorOutput ε a h hε ha hh hb C p b B n v l j) ∈
      (energyFactor ε hε h v l j).graph :=
  KFCausalPolynomialGaussianDomain.output_graph ε a h hε ha hh C p b 4 hb
    (multiplier (neutralWidth h) B n) v l j

theorem vacuum_coe (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    factorOutput ε a h hε ha hh hb C p b B n v l 7 =ᵐ[volume] shiftedProfile ε a h C p b B n := by
  rw [← orderedProfile_eq]
  exact KFCausalPolynomialOrderedProfile.output_vacuum_coe ε a h hε ha hh hb C p b 4
    (multiplier (neutralWidth h) B n) v l

theorem linear_coe (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    factorOutput ε a h hε ha hh hb C p b B n v l 5 =ᵐ[volume] fun x : Configuration =>
      (l x.2:ℂ)*shiftedProfile ε a h C p b B n x := by
  rw [← orderedProfile_eq]
  exact KFCausalPolynomialOrderedProfile.output_linear_coe ε a h hε ha hh hb C p b 4
    (multiplier (neutralWidth h) B n) v l

theorem quadratic_coe (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    factorOutput ε a h hε ha hh hb C p b B n v l 6 =ᵐ[volume] fun x : Configuration =>
      (l x.2:ℂ)^2*shiftedProfile ε a h C p b B n x := by
  rw [← orderedProfile_eq]
  exact KFCausalPolynomialOrderedProfile.output_quadratic_coe ε a h hε ha hh hb C p b 4
    (multiplier (neutralWidth h) B n) v l

include hb in
theorem momentum_response_domain (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    ∃ k : Hilbert, (state ε a h hε ha hh C p b B n,k) ∈ (pureMomentum ε hε h).graph ∧
      k ∈ commonEnergyDomain ε hε h v l :=
  ⟨_,KFCausalPolynomialMomentumDomain.momentum_graph ε a h hε ha hh p b 4 C
    (multiplier (neutralWidth h) B n),
    KFCausalPolynomialMomentumDomain.momentum_commonEnergyDomain ε a h hε ha hh p b 4 C hb
      (multiplier (neutralWidth h) B n) v l⟩

#print axioms orderedProfile_eq
#print axioms factorOutput_graph
#print axioms vacuum_coe
#print axioms linear_coe
#print axioms quadratic_coe
#print axioms momentum_response_domain
end
end UnifiedTheory.Audit.KFCausalNeutralHermiteOutputs
