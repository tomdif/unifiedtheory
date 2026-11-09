/- Exact polynomial factorization of all three projected ordered
outputs. The complex neutral shear survives charge projection. A
bounded-reciprocal integral theorem justifies the unbounded multiplier. -/
import UnifiedTheory.Audit.KFCausalUnboundedMultiplierIntegral
import UnifiedTheory.Audit.KFCausalPolynomialOrderedProfile
import UnifiedTheory.Audit.KFCausalDisplacedPolynomialProjectedResponse
import UnifiedTheory.Audit.KFCausalNeutralHermiteDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalProjectedPolynomialOrderedProfile
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential (position)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (scale scale_smooth)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalPolynomialOrderedProfile
open UnifiedTheory.Audit.KFCausalPolynomialGaussianDomain (output)
open UnifiedTheory.Audit.KFCausalSourcedResponseFactorBridge (index)
open UnifiedTheory.Audit.KFCausalUnboundedMultiplierIntegral (relation relation_integral)
open UnifiedTheory.Audit.KFCausalDisplacedPolynomialEnergyLift (inputOrbit orbit_memLp)
open UnifiedTheory.Audit.KFCausalDisplacedPolynomialProjectedResponse (meanInput)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources (amplitude clockFrequency source)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth)

def shiftedWeight (ε h : ℝ) (P : Polynomial ℂ) (x : Configuration) : ℂ :=
  P.eval (position (scale ε (-h/2) x.1) x.2 4)

theorem shiftedWeight_continuous (ε h : ℝ) (hε : 0 < ε)
    (hb : |h| ≤ 2*Real.pi*ε/3) (P : Polynomial ℂ) : Continuous (shiftedWeight ε h P) :=
  P.continuous.comp (KFCausalShiftedPolynomialMoments.position_continuous
    (scale ε (-h/2)) (scale_smooth ε (-h/2) hε (shift_bound ε h hb)).continuous 4)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3)

theorem source_factor_coe (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) (P : Polynomial ℂ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (n : Fin 3) :
    output ε a h hε ha hh C p b 4 hb P v l (index n) =ᵐ[volume]
      fun x : Configuration => (l x.2:ℂ)^n.val*orderedProfile ε a h C p b 4 P x := by
  fin_cases n
  · simpa only [pow_zero,one_mul] using output_vacuum_coe ε a h hε ha hh hb C p b 4 P v l
  · simpa only [pow_one] using output_linear_coe ε a h hε ha hh hb C p b 4 P v l
  · exact output_quadratic_coe ε a h hε ha hh hb C p b 4 P v l

theorem source_factor_relation (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) (P : Polynomial ℂ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (n : Fin 3) :
    relation (shiftedWeight ε h P)
      (output ε a h hε ha hh C p b 4 hb 1 v l (index n))
      (output ε a h hε ha hh C p b 4 hb P v l (index n)) := by
  filter_upwards [source_factor_coe ε a h hε ha hh hb C p b P v l n,
    source_factor_coe ε a h hε ha hh hb C p b 1 v l n] with x hp h1
  rw [hp,h1]
  simp only [orderedProfile,shiftedWeight,Polynomial.eval_one,one_mul]
  ring

variable (q k : Joint 2 4) (P : Polynomial ℂ)

theorem orbit_relation (n : Fin 3) (θ : ℝ) :
    relation (shiftedWeight ε h P)
      (inputOrbit ε a h hε ha hh hb q k 1 (index n) θ)
      (inputOrbit ε a h hε ha hh hb q k P (index n) θ) :=
  source_factor_relation ε a h hε ha hh hb
    (amplitude h (parameter (2*Real.pi*θ) q) (parameter (2*Real.pi*θ) k))
    (clockFrequency h (parameter (2*Real.pi*θ) k))
    (source h (parameter (2*Real.pi*θ) q) (parameter (2*Real.pi*θ) k))
    P modelDirections pointField n

theorem mean_relation (n : Fin 3) :
    relation (shiftedWeight ε h P)
      (meanInput ε a h hε ha hh hb q k 1 (index n))
      (meanInput ε a h hε ha hh hb q k P (index n)) :=
  relation_integral _ (shiftedWeight_continuous ε h hε hb P).measurable _ _
    ((orbit_memLp ε a h hε ha hh hb q k 1 (index n)).1.integrable (by norm_num))
    ((orbit_memLp ε a h hε ha hh hb q k P (index n)).1.integrable (by norm_num))
    (Filter.Eventually.of_forall (orbit_relation ε a h hε ha hh hb q k P n))

theorem mean_weight_memLp (n : Fin 3) :
    MemLp (fun x : Configuration => shiftedWeight ε h P x*
      meanInput ε a h hε ha hh hb q k 1 (index n) x) 2 volume :=
  (Lp.memLp (meanInput ε a h hε ha hh hb q k P (index n))).ae_eq
    (mean_relation ε a h hε ha hh hb q k P n)

omit P in
theorem hermite_mean_coe (B : ℝ) (d : ℕ) (n : Fin 3) :
    meanInput ε a h hε ha hh hb q k
      (KFCausalNeutralHermiteDomain.multiplier (neutralWidth h) B d) (index n) =ᵐ[volume]
        fun x : Configuration =>
          ((KFCausalNeutralHermiteDomain.physicistsHermite d).eval
            ((Real.sqrt (2*neutralWidth h):ℂ)*
              ((x.2 4:ℂ)+2*(scale ε (-h/2) x.1-1)*((x.2 2:ℂ)+(x.2 3:ℂ))-(B:ℂ)))/
                (Real.sqrt ((2:ℝ)^d*d.factorial):ℂ))*
            meanInput ε a h hε ha hh hb q k 1 (index n) x := by
  filter_upwards [mean_relation ε a h hε ha hh hb q k
    (KFCausalNeutralHermiteDomain.multiplier (neutralWidth h) B d) n] with x hx
  rw [hx]
  simp only [shiftedWeight,KFCausalNeutralHermiteDomain.multiplier_eval,position,ite_true]

#print axioms shiftedWeight_continuous
#print axioms source_factor_coe
#print axioms source_factor_relation
#print axioms orbit_relation
#print axioms mean_relation
#print axioms mean_weight_memLp
#print axioms hermite_mean_coe
end
end UnifiedTheory.Audit.KFCausalProjectedPolynomialOrderedProfile
