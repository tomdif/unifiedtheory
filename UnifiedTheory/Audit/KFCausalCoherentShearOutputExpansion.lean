/- The actual J(T psi) output is a finite combination of existing field
outputs and a fixed bounded clock multiplier. This is equality in the
physical Hilbert space, not just a pointwise differential formula. -/
import UnifiedTheory.Audit.KFCausalShearOutputCoefficients

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCoherentShearOutputExpansion
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral (shiftedOutput)
open UnifiedTheory.Audit.KFCausalCoherentShearCompositions (shiftedShearOutput)
open UnifiedTheory.Audit.KFCausalCoherentShearPolynomial
open UnifiedTheory.Audit.KFCausalCoherentShearMoments
open UnifiedTheory.Audit.KFCausalShearOutputCoefficients
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (scale)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary (sourceCoefficients)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
variable (hbound : |h| ≤ 2*Real.pi*ε/3)
local notation "R" => scaleOperator ε h hε hbound
local notation "L" => linear ε a h hε ha hh hbound
local notation "Q" => quadratic ε a h hε ha hh hbound

def expandedOutput (k : Joint 2 4) : Hilbert := (-Complex.I*(h:ℂ)) •
  (shiftedOutput ε a h hε ha hh hbound k+
    (∑ i : Fin 4, (sourceCoefficients h k i.castSucc/2) • R (L k (coordinate i.castSucc)))+
    (sourceCoefficients h k 4) • R (L k mix)-
    (groundWidth h:ℂ) • R (R (∑ i : Fin 4, Q k (coordinate i.castSucc)))-
    (2*(neutralWidth h:ℂ)) • R (mixed ε a h hε ha hh hbound k)-
    (4*(neutralWidth h:ℂ)) • (R (R (Q k mix))-R (Q k mix)))

theorem expandedOutput_eq (k : Joint 2 4) :
    expandedOutput ε a h hε ha hh hbound k = shiftedShearOutput ε a h hε ha hh hbound k := by
  let g := shiftedOutput ε a h hε ha hh hbound k
  let b := sourceCoefficients h k
  have hid : g =ᵐ[volume] fun x => (1:ℂ)*g x := Filter.Eventually.of_forall (fun x => by simp)
  have hl (i : Fin 4) : ((b i.castSucc/2) • R (L k (coordinate i.castSucc))) =ᵐ[volume]
      fun x => ((b i.castSucc/2)*scale ε (-h/2) x.1*(x.2 i.castSucc:ℂ))*g x := by
    simpa only [coordinate,ContinuousLinearMap.proj_apply,mul_assoc] using
      product_smul g _ _ (b i.castSucc/2) (product_scale ε h hε hbound g _ _
        (linear_coe ε a h hε ha hh hbound k (coordinate i.castSucc)))
  have hls := product_sum g _ _ Finset.univ hl
  have hlm := product_smul g _ _ (b 4) (product_scale ε h hε hbound g _ _
    (linear_coe ε a h hε ha hh hbound k mix))
  have hqs : (∑ i : Fin 4, Q k (coordinate i.castSucc) : Hilbert) =ᵐ[volume]
      fun x => (∑ i : Fin 4, (x.2 i.castSucc:ℂ)^2)*g x := by
    simpa only [coordinate,ContinuousLinearMap.proj_apply] using product_sum g
      (fun i : Fin 4 => Q k (coordinate i.castSucc)) _ Finset.univ
      (fun i => quadratic_coe ε a h hε ha hh hbound k (coordinate i.castSucc))
  have hq := product_smul g _ _ (groundWidth h:ℂ)
    (product_scale ε h hε hbound g _ _ (product_scale ε h hε hbound g _ _ hqs))
  have hmix := product_smul g _ _ (2*(neutralWidth h:ℂ))
    (product_scale ε h hε hbound g _ _ (mixed_coe ε a h hε ha hh hbound k))
  have hqm := product_scale ε h hε hbound g _ _ (quadratic_coe ε a h hε ha hh hbound k mix)
  have hqm2 := product_scale ε h hε hbound g _ _ hqm
  have hdiff := product_smul g _ _ (4*(neutralWidth h:ℂ)) (product_sub g _ _ _ _ hqm2 hqm)
  have hbody := product_sub g _ _ _ _
    (product_sub g _ _ _ _ (product_sub g _ _ _ _
      (product_add g _ _ _ _ (product_add g _ _ _ _ hid hls) hlm) hq) hmix) hdiff
  have hout := product_smul g _ _ (-Complex.I*(h:ℂ)) hbody
  apply Lp.ext
  filter_upwards [hout,shiftedShearOutput_coe ε a h hε ha hh hbound k] with x hx hy
  change expandedOutput ε a h hε ha hh hbound k x = _ at hx
  rw [hx,hy,slope_expansion]
  dsimp only [b,g]
  ring

#print axioms expandedOutput_eq
end
end UnifiedTheory.Audit.KFCausalCoherentShearOutputExpansion
