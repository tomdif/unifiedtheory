/- A strong derivative product rule for moving unitary actions. It needs
strong continuity only, not operator-norm differentiability. -/
import UnifiedTheory.Audit.KFCausalStrongUnitaryContinuity
import UnifiedTheory.Audit.KFCausalUnitaryMomentumEvolution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalStrongUnitaryProductDerivative
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalStrongUnitaryContinuity
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage
open UnifiedTheory.Audit.KFCausalUnitaryMomentumEvolution
open UnifiedTheory.Audit.KFCausalUnitaryMomentumSelfAdjoint

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem product_derivative (U : ℝ → H ≃ₗᵢ[ℂ] H)
    (hc : ∀ x, Continuous (fun t => U t x)) (hi : ∀ x, U 0 x = x)
    (v : ℝ → H) (a b : H)
    (hu : HasDerivAt (fun t => U t (v 0)) a 0) (hv : HasDerivAt v b 0) :
    HasDerivAt (fun t => U t (v t)) (b+a) 0 := by
  have hs : Tendsto (fun t : ℝ => t⁻¹ • (v t-v 0)) (𝓝[≠] 0) (𝓝 b) := by
    simpa only [zero_add] using hv.tendsto_slope_zero
  have ht : Tendsto (fun t : ℝ => t) (𝓝[≠] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hj := (joint_evaluation_continuous U hc).continuousAt.tendsto.comp (ht.prodMk_nhds hs)
  have ha : Tendsto (fun t : ℝ => t⁻¹ • (U t (v 0)-v 0)) (𝓝[≠] 0) (𝓝 a) := by
    simpa only [zero_add,hi] using hu.tendsto_slope_zero
  have hh : Tendsto (fun t : ℝ => U t (t⁻¹ • (v t-v 0))+t⁻¹ • (U t (v 0)-v 0))
      (𝓝[≠] 0) (𝓝 (b+a)) := by
    simpa only [Function.comp_apply,hi] using hj.add ha
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  convert hh using 1
  funext t
  simp only [zero_add,hi,map_real_smul (U t) (U t).continuous,map_sub,smul_sub]
  abel

theorem conjugate_difference_derivative (U : StrongUnitaryGroup H)
    (V : H ≃ₗᵢ[ℂ] H) (f p q : H)
    (hp : HasDerivAt (fun t => U.action t f) p 0)
    (hq : HasDerivAt (fun t => U.action t (V.symm f)) q 0) :
    HasDerivAt (fun t => V (U.action t (V.symm (U.action (-t) f)))) (V q-p) 0 := by
  let F : ℝ → H ≃ₗᵢ[ℂ] H := fun t => V.symm.trans ((U.action t).trans V)
  have hc (x : H) : Continuous (fun t => F t x) :=
    V.continuous.comp (U.continuous_orbit (V.symm x))
  have hi (x : H) : F 0 x = x := by
    change V (U.action 0 (V.symm x)) = x
    rw [U.initial,LinearIsometryEquiv.apply_symm_apply]
  have hu : HasDerivAt (fun t => F t (U.action (-0) f)) (V q) 0 := by
    have hd := ((V : H →L[ℂ] H).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hq
    change HasDerivAt (fun t => V (U.action t (V.symm f))) (V q) 0 at hd
    simpa only [neg_zero,U.initial] using hd
  have hv : HasDerivAt (fun t : ℝ => U.action (-t) f) (-p) 0 := by
    have hd : HasDerivAt (fun t => U.action t f) p (-0) := by simpa only [neg_zero] using hp
    simpa only [neg_smul,one_smul] using hd.scomp 0 (hasDerivAt_id 0).neg
  have hd := product_derivative F hc hi (fun t => U.action (-t) f) _ _ hu hv
  exact hd.congr_deriv (by abel)

theorem graph_of_commutes (U : StrongUnitaryGroup H) (h : ℝ) (hh : h ≠ 0)
    (Q : H →L[ℂ] H) (hc : ∀ t x, U.action t (Q x) = Q (U.action t x))
    (f g : H) (hfg : (f,g) ∈ (momentum U h).graph) :
    (Q f,Q g) ∈ (momentum U h).graph := by
  apply (momentum_graph_iff U h hh _ _).mpr
  have hd := (Q.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    ((momentum_graph_iff U h hh f g).mp hfg)
  change HasDerivAt (fun t => Q (U.action t f)) (Q ((Complex.I/(h:ℂ)) • g)) 0 at hd
  simpa only [← hc,map_smul] using hd

#print axioms product_derivative
#print axioms graph_of_commutes
#print axioms conjugate_difference_derivative
end
end UnifiedTheory.Audit.KFCausalStrongUnitaryProductDerivative
