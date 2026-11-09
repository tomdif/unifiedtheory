/- A quantitative comparison of two unitary groups using their shifted
resolvents. A double-resolvent initial state supplies the necessary
regularity, without assuming bounded generators or shared domains. -/
import UnifiedTheory.Audit.KFCausalResolventUnitaryResidual

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalStrongResolventFlowComparison
noncomputable section
open Set
open KFCausalUnitaryOrbitAverage (StrongUnitaryGroup)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem double_resolvent_bound (U V : StrongUnitaryGroup H) (R S : H →L[ℂ] H) (c : ℂ)
    (hU : ∀ f t, HasDerivAt (fun u => U.action u (R f)) (c • U.action t (f-R f)) t)
    (hV : ∀ f t, HasDerivAt (fun u => V.action u (S f)) (c • V.action t (f-S f)) t)
    (hc : ∀ t x, S (V.action t x)=V.action t (S x))
    (x : H) (L δ t : ℝ) (hL : 0 ≤ L) (hδ : 0 ≤ δ) (ht : |t| ≤ L)
    (hb₁ : ∀ s ∈ Icc (-L) L, ‖R (V.action s x)-S (V.action s x)‖ ≤ δ)
    (hb₂ : ∀ s ∈ Icc (-L) L, ‖R (V.action s (S x))-S (V.action s (S x))‖ ≤ δ) :
    ‖U.action t (S (S x))-V.action t (S (S x))‖ ≤ (2+‖c‖*L)*δ := by
  have h0 : (0:ℝ) ∈ Icc (-L) L := ⟨neg_nonpos.mpr hL,hL⟩
  have hti : t ∈ Icc (-L) L := abs_le.mp ht
  have hi : ‖R (S x)-S (S x)‖ ≤ δ := by simpa only [V.initial] using hb₂ 0 h0
  have he : ‖R (V.action t (S x))-V.action t (S (S x))‖ ≤ δ := by
    simpa only [hc] using hb₂ t hti
  have hm : ‖U.action t (R (S x))-R (V.action t (S x))‖ ≤ (‖c‖*δ)*|t| := by
    have hb (s : ℝ) (hs : s ∈ uIcc 0 t) :
        ‖R (c • V.action s (x-S x))-c • (V.action s (S x)-R (V.action s (S x)))‖ ≤ ‖c‖*δ := by
      have hsi : s ∈ Icc (-L) L := by
        rcases mem_uIcc.mp hs with hs | hs <;> constructor <;> linarith [hti.1,hti.2]
      have halg : R (c • V.action s (x-S x))-c • (V.action s (S x)-R (V.action s (S x)))=
          c • (R (V.action s x)-S (V.action s x)) := by
        rw [hc]
        simp only [map_smul,map_sub]
        module
      rw [halg,norm_smul]
      exact mul_le_mul_of_nonneg_left (hb₁ s hsi) (norm_nonneg c)
    simpa only [V.initial] using KFCausalResolventUnitaryResidual.error_bound U R c hU
      (fun s => V.action s (S x)) (fun s => c • V.action s (x-S x)) (hV x) t (‖c‖*δ) hb
  have hfirst : ‖U.action t (S (S x))-U.action t (R (S x))‖ ≤ δ := by
    rw [← map_sub,(U.action t).norm_map,norm_sub_rev]
    exact hi
  have htri := dist_triangle (U.action t (S (S x))) (U.action t (R (S x))) (V.action t (S (S x)))
  have htri' := dist_triangle (U.action t (R (S x))) (R (V.action t (S x))) (V.action t (S (S x)))
  simp only [dist_eq_norm] at htri htri'
  have htime := mul_le_mul_of_nonneg_left ht (mul_nonneg (norm_nonneg c) hδ)
  nlinarith only [htri,htri',hfirst,hm,he,htime]

theorem dense_comparison (U V : H ≃ₗᵢ[ℂ] H) (x y : H) :
    ‖U x-V x‖ ≤ 2*‖x-y‖+‖U y-V y‖ := by
  have h₁ := dist_triangle (U x) (U y) (V x)
  have h₂ := dist_triangle (U y) (V y) (V x)
  simp only [dist_eq_norm] at h₁ h₂
  have hu : ‖U x-U y‖=‖x-y‖ := by rw [← map_sub,U.norm_map]
  have hv : ‖V y-V x‖=‖x-y‖ := by rw [← map_sub,V.norm_map,norm_sub_rev]
  rw [hu] at h₁
  rw [hv] at h₂
  linarith

#print axioms double_resolvent_bound
#print axioms dense_comparison
end
end UnifiedTheory.Audit.KFCausalStrongResolventFlowComparison
