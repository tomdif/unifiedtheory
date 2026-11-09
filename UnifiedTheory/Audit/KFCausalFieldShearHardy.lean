/- A field-derivative estimate in the actual shear graph. The estimate
does not replace the shear graph norm by Hamiltonian energy. -/
import UnifiedTheory.Audit.KFCausalFieldSlopeShearGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalFieldShearHardy
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalFieldShearDifferential
open UnifiedTheory.Audit.KFCausalFieldSlopeShearGraph
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum shear_selfAdjoint)
open UnifiedTheory.Audit.KFCausalSelfAdjointCoreWeakGraph (graph_iff_weak)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower fieldPower_graph)

theorem real_multiplier_inner (a b : ℝ) (z w : ℂ) :
    inner ℂ ((a:ℂ)*z) ((b:ℂ)*w) = ((a*b:ℝ):ℂ)*inner ℂ z w := by
  change inner ℂ ((a:ℂ) • z) ((b:ℂ) • w) = _
  rw [inner_smul_left,inner_smul_right,Complex.conj_ofReal]
  push_cast
  ring

def realSlope (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (x : Configuration) : ℝ :=
  (i.val+1:ℕ)*(l x.2)^i.val*fieldSlope l x.2

def realSecond (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (x : Configuration) : ℝ :=
  if i=0 then (1/2:ℝ)*realSlope l i x
  else 2*(fieldSlope l x.2)^2+(1/2:ℝ)*realSlope l i x

theorem powerSlope_real (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (x : Configuration) :
    powerSlope l i x = (realSlope l i x:ℂ) := by
  simp only [powerSlope,realSlope,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast]

theorem secondSlope_real (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (x : Configuration) :
    secondSlope l i x = (realSecond l i x:ℂ) := by
  fin_cases i <;> norm_num [secondSlope,realSecond,powerSlope_real]

theorem second_product (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (x : Configuration) :
    (l x.2)^(i.val+1)*realSecond l i x =
      (1-1/((i.val:ℝ)+1))* (realSlope l i x)^2+
        (1/2:ℝ)*(l x.2)^(i.val+1)*realSlope l i x := by
  fin_cases i <;> norm_num [realSecond,realSlope] <;> ring

theorem crossed_pairing (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (g jg u j d v : Hilbert)
    (hu : (g,u) ∈ (fieldPower l i).graph) (hj : (jg,j) ∈ (fieldPower l i).graph)
    (hd : d =ᵐ[volume] fun x => powerSlope l i x*g x)
    (hv : v =ᵐ[volume] fun x => powerSlope l i x*jg x) :
    inner ℂ u v = inner ℂ d j := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(fieldPower_graph l i g u).mp hu,(fieldPower_graph l i jg j).mp hj,hd,hv]
    with x hu hj hd hv
  rw [hu,hj,hd,hv,powerSlope_real,← Complex.ofReal_pow,real_multiplier_inner,real_multiplier_inner]
  push_cast
  ring

theorem second_pairing (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (g u d e : Hilbert)
    (hu : (g,u) ∈ (fieldPower l i).graph)
    (hd : d =ᵐ[volume] fun x => powerSlope l i x*g x)
    (he : e =ᵐ[volume] fun x => secondSlope l i x*g x) :
    inner ℂ u e = ((1-1/((i.val:ℝ)+1):ℝ):ℂ)*inner ℂ d d+
      (1/2:ℂ)*inner ℂ u d := by
  rw [L2.inner_def,L2.inner_def,L2.inner_def,← integral_const_mul,← integral_const_mul,
    ← integral_add ((L2.integrable_inner (𝕜 := ℂ) d d).const_mul _)
      ((L2.integrable_inner (𝕜 := ℂ) u d).const_mul _)]
  apply integral_congr_ae
  filter_upwards [(fieldPower_graph l i g u).mp hu,hd,he] with x hu hd he
  rw [hu,hd,he,powerSlope_real,secondSlope_real,← Complex.ofReal_pow]
  simp only [real_multiplier_inner]
  have hs := congrArg Complex.ofReal (second_product l i x)
  push_cast at hs
  push_cast
  rw [hs]
  ring

theorem graph_identity (h p : ℝ) (hh : h ≠ 0) (hp : 0 < p) (u j d v e k : Hilbert)
    (hu : (u,k) ∈ (shearMomentum h).graph)
    (hd : (d,v+(-Complex.I*(h:ℂ)) • e) ∈ (shearMomentum h).graph)
    (hk : k = j+(-Complex.I*(h:ℂ)) • d)
    (hc : inner ℂ u v = inner ℂ d j)
    (he : inner ℂ u e = ((1-1/p:ℝ):ℂ)*inner ℂ d d+(1/2:ℂ)*inner ℂ u d) :
    ‖d‖^2 = -(2*p/h)*(inner ℂ d k).im+(p/2)*(inner ℂ u d).re := by
  have hs := (graph_iff_weak _ (shear_selfAdjoint h hh) d _).mp hd u k hu
  rw [inner_add_right,inner_smul_right,hc,he] at hs
  have hs' := congrArg Complex.im hs
  have hk' := congrArg (fun z : Hilbert => (inner ℂ d z).im) hk
  change (inner ℂ d k).im = (inner ℂ d (j+(-Complex.I*(h:ℂ)) • d)).im at hk'
  rw [inner_add_right,inner_smul_right] at hk'
  have hsym : (inner ℂ k d).im = -(inner ℂ d k).im := inner_im_symm (𝕜 := ℂ) k d
  rw [hsym] at hs'
  have hdd : inner ℂ d d = ((‖d‖^2:ℝ):ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    exact (Complex.ofReal_pow ‖d‖ 2).symm
  rw [hdd] at hs' hk'
  simp only [Complex.add_im,Complex.mul_im,
    Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,
    Complex.div_ofNat_re,Complex.div_ofNat_im,Complex.one_re,Complex.one_im,
    zero_mul,mul_zero,zero_add,add_zero,sub_zero,neg_zero] at hs' hk'
  field_simp [hh,hp.ne'] at hs' ⊢
  linear_combination -hs'+(2*p)*hk'

theorem norm_bound_of_identity (h p : ℝ) (hh : h ≠ 0) (hp : 0 < p) (u d k : Hilbert)
    (he : ‖d‖^2 = -(2*p/h)*(inner ℂ d k).im+(p/2)*(inner ℂ u d).re) :
    ‖d‖ ≤ (2*p/|h|)*‖k‖+(p/2)*‖u‖ := by
  have hi : -(2*p/h)*(inner ℂ d k).im ≤ (2*p/|h|)*(‖d‖*‖k‖) := by
    calc
      _ ≤ |-(2*p/h)*(inner ℂ d k).im| := le_abs_self _
      _ = (2*p/|h|)*|(inner ℂ d k).im| := by
        rw [abs_mul,abs_neg,abs_div,abs_mul,abs_of_pos hp]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((Complex.abs_im_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ) d k)) (by positivity)
  have hr := mul_le_mul_of_nonneg_left (re_inner_le_norm (𝕜 := ℂ) u d)
    (show 0 ≤ p/2 by positivity)
  change p/2*(inner ℂ u d).re ≤ p/2*(‖u‖*‖d‖) at hr
  have hbound : ‖d‖*‖d‖ ≤ ‖d‖*((2*p/|h|)*‖k‖+(p/2)*‖u‖) := by
    nlinarith only [he,hi,hr]
  by_cases hd : d=0
  · simp only [hd,norm_zero]
    positivity
  · have hpos : 0 < ‖d‖ := norm_pos_iff.mpr hd
    nlinarith only [hbound,hpos]

theorem clock_polynomial (W : Hilbert →L[ℂ] Hilbert) (w : ℝ → ℂ)
    (hW : ∀ f : Hilbert, W f =ᵐ[volume] fun x => w x.1*f x)
    (P : Configuration → ℂ) (g u : Hilbert) (hu : u =ᵐ[volume] fun x => P x*g x) :
    W u =ᵐ[volume] fun x => P x*W g x := by
  filter_upwards [hW u,hW g,hu] with x hw hg hu
  rw [hw,hg,hu]
  ring

theorem weighted_graph_bound (h : ℝ) (hh : h ≠ 0) (l : Transverse →L[ℝ] ℝ) (i : Fin 2)
    (g jg u j d v e : Hilbert) (hu : (g,u) ∈ (fieldPower l i).graph)
    (hj : (jg,j) ∈ (fieldPower l i).graph)
    (hd : d =ᵐ[volume] fun x => powerSlope l i x*g x)
    (hv : v =ᵐ[volume] fun x => powerSlope l i x*jg x)
    (he : e =ᵐ[volume] fun x => secondSlope l i x*g x)
    (hJu : (u,j+(-Complex.I*(h:ℂ)) • d) ∈ (shearMomentum h).graph)
    (hJd : (d,v+(-Complex.I*(h:ℂ)) • e) ∈ (shearMomentum h).graph)
    (W : Hilbert →L[ℂ] Hilbert) (w : ℝ → ℂ)
    (hW : ∀ f : Hilbert, W f =ᵐ[volume] fun x => w x.1*f x) :
    ‖W d‖ ≤ (2*((i.val:ℝ)+1)/|h|)*‖W (j+(-Complex.I*(h:ℂ)) • d)‖+
      (((i.val:ℝ)+1)/2)*‖W u‖ := by
  have hWu : (W g,W u) ∈ (fieldPower l i).graph :=
    (fieldPower_graph l i _ _).mpr (clock_polynomial W w hW _ _ _ ((fieldPower_graph l i _ _).mp hu))
  have hWj : (W jg,W j) ∈ (fieldPower l i).graph :=
    (fieldPower_graph l i _ _).mpr (clock_polynomial W w hW _ _ _ ((fieldPower_graph l i _ _).mp hj))
  have hWd := clock_polynomial W w hW _ _ _ hd
  have hWv := clock_polynomial W w hW _ _ _ hv
  have hWe := clock_polynomial W w hW _ _ _ he
  have hJd' : (W d,W v+(-Complex.I*(h:ℂ)) • W e) ∈ (shearMomentum h).graph := by
    simpa only [map_add,map_smul] using KFCausalClockShearRealMultiplier.clock_graph W w hW h hh _ _ hJd
  have hI := graph_identity h ((i.val:ℝ)+1) hh (by positivity) (W u) (W j) (W d) (W v) (W e)
    (W (j+(-Complex.I*(h:ℂ)) • d))
    (KFCausalClockShearRealMultiplier.clock_graph W w hW h hh _ _ hJu) hJd'
    (by simp only [map_add,map_smul])
    (crossed_pairing l i _ _ _ _ _ _ hWu hWj hWd hWv)
    (second_pairing l i _ _ _ _ hWu hWd hWe)
  exact norm_bound_of_identity h ((i.val:ℝ)+1) hh (by positivity) _ _ _ hI

open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)

include hb in
theorem actual_weighted_bound (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (f : Hilbert)
    (hf : f ∈ coherentSpan ε a h hε ha hh) (g jg u j : Hilbert)
    (hg : (f,g) ∈ (orderedExponential ε hε h).graph) (hjg : (g,jg) ∈ (shearMomentum h).graph)
    (hu : (g,u) ∈ (fieldPower l i).graph) (hj : (jg,j) ∈ (fieldPower l i).graph)
    (W : Hilbert →L[ℂ] Hilbert) (w : ℝ → ℂ)
    (hW : ∀ f : Hilbert, W f =ᵐ[volume] fun x => w x.1*f x) :
    ∃ d : Hilbert, d =ᵐ[volume] (fun x => powerSlope l i x*g x) ∧
      (u,j+(-Complex.I*(h:ℂ)) • d) ∈ (shearMomentum h).graph ∧
      ‖W d‖ ≤ (2*((i.val:ℝ)+1)/|h|)*‖W (j+(-Complex.I*(h:ℂ)) • d)‖+
        (((i.val:ℝ)+1)/2)*‖W u‖ := by
  obtain ⟨d,v,e,hd,hv,he,hJd⟩ := actual_slope_graph ε a h hε ha hh hb l i f hf g jg hg hjg
  obtain ⟨d',hd',hJu⟩ := KFCausalCoherentFieldShearGraph.actual_power_graph
    ε a h hε ha hh hb l i f hf g jg u j hg hjg hu hj
  have ed : d'=d := Lp.ext (hd'.trans hd.symm)
  rw [ed] at hJu
  exact ⟨d,hd,hJu,weighted_graph_bound h hh l i g jg u j d v e hu hj hd hv he hJu hJd W w hW⟩

#print axioms real_multiplier_inner
#print axioms powerSlope_real
#print axioms secondSlope_real
#print axioms second_product
#print axioms crossed_pairing
#print axioms second_pairing
#print axioms graph_identity
#print axioms norm_bound_of_identity
#print axioms clock_polynomial
#print axioms weighted_graph_bound
#print axioms actual_weighted_bound
end
end UnifiedTheory.Audit.KFCausalFieldShearHardy
