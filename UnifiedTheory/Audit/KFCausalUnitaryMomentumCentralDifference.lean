/- Bounded symmetric differences of the actual unitary clock group converge
to its maximal momentum on its domain. Their expectations along any strong
Hilbert-space trajectory have actual derivatives. No unbounded-domain
invariance or exchange of the two differentiation limits is asserted. -/
import UnifiedTheory.Audit.KFCausalUnitaryMomentumEvolution
import UnifiedTheory.Audit.KFCausalUnitaryWeakGenerator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalUnitaryMomentumCentralDifference
noncomputable section
open Filter
open scoped Topology
open KFCausalUnitaryOrbitAverage (StrongUnitaryGroup)
open KFCausalUnitaryMomentumSelfAdjoint (momentum)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (U : StrongUnitaryGroup H)

def central (h τ : ℝ) : H →L[ℂ] H :=
  (-Complex.I*(h:ℂ)/2) • (τ⁻¹:ℝ) •
    ((U.action τ : H →L[ℂ] H)-(U.action (-τ) : H →L[ℂ] H))

theorem central_apply (h τ : ℝ) (x : H) :
    central U h τ x = (-Complex.I*(h:ℂ)/2) •
      (τ⁻¹ • (U.action τ x-U.action (-τ) x)) := rfl

theorem central_tendsto (h : ℝ) (hh : h ≠ 0) (x y : H)
    (hg : (x,y) ∈ (momentum U h).graph) :
    Tendsto (fun τ => central U h τ x) (𝓝[≠] 0) (𝓝 y) := by
  have hd := (KFCausalUnitaryMomentumEvolution.momentum_graph_iff U h hh x y).mp hg
  have hm : HasDerivAt (fun τ : ℝ => U.action (-τ) x)
      (-((Complex.I/(h:ℂ)) • y)) 0 := by
    have hd' : HasDerivAt (fun τ => U.action τ x) ((Complex.I/(h:ℂ)) • y) (-(0:ℝ)) := by
      simpa only [neg_zero] using hd
    simpa only [neg_zero,neg_one_smul] using
      hd'.scomp 0 (hasDerivAt_id (0:ℝ)).neg
  have hs := ((hd.sub hm).tendsto_slope_zero).const_smul (-Complex.I*(h:ℂ)/2)
  have he : (-Complex.I*(h:ℂ)/2) •
      ((Complex.I/(h:ℂ)) • y- -((Complex.I/(h:ℂ)) • y)) = y := by
    rw [sub_neg_eq_add,← add_smul,smul_smul]
    have hc : (-Complex.I*(h:ℂ)/2)*(Complex.I/(h:ℂ)+Complex.I/(h:ℂ)) = 1 := by
      field_simp [Complex.ofReal_ne_zero.mpr hh]
      ring_nf
      simp only [Complex.I_sq]
      ring
    rw [hc,one_smul]
  simpa only [central_apply,zero_add,Pi.sub_apply,neg_zero,U.initial,sub_self,sub_zero,he] using hs

theorem central_symmetric (h τ : ℝ) (x y : H) :
    inner ℂ (central U h τ x) y = inner ℂ x (central U h τ y) := by
  have hi (t : ℝ) (v w : H) : inner ℂ (U.action t v) w = inner ℂ v (U.action (-t) w) := by
    rw [← (U.action (-t)).inner_map_map (U.action t v) w,
      U.compose,add_neg_cancel,U.initial]
  simp only [central_apply,← Complex.coe_smul,inner_smul_left,inner_smul_right,
    inner_sub_left,inner_sub_right,hi,neg_neg,
    map_div₀,map_mul,map_neg,Complex.conj_I,Complex.conj_ofReal,map_ofNat]
  ring

theorem expectation_hasDerivAt (h τ s : ℝ) (f : ℝ → H) (v : H)
    (hf : HasDerivAt f v s) :
    HasDerivAt (fun t => (inner ℂ (f t) (central U h τ (f t))).re)
      (2*(inner ℂ v (central U h τ (f s))).re) s := by
  have hb := ((central U h τ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s hf
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s (hf.inner ℂ hb)
  convert hd using 1
  change 2*(inner ℂ v (central U h τ (f s))).re =
    (inner ℂ (f s) (central U h τ v)+inner ℂ v (central U h τ (f s))).re
  rw [Complex.add_re,← central_symmetric]
  have hr : (inner ℂ (f s) (central U h τ v)).re =
      (inner ℂ (central U h τ v) (f s)).re := inner_re_symm (𝕜 := ℂ) _ _
  linarith

#print axioms central_apply
#print axioms central_tendsto
#print axioms central_symmetric
#print axioms expectation_hasDerivAt
end
end UnifiedTheory.Audit.KFCausalUnitaryMomentumCentralDifference
