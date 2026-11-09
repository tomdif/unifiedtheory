/- Actual field/shear commutation on the coherent span. The correction
is a derived L2 field derivative, and the output lies in the actual closed
shear graph. No formal interchange of unbounded operators is used. -/
import UnifiedTheory.Audit.KFCausalCoherentShiftedRegularity
import UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCoherentFieldShearGraph
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalReconstruction (shearDerivative)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalFieldShearDifferential
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower fieldPower_graph)
open UnifiedTheory.Audit.KFCausalCoherentShiftedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare (fieldSquare fieldSquare_domain fieldSquare_linear_energy)

theorem graph_from_representatives (h : ℝ) (hh : h ≠ 0) (φ : Configuration → ℂ)
    (hs : ContDiff ℝ 1 φ) (u w : Hilbert) (hu : u =ᵐ[volume] φ)
    (hw : w =ᵐ[volume] fun x => (-Complex.I*(h:ℂ))*shearDerivative φ x) :
    (u,w) ∈ (shearMomentum h).graph := by
  have hm : MemLp φ 2 volume := (Lp.memLp u).ae_eq hu
  have hd : MemLp (shearDerivative φ) 2 volume := by
    apply ((Lp.memLp w).const_mul (Complex.I/(h:ℂ))).ae_eq
    filter_upwards [hw] with x hx
    simp only [hx,← mul_assoc,KFCausalUnitaryMomentumEvolution.inverse_coefficient h hh,one_mul]
  have eu : hm.toLp φ = u := Lp.ext (hm.coeFn_toLp.trans hu.symm)
  have ew : (-Complex.I*(h:ℂ)) • hd.toLp (shearDerivative φ) = w := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul (-Complex.I*(h:ℂ)) (hd.toLp (shearDerivative φ)),hd.coeFn_toLp,hw]
      with x hx hd hw
    simp only [hx,Pi.smul_apply,smul_eq_mul,hd,hw]
  simpa only [eu,ew] using
    KFCausalShearMaximalDifferential.graph_of_shear_differential h hh φ hs hm hd

theorem powerSlope_memLp (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (g : Hilbert)
    (hd : ∀ m : Transverse →L[ℝ] ℝ, g ∈ (fieldSquare m).domain) :
    MemLp (fun x => powerSlope l i x*g x) 2 volume := by
  fin_cases i
  · simpa only [powerSlope,Fin.val_zero,Nat.zero_add,Nat.cast_one,pow_zero,one_mul] using
      fieldSquare_linear_energy (fieldSlope l) g (hd (fieldSlope l))
  · have hm := (((fieldSquare_domain (l+fieldSlope l) g).mp (hd _)).sub
      ((fieldSquare_domain l g).mp (hd _))).sub
      ((fieldSquare_domain (fieldSlope l) g).mp (hd _))
    apply hm.ae_eq
    filter_upwards [] with x
    simp only [Pi.sub_apply,ContinuousLinearMap.add_apply,Complex.ofReal_add,powerSlope]
    norm_num
    ring

theorem smooth_power_graph (h : ℝ) (hh : h ≠ 0) (l : Transverse →L[ℝ] ℝ) (i : Fin 2)
    (φ : Configuration → ℂ) (hs : ContDiff ℝ 1 φ) (g jg u j d : Hilbert)
    (hg : g =ᵐ[volume] φ) (hjg : (g,jg) ∈ (shearMomentum h).graph)
    (hu : (g,u) ∈ (fieldPower l i).graph) (hj : (jg,j) ∈ (fieldPower l i).graph)
    (hd : d =ᵐ[volume] fun x => powerSlope l i x*g x) :
    (u,j+(-Complex.I*(h:ℂ)) • d) ∈ (shearMomentum h).graph := by
  have hm : MemLp φ 2 volume := (Lp.memLp g).ae_eq hg
  have eg : hm.toLp φ = g := Lp.ext (hm.coeFn_toLp.trans hg.symm)
  have hjg' : jg =ᵐ[volume] fun x => (-Complex.I*(h:ℂ))*shearDerivative φ x := by
    apply KFCausalTransverseShearDifferential.graph_representative h hh φ hm
      (hs.differentiable (by norm_num)) jg
    simpa only [eg] using hjg
  apply graph_from_representatives h hh (powerProfile l i φ)
    ((powerValue_smooth l i).mul hs) u (j+(-Complex.I*(h:ℂ)) • d)
  · filter_upwards [(fieldPower_graph l i g u).mp hu,hg] with x hx he
    simp only [hx,he,powerProfile,powerValue]
  · filter_upwards [Lp.coeFn_add j ((-Complex.I*(h:ℂ)) • d),
      Lp.coeFn_smul (-Complex.I*(h:ℂ)) d,(fieldPower_graph l i jg j).mp hj,hjg',hd,hg]
      with x hx hc hj hjg hd hg
    simp only [hx,Pi.add_apply,hc,Pi.smul_apply,smul_eq_mul,hj,hjg,hd,hg,
      power_shear l i φ (hs.differentiable (by norm_num)) x,powerValue]
    ring

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
include hb in
theorem actual_power_graph (l : Transverse →L[ℝ] ℝ) (i : Fin 2)
    (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh) (g jg u j : Hilbert)
    (hg : (f,g) ∈ (orderedExponential ε hε h).graph) (hjg : (g,jg) ∈ (shearMomentum h).graph)
    (hu : (g,u) ∈ (fieldPower l i).graph) (hj : (jg,j) ∈ (fieldPower l i).graph) :
    ∃ d : Hilbert, d =ᵐ[volume] (fun x => powerSlope l i x*g x) ∧
      (u,j+(-Complex.I*(h:ℂ)) • d) ∈ (shearMomentum h).graph := by
  obtain ⟨φ,hs,he⟩ := actual_smooth_representative ε a h hε ha hh hb f hf g hg
  have hd := powerSlope_memLp l i g (actual_fieldSquare_domain ε a h hε ha hh hb f hf g hg)
  exact ⟨hd.toLp _,hd.coeFn_toLp,
    smooth_power_graph h hh l i φ hs g jg u j (hd.toLp _) he hjg hu hj hd.coeFn_toLp⟩

#print axioms graph_from_representatives
#print axioms powerSlope_memLp
#print axioms smooth_power_graph
#print axioms actual_power_graph
end
end UnifiedTheory.Audit.KFCausalCoherentFieldShearGraph
