/- The first field derivative has its own actual shear graph. Its second
derivative is constructed from the existing quadratic field domains,
including the mixed term of the original quadratic matter factor. -/
import UnifiedTheory.Audit.KFCausalFieldEigenpolynomials

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalFieldSlopeShearGraph
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse velocity)
open UnifiedTheory.Audit.KFCausalFieldShearDifferential
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalReconstruction (shearDerivative)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalCoherentFieldShearGraph (powerSlope_memLp graph_from_representatives)
open UnifiedTheory.Audit.KFCausalCoherentShiftedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare (fieldSquare fieldSquare_domain)

def secondSlope (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (x : Configuration) : ℂ :=
  if i=0 then (1/2:ℂ)*powerSlope l i x
  else 2*(fieldSlope l x.2:ℂ)^2+(1/2:ℂ)*powerSlope l i x

theorem fieldSlope_velocity (l : Transverse →L[ℝ] ℝ) (x : Transverse) :
    fieldSlope l (velocity x) = (1/2:ℝ)*fieldSlope l x := by
  have hv : velocity (velocity x) = (1/2:ℝ) • velocity x := by
    funext i
    by_cases hi : i=4 <;> simp [velocity,hi] <;> ring
  rw [fieldSlope_apply,hv,map_smul,← fieldSlope_apply]
  rfl

theorem slope_line_derivative (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (x : Configuration) :
    HasLineDerivAt ℝ (powerSlope l i) (secondSlope l i x) x ((0,velocity x.2):Configuration) := by
  have hl := KFCausalFieldEigenpolynomials.linear_line l x
  have hs := KFCausalFieldEigenpolynomials.linear_line (fieldSlope l) x
  fin_cases i
  · convert hs using 1
    · funext y
      simp [powerSlope]
    · norm_num [secondSlope,powerSlope,fieldSlope_velocity]
  · have hd := (hl.mul hs).const_mul 2
    change HasDerivAt (fun t : ℝ => powerSlope l 1 (x+t • (0,velocity x.2)))
      (secondSlope l 1 x) 0
    convert hd using 1
    · funext t
      simp [powerSlope]
      ring
    · norm_num [secondSlope,powerSlope,fieldSlope_velocity]
      rw [← fieldSlope_apply l x.2]
      ring

theorem slope_shear (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (φ : Configuration → ℂ)
    (hφ : Differentiable ℝ φ) (x : Configuration) :
    shearDerivative (fun y => powerSlope l i y*φ y) x =
      powerSlope l i x*shearDerivative φ x+secondSlope l i x*φ x := by
  have hm := ((powerSlope_smooth l i).differentiable (by norm_num) x).hasFDerivAt
  have hp := hm.mul (hφ x).hasFDerivAt
  change HasFDerivAt (fun y => powerSlope l i y*φ y) _ x at hp
  have he := (slope_line_derivative l i x).unique (hm.hasLineDerivAt ((0,velocity x.2):Configuration))
  rw [shearDerivative,hp.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  rw [← he]
  unfold shearDerivative
  ring

theorem secondSlope_memLp (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (g : Hilbert)
    (hd : ∀ m : Transverse →L[ℝ] ℝ, g ∈ (fieldSquare m).domain) :
    MemLp (fun x => secondSlope l i x*g x) 2 volume := by
  have hs := powerSlope_memLp l i g hd
  have hq := (fieldSquare_domain (fieldSlope l) g).mp (hd _)
  fin_cases i
  · convert hs.const_mul (1/2:ℂ) using 1
    funext x
    norm_num [secondSlope]
    ring
  · convert (hq.const_mul (2:ℂ)).add (hs.const_mul (1/2:ℂ)) using 1
    funext x
    norm_num [secondSlope]
    ring

theorem smooth_slope_graph (h : ℝ) (hh : h ≠ 0) (l : Transverse →L[ℝ] ℝ) (i : Fin 2)
    (φ : Configuration → ℂ) (hs : ContDiff ℝ 1 φ) (g jg d v e : Hilbert)
    (hg : g =ᵐ[volume] φ) (hjg : (g,jg) ∈ (shearMomentum h).graph)
    (hd : d =ᵐ[volume] fun x => powerSlope l i x*g x)
    (hv : v =ᵐ[volume] fun x => powerSlope l i x*jg x)
    (he : e =ᵐ[volume] fun x => secondSlope l i x*g x) :
    (d,v+(-Complex.I*(h:ℂ)) • e) ∈ (shearMomentum h).graph := by
  have hm : MemLp φ 2 volume := (Lp.memLp g).ae_eq hg
  have eg : hm.toLp φ = g := Lp.ext (hm.coeFn_toLp.trans hg.symm)
  have hjg' : jg =ᵐ[volume] fun x => (-Complex.I*(h:ℂ))*shearDerivative φ x := by
    apply KFCausalTransverseShearDifferential.graph_representative h hh φ hm
      (hs.differentiable (by norm_num)) jg
    simpa only [eg] using hjg
  apply graph_from_representatives h hh (fun x => powerSlope l i x*φ x)
    ((powerSlope_smooth l i).mul hs) d (v+(-Complex.I*(h:ℂ)) • e)
  · filter_upwards [hd,hg] with x hx hφ
    rw [hx,hφ]
  · filter_upwards [Lp.coeFn_add v ((-Complex.I*(h:ℂ)) • e),
      Lp.coeFn_smul (-Complex.I*(h:ℂ)) e,hv,he,hjg',hg] with x ha hc hv he hjg hg
    rw [ha]
    simp only [Pi.add_apply,hc,Pi.smul_apply,smul_eq_mul,hv,he,hjg,hg,
      slope_shear l i φ (hs.differentiable (by norm_num)) x]
    ring

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)

include hb in
theorem actual_slope_graph (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (f : Hilbert)
    (hf : f ∈ coherentSpan ε a h hε ha hh) (g jg : Hilbert)
    (hg : (f,g) ∈ (orderedExponential ε hε h).graph) (hjg : (g,jg) ∈ (shearMomentum h).graph) :
    ∃ d v e : Hilbert,
      d =ᵐ[volume] (fun x => powerSlope l i x*g x) ∧
      v =ᵐ[volume] (fun x => powerSlope l i x*jg x) ∧
      e =ᵐ[volume] (fun x => secondSlope l i x*g x) ∧
      (d,v+(-Complex.I*(h:ℂ)) • e) ∈ (shearMomentum h).graph := by
  have hG := actual_fieldSquare_domain ε a h hε ha hh hb f hf g hg
  have hJ : ∀ m : Transverse →L[ℝ] ℝ, jg ∈ (fieldSquare m).domain := fun m =>
    (KFCausalCoherentWeightedShearDomains.actual_shear_field_domains ε a h hε ha hh hb f hf g jg hg hjg m).2
  have hd := powerSlope_memLp l i g hG
  have hv := powerSlope_memLp l i jg hJ
  have he := secondSlope_memLp l i g hG
  obtain ⟨φ,hs,hφ⟩ := actual_smooth_representative ε a h hε ha hh hb f hf g hg
  exact ⟨hd.toLp _,hv.toLp _,he.toLp _,hd.coeFn_toLp,hv.coeFn_toLp,he.coeFn_toLp,
    smooth_slope_graph h hh l i φ hs g jg _ _ _ hφ hjg hd.coeFn_toLp hv.coeFn_toLp he.coeFn_toLp⟩

#print axioms fieldSlope_velocity
#print axioms slope_line_derivative
#print axioms slope_shear
#print axioms secondSlope_memLp
#print axioms smooth_slope_graph
#print axioms actual_slope_graph
end
end UnifiedTheory.Audit.KFCausalFieldSlopeShearGraph
