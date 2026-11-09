/- Polynomial field components with a definite shear degree have actual
first and second shear graphs. These derive the hypotheses needed for
bounded clock transport on the existing Gaussian interpolation. -/
import UnifiedTheory.Audit.KFCausalFieldShearPathGraphs
import UnifiedTheory.Audit.KFCausalTransportedShearCurve

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalEigenfieldShearGraphs
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (velocity)
open UnifiedTheory.Audit.KFCausalPolynomialImaginaryShearCurve (Weight)
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (Interval)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalReconstruction (shearDerivative)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalCoherentFieldShearGraph (graph_from_representatives)

structure EigenWeight extends Weight where
  degree : ℝ
  differential : ∀ x, HasLineDerivAt ℝ value ((degree:ℂ)*value x) x ((0,velocity x.2):Configuration)

def scalar (P : EigenWeight) (h : ℝ) : ℂ := (-Complex.I*(h:ℂ))*(P.degree:ℂ)

theorem weight_shear (P : EigenWeight) (φ : Configuration → ℂ) (hφ : Differentiable ℝ φ)
    (x : Configuration) :
    shearDerivative (fun y => P.value y*φ y) x =
      P.value x*shearDerivative φ x+(P.degree:ℂ)*P.value x*φ x := by
  have hp := (P.smooth.differentiable (by norm_num) x).hasFDerivAt
  have hd := hp.mul (hφ x).hasFDerivAt
  change HasFDerivAt (fun y => P.value y*φ y) _ x at hd
  have he := (P.differential x).unique (hp.hasLineDerivAt ((0,velocity x.2):Configuration))
  rw [shearDerivative,hd.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  rw [← he]
  unfold shearDerivative
  ring

theorem smooth_graph (P : EigenWeight) (h : ℝ) (hh : h ≠ 0)
    (φ : Configuration → ℂ) (hφ : ContDiff ℝ 1 φ) (g jg u v : Hilbert)
    (hg : g =ᵐ[volume] φ) (hj : (g,jg) ∈ (shearMomentum h).graph)
    (hu : u =ᵐ[volume] fun x => P.value x*g x)
    (hv : v =ᵐ[volume] fun x => P.value x*jg x) :
    (u,v+scalar P h • u) ∈ (shearMomentum h).graph := by
  have hm : MemLp φ 2 volume := (Lp.memLp g).ae_eq hg
  have eg : hm.toLp φ = g := Lp.ext (hm.coeFn_toLp.trans hg.symm)
  have hjg : jg =ᵐ[volume] fun x => (-Complex.I*(h:ℂ))*shearDerivative φ x := by
    apply KFCausalTransverseShearDifferential.graph_representative h hh φ hm
      (hφ.differentiable (by norm_num)) jg
    simpa only [eg] using hj
  apply graph_from_representatives h hh (fun x => P.value x*φ x) (P.smooth.mul hφ)
  · filter_upwards [hu,hg] with x hx he
    rw [hx,he]
  · filter_upwards [Lp.coeFn_add v (scalar P h • u),Lp.coeFn_smul (scalar P h) u,
      hv,hu,hjg,hg] with x ha hs hv hu hjg hg
    rw [ha]
    simp only [Pi.add_apply,hs,Pi.smul_apply,smul_eq_mul,hv,hu,hjg,hg]
    rw [weight_shear P φ (hφ.differentiable (by norm_num)) x]
    unfold scalar
    ring

open UnifiedTheory.Audit.KFCausalImaginaryShearSuperposition (Seed)
open UnifiedTheory.Audit.KFCausalActualPolynomialShearCurve
open UnifiedTheory.Audit.KFCausalFieldShearPathGraphs (state firstState secondState base_coe)
open UnifiedTheory.Audit.KFCausalImaginaryShearInterpolation
open UnifiedTheory.Audit.KFCausalImaginaryShearCoefficient
open UnifiedTheory.Audit.KFCausalGaussianSecondShearDifferential (first first_smooth)

variable (ε h : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3)
  (s : Seed) (P : EigenWeight)
local notation "U" => state ε h hε hb s P.toWeight
local notation "V" => firstState ε h hε hb s P.toWeight
local notation "K" => secondState ε h hε hb s P.toWeight
local notation "G" => KFCausalActualImaginaryShearCurve.input ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b
local notation "JG" => KFCausalActualImaginaryShearCurve.shear ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b
local notation "J2G" => KFCausalActualImaginaryShearCurve.secondShear ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b
local notation "A" => KFCausalShiftedGaussianPhysicalProfile.clockAmplitude ε s.a s.p (-h/2)
local notation "D" => displacement ε h
local notation "hA" => KFCausalShiftedGaussianPhysicalProfile.clockAmplitude_smooth ε s.a s.p (-h/2) hε (half_shift_bound ε h hb)
local notation "hD" => displacement_smooth ε h hε hb

theorem state_coe (t : Interval) : U t =ᵐ[volume] fun x => P.value x*G t x := by
  filter_upwards [input_coe P.toWeight ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b t,
    base_coe ε h hε hb s t] with x hu hg
  change U t x = _ at hu
  rw [hu,hg]

theorem firstState_coe (t : Interval) : V t =ᵐ[volume] fun x => P.value x*JG t x := by
  filter_upwards [weightedFirst_coe P.toWeight ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b t,
    KFCausalActualImaginaryShearCurve.shear_coe ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b t] with x hv hj
  change V t x = _ at hv
  rw [hv,hj]
  ring

theorem secondState_coe (t : Interval) : K t =ᵐ[volume] fun x => P.value x*J2G t x := by
  filter_upwards [weightedSecond_coe P.toWeight ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b t,
    KFCausalActualImaginaryShearCurve.secondShear_coe ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b t] with x hk hj
  change K t x = _ at hk
  rw [hk,hj]
  ring

theorem state_graph (hh : h ≠ 0) (t : Interval) :
    (U t,V t+scalar P h • U t) ∈ (shearMomentum h).graph :=
  smooth_graph P h hh (actualPath ε s.a s.α s.β s.p h s.b t)
    (path_smooth A D hA hD s.α s.β s.b t) (G t) (JG t) (U t) (V t)
    (base_coe ε h hε hb s t)
    (KFCausalActualImaginaryShearCurve.input_shear_graph ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b hh t)
    (state_coe ε h hε hb s P t) (firstState_coe ε h hε hb s P t)

theorem first_graph (hh : h ≠ 0) (t : Interval) :
    (V t,K t+scalar P h • V t) ∈ (shearMomentum h).graph := by
  let φ := first (timeAmplitude A D t) (timeScale D t) s.α s.β s.b
  have hs : ContDiff ℝ 1 φ := first_smooth _ _
    (timeAmplitude_smooth A D hA hD t) (timeScale_smooth D hD t) s.α s.β s.b
  exact smooth_graph P h hh (fun x => (-Complex.I*(h:ℂ))*φ x) (contDiff_const.mul hs)
    (JG t) (J2G t) (V t) (K t)
    (KFCausalActualImaginaryShearCurve.shear_coe ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b t)
    (KFCausalActualImaginaryShearCurve.shear_second_graph ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b hh t)
    (firstState_coe ε h hε hb s P t) (secondState_coe ε h hε hb s P t)

#print axioms weight_shear
#print axioms smooth_graph
#print axioms state_coe
#print axioms firstState_coe
#print axioms secondState_coe
#print axioms state_graph
#print axioms first_graph
end
end UnifiedTheory.Audit.KFCausalEigenfieldShearGraphs
