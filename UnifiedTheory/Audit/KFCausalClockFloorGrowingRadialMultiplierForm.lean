/- The two actual growing kinetic rows identify the maximal radial
square-root multiplier on EVERY vector of the completed growing form.
The exact sesquilinear identity follows from the actual norm identity.
No full radial operator-domain domination is inferred here. -/
import UnifiedTheory.Audit.KFCausalClockFloorGrowingRadialFormIdentity
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaSymbol
import UnifiedTheory.Audit.KFCausalRealMultiplierSelfAdjoint

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGrowingRadialMultiplierForm
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalClockFloorRadialYosidaSymbol (radial radial_nonnegative)
open KFCausalClockFloorRotatedAntiSymbol (chargedWeight chargedWeight_continuous)
open KFCausalClockFloorAveragedChargedMoment (chargedMoment)
open KFCausalClockFloorGrowingRadialFormIdentity (charged_integrable kinetic_energy)
open KFCausalClockFloorAveragedSqueezeEnergy (coordinateLp)
open KFCausalClockFloorOrbitVacuumGraph (OrbitSpace)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalUnitaryRealMultiplier (realPullback realPullback_domain)
open KFCausalRealMultiplierSelfAdjoint (realPullback_selfAdjoint realPullback_norm_square)

private theorem equal_norm_inner {V H K : Type*} [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (A : V →ₗ[ℂ] H) (B : V →ₗ[ℂ] K) (hn : ∀ u, ‖A u‖=‖B u‖) (u v : V) :
    inner ℂ (A u) (A v)=inner ℂ (B u) (B v) := by
  rw [inner_eq_sum_norm_sq_div_four,inner_eq_sum_norm_sq_div_four]
  simp only [← map_add,← map_sub,← map_smul,hn]

private theorem form_graph {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (D : KFCausalClosedGraphForm.Data X Y) (u : KFCausalClosedGraphForm.FormSpace D) :
    (KFCausalClosedGraphForm.embedding D u,KFCausalClosedGraphForm.energyOutput D u) ∈
      D.operator.graph := u.property

private theorem radial_continuous (ε : ℝ) (hε : 0 < ε) (h : ℝ) :
    Continuous (radial ε h) :=
  ((chargedWeight_continuous ε hε h 0).add (chargedWeight_continuous ε hε h 1)).div_const 2

def rootSymbol (ε h : ℝ) (x : Joint 2 4) : ℝ := Real.sqrt (radial ε h x)

def rootOperator (ε : ℝ) (hε : 0 < ε) (h : ℝ) : Hilbert →ₗ.[ℂ] Hilbert :=
  realPullback chargeCoordinates (rootSymbol ε h) (radial_continuous ε hε h).sqrt.measurable

theorem root_selfAdjoint (ε : ℝ) (hε : 0 < ε) (h : ℝ) :
    IsSelfAdjoint (rootOperator ε hε h) :=
  realPullback_selfAdjoint chargeCoordinates (rootSymbol ε h) (radial_continuous ε hε h).sqrt.measurable

private theorem root_square (ε : ℝ) (hε : 0 < ε) (h : ℝ) (x : Joint 2 4) :
    rootSymbol ε h x^2=radial ε h x := Real.sq_sqrt (radial_nonnegative ε hε h x)

private theorem weighted_density (ε : ℝ) (hε : 0 < ε) (h : ℝ) (f : Hilbert) (x : Joint 2 4) :
    ‖(rootSymbol ε h x:ℂ)*(chargeCoordinates f) x‖^2 =
      (chargedWeight ε h 0 x*‖(chargeCoordinates f) x‖^2+
        chargedWeight ε h 1 x*‖(chargeCoordinates f) x‖^2)/2 := by
  rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,root_square ε hε h]
  unfold radial
  ring

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ : ℝ)

theorem root_domain (f : Hilbert) (y : EnergyOutputSpace)
    (hy : (f,y) ∈ (KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hb m g κ).graph) :
    f ∈ (rootOperator ε hε h).domain := by
  apply (realPullback_domain chargeCoordinates (rootSymbol ε h)
    (radial_continuous ε hε h).sqrt.measurable f).mpr
  have h0 := charged_integrable ε hε h hh hb m g κ f y hy 0
  have h1 := charged_integrable ε hε h hh hb m g κ f y hy 1
  have ha := (Complex.continuous_ofReal.comp (radial_continuous ε hε h).sqrt).aestronglyMeasurable.mul
    (Lp.aestronglyMeasurable (chargeCoordinates f))
  apply (memLp_two_iff_integrable_sq_norm ha).mpr
  exact ((h0.add h1).div_const 2).congr
    (Filter.Eventually.of_forall (fun x => (weighted_density ε hε h f x).symm))

theorem root_norm (f : Hilbert) (y : EnergyOutputSpace)
    (hy : (f,y) ∈ (KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hb m g κ).graph) :
    ‖rootOperator ε hε h ⟨f,root_domain ε hε h hh hb m g κ f y hy⟩‖^2 =
      ‖coordinateLp 3 y‖^2+‖coordinateLp 4 y‖^2 := by
  change ‖realPullback chargeCoordinates (rootSymbol ε h)
    (radial_continuous ε hε h).sqrt.measurable _‖^2 = _
  rw [realPullback_norm_square]
  simp_rw [root_square ε hε h]
  have h0 := charged_integrable ε hε h hh hb m g κ f y hy 0
  have h1 := charged_integrable ε hε h hh hb m g κ f y hy 1
  have he : (fun x => radial ε h x*‖(chargeCoordinates f) x‖^2) =
      fun x => (chargedWeight ε h 0 x*‖(chargeCoordinates f) x‖^2+
        chargedWeight ε h 1 x*‖(chargeCoordinates f) x‖^2)/2 := by
    funext x; unfold radial; ring
  rw [he,integral_div,integral_add h0 h1]
  have e0 := kinetic_energy ε hε h hh hb m g κ f y hy 0
  have e1 := kinetic_energy ε hε h hh hb m g κ f y hy 1
  change (1/2)*chargedMoment ε h 0 f=‖coordinateLp 3 y‖^2 at e0
  change (1/2)*chargedMoment ε h 1 f=‖coordinateLp 4 y‖^2 at e1
  change (chargedMoment ε h 0 f+chargedMoment ε h 1 f)/2=_
  linarith

local notation "D" => KFCausalClockFloorGrowingHamiltonian.formData ε hε h hh hb m g κ
local notation "V" => KFCausalClockFloorGrowingHamiltonian.GrowingForm ε hε h hh hb m g κ
local notation "J" => KFCausalClosedGraphForm.embedding D
local notation "B" => KFCausalClosedGraphForm.energyOutput D

def rootOutput : V →ₗ[ℂ] Hilbert :=
  (rootOperator ε hε h).toFun.comp ((J).toLinearMap.codRestrict (rootOperator ε hε h).domain
    (fun u => root_domain ε hε h hh hb m g κ (J u) (B u) (form_graph D u)))

private def columns : V →ₗ[ℂ] WithLp 2 (OrbitSpace × OrbitSpace) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ OrbitSpace OrbitSpace).symm.toLinearMap.comp
    (((coordinateLp 3).comp B).prod ((coordinateLp 4).comp B)).toLinearMap

theorem rootOutput_graph (u : V) :
    (J u,rootOutput ε hε h hh hb m g κ u) ∈ (rootOperator ε hε h).graph :=
  (rootOperator ε hε h).mem_graph
    ⟨J u,root_domain ε hε h hh hb m g κ (J u) (B u) (form_graph D u)⟩

private theorem output_norm (u : V) :
    ‖rootOutput ε hε h hh hb m g κ u‖=‖columns ε hε h hh hb m g κ u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact (root_norm ε hε h hh hb m g κ (J u) (B u) (form_graph D u)).trans
    (WithLp.prod_norm_sq_eq_of_L2 (columns ε hε h hh hb m g κ u)).symm

theorem rootOutput_inner (u v : V) :
    inner ℂ (rootOutput ε hε h hh hb m g κ u) (rootOutput ε hε h hh hb m g κ v) =
      inner ℂ (coordinateLp 3 (B u)) (coordinateLp 3 (B v))+
        inner ℂ (coordinateLp 4 (B u)) (coordinateLp 4 (B v)) :=
  equal_norm_inner (rootOutput ε hε h hh hb m g κ) (columns ε hε h hh hb m g κ)
    (output_norm ε hε h hh hb m g κ) u v

#print axioms root_selfAdjoint
#print axioms root_domain
#print axioms root_norm
#print axioms rootOutput_graph
#print axioms rootOutput_inner
end
end UnifiedTheory.Audit.KFCausalClockFloorGrowingRadialMultiplierForm
