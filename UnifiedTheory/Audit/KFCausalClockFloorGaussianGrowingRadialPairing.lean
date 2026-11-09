/- Complex centered clock Gaussians commute with the actual maximal
radial multiplier and its square root. On the entire growing Hamiltonian
domain, the proved radial domination supplies the second root graph and
the exact pairing against every vector of the original growing form.
No separate radial moment or second-factor domain premise is imposed. -/
import UnifiedTheory.Audit.KFCausalClockFloorGaussianGrowingForm
import UnifiedTheory.Audit.KFCausalClockFloorGrowingRadialDomination

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGaussianGrowingRadialPairing
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalClockFloorGaussianGrowingTransport (action action_coordinates action_pairing)
open KFCausalClockFloorGrowingRadialMultiplierForm (rootSymbol rootOperator rootOutput rootOutput_graph)
open KFCausalClockFloorRadialYosidaSymbol (radial radial_nonnegative)
open KFCausalClockFloorRadialYosidaDomain (operator)
open KFCausalClockFloorRotatedAntiSymbol (chargedWeight_continuous)
open KFCausalUnitaryRealMultiplier (realPullback_graph)

private theorem radial_measurable (ε : ℝ) (hε : 0 < ε) (h : ℝ) :
    Measurable (radial ε h) :=
  (((chargedWeight_continuous ε hε h 0).add
    (chargedWeight_continuous ε hε h 1)).div_const 2).measurable

private theorem root_measurable (ε : ℝ) (hε : 0 < ε) (h : ℝ) :
    Measurable (rootSymbol ε h) := (radial_measurable ε hε h).sqrt

theorem root_gaussian_graph (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a)
    (h y : ℝ) (f z : Hilbert) (hfg : (f,z) ∈ (rootOperator ε hε h).graph) :
    (action ε a ha y f,action ε a ha y z) ∈ (rootOperator ε hε h).graph := by
  have hr := (realPullback_graph chargeCoordinates (rootSymbol ε h)
    (root_measurable ε hε h) f z).mp hfg
  apply (realPullback_graph chargeCoordinates (rootSymbol ε h)
    (root_measurable ε hε h) _ _).mpr
  filter_upwards [hr,action_coordinates ε a ha y f,action_coordinates ε a ha y z]
    with x hx hf hz
  rw [hz,hf,hx]
  ring

theorem radial_gaussian_graph (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a)
    (h y : ℝ) (f z : Hilbert) (hfg : (f,z) ∈ (operator ε hε h).graph) :
    (action ε a ha y f,action ε a ha y z) ∈ (operator ε hε h).graph := by
  have hr := (realPullback_graph chargeCoordinates (radial ε h)
    (radial_measurable ε hε h) f z).mp hfg
  apply (realPullback_graph chargeCoordinates (radial ε h)
    (radial_measurable ε hε h) _ _).mpr
  filter_upwards [hr,action_coordinates ε a ha y f,action_coordinates ε a ha y z]
    with x hx hf hz
  rw [hz,hf,hx]
  ring

theorem root_square_graph (ε : ℝ) (hε : 0 < ε) (h : ℝ) (f u z : Hilbert)
    (hu : (f,u) ∈ (rootOperator ε hε h).graph)
    (hz : (f,z) ∈ (operator ε hε h).graph) :
    (u,z) ∈ (rootOperator ε hε h).graph := by
  have hur := (realPullback_graph chargeCoordinates (rootSymbol ε h)
    (root_measurable ε hε h) f u).mp hu
  have hzr := (realPullback_graph chargeCoordinates (radial ε h)
    (radial_measurable ε hε h) f z).mp hz
  apply (realPullback_graph chargeCoordinates (rootSymbol ε h)
    (root_measurable ε hε h) u z).mpr
  filter_upwards [hur,hzr] with x hx hz'
  rw [hz',hx,← mul_assoc,← Complex.ofReal_mul]
  have he : rootSymbol ε h x*rootSymbol ε h x=radial ε h x := by
    rw [← pow_two,rootSymbol,Real.sq_sqrt (radial_nonnegative ε hε h x)]
  rw [he]

private theorem root_graph_pairing (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (f z v u : Hilbert)
    (hf : (f,z) ∈ (rootOperator ε hε h).graph)
    (hv : (v,u) ∈ (rootOperator ε hε h).graph) :
    inner ℂ f u=inner ℂ z v := by
  have hfr := (realPullback_graph chargeCoordinates (rootSymbol ε h)
    (root_measurable ε hε h) f z).mp hf
  have hvr := (realPullback_graph chargeCoordinates (rootSymbol ε h)
    (root_measurable ε hε h) v u).mp hv
  rw [← chargeCoordinates.inner_map_map f u,← chargeCoordinates.inner_map_map z v,
    L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hfr,hvr] with x hx hy
  rw [hx,hy]
  change inner ℂ ((chargeCoordinates f) x)
    ((rootSymbol ε h x:ℂ) • (chargeCoordinates v) x)=
      inner ℂ ((rootSymbol ε h x:ℂ) • (chargeCoordinates f) x)
        ((chargeCoordinates v) x)
  rw [inner_smul_left,inner_smul_right,Complex.conj_ofReal]

theorem root_output_intertwining (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a)
    (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (y m g k : ℝ)
    (v : KFCausalClockFloorGrowingHamiltonian.GrowingForm ε hε h hh hb m g k) :
    rootOutput ε hε h hh hb m g k
      (KFCausalClockFloorGaussianGrowingForm.formAction ε hε a ha h hh hb y m g k v)=
        action ε a ha y (rootOutput ε hε h hh hb m g k v) := by
  have h1 := rootOutput_graph ε hε h hh hb m g k
    (KFCausalClockFloorGaussianGrowingForm.formAction ε hε a ha h hh hb y m g k v)
  have h2 := root_gaussian_graph ε hε a ha h y _ _
    (rootOutput_graph ε hε h hh hb m g k v)
  rw [KFCausalClockFloorGaussianGrowingForm.formAction_embedding] at h1
  exact (rootOperator ε hε h).mem_graph_snd_inj' h1 h2 rfl

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi*ε/3) (m g k : ℝ)
local notation "hw" => KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb
local notation "D" => KFCausalClockFloorGrowingHamiltonian.formData ε hε h hh hw m g k
local notation "V" => KFCausalClockFloorGrowingHamiltonian.GrowingForm ε hε h hh hw m g k
local notation "J" => KFCausalClosedGraphForm.embedding D
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "R" => rootOutput ε hε h hh hw m g k

def radialOutput (x : (G).domain) : Hilbert := operator ε hε h
  ⟨(x:Hilbert),KFCausalClockFloorGrowingRadialDomination.radial_domain ε hε h hh hb m g k x⟩

theorem root_second_graph (x : (G).domain) :
    (R (KFCausalClosedGraphForm.formLift D x),radialOutput ε hε h hh hb m g k x) ∈
      (rootOperator ε hε h).graph := by
  have hr := rootOutput_graph ε hε h hh hw m g k (KFCausalClosedGraphForm.formLift D x)
  rw [KFCausalClosedGraphForm.embedding_formLift] at hr
  exact root_square_graph ε hε h (x:Hilbert) _ _ hr ((operator ε hε h).mem_graph
    ⟨(x:Hilbert),KFCausalClockFloorGrowingRadialDomination.radial_domain ε hε h hh hb m g k x⟩)

theorem root_second_domain (x : (G).domain) :
    R (KFCausalClosedGraphForm.formLift D x) ∈ (rootOperator ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph (root_second_graph ε hε h hh hb m g k x)

theorem root_form_pairing (x : (G).domain) (v : V) :
    inner ℂ (R (KFCausalClosedGraphForm.formLift D x)) (R v)=
      inner ℂ (radialOutput ε hε h hh hb m g k x) (J v) :=
  root_graph_pairing ε hε h _ _ _ _
    (root_second_graph ε hε h hh hb m g k x) (rootOutput_graph ε hε h hh hw m g k v)

theorem gaussian_root_pairing (a : ℝ) (ha : 0 ≤ a) (y : ℝ)
    (x : (G).domain) (v : V) :
    inner ℂ (action ε a ha y (R (KFCausalClosedGraphForm.formLift D x))) (R v)=
      inner ℂ (action ε a ha y (radialOutput ε hε h hh hb m g k x)) (J v) :=
  root_graph_pairing ε hε h _ _ _ _
    (root_gaussian_graph ε hε a ha h y _ _ (root_second_graph ε hε h hh hb m g k x))
    (rootOutput_graph ε hε h hh hw m g k v)

theorem gaussian_form_pairing (a : ℝ) (ha : 0 ≤ a) (y : ℝ)
    (x : (G).domain) (v : V) :
    inner ℂ (R (KFCausalClosedGraphForm.formLift D x))
      (R (KFCausalClockFloorGaussianGrowingForm.formAction ε hε a ha h hh hw y m g k v))=
        inner ℂ (action ε a ha (-y) (radialOutput ε hε h hh hb m g k x)) (J v) := by
  rw [root_form_pairing,KFCausalClockFloorGaussianGrowingForm.formAction_embedding]
  simpa only [neg_neg] using
    (action_pairing ε a ha (-y) (radialOutput ε hε h hh hb m g k x) (J v)).symm

#print axioms root_gaussian_graph
#print axioms radial_gaussian_graph
#print axioms root_square_graph
#print axioms root_output_intertwining
#print axioms root_second_graph
#print axioms root_second_domain
#print axioms root_form_pairing
#print axioms gaussian_root_pairing
#print axioms gaussian_form_pairing
end
end UnifiedTheory.Audit.KFCausalClockFloorGaussianGrowingRadialPairing
