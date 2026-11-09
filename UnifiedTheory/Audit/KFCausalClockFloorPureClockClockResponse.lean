/- The clock-half factor has the opposite pure-clock response to the
kinetic factor. A bounded inverse map constructs its common-composition
graph core and the response extends to the full clock-half graph. -/
import UnifiedTheory.Audit.KFCausalClockFloorPureClockKineticResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorPureClockClockResponse
noncomputable section
open Filter MeasureTheory
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf (clockHalf half_inverse_graph clockHalf_selfAdjoint)
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse (inverseL inverseL_graph inverseL_defect)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum pure_dense)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockInverseHalf (inverse_momentum_graph inverse_momentum_domain)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockKinetic (correction)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockKineticResponse (response correction_pairing response_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumResponse (pure_pairing_real)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ)
local notation "B" => pureMomentum ε hε h
local notation "H" => clockHalf ε
local notation "R" => inverseL ε hε

theorem half_graph (f g : Hilbert) : (f,g) ∈ (H).graph ↔ f = R g := by
  rw [half_inverse_graph ε hε,inverseL_graph]

theorem inverse_correction (g : Hilbert) : R (correction ε hε h g) = correction ε hε h (R g) := by
  simp only [correction,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    KFCausalClockFloorMomentumResponse.responseOperator,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply,map_smul,map_sub,inverseL_defect]

theorem inverse_compositions (hh : h ≠ 0) (f g bg : Hilbert)
    (hg : (f,g) ∈ (H).graph) (hbg : (g,bg) ∈ (B).graph) :
    ∃ b : Hilbert, (f,b) ∈ (B).graph ∧ (b,bg+correction ε hε h g) ∈ (H).graph := by
  have he := (half_graph ε hε f g).mp hg
  refine ⟨R bg+correction ε hε h f,?_,?_⟩
  · rw [he]
    exact inverse_momentum_graph ε hε h hh g bg hbg
  · apply (half_graph ε hε _ _).mpr
    rw [map_add,inverse_correction,he]

theorem commutator (hh : h ≠ 0) (f g b k bg : Hilbert)
    (hg : (f,g) ∈ (H).graph) (hb : (f,b) ∈ (B).graph)
    (hk : (b,k) ∈ (H).graph) (hbg : (g,bg) ∈ (B).graph) :
    bg-k = -correction ε hε h g := by
  obtain ⟨b',hb',hk'⟩ := inverse_compositions ε hε h hh f g bg hg hbg
  have eb : b = b' := (B).mem_graph_snd_inj' hb hb' rfl
  have ek : k = bg+correction ε hε h g := (H).mem_graph_snd_inj' hk hk' eb
  rw [ek]
  abel

def regularGraph : Submodule ℂ (Hilbert × Hilbert) := (H).graph ⊓ (B).domain.prod (B).domain

theorem inverse_regular (hh : h ≠ 0) (g : Hilbert) (hg : g ∈ (B).domain) :
    (R g,g) ∈ regularGraph ε hε h :=
  ⟨(half_graph ε hε _ _).mpr rfl,inverse_momentum_domain ε hε h hh g hg,hg⟩

theorem regular_graph_core (hh : h ≠ 0) : (regularGraph ε hε h).topologicalClosure = (H).graph := by
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _ (fun _ hz => hz.1) (clockHalf_selfAdjoint ε).isClosed
  · rintro ⟨f,g⟩ hg
    have he := (half_graph ε hε f g).mp hg
    obtain ⟨u,hu,ht⟩ := mem_closure_iff_seq_limit.mp ((pure_dense ε hε h) g)
    have hp := ((R).continuous.continuousAt.tendsto.comp ht).prodMk_nhds ht
    rw [← he] at hp
    exact mem_closure_of_tendsto hp (Filter.Eventually.of_forall (fun n => inverse_regular ε hε h hh (u n) (hu n)))

theorem weak_response (hh : h ≠ 0) (f g b k bg : Hilbert)
    (hg : (f,g) ∈ (H).graph) (hb : (f,b) ∈ (B).graph)
    (hk : (b,k) ∈ (H).graph) (hbg : (g,bg) ∈ (B).graph) :
    (-2/h)*(inner ℂ g k).im = -response ε hε g := by
  have he := congrArg (fun u : Hilbert => (inner ℂ g u).im)
    (commutator ε hε h hh f g b k bg hg hb hk hbg)
  change (inner ℂ g (bg-k)).im = (inner ℂ g (-correction ε hε h g)).im at he
  rw [inner_sub_right,Complex.sub_im,inner_neg_right,Complex.neg_im,
    pure_pairing_real ε hε h hh g bg hbg,zero_sub] at he
  rw [← correction_pairing ε hε h hh g]
  linear_combination (2/h)*he

local notation "G" => regularGraph ε hε h
def inputMomentum (z : G) : Hilbert := (B) ⟨z.val.1,z.property.2.1⟩
def outputMomentum (z : G) : Hilbert := (B) ⟨z.val.2,z.property.2.2⟩
def halfMomentum (z : G) : Hilbert := outputMomentum ε hε h z+correction ε hε h z.val.2
def weakRate (z : G) : ℝ := (-2/h)*(inner ℂ z.val.2 (halfMomentum ε hε h z)).im
def graphResponse (z : Hilbert × Hilbert) : ℝ := -response ε hε z.2

theorem halfMomentum_graph (hh : h ≠ 0) (z : G) :
    (inputMomentum ε hε h z,halfMomentum ε hε h z) ∈ (H).graph := by
  obtain ⟨b,hb,hk⟩ := inverse_compositions ε hε h hh z.val.1 z.val.2 (outputMomentum ε hε h z)
    z.property.1 ((B).mem_graph ⟨z.val.2,z.property.2.2⟩)
  have he : inputMomentum ε hε h z = b := (B).mem_graph_snd_inj'
    ((B).mem_graph ⟨z.val.1,z.property.2.1⟩) hb rfl
  simpa only [he] using hk

theorem weakRate_eq (hh : h ≠ 0) (z : G) : weakRate ε hε h z = graphResponse ε hε z.val :=
  weak_response ε hε h hh z.val.1 z.val.2 (inputMomentum ε hε h z) (halfMomentum ε hε h z)
    (outputMomentum ε hε h z) z.property.1 ((B).mem_graph ⟨z.val.1,z.property.2.1⟩)
      (halfMomentum_graph ε hε h hh z) ((B).mem_graph ⟨z.val.2,z.property.2.2⟩)

theorem response_bounds (f g : Hilbert) :
    -(1/(4*ε))*‖g‖^2 ≤ graphResponse ε hε (f,g) ∧ graphResponse ε hε (f,g) ≤ 0 := by
  have hb := KFCausalClockFloorPureClockKineticResponse.response_bounds ε hε g
  change -(1/(4*ε))*‖g‖^2 ≤ -response ε hε g ∧ -response ε hε g ≤ 0
  constructor <;> linarith

theorem response_input (f g : Hilbert) (hg : (f,g) ∈ (H).graph) :
    graphResponse ε hε (f,g) = -(inner ℂ f (KFCausalClockFloorMomentumResponse.responseOperator ε hε f)).re := by
  have hp : (inner ℂ g (KFCausalClockFloorPureClockKineticResponse.multiplier ε hε g)).re =
      ε*(inner ℂ f (KFCausalClockFloorMomentumResponse.responseOperator ε hε f)).re := by
    rw [KFCausalClockFloorPureClockKineticResponse.pairing_integral,
      KFCausalClockFloorInitialDriftPairing.real_multiplier_pairing volume _ _ _
        (KFCausalClockFloorMomentumResponse.responseOperator_coe ε hε f),← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [(KFCausalClockFloorClockHalf.clockHalf_graph ε f g).mp hg] with x hx
    rw [hx,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
      KFCausalClockFloorClockHalf.halfWeight,Real.sq_sqrt (by positivity)]
    unfold KFCausalClockFloorCanonicalDefect.defect KFCausalClockFloorFlow.clock
    have hn : Real.exp x.1+ε ≠ 0 := by positivity
    field_simp [hn]
  change -((1/ε)*(inner ℂ g (KFCausalClockFloorPureClockKineticResponse.multiplier ε hε g)).re) = _
  rw [hp,← mul_assoc,one_div,inv_mul_cancel₀ hε.ne',one_mul]

theorem response_norm_bound (f g : Hilbert) (hg : (f,g) ∈ (H).graph) :
    -‖f‖^2 ≤ graphResponse ε hε (f,g) ∧ graphResponse ε hε (f,g) ≤ 0 := by
  have hu := (response_bounds ε hε f g).2
  have hb := (re_inner_le_norm (𝕜 := ℂ) f (KFCausalClockFloorMomentumResponse.responseOperator ε hε f)).trans
    (mul_le_mul_of_nonneg_left (KFCausalClockFloorMomentumResponse.responseOperator_norm ε hε f) (norm_nonneg f))
  refine ⟨?_,hu⟩
  rw [response_input ε hε f g hg]
  exact neg_le_neg (by simpa only [pow_two] using hb)

theorem core_rate_approximation (hh : h ≠ 0) (f g : Hilbert) (hg : (f,g) ∈ (H).graph) :
    ∃ z : ℕ → G, Tendsto (fun n => (z n).val) atTop (𝓝 (f,g)) ∧
      Tendsto (fun n => weakRate ε hε h (z n)) atTop (𝓝 (graphResponse ε hε (f,g))) := by
  have hc : (f,g) ∈ (regularGraph ε hε h).topologicalClosure := by
    rw [regular_graph_core ε hε h hh]
    exact hg
  obtain ⟨w,hw,ht⟩ := mem_closure_iff_seq_limit.mp hc
  let z : ℕ → G := fun n => ⟨w n,hw n⟩
  refine ⟨z,ht,?_⟩
  have hr := (((response_continuous ε hε).comp continuous_snd).neg).continuousAt.tendsto.comp ht
  exact hr.congr' (Filter.Eventually.of_forall (fun n => (weakRate_eq ε hε h hh (z n)).symm))

theorem extension_unique (hh : h ≠ 0) (F : Hilbert × Hilbert → ℝ)
    (hF : ContinuousOn F ((H).graph : Set (Hilbert × Hilbert)))
    (hagree : ∀ z : G, F z.val = weakRate ε hε h z) :
    ∀ z ∈ (H).graph, F z = graphResponse ε hε z := by
  rintro ⟨f,g⟩ hg
  obtain ⟨z,hz,hr⟩ := core_rate_approximation ε hε h hh f g hg
  have ht : Tendsto (fun n => (z n).val) atTop (𝓝[((H).graph : Set (Hilbert × Hilbert))] (f,g)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hz,Filter.Eventually.of_forall (fun n => (z n).property.1)⟩
  have hl := (hF (f,g) hg).tendsto.comp ht
  exact tendsto_nhds_unique hl (hr.congr' (Filter.Eventually.of_forall (fun n => (hagree (z n)).symm)))

#print axioms half_graph
#print axioms inverse_correction
#print axioms inverse_compositions
#print axioms commutator
#print axioms inverse_regular
#print axioms regular_graph_core
#print axioms weak_response
#print axioms halfMomentum_graph
#print axioms weakRate_eq
#print axioms response_bounds
#print axioms response_input
#print axioms response_norm_bound
#print axioms core_rate_approximation
#print axioms extension_unique
end
end UnifiedTheory.Audit.KFCausalClockFloorPureClockClockResponse
