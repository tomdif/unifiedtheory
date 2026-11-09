/- The unscaled kinetic-factor pure-clock response is nonnegative,
bounded by kinetic energy, and extends from a constructed graph core to
the full natural kinetic form domain. This is not a Hamiltonian evolution law. -/
import UnifiedTheory.Audit.KFCausalClockFloorPureClockKineticCore
import UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumResponse
import UnifiedTheory.Audit.KFCausalClockFloorInitialDriftPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorPureClockKineticResponse
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockKinetic
open UnifiedTheory.Audit.KFCausalClockFloorPureClockKineticCore
open UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumResponse (pure_pairing_real)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum (clockMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator (defectOperator defectOperator_coe)
open UnifiedTheory.Audit.KFCausalClockFloorMomentumResponse (responseOperator responseOperator_coe)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect response_bounds defect_positive response_add_defect)

variable (ε : ℝ) (hε : 0 < ε)
local notation "D" => defectOperator ε hε
local notation "Q" => responseOperator ε hε
local notation "q" => KFCausalClockFloorCanonicalDefect.response ε

def multiplier : Hilbert →L[ℂ] Hilbert := (D).comp Q
def response (g : Hilbert) : ℝ := (1/ε)*(inner ℂ g (multiplier ε hε g)).re

include hε in
theorem coefficient_bounds (s : ℝ) : 0 < defect ε s*q s ∧ defect ε s*q s ≤ 1/4 := by
  have hd := defect_positive ε s hε
  have hq := (response_bounds ε s hε).1
  have hs := response_add_defect ε s hε.le
  refine ⟨mul_pos hd hq,?_⟩
  nlinarith [sq_nonneg (defect ε s-q s)]

theorem multiplier_coe (g : Hilbert) : multiplier ε hε g =ᵐ[volume]
    fun x => ((defect ε x.1*q x.1:ℝ):ℂ)*g x := by
  filter_upwards [defectOperator_coe ε hε (Q g),responseOperator_coe ε hε g] with x hd hq
  change D (Q g) x = _
  rw [hd,hq,Complex.ofReal_mul,mul_assoc]

theorem multiplier_bound (g : Hilbert) : ‖multiplier ε hε g‖ ≤ (1/4)*‖g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [multiplier_coe ε hε g] with x hx
  rw [hx,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (coefficient_bounds ε hε x.1).1]
  exact mul_le_mul_of_nonneg_right (coefficient_bounds ε hε x.1).2 (norm_nonneg _)

theorem pairing_integral (g : Hilbert) :
    (inner ℂ g (multiplier ε hε g)).re = ∫ x, (defect ε x.1*q x.1)*‖g x‖^2 :=
  KFCausalClockFloorInitialDriftPairing.real_multiplier_pairing volume _ _ _ (multiplier_coe ε hε g)

theorem response_bounds (g : Hilbert) :
    0 ≤ response ε hε g ∧ response ε hε g ≤ (1/(4*ε))*‖g‖^2 := by
  have hp : 0 ≤ (inner ℂ g (multiplier ε hε g)).re := by
    rw [pairing_integral]
    exact integral_nonneg (fun x => mul_nonneg (coefficient_bounds ε hε x.1).1.le (sq_nonneg _))
  refine ⟨mul_nonneg (by positivity) hp,?_⟩
  have hb := (re_inner_le_norm (𝕜 := ℂ) g (multiplier ε hε g)).trans
    (mul_le_mul_of_nonneg_left (multiplier_bound ε hε g) (norm_nonneg g))
  exact (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 1/ε)).trans_eq (by ring)

theorem response_continuous : Continuous (response ε hε) :=
  continuous_const.mul (Complex.continuous_re.comp (continuous_id.inner (multiplier ε hε).continuous))

theorem correction_bound (h : ℝ) (g : Hilbert) :
    ‖correction ε hε h g‖ ≤ (|h|/(8*ε))*‖g‖ := by
  change ‖(Complex.I*(h:ℂ)/(2*(ε:ℂ))) • multiplier ε hε g‖ ≤ _
  rw [norm_smul,norm_div,norm_mul,Complex.norm_I,one_mul,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε]
  norm_num only [Complex.norm_ofNat]
  exact (mul_le_mul_of_nonneg_left (multiplier_bound ε hε g)
    (by positivity : 0 ≤ |h|/(2*ε))).trans_eq (by ring)

theorem correction_pairing (h : ℝ) (hh : h ≠ 0) (g : Hilbert) :
    (2/h)*(inner ℂ g (correction ε hε h g)).im = response ε hε g := by
  change (2/h)*(inner ℂ g ((Complex.I*(h:ℂ)/(2*(ε:ℂ))) • multiplier ε hε g)).im = _
  have hc : Complex.I*(h:ℂ)/(2*(ε:ℂ)) = ((h/(2*ε):ℝ):ℂ)*Complex.I := by push_cast; ring
  rw [inner_smul_right,hc]
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_mul,sub_zero,add_zero,zero_add]
  unfold response
  field_simp [hh,hε.ne']

theorem weak_response (h : ℝ) (hh : h ≠ 0) (v : Transverse) (f g b k : Hilbert)
    (hg : (f,g) ∈ (clockMomentum ε h v).graph) (hb : (f,b) ∈ (pureMomentum ε hε h).graph)
    (hk : (b,k) ∈ (clockMomentum ε h v).graph) :
    (-2/h)*(inner ℂ g k).im = response ε hε g := by
  have hr := pure_pairing_real ε hε h hh g _ (kinetic_momentum_graph ε hε h v hh f g b k hg hb hk)
  rw [inner_add_right,Complex.add_im] at hr
  rw [← correction_pairing ε hε h hh g]
  linear_combination (-2/h)*hr

variable (h : ℝ) (v : Transverse)
local notation "B" => pureMomentum ε hε h
local notation "K" => clockMomentum ε h v
local notation "G" => regularGraph ε hε h v

def inputMomentum (z : G) : Hilbert := (B) ⟨z.val.1,z.property.2.1⟩
def outputMomentum (z : G) : Hilbert := (B) ⟨z.val.2,z.property.2.2⟩
def kineticMomentum (z : G) : Hilbert := outputMomentum ε hε h v z-correction ε hε h z.val.2
def weakRate (z : G) : ℝ := (-2/h)*(inner ℂ z.val.2 (kineticMomentum ε hε h v z)).im
def graphResponse (z : Hilbert × Hilbert) : ℝ := response ε hε z.2

theorem kineticMomentum_graph (hh : h ≠ 0) (z : G) :
    (inputMomentum ε hε h v z,kineticMomentum ε hε h v z) ∈ (K).graph :=
  momentum_kinetic_graph ε hε h v hh z.val.1 z.val.2 (inputMomentum ε hε h v z)
    (outputMomentum ε hε h v z) z.property.1 ((B).mem_graph ⟨z.val.1,z.property.2.1⟩)
      ((B).mem_graph ⟨z.val.2,z.property.2.2⟩)

theorem weakRate_eq (hh : h ≠ 0) (z : G) : weakRate ε hε h v z = graphResponse ε hε z.val :=
  weak_response ε hε h hh v z.val.1 z.val.2 (inputMomentum ε hε h v z) (kineticMomentum ε hε h v z)
    z.property.1 ((B).mem_graph ⟨z.val.1,z.property.2.1⟩) (kineticMomentum_graph ε hε h v hh z)

theorem core_rate_approximation (hh : h ≠ 0) (f g : Hilbert) (hg : (f,g) ∈ (K).graph) :
    ∃ z : ℕ → G, Tendsto (fun n => (z n).val) atTop (𝓝 (f,g)) ∧
      Tendsto (fun n => weakRate ε hε h v (z n)) atTop (𝓝 (graphResponse ε hε (f,g))) := by
  obtain ⟨w,hw,ht⟩ := graph_approximation ε hε h v hh f g hg
  let z : ℕ → G := fun n => ⟨w n,hw n⟩
  refine ⟨z,ht,?_⟩
  have hc := ((response_continuous ε hε).comp continuous_snd).continuousAt.tendsto.comp ht
  exact hc.congr' (Filter.Eventually.of_forall (fun n => (weakRate_eq ε hε h v hh (z n)).symm))

theorem extension_unique (hh : h ≠ 0) (F : Hilbert × Hilbert → ℝ)
    (hF : ContinuousOn F ((K).graph : Set (Hilbert × Hilbert)))
    (hagree : ∀ z : G, F z.val = weakRate ε hε h v z) :
    ∀ z ∈ (K).graph, F z = graphResponse ε hε z := by
  rintro ⟨f,g⟩ hg
  obtain ⟨z,hz,hr⟩ := core_rate_approximation ε hε h v hh f g hg
  have ht : Tendsto (fun n => (z n).val) atTop (𝓝[((K).graph : Set (Hilbert × Hilbert))] (f,g)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hz,Filter.Eventually.of_forall (fun n => (z n).property.1)⟩
  have hl := (hF (f,g) hg).tendsto.comp ht
  exact tendsto_nhds_unique hl (hr.congr' (Filter.Eventually.of_forall (fun n => (hagree (z n)).symm)))

#print axioms coefficient_bounds
#print axioms multiplier_coe
#print axioms multiplier_bound
#print axioms pairing_integral
#print axioms response_bounds
#print axioms response_continuous
#print axioms correction_bound
#print axioms correction_pairing
#print axioms weak_response
#print axioms kineticMomentum_graph
#print axioms weakRate_eq
#print axioms core_rate_approximation
#print axioms extension_unique
end
end UnifiedTheory.Audit.KFCausalClockFloorPureClockKineticResponse
