/- Two distinct instantaneous Hamiltonian graphs determine the actual
growing-operator graph. The resulting estimate uses both graph outputs; it
does not give a bound in one instantaneous graph norm or flow invariance. -/
import UnifiedTheory.Audit.KFCausalClockFloorGrowingCommonDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClockFloorTwoTimeGrowingGraph
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorAveragedFormTransport
open KFCausalClockFloorAveragedRegularity
open KFCausalBoundedFormCurve (gram formOperator)

private theorem difference_pairing
    {X Y Z : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
    (J : X →L[ℂ] Y) (A B : X →L[ℂ] Z) (s t : ℝ)
    (hc : Real.exp (2*t)-Real.exp (2*s) ≠ 0) (u : X) (y z : Y)
    (hs : ∀ v, inner ℂ u (formOperator A B s v)=inner ℂ y (J v))
    (ht : ∀ v, inner ℂ u (formOperator A B t v)=inner ℂ z (J v)) (v : X) :
    inner ℂ (B u) (B v)=
      inner ℂ ((Real.exp (2*t)-Real.exp (2*s))⁻¹ • (z-y)) (J v) := by
  have hd : (Real.exp (2*t)-Real.exp (2*s)) • inner ℂ (B u) (B v)=
      inner ℂ (z-y) (J v) := by
    rw [inner_sub_left,← ht v,← hs v]
    simp only [formOperator,gram,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
      inner_add_right,inner_smul_right_eq_smul,ContinuousLinearMap.adjoint_inner_right,
      sub_smul]
    abel
  have he := congrArg (fun q : ℂ => (Real.exp (2*t)-Real.exp (2*s))⁻¹ • q) hd
  simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul,inner_smul_left_eq_smul] using he

private theorem exp_difference_ne_zero (s t : ℝ) (hst : s ≠ t) :
    Real.exp (2*t)-Real.exp (2*s) ≠ 0 := by
  apply sub_ne_zero.mpr
  intro he
  have ht := Real.exp_injective he
  exact hst (by linarith)

private theorem difference_norm_bound
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (c : ℝ) (y z : X) : ‖c⁻¹ • (z-y)‖ ≤ |c|⁻¹*(‖z‖+‖y‖) := by
  rw [norm_smul,Real.norm_eq_abs,abs_inv]
  exact mul_le_mul_of_nonneg_left (norm_sub_le z y) (inv_nonneg.mpr (abs_nonneg c))

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum : ℝ)
local notation "V" => FormSpace ε hε h hh hb mass2 quartic vacuum 0
local notation "J" => embedding ε hε h hh hb mass2 quartic vacuum 0
local notation "A" => staticMap ε hε h hh hb mass2 quartic vacuum
local notation "B" => growingMap ε hε h hh hb mass2 quartic vacuum
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hb mass2 quartic vacuum
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hb mass2 quartic vacuum

theorem difference_graph (s t : ℝ) (hst : s ≠ t) (x y z : Hilbert)
    (hs : (x,y) ∈ (H s).graph) (ht : (x,z) ∈ (H t).graph) :
    (x,(Real.exp (2*t)-Real.exp (2*s))⁻¹ • (z-y)) ∈ (G).graph := by
  let u : V := KFCausalClockFloorAveragedHamiltonianBridge.referenceLift
    ε hε h hh hb mass2 quartic vacuum s
    ⟨x,LinearPMap.mem_domain_of_mem_graph hs⟩
  have hj : J u=x :=
    KFCausalClockFloorAveragedHamiltonianBridge.embedding_referenceLift
      ε hε h hh hb mass2 quartic vacuum s _
  have hs' : (J u,y) ∈ (H s).graph := by simpa only [hj] using hs
  have ht' : (J u,z) ∈ (H t).graph := by simpa only [hj] using ht
  have hp := (KFCausalClockFloorAveragedHamiltonianBridge.hamiltonian_reference_domain
    ε hε h hh hb mass2 quartic vacuum s u y).mp
      ((KFCausalMassFormOperator.graph_domain_iff (H s) (J u) y).mp hs')
  have hq := (KFCausalClockFloorAveragedHamiltonianBridge.hamiltonian_reference_domain
    ε hε h hh hb mass2 quartic vacuum t u z).mp
      ((KFCausalMassFormOperator.graph_domain_iff (H t) (J u) z).mp ht')
  have hg := (KFCausalMassFormOperator.graph_domain_iff G (J u)
    ((Real.exp (2*t)-Real.exp (2*s))⁻¹ • (z-y))).mpr
      ((KFCausalClockFloorGrowingHamiltonian.reference_domain_characterization
        ε hε h hh hb mass2 quartic vacuum u _).mpr
          (difference_pairing J A B s t (exp_difference_ne_zero s t hst) u y z hp hq))
  simpa only [hj] using hg

theorem two_time_domain_eq (s t : ℝ) (hst : s ≠ t) :
    (H s).domain ⊓ (H t).domain=(H s).domain ⊓ (G).domain := by
  ext x
  constructor
  · rintro ⟨hs,ht⟩
    exact ⟨hs,LinearPMap.mem_domain_of_mem_graph
      (difference_graph ε hε h hh hb mass2 quartic vacuum s t hst x
        (H s ⟨x,hs⟩) (H t ⟨x,ht⟩) ((H s).mem_graph ⟨x,hs⟩)
          ((H t).mem_graph ⟨x,ht⟩))⟩
  · rintro ⟨hs,hg⟩
    exact ⟨hs,LinearPMap.mem_domain_of_mem_graph
      (KFCausalClockFloorGrowingCommonDomain.affine_graph
        ε hε h hh hb mass2 quartic vacuum s t x (H s ⟨x,hs⟩) (G ⟨x,hg⟩)
          ((H s).mem_graph ⟨x,hs⟩) ((G).mem_graph ⟨x,hg⟩))⟩

theorem growing_output_eq (s t : ℝ) (hst : s ≠ t) (x : Hilbert)
    (hs : x ∈ (H s).domain) (ht : x ∈ (H t).domain) (hg : x ∈ (G).domain) :
    G ⟨x,hg⟩=(Real.exp (2*t)-Real.exp (2*s))⁻¹ • (H t ⟨x,ht⟩-H s ⟨x,hs⟩) :=
  (G).mem_graph_snd_inj' ((G).mem_graph ⟨x,hg⟩)
    (difference_graph ε hε h hh hb mass2 quartic vacuum s t hst x
      (H s ⟨x,hs⟩) (H t ⟨x,ht⟩) ((H s).mem_graph ⟨x,hs⟩)
        ((H t).mem_graph ⟨x,ht⟩)) rfl

theorem growing_norm_bound (s t : ℝ) (hst : s ≠ t) (x : Hilbert)
    (hs : x ∈ (H s).domain) (ht : x ∈ (H t).domain) (hg : x ∈ (G).domain) :
    ‖G ⟨x,hg⟩‖ ≤ |Real.exp (2*t)-Real.exp (2*s)|⁻¹*
      (‖H t ⟨x,ht⟩‖+‖H s ⟨x,hs⟩‖) := by
  rw [growing_output_eq ε hε h hh hb mass2 quartic vacuum s t hst x hs ht hg]
  exact difference_norm_bound _ _ _

#print axioms difference_graph
#print axioms two_time_domain_eq
#print axioms growing_output_eq
#print axioms growing_norm_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorTwoTimeGrowingGraph
