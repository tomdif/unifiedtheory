/- Joint cross-estimates for the three self-adjoint component operators
T (maximal static), Kr (maximal radial), and P (closed potential), combining
the positive potential-radial pairing from the growing Hamiltonian G = Kr + P
with the static-radial and residual-radial pairings from the full Hamiltonian
decomposition. Includes positive-vacuum joint bounds on Dom T ∩ Dom G. -/
import UnifiedTheory.Audit.KFCausalClockFloorResidualRadialCrossEstimate
import UnifiedTheory.Audit.KFCausalClockFloorGrowingRadialCrossEstimate
import UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumThreeOperatorDomain

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorThreeOperatorCrossEstimate
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorRadialYosidaReference (wide_bound)

private theorem sum_graph {X : Type*} [AddCommGroup X] [Module ℂ X]
    (A B : X →ₗ.[ℂ] X) (f a b : X)
    (ha : (f,a) ∈ A.graph) (hb : (f,b) ∈ B.graph) : (f,a+b) ∈ (A+B).graph := by
  have hda := LinearPMap.mem_domain_of_mem_graph ha
  have hdb := LinearPMap.mem_domain_of_mem_graph hb
  have hea : A ⟨f,hda⟩=a := A.mem_graph_snd_inj' (A.mem_graph ⟨f,hda⟩) ha rfl
  have heb : B ⟨f,hdb⟩=b := B.mem_graph_snd_inj' (B.mem_graph ⟨f,hdb⟩) hb rfl
  exact (LinearPMap.mem_graph_iff _).mpr ⟨⟨f,⟨hda,hdb⟩⟩,rfl,by
    change A ⟨f,hda⟩+B ⟨f,hdb⟩=a+b
    rw [hea,heb]⟩

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi*ε/3) (m g k t : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k t
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k t

theorem potential_radial_pairing (f r z : Hilbert)
    (hr : (f,r) ∈ (K).graph) (hp : (f,z) ∈ (P).graph) :
    0 ≤ (inner ℂ z r).re ∧ ‖r‖^2+‖z‖^2 ≤ ‖r+z‖^2 := by
  have hg : (f,r+z) ∈ (G).graph := by
    rw [KFCausalClockFloorGrowingPotentialSum.operator_sum ε hε h hh hb m g k]
    exact sum_graph (K) (P) f r z hr hp
  let x : (G).domain := ⟨f,LinearPMap.mem_domain_of_mem_graph hg⟩
  have hG : G x=r+z := (G).mem_graph_snd_inj' ((G).mem_graph x) hg rfl
  have hK : KFCausalClockFloorGrowingRadialCrossEstimate.radialOutput ε hε h hh hb m g k x=r :=
    (K).mem_graph_snd_inj' ((K).mem_graph _) hr rfl
  have hrem : KFCausalClockFloorGrowingRadialCrossEstimate.remainderOutput ε hε h hh hb m g k x=z := by
    unfold KFCausalClockFloorGrowingRadialCrossEstimate.remainderOutput
    rw [hG,hK]
    abel
  have hp' := KFCausalClockFloorGrowingRadialCrossEstimate.remainder_pairing ε hε h hh hb m g k x
  have hs' := KFCausalClockFloorGrowingRadialCrossEstimate.split_norm_square ε hε h hh hb m g k x
  exact ⟨by simpa only [hK,hrem] using hp',by simpa only [hG,hK,hrem] using hs'⟩

theorem three_operator_radial_pairing (f y r z : Hilbert)
    (ht : (f,y) ∈ (T).graph) (hr : (f,r) ∈ (K).graph) (hp : (f,z) ∈ (P).graph) :
    -(h^2/ε^2)*‖f‖^2 ≤ (inner ℂ (y+(Real.exp (2*t):ℂ) • z) r).re := by
  have hstat := KFCausalClockFloorResidualRadialCrossEstimate.static_radial_pairing
    ε hε h hh hb f y r ht hr
  have hpot := (potential_radial_pairing ε hε h hh hb m g k f r z hr hp).1
  have hmul : 0 ≤ Real.exp (2*t)*(inner ℂ z r).re :=
    mul_nonneg (Real.exp_pos (2*t)).le hpot
  rw [inner_add_left,inner_smul_left,Complex.conj_ofReal,
    Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]
  linarith

theorem three_operator_residual_sum_norm_sq (f y r z : Hilbert)
    (ht : (f,y) ∈ (T).graph) (hr : (f,r) ∈ (K).graph) (hp : (f,z) ∈ (P).graph) :
    Real.exp (4*t)*‖r‖^2+‖y+(Real.exp (2*t):ℂ) • z‖^2 ≤
      ‖y+(Real.exp (2*t):ℂ) • (r+z)‖^2+2*Real.exp (2*t)*(h^2/ε^2)*‖f‖^2 := by
  let s := y+(Real.exp (2*t):ℂ) • z
  have hp' := three_operator_radial_pairing ε hε h hh hb m g k t f y r z ht hr hp
  have hm := mul_le_mul_of_nonneg_left hp' (show 0 ≤ 2*Real.exp (2*t) by positivity)
  have he : Real.exp (2*t)^2=Real.exp (4*t) := by
    rw [sq,← Real.exp_add,show 2*t+2*t=4*t by ring]
  have hn : ‖(Real.exp (2*t):ℂ) • r‖^2=Real.exp (4*t)*‖r‖^2 := by
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos (2*t)),mul_pow,he]
  have hi : (inner ℂ s ((Real.exp (2*t):ℂ) • r)).re=
      Real.exp (2*t)*(inner ℂ s r).re := by
    rw [inner_smul_right,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hsum : y+(Real.exp (2*t):ℂ) • (r+z)=s+(Real.exp (2*t):ℂ) • r := by
    dsimp [s]
    rw [smul_add]
    abel
  have hexp : ‖s+(Real.exp (2*t):ℂ) • r‖^2=
      ‖s‖^2+2*(inner ℂ s ((Real.exp (2*t):ℂ) • r)).re+‖(Real.exp (2*t):ℂ) • r‖^2 :=
    norm_add_sq (𝕜 := ℂ) s ((Real.exp (2*t):ℂ) • r)
  change Real.exp (4*t)*‖r‖^2+‖s‖^2 ≤
    ‖y+(Real.exp (2*t):ℂ) • (r+z)‖^2+2*Real.exp (2*t)*(h^2/ε^2)*‖f‖^2
  rw [hsum,hexp,hn,hi]
  change -(h^2/ε^2)*‖f‖^2 ≤ (inner ℂ s r).re at hp'
  nlinarith [Real.exp_pos (2*t)]

theorem three_operator_component_norm_sq (f y r z : Hilbert)
    (ht : (f,y) ∈ (T).graph) (hr : (f,r) ∈ (K).graph) (hp : (f,z) ∈ (P).graph) :
    Real.exp (4*t)*(‖r‖^2+‖z‖^2)+‖y+(Real.exp (2*t):ℂ) • z‖^2 ≤
      ‖y+(Real.exp (2*t):ℂ) • (r+z)‖^2+Real.exp (4*t)*‖r+z‖^2+
        2*Real.exp (2*t)*(h^2/ε^2)*‖f‖^2 := by
  have hpot := mul_le_mul_of_nonneg_left
    (potential_radial_pairing ε hε h hh hb m g k f r z hr hp).2
    (Real.exp_pos (4*t)).le
  have hres := three_operator_residual_sum_norm_sq ε hε h hh hb m g k t f y r z ht hr hp
  have hr0 : 0 ≤ Real.exp (4*t)*‖r‖^2 := by positivity
  linarith

theorem positive_vacuum_hamiltonian_cross_estimate (hk : 0 < k)
    (f y r z : Hilbert)
    (ht : (f,y) ∈ (T).graph) (hr : (f,r) ∈ (K).graph) (hp : (f,z) ∈ (P).graph) :
    (f,y+(Real.exp (2*t):ℂ) • z) ∈ (S).graph ∧
      (f,y+(Real.exp (2*t):ℂ) • (r+z)) ∈ (H).graph ∧
      0 ≤ (inner ℂ z r).re ∧
      -(h^2/ε^2)*‖f‖^2 ≤ (inner ℂ (y+(Real.exp (2*t):ℂ) • z) r).re ∧
      Real.exp (4*t)*‖r‖^2+‖y+(Real.exp (2*t):ℂ) • z‖^2 ≤
        ‖y+(Real.exp (2*t):ℂ) • (r+z)‖^2+2*Real.exp (2*t)*(h^2/ε^2)*‖f‖^2 := by
  have hs := KFCausalClockFloorPositiveVacuumThreeOperatorDomain.three_operator_residual_graph
    ε hε h hh hb m g k t hk f y r z ht hr hp
  have hh_g := KFCausalClockFloorPositiveVacuumThreeOperatorDomain.three_operator_hamiltonian_graph
    ε hε h hh hb m g k t hk f y r z ht hr hp
  have hpot := (potential_radial_pairing ε hε h hh hb m g k f r z hr hp).1
  have hH := KFCausalClockFloorHamiltonianRadialCrossEstimate.graph_residual_radial_pairing
    ε hε h hh hb m g k t f (y+(Real.exp (2*t):ℂ) • (r+z)) r (y+(Real.exp (2*t):ℂ) • z)
    hh_g hr hs
  exact ⟨hs,hh_g,hpot,hH.1,hH.2⟩

theorem positive_vacuum_static_growing_cross_estimate (hk : 0 < k)
    (f y g_out : Hilbert)
    (ht : (f,y) ∈ (T).graph) (hg : (f,g_out) ∈ (G).graph) :
    let xG : (G).domain := ⟨f,LinearPMap.mem_domain_of_mem_graph hg⟩
    let r := KFCausalClockFloorGrowingRadialCrossEstimate.radialOutput ε hε h hh hb m g k xG
    let z := KFCausalClockFloorGrowingRadialCrossEstimate.remainderOutput ε hε h hh hb m g k xG
    ‖r‖^2+‖z‖^2 ≤ ‖g_out‖^2 ∧
      (f,y+(Real.exp (2*t):ℂ) • z) ∈ (S).graph ∧
      (f,y+(Real.exp (2*t):ℂ) • g_out) ∈ (H).graph ∧
      Real.exp (4*t)*‖r‖^2+‖y+(Real.exp (2*t):ℂ) • z‖^2 ≤
        ‖y+(Real.exp (2*t):ℂ) • g_out‖^2+2*Real.exp (2*t)*(h^2/ε^2)*‖f‖^2 := by
  let xG : (G).domain := ⟨f,LinearPMap.mem_domain_of_mem_graph hg⟩
  let r := KFCausalClockFloorGrowingRadialCrossEstimate.radialOutput ε hε h hh hb m g k xG
  let z := KFCausalClockFloorGrowingRadialCrossEstimate.remainderOutput ε hε h hh hb m g k xG
  have hG : G xG=g_out := (G).mem_graph_snd_inj' ((G).mem_graph xG) hg rfl
  have hr : (f,r) ∈ (K).graph :=
    (K).mem_graph ⟨f,KFCausalClockFloorGrowingRadialDomination.radial_domain ε hε h hh hb m g k xG⟩
  have hp : (f,z) ∈ (P).graph :=
    KFCausalClockFloorGrowingPotentialSum.potential_graph ε hε h hh hb m g k xG
  have hrz : r+z=g_out := by
    dsimp [r,z]
    unfold KFCausalClockFloorGrowingRadialCrossEstimate.remainderOutput
    rw [hG]
    abel
  have hsplit : ‖r‖^2+‖z‖^2 ≤ ‖g_out‖^2 := by
    simpa only [hG] using
      KFCausalClockFloorGrowingRadialCrossEstimate.split_norm_square ε hε h hh hb m g k xG
  have hs : (f,y+(Real.exp (2*t):ℂ) • z) ∈ (S).graph :=
    KFCausalClockFloorPositiveVacuumThreeOperatorDomain.three_operator_residual_graph
      ε hε h hh hb m g k t hk f y r z ht hr hp
  have hh_g : (f,y+(Real.exp (2*t):ℂ) • g_out) ∈ (H).graph := by
    rw [← hrz]
    exact KFCausalClockFloorPositiveVacuumThreeOperatorDomain.three_operator_hamiltonian_graph
      ε hε h hh hb m g k t hk f y r z ht hr hp
  have hcross := (KFCausalClockFloorHamiltonianRadialCrossEstimate.graph_residual_radial_pairing
    ε hε h hh hb m g k t f (y+(Real.exp (2*t):ℂ) • g_out) r (y+(Real.exp (2*t):ℂ) • z)
    hh_g hr hs).2
  exact ⟨hsplit,hs,hh_g,hcross⟩

#print axioms potential_radial_pairing
#print axioms three_operator_radial_pairing
#print axioms three_operator_residual_sum_norm_sq
#print axioms three_operator_component_norm_sq
#print axioms positive_vacuum_hamiltonian_cross_estimate
#print axioms positive_vacuum_static_growing_cross_estimate
end
end UnifiedTheory.Audit.KFCausalClockFloorThreeOperatorCrossEstimate
