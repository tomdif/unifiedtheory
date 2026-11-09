/- Unconditional two-time norm and cross-estimates for all real couplings and
times on the time-independent common operator domain
Dom_common = (Dom T ∩ Dom Kr ∩ Dom P) ∩ Dom Tres(0). Controls both Kr and P by
G, bounds T and Kr jointly by H(s) and P (or G) plus the clock-floor Leibniz
defect, and transfers operator norms of S(t) and H(t) across arbitrary times
with exact Lipschitz factor |exp(2t) - exp(2s)|. -/
import UnifiedTheory.Audit.KFCausalClockFloorUnconditionalHamiltonianCrossEstimate
import UnifiedTheory.Audit.KFCausalClockFloorUnconditionalTwoTimeEvolution

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorUnconditionalTwoTimeCrossEstimate
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorThreeOperatorCrossEstimate (potential_radial_pairing)
open KFCausalClockFloorUnconditionalThreeOperatorDecomposition
  (unconditional_three_operator_residual_graph)
open KFCausalClockFloorUnconditionalTwoTimeEvolution
  (commonOperatorDomain
   common_domain_subset_hamiltonian
   common_domain_subset_residual
   common_domain_subset_growing
   unconditional_two_time_residual_difference
   unconditional_two_time_hamiltonian_growing_difference)

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

private theorem norm_sq_sub_le_two {X : Type*} [SeminormedAddCommGroup X] (u v : X) :
    ‖u-v‖^2 ≤ 2*‖u‖^2+2*‖v‖^2 := by
  have htri : ‖u-v‖ ≤ ‖u‖+‖v‖ := norm_sub_le u v
  have hsq : ‖u-v‖^2 ≤ (‖u‖+‖v‖)^2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr htri
  nlinarith [sq_nonneg (‖u‖-‖v‖)]

private theorem norm_le_add_norm_sub {X : Type*} [SeminormedAddCommGroup X] (u v : X) :
    ‖u‖ ≤ ‖v‖+‖u-v‖ := by
  have heq : u=v+(u-v) := by abel
  calc
    ‖u‖ = ‖v+(u-v)‖ := congrArg norm heq
    _ ≤ ‖v‖+‖u-v‖ := norm_add_le v (u-v)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi*ε/3) (m g k : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k

theorem unconditional_radial_potential_norm_le_growing (x : Hilbert)
    (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    ‖(K) ⟨x,hx.1.1.2⟩‖^2+‖(P) ⟨x,hx.1.2⟩‖^2 ≤
        ‖(G) ⟨x,common_domain_subset_growing ε hε h hh hb m g k hx⟩‖^2 ∧
      ‖(K) ⟨x,hx.1.1.2⟩‖ ≤
        ‖(G) ⟨x,common_domain_subset_growing ε hε h hh hb m g k hx⟩‖ ∧
      ‖(P) ⟨x,hx.1.2⟩‖ ≤
        ‖(G) ⟨x,common_domain_subset_growing ε hε h hh hb m g k hx⟩‖ := by
  have hg' : (x,(K) ⟨x,hx.1.1.2⟩+(P) ⟨x,hx.1.2⟩) ∈ (G).graph := by
    rw [KFCausalClockFloorGrowingPotentialSum.operator_sum ε hε h hh hb m g k]
    exact sum_graph (K) (P) x ((K) ⟨x,hx.1.1.2⟩) ((P) ⟨x,hx.1.2⟩)
      ((K).mem_graph ⟨x,hx.1.1.2⟩) ((P).mem_graph ⟨x,hx.1.2⟩)
  have hG_eq : (G) ⟨x,common_domain_subset_growing ε hε h hh hb m g k hx⟩=
      (K) ⟨x,hx.1.1.2⟩+(P) ⟨x,hx.1.2⟩ :=
    (G).mem_graph_snd_inj'
      ((G).mem_graph ⟨x,common_domain_subset_growing ε hε h hh hb m g k hx⟩) hg' rfl
  have hsq : ‖(K) ⟨x,hx.1.1.2⟩‖^2+‖(P) ⟨x,hx.1.2⟩‖^2 ≤
      ‖(G) ⟨x,common_domain_subset_growing ε hε h hh hb m g k hx⟩‖^2 := by
    rw [hG_eq]
    exact (potential_radial_pairing ε hε h hh hb m g k x ((K) ⟨x,hx.1.1.2⟩) ((P) ⟨x,hx.1.2⟩)
      ((K).mem_graph ⟨x,hx.1.1.2⟩) ((P).mem_graph ⟨x,hx.1.2⟩)).2
  have hK : ‖(K) ⟨x,hx.1.1.2⟩‖ ≤
      ‖(G) ⟨x,common_domain_subset_growing ε hε h hh hb m g k hx⟩‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    nlinarith [sq_nonneg ‖(P) ⟨x,hx.1.2⟩‖]
  have hP : ‖(P) ⟨x,hx.1.2⟩‖ ≤
      ‖(G) ⟨x,common_domain_subset_growing ε hε h hh hb m g k hx⟩‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    nlinarith [sq_nonneg ‖(K) ⟨x,hx.1.1.2⟩‖]
  exact ⟨hsq,hK,hP⟩

theorem unconditional_static_norm_sq_bound (s : ℝ) (x : Hilbert)
    (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    ‖(T) ⟨x,hx.1.1.1⟩‖^2 ≤
      2*‖S s ⟨x,common_domain_subset_residual ε hε h hh hb m g k s hx⟩‖^2+
        2*Real.exp (4*s)*‖(P) ⟨x,hx.1.2⟩‖^2 := by
  have hs_graph := unconditional_three_operator_residual_graph ε hε h hh hb m g k s
    x ((T) ⟨x,hx.1.1.1⟩) ((P) ⟨x,hx.1.2⟩)
    ((T).mem_graph ⟨x,hx.1.1.1⟩) ((P).mem_graph ⟨x,hx.1.2⟩) hx.2
  have hs_eq : S s ⟨x,common_domain_subset_residual ε hε h hh hb m g k s hx⟩=
      (T) ⟨x,hx.1.1.1⟩+(Real.exp (2*s):ℂ) • (P) ⟨x,hx.1.2⟩ :=
    (S s).mem_graph_snd_inj'
      ((S s).mem_graph ⟨x,common_domain_subset_residual ε hε h hh hb m g k s hx⟩)
      hs_graph rfl
  have ht_eq : (T) ⟨x,hx.1.1.1⟩=
      S s ⟨x,common_domain_subset_residual ε hε h hh hb m g k s hx⟩-
        (Real.exp (2*s):ℂ) • (P) ⟨x,hx.1.2⟩ := by
    rw [hs_eq]
    abel
  have hsub := norm_sq_sub_le_two
    (S s ⟨x,common_domain_subset_residual ε hε h hh hb m g k s hx⟩)
    ((Real.exp (2*s):ℂ) • (P) ⟨x,hx.1.2⟩)
  have he : Real.exp (2*s)^2=Real.exp (4*s) := by
    rw [sq,← Real.exp_add,show 2*s+2*s=4*s by ring]
  have hn : ‖(Real.exp (2*s):ℂ) • (P) ⟨x,hx.1.2⟩‖^2=
      Real.exp (4*s)*‖(P) ⟨x,hx.1.2⟩‖^2 := by
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos (2*s)),mul_pow,he]
  rw [ht_eq]
  linarith

theorem unconditional_static_radial_domination (s : ℝ) (x : Hilbert)
    (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    ‖(T) ⟨x,hx.1.1.1⟩‖^2+2*Real.exp (4*s)*‖(K) ⟨x,hx.1.1.2⟩‖^2 ≤
        2*‖H s ⟨x,common_domain_subset_hamiltonian ε hε h hh hb m g k s hx⟩‖^2+
          2*Real.exp (4*s)*‖(P) ⟨x,hx.1.2⟩‖^2+
          4*Real.exp (2*s)*(h^2/ε^2)*‖x‖^2 ∧
      ‖(T) ⟨x,hx.1.1.1⟩‖^2+2*Real.exp (4*s)*‖(K) ⟨x,hx.1.1.2⟩‖^2 ≤
        2*‖H s ⟨x,common_domain_subset_hamiltonian ε hε h hh hb m g k s hx⟩‖^2+
          2*Real.exp (4*s)*‖(G) ⟨x,common_domain_subset_growing ε hε h hh hb m g k hx⟩‖^2+
          4*Real.exp (2*s)*(h^2/ε^2)*‖x‖^2 := by
  have hT := unconditional_static_norm_sq_bound ε hε h hh hb m g k s x hx
  have hH := (KFCausalClockFloorHamiltonianRadialCrossEstimate.graph_residual_radial_pairing
    ε hε h hh hb m g k s x
    (H s ⟨x,common_domain_subset_hamiltonian ε hε h hh hb m g k s hx⟩)
    ((K) ⟨x,hx.1.1.2⟩)
    (S s ⟨x,common_domain_subset_residual ε hε h hh hb m g k s hx⟩)
    ((H s).mem_graph ⟨x,common_domain_subset_hamiltonian ε hε h hh hb m g k s hx⟩)
    ((K).mem_graph ⟨x,hx.1.1.2⟩)
    ((S s).mem_graph ⟨x,common_domain_subset_residual ε hε h hh hb m g k s hx⟩)).2
  have h1 : ‖(T) ⟨x,hx.1.1.1⟩‖^2+2*Real.exp (4*s)*‖(K) ⟨x,hx.1.1.2⟩‖^2 ≤
      2*‖H s ⟨x,common_domain_subset_hamiltonian ε hε h hh hb m g k s hx⟩‖^2+
        2*Real.exp (4*s)*‖(P) ⟨x,hx.1.2⟩‖^2+
        4*Real.exp (2*s)*(h^2/ε^2)*‖x‖^2 := by
    linarith
  have hPG := (unconditional_radial_potential_norm_le_growing ε hε h hh hb m g k x hx).1
  have h2_aux : 2*Real.exp (4*s)*‖(P) ⟨x,hx.1.2⟩‖^2 ≤
      2*Real.exp (4*s)*‖(G) ⟨x,common_domain_subset_growing ε hε h hh hb m g k hx⟩‖^2 := by
    have hP_le : ‖(P) ⟨x,hx.1.2⟩‖^2 ≤
        ‖(G) ⟨x,common_domain_subset_growing ε hε h hh hb m g k hx⟩‖^2 := by
      nlinarith [sq_nonneg ‖(K) ⟨x,hx.1.1.2⟩‖]
    exact mul_le_mul_of_nonneg_left hP_le (by positivity)
  exact ⟨h1,by linarith⟩

theorem unconditional_two_time_residual_norm_diff (t s : ℝ) (x : Hilbert)
    (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    ‖S t ⟨x,common_domain_subset_residual ε hε h hh hb m g k t hx⟩-
      S s ⟨x,common_domain_subset_residual ε hε h hh hb m g k s hx⟩‖=
      |Real.exp (2*t)-Real.exp (2*s)| *‖(P) ⟨x,hx.1.2⟩‖ := by
  rw [unconditional_two_time_residual_difference ε hε h hh hb m g k t s x hx,
    norm_smul,Complex.norm_real,Real.norm_eq_abs]

theorem unconditional_two_time_hamiltonian_norm_diff (t s : ℝ) (x : Hilbert)
    (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    ‖H t ⟨x,common_domain_subset_hamiltonian ε hε h hh hb m g k t hx⟩-
      H s ⟨x,common_domain_subset_hamiltonian ε hε h hh hb m g k s hx⟩‖=
      |Real.exp (2*t)-Real.exp (2*s)| *
        ‖(G) ⟨x,common_domain_subset_growing ε hε h hh hb m g k hx⟩‖ := by
  rw [unconditional_two_time_hamiltonian_growing_difference ε hε h hh hb m g k t s x hx,
    norm_smul,Complex.norm_real,Real.norm_eq_abs]

theorem unconditional_two_time_hamiltonian_norm_transfer (t s : ℝ) (x : Hilbert)
    (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    ‖H t ⟨x,common_domain_subset_hamiltonian ε hε h hh hb m g k t hx⟩‖ ≤
      ‖H s ⟨x,common_domain_subset_hamiltonian ε hε h hh hb m g k s hx⟩‖+
        |Real.exp (2*t)-Real.exp (2*s)| *
          ‖(G) ⟨x,common_domain_subset_growing ε hε h hh hb m g k hx⟩‖ := by
  have htri := norm_le_add_norm_sub
    (H t ⟨x,common_domain_subset_hamiltonian ε hε h hh hb m g k t hx⟩)
    (H s ⟨x,common_domain_subset_hamiltonian ε hε h hh hb m g k s hx⟩)
  rw [unconditional_two_time_hamiltonian_norm_diff ε hε h hh hb m g k t s x hx] at htri
  exact htri

theorem unconditional_two_time_residual_norm_transfer (t s : ℝ) (x : Hilbert)
    (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    ‖S t ⟨x,common_domain_subset_residual ε hε h hh hb m g k t hx⟩‖ ≤
      ‖S s ⟨x,common_domain_subset_residual ε hε h hh hb m g k s hx⟩‖+
        |Real.exp (2*t)-Real.exp (2*s)| *‖(P) ⟨x,hx.1.2⟩‖ := by
  have htri := norm_le_add_norm_sub
    (S t ⟨x,common_domain_subset_residual ε hε h hh hb m g k t hx⟩)
    (S s ⟨x,common_domain_subset_residual ε hε h hh hb m g k s hx⟩)
  rw [unconditional_two_time_residual_norm_diff ε hε h hh hb m g k t s x hx] at htri
  exact htri

#print axioms unconditional_radial_potential_norm_le_growing
#print axioms unconditional_static_norm_sq_bound
#print axioms unconditional_static_radial_domination
#print axioms unconditional_two_time_residual_norm_diff
#print axioms unconditional_two_time_hamiltonian_norm_diff
#print axioms unconditional_two_time_hamiltonian_norm_transfer
#print axioms unconditional_two_time_residual_norm_transfer
end
end UnifiedTheory.Audit.KFCausalClockFloorUnconditionalTwoTimeCrossEstimate
