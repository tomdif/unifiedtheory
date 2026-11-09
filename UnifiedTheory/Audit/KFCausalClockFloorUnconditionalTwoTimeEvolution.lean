/- Unconditional Two-Time Evolution Identities for all real couplings:
the time-independent common operator domain
Dom_common = (Dom T ∩ Dom Kr ∩ Dom P) ∩ Dom Tres(0) embeds into Dom H(t),
Dom S(t), and Dom G for every time t; all pairwise common domains of H(t) with
T, G, and P are time-invariant; and on Dom_common (and unconditionally on
Dom T ∩ Dom Kr ∩ Dom P when k > 0) the two-time differences S(t)x - S(s)x and
H(t)x - H(s)x equal (e^{2t} - e^{2s})Px and (e^{2t} - e^{2s})(Krx + Px). -/
import UnifiedTheory.Audit.KFCausalClockFloorUnconditionalThreeOperatorDecomposition

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorUnconditionalTwoTimeEvolution
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorUnconditionalThreeOperatorDecomposition
  (unconditional_three_operator_residual_graph
   unconditional_three_operator_hamiltonian_graph
   unconditional_static_growing_hamiltonian_graph
   hamiltonian_residual_common_domain_eq
   hamiltonian_growing_common_domain_eq
   hamiltonian_static_common_domain_eq)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi*ε/3) (m g k : ℝ)
local notation "hw" => KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k

def commonOperatorDomain : Submodule ℂ Hilbert :=
  ((T).domain ⊓ (K).domain ⊓ (P).domain) ⊓ (Tres 0).domain

theorem common_domain_subset_hamiltonian (t : ℝ) :
    commonOperatorDomain ε hε h hh hb m g k ≤ (H t).domain := by
  intro x hx
  exact LinearPMap.mem_domain_of_mem_graph
    (unconditional_three_operator_hamiltonian_graph ε hε h hh hb m g k t
      x ((T) ⟨x,hx.1.1.1⟩) ((K) ⟨x,hx.1.1.2⟩) ((P) ⟨x,hx.1.2⟩)
      ((T).mem_graph ⟨x,hx.1.1.1⟩) ((K).mem_graph ⟨x,hx.1.1.2⟩)
      ((P).mem_graph ⟨x,hx.1.2⟩) hx.2)

theorem common_domain_subset_residual (t : ℝ) :
    commonOperatorDomain ε hε h hh hb m g k ≤ (S t).domain := by
  intro x hx
  exact LinearPMap.mem_domain_of_mem_graph
    (unconditional_three_operator_residual_graph ε hε h hh hb m g k t
      x ((T) ⟨x,hx.1.1.1⟩) ((P) ⟨x,hx.1.2⟩)
      ((T).mem_graph ⟨x,hx.1.1.1⟩) ((P).mem_graph ⟨x,hx.1.2⟩) hx.2)

theorem common_domain_subset_growing :
    commonOperatorDomain ε hε h hh hb m g k ≤ (G).domain := by
  intro x hx
  exact (KFCausalClockFloorGrowingPotentialSum.domain_iff ε hε h hh hb m g k x).mpr
    ⟨hx.1.1.2,hx.1.2⟩

theorem hamiltonian_static_common_time_invariant (t s : ℝ) :
    (H t).domain ⊓ (T).domain=(H s).domain ⊓ (T).domain :=
  (hamiltonian_static_common_domain_eq ε hε h hh hb m g k t).trans
    (hamiltonian_static_common_domain_eq ε hε h hh hb m g k s).symm

theorem hamiltonian_growing_common_time_invariant (t s : ℝ) :
    (H t).domain ⊓ (G).domain=(H s).domain ⊓ (G).domain :=
  (hamiltonian_growing_common_domain_eq ε hε h hh hb m g k t).trans
    (hamiltonian_growing_common_domain_eq ε hε h hh hb m g k s).symm

theorem hamiltonian_potential_common_time_invariant (t s : ℝ) :
    (H t).domain ⊓ (P).domain=(H s).domain ⊓ (P).domain :=
  (hamiltonian_residual_common_domain_eq ε hε h hh hb m g k t).trans
    (hamiltonian_residual_common_domain_eq ε hε h hh hb m g k s).symm

private theorem residual_apply_on_common (t : ℝ) (x : Hilbert)
    (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    S t ⟨x,common_domain_subset_residual ε hε h hh hb m g k t hx⟩=
      (T) ⟨x,hx.1.1.1⟩+(Real.exp (2*t):ℂ) • (P) ⟨x,hx.1.2⟩ :=
  (S t).mem_graph_snd_inj'
    ((S t).mem_graph ⟨x,common_domain_subset_residual ε hε h hh hb m g k t hx⟩)
    (unconditional_three_operator_residual_graph ε hε h hh hb m g k t
      x ((T) ⟨x,hx.1.1.1⟩) ((P) ⟨x,hx.1.2⟩)
      ((T).mem_graph ⟨x,hx.1.1.1⟩) ((P).mem_graph ⟨x,hx.1.2⟩) hx.2) rfl

private theorem hamiltonian_growing_apply_on_common (t : ℝ) (x : Hilbert)
    (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    H t ⟨x,common_domain_subset_hamiltonian ε hε h hh hb m g k t hx⟩=
      (T) ⟨x,hx.1.1.1⟩+
        (Real.exp (2*t):ℂ) • (G) ⟨x,common_domain_subset_growing ε hε h hh hb m g k hx⟩ :=
  (H t).mem_graph_snd_inj'
    ((H t).mem_graph ⟨x,common_domain_subset_hamiltonian ε hε h hh hb m g k t hx⟩)
    (unconditional_static_growing_hamiltonian_graph ε hε h hh hb m g k t
      x ((T) ⟨x,hx.1.1.1⟩) ((G) ⟨x,common_domain_subset_growing ε hε h hh hb m g k hx⟩)
      ((T).mem_graph ⟨x,hx.1.1.1⟩)
      ((G).mem_graph ⟨x,common_domain_subset_growing ε hε h hh hb m g k hx⟩) hx.2) rfl

private theorem hamiltonian_three_operator_apply_on_common (t : ℝ) (x : Hilbert)
    (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    H t ⟨x,common_domain_subset_hamiltonian ε hε h hh hb m g k t hx⟩=
      (T) ⟨x,hx.1.1.1⟩+
        (Real.exp (2*t):ℂ) • ((K) ⟨x,hx.1.1.2⟩+(P) ⟨x,hx.1.2⟩) :=
  (H t).mem_graph_snd_inj'
    ((H t).mem_graph ⟨x,common_domain_subset_hamiltonian ε hε h hh hb m g k t hx⟩)
    (unconditional_three_operator_hamiltonian_graph ε hε h hh hb m g k t
      x ((T) ⟨x,hx.1.1.1⟩) ((K) ⟨x,hx.1.1.2⟩) ((P) ⟨x,hx.1.2⟩)
      ((T).mem_graph ⟨x,hx.1.1.1⟩) ((K).mem_graph ⟨x,hx.1.1.2⟩)
      ((P).mem_graph ⟨x,hx.1.2⟩) hx.2) rfl

theorem unconditional_two_time_residual_difference (t s : ℝ) (x : Hilbert)
    (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    S t ⟨x,common_domain_subset_residual ε hε h hh hb m g k t hx⟩-
      S s ⟨x,common_domain_subset_residual ε hε h hh hb m g k s hx⟩=
      ((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ) • (P) ⟨x,hx.1.2⟩ := by
  rw [residual_apply_on_common ε hε h hh hb m g k t x hx,
    residual_apply_on_common ε hε h hh hb m g k s x hx,
    Complex.ofReal_sub,sub_smul]
  abel

theorem unconditional_two_time_hamiltonian_growing_difference (t s : ℝ) (x : Hilbert)
    (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    H t ⟨x,common_domain_subset_hamiltonian ε hε h hh hb m g k t hx⟩-
      H s ⟨x,common_domain_subset_hamiltonian ε hε h hh hb m g k s hx⟩=
      ((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ) •
        (G) ⟨x,common_domain_subset_growing ε hε h hh hb m g k hx⟩ := by
  rw [hamiltonian_growing_apply_on_common ε hε h hh hb m g k t x hx,
    hamiltonian_growing_apply_on_common ε hε h hh hb m g k s x hx,
    Complex.ofReal_sub,sub_smul]
  abel

theorem unconditional_two_time_hamiltonian_three_operator_difference (t s : ℝ) (x : Hilbert)
    (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    H t ⟨x,common_domain_subset_hamiltonian ε hε h hh hb m g k t hx⟩-
      H s ⟨x,common_domain_subset_hamiltonian ε hε h hh hb m g k s hx⟩=
      ((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ) •
        ((K) ⟨x,hx.1.1.2⟩+(P) ⟨x,hx.1.2⟩) := by
  rw [hamiltonian_three_operator_apply_on_common ε hε h hh hb m g k t x hx,
    hamiltonian_three_operator_apply_on_common ε hε h hh hb m g k s x hx,
    Complex.ofReal_sub,sub_smul]
  abel

theorem positive_vacuum_common_domain_eq (hk : 0 < k) :
    commonOperatorDomain ε hε h hh hb m g k=(T).domain ⊓ (K).domain ⊓ (P).domain :=
  (hamiltonian_residual_common_domain_eq ε hε h hh hb m g k 0).symm.trans
    (KFCausalClockFloorPositiveVacuumThreeOperatorDomain.hamiltonian_potential_domain_eq
      ε hε h hh hb m g k 0 hk)

theorem positive_vacuum_two_time_hamiltonian_difference (hk : 0 < k) (t s : ℝ) (x : Hilbert)
    (hx : x ∈ (T).domain ⊓ (K).domain ⊓ (P).domain) :
    have hxc : x ∈ commonOperatorDomain ε hε h hh hb m g k := by
      rw [positive_vacuum_common_domain_eq ε hε h hh hb m g k hk]
      exact hx
    H t ⟨x,common_domain_subset_hamiltonian ε hε h hh hb m g k t hxc⟩-
      H s ⟨x,common_domain_subset_hamiltonian ε hε h hh hb m g k s hxc⟩=
      ((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ) •
        ((K) ⟨x,hx.1.2⟩+(P) ⟨x,hx.2⟩) := by
  intro hxc
  exact unconditional_two_time_hamiltonian_three_operator_difference ε hε h hh hb m g k t s x hxc

#print axioms common_domain_subset_hamiltonian
#print axioms common_domain_subset_residual
#print axioms common_domain_subset_growing
#print axioms hamiltonian_static_common_time_invariant
#print axioms hamiltonian_growing_common_time_invariant
#print axioms hamiltonian_potential_common_time_invariant
#print axioms unconditional_two_time_residual_difference
#print axioms unconditional_two_time_hamiltonian_growing_difference
#print axioms unconditional_two_time_hamiltonian_three_operator_difference
#print axioms positive_vacuum_common_domain_eq
#print axioms positive_vacuum_two_time_hamiltonian_difference
end
end UnifiedTheory.Audit.KFCausalClockFloorUnconditionalTwoTimeEvolution
