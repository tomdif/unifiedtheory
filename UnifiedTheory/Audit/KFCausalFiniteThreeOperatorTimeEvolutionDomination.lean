/- Three-Operator Time-Evolution Domination on the original finite sourced
packet family: exact two-time difference identity H(t)ψ - H(s)ψ =
(e^{2t} - e^{2s})Gψ, three-operator decomposition H(t)ψ = Tψ + e^{2t}(Krψ + Pψ),
joint norm domination of Tψ, Krψ, Pψ, and Gψ at any reference time s, and
transfer of full Hamiltonian norm control from time s to any target time t. -/
import UnifiedTheory.Audit.KFCausalFiniteFullHamiltonianDomination
import UnifiedTheory.Audit.KFCausalClockFloorStaticGrowingDecomposition

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalFiniteThreeOperatorTimeEvolutionDomination
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalFinitePotentialHamiltonianDomain (hamiltonian_strip)
open KFCausalFinitePotentialStaticMixedBound (potentialPoint staticPoint)
open KFCausalFiniteFullHamiltonianDomination (hamiltonianPoint growingPoint
  radial_scaled_norm_le static_potential_hamiltonian_bound growing_hamiltonian_bound)

private theorem norm_add_sq_le_two (u v : Hilbert) :
    ‖u+v‖^2 ≤ 2*‖u‖^2+2*‖v‖^2 := by
  have h1 : ‖u+v‖ ≤ ‖u‖+‖v‖ := norm_add_le u v
  have h2 : ‖u+v‖^2 ≤ (‖u‖+‖v‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : 0 ≤ (‖u‖-‖v‖)^2 := sq_nonneg _
  nlinarith

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i)
  (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ ε/10)
local notation "ψ" => KFCausalReciprocalNeutralSuperposition.state n ε h a w p C b P hε ha hh hw
local notation "hb₀" => hamiltonian_strip ε h hε hb
local notation "hb₁" => KFCausalSingleGaussianMixedSquare.original_strip ε h hε hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "Kr" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "Pot" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hb₀
local notation "Grow" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hb₀
local notation "FullH" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hb₀

def radialPoint : (Kr).domain :=
  ⟨ψ,LinearPMap.mem_domain_of_mem_graph
    (KFCausalFinitePotentialStaticGraph.radial_graph n ε h a w p C b P hε ha hh hw hb)⟩

theorem finite_packet_hamiltonian_decomposition (m g k t : ℝ) :
    FullH m g k t (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k t)=
      (T) (staticPoint n ε h a w p C b P hε ha hh hw hb)+
      (Real.exp (2*t):ℂ) • Grow m g k (growingPoint n ε h a w p C b P hε ha hh hw hb m g k) := by
  let v₀ := KFCausalFiniteGrowingHamiltonianOutput.referenceVector
    n ε h a w p C b P hε ha hh hw hb m g k
  have hv₀ : KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hb₀ m g k 0 v₀=ψ :=
    KFCausalFiniteGrowingHamiltonianOutput.referenceVector_embedding
      n ε h a w p C b P hε ha hh hw hb m g k
  have ht : (KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hb₀ m g k 0 v₀,
      (T) (staticPoint n ε h a w p C b P hε ha hh hw hb)) ∈ (T).graph :=
    (congrArg (fun x : Hilbert =>
      (x,(T) (staticPoint n ε h a w p C b P hε ha hh hw hb)) ∈ (T).graph) hv₀.symm).mp
      ((T).mem_graph (staticPoint n ε h a w p C b P hε ha hh hw hb))
  have hg : (KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hb₀ m g k 0 v₀,
      Grow m g k (growingPoint n ε h a w p C b P hε ha hh hw hb m g k)) ∈ (Grow m g k).graph :=
    (congrArg (fun x : Hilbert =>
      (x,Grow m g k (growingPoint n ε h a w p C b P hε ha hh hw hb m g k)) ∈ (Grow m g k).graph) hv₀.symm).mp
      ((Grow m g k).mem_graph (growingPoint n ε h a w p C b P hε ha hh hw hb m g k))
  have hsum := KFCausalClockFloorStaticGrowingDecomposition.sum_graph
    ε hε h hh hb₀ m g k t v₀ _ _ ht hg
  have hsum' : (ψ,(T) (staticPoint n ε h a w p C b P hε ha hh hw hb)+
      (Real.exp (2*t):ℂ) • Grow m g k (growingPoint n ε h a w p C b P hε ha hh hw hb m g k)) ∈
      (FullH m g k t).graph := by
    rw [hv₀,← Complex.coe_smul] at hsum
    exact hsum
  exact (FullH m g k t).mem_graph_snd_inj'
    ((FullH m g k t).mem_graph (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k t))
    hsum' rfl

theorem finite_packet_two_time_difference (m g k t s : ℝ) :
    FullH m g k t (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k t)-
      FullH m g k s (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k s)=
      ((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ) •
        Grow m g k (growingPoint n ε h a w p C b P hε ha hh hw hb m g k) := by
  rw [finite_packet_hamiltonian_decomposition n ε h a w p C b P hε ha hh hw hb m g k t,
    finite_packet_hamiltonian_decomposition n ε h a w p C b P hε ha hh hw hb m g k s,
    Complex.ofReal_sub,sub_smul]
  abel

theorem finite_packet_three_operator_decomposition (m g k t : ℝ)
    (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k) :
    FullH m g k t (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k t)=
      (T) (staticPoint n ε h a w p C b P hε ha hh hw hb)+
      (Real.exp (2*t):ℂ) •
        ((Kr) (radialPoint n ε h a w p C b P hε ha hh hw hb)+
          (Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk)) := by
  have hG : Grow m g k (growingPoint n ε h a w p C b P hε ha hh hw hb m g k)=
      KFCausalFiniteGrowingHamiltonianOutput.growingOutput n ε h a w p C b P hε ha hh hw hb m g k :=
    (Grow m g k).mem_graph_snd_inj' ((Grow m g k).mem_graph _)
      (KFCausalFiniteGrowingHamiltonianOutput.growing_graph n ε h a w p C b P hε ha hh hw hb m g k) rfl
  have hK : (Kr) (radialPoint n ε h a w p C b P hε ha hh hw hb)=
      KFCausalFinitePotentialStaticGraph.radialOutput n ε h a w p C b P hε ha hh hw hb :=
    (Kr).mem_graph_snd_inj' ((Kr).mem_graph _)
      (KFCausalFinitePotentialStaticGraph.radial_graph n ε h a w p C b P hε ha hh hw hb) rfl
  have hP : (Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk)=
      KFCausalOrderedStaticPotentialHilbertBound.weightedOutput n ε h a w p C b P hε ha hh hw hb m g k :=
    (Pot m g k).mem_graph_snd_inj' ((Pot m g k).mem_graph _)
      (KFCausalFinitePotentialStaticGraph.potential_graph n ε h a w p C b P hε ha hh hw hb m g k hm hg hk) rfl
  have hsplit : Grow m g k (growingPoint n ε h a w p C b P hε ha hh hw hb m g k)=
      (Kr) (radialPoint n ε h a w p C b P hε ha hh hw hb)+
      (Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk) := by
    rw [hG,hK,hP]
    exact KFCausalFinitePotentialStaticGraph.growing_split n ε h a w p C b P hε ha hh hw hb m g k hm hg hk
  rw [finite_packet_hamiltonian_decomposition n ε h a w p C b P hε ha hh hw hb m g k t,hsplit]

theorem finite_packet_static_plus_growing_norm_sq_le (m g k t : ℝ)
    (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 < k) :
    ‖(T) (staticPoint n ε h a w p C b P hε ha hh hw hb)‖^2+
      Real.exp (4*t)*‖Grow m g k (growingPoint n ε h a w p C b P hε ha hh hw hb m g k)‖^2 ≤
      2*(‖FullH m g k t (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k t)‖+
        (|h| /ε)*Real.exp t*‖ψ‖)^2+
      5*(2*‖FullH m g k t (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k t)‖+
        (|h| /ε)*Real.exp t*‖ψ‖)^2+
      10*((2*h^2/ε)*(12+(m+3*g)/k))^2*‖ψ‖^2 := by
  have hsp := static_potential_hamiltonian_bound n ε h a w p C b P hε ha hh hw hb m g k t hm hg hk
  have hgr := growing_hamiltonian_bound n ε h a w p C b P hε ha hh hw hb m g k t hm hg hk
  have hp_nonneg : 0 ≤ (1/2)*Real.exp (4*t)*‖(Pot m g k)
      (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk.le)‖^2 := by positivity
  linarith

theorem finite_packet_three_operator_norm_sq_le (m g k s : ℝ)
    (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 < k) :
    ‖(T) (staticPoint n ε h a w p C b P hε ha hh hw hb)‖^2+
      Real.exp (4*s)*‖(Kr) (radialPoint n ε h a w p C b P hε ha hh hw hb)‖^2+
      (1/2)*Real.exp (4*s)*‖(Pot m g k)
        (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk.le)‖^2 ≤
      (‖FullH m g k s (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k s)‖+
        (|h| /ε)*Real.exp s*‖ψ‖)^2+
      (2*‖FullH m g k s (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k s)‖+
        (|h| /ε)*Real.exp s*‖ψ‖)^2+
      2*((2*h^2/ε)*(12+(m+3*g)/k))^2*‖ψ‖^2 := by
  have hK : KFCausalClockFloorHamiltonianRadialSum.radialOutput ε hε h hh hb₁ m g k s
      (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k s)=
      (Kr) (radialPoint n ε h a w p C b P hε ha hh hw hb) :=
    (Kr).mem_graph_snd_inj' ((Kr).mem_graph _)
      ((Kr).mem_graph (radialPoint n ε h a w p C b P hε ha hh hw hb)) rfl
  have hr := radial_scaled_norm_le ε hε h hh hb₁ m g k s
    (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k s)
  rw [hK] at hr
  have hrsq : (Real.exp (2*s)*‖(Kr) (radialPoint n ε h a w p C b P hε ha hh hw hb)‖)^2 ≤
      (‖FullH m g k s (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k s)‖+
        (|h| /ε)*Real.exp s*‖ψ‖)^2 :=
    pow_le_pow_left₀ (by positivity) hr 2
  have hexp : (Real.exp (2*s)*‖(Kr) (radialPoint n ε h a w p C b P hε ha hh hw hb)‖)^2=
      Real.exp (4*s)*‖(Kr) (radialPoint n ε h a w p C b P hε ha hh hw hb)‖^2 := by
    rw [mul_pow,← Real.exp_nat_mul,show (2:ℕ)*(2*s)=4*s by push_cast; ring]
  have hsp := static_potential_hamiltonian_bound n ε h a w p C b P hε ha hh hw hb m g k s hm hg hk
  linarith

theorem finite_packet_two_time_norm_transfer (m g k t s : ℝ) :
    ‖FullH m g k t (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k t)‖ ≤
      ‖FullH m g k s (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k s)‖+
      |Real.exp (2*t)-Real.exp (2*s)| *
        ‖Grow m g k (growingPoint n ε h a w p C b P hε ha hh hw hb m g k)‖ := by
  have hdiff := finite_packet_two_time_difference n ε h a w p C b P hε ha hh hw hb m g k t s
  have hsum : FullH m g k t (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k t)=
      FullH m g k s (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k s)+
      ((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ) •
        Grow m g k (growingPoint n ε h a w p C b P hε ha hh hw hb m g k) :=
    eq_add_of_sub_eq' hdiff
  rw [hsum]
  have htri := norm_add_le
    (FullH m g k s (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k s))
    (((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ) •
      Grow m g k (growingPoint n ε h a w p C b P hε ha hh hw hb m g k))
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs] at htri
  exact htri

theorem finite_packet_two_time_domination_sq (m g k t s : ℝ)
    (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 < k) :
    Real.exp (4*s)*‖FullH m g k t (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k t)‖^2 ≤
      2*Real.exp (4*s)*‖FullH m g k s (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k s)‖^2+
      2*(Real.exp (2*t)-Real.exp (2*s))^2*
        (2*(‖FullH m g k s (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k s)‖+
          (|h| /ε)*Real.exp s*‖ψ‖)^2+
        4*(2*‖FullH m g k s (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k s)‖+
          (|h| /ε)*Real.exp s*‖ψ‖)^2+
        8*((2*h^2/ε)*(12+(m+3*g)/k))^2*‖ψ‖^2) := by
  have hdiff := finite_packet_two_time_difference n ε h a w p C b P hε ha hh hw hb m g k t s
  have hsum : FullH m g k t (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k t)=
      FullH m g k s (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k s)+
      ((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ) •
        Grow m g k (growingPoint n ε h a w p C b P hε ha hh hw hb m g k) :=
    eq_add_of_sub_eq' hdiff
  have h2 := norm_add_sq_le_two
    (FullH m g k s (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k s))
    (((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ) •
      Grow m g k (growingPoint n ε h a w p C b P hε ha hh hw hb m g k))
  rw [← hsum,norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs] at h2
  have hm4 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos (4*s)).le
  have hgr := growing_hamiltonian_bound n ε h a w p C b P hε ha hh hw hb m g k s hm hg hk
  have hgr_mul := mul_le_mul_of_nonneg_left hgr (by positivity : 0 ≤ 2*(Real.exp (2*t)-Real.exp (2*s))^2)
  nlinarith

#print axioms finite_packet_hamiltonian_decomposition
#print axioms finite_packet_two_time_difference
#print axioms finite_packet_three_operator_decomposition
#print axioms finite_packet_static_plus_growing_norm_sq_le
#print axioms finite_packet_three_operator_norm_sq_le
#print axioms finite_packet_two_time_norm_transfer
#print axioms finite_packet_two_time_domination_sq
end
end UnifiedTheory.Audit.KFCausalFiniteThreeOperatorTimeEvolutionDomination
