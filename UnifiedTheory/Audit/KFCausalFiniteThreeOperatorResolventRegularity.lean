/- Resolvent regularity and two-time resolvent defect estimates across the
three-operator decomposition H(t) = T + e^{2t}(Kr + P), the residual
decomposition S(t) = T + e^{2t}P, and the growing decomposition G = Kr + P,
both on the unconditional common operator domain and with explicit norm
domination bounds on the finite sourced packet family. -/
import UnifiedTheory.Audit.KFCausalFiniteThreeOperatorTimeEvolutionDomination
import UnifiedTheory.Audit.KFCausalClockFloorHamiltonianClockCore
import UnifiedTheory.Audit.KFCausalClockFloorResidualClockCore
import UnifiedTheory.Audit.KFCausalClockFloorStaticClockCore
import UnifiedTheory.Audit.KFCausalClockFloorUnconditionalTwoTimeEvolution

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalFiniteThreeOperatorResolventRegularity
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalFinitePotentialHamiltonianDomain (hamiltonian_strip)
open KFCausalFinitePotentialStaticMixedBound (potentialPoint staticPoint)
open KFCausalFiniteResidualStaticPotentialDomination (residualPoint residual_output_eq split_norm_domination)
open KFCausalFiniteFullHamiltonianDomination (hamiltonianPoint growingPoint
  radial_scaled_norm_le static_potential_hamiltonian_bound growing_hamiltonian_bound)
open KFCausalFiniteThreeOperatorTimeEvolutionDomination (radialPoint
  finite_packet_hamiltonian_decomposition finite_packet_two_time_difference
  finite_packet_three_operator_decomposition)
open KFCausalClockFloorUnconditionalThreeOperatorDecomposition
  (unconditional_three_operator_residual_graph unconditional_three_operator_hamiltonian_graph)
open KFCausalClockFloorUnconditionalTwoTimeEvolution
  (commonOperatorDomain common_domain_subset_hamiltonian common_domain_subset_residual
   common_domain_subset_growing unconditional_two_time_residual_difference
   unconditional_two_time_hamiltonian_three_operator_difference)

private theorem nonneg_le_of_sq_le_sq {a b : ℝ} (hb : 0 ≤ b)
    (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra! hlt
  have hsq : b ^ 2 < a ^ 2 := by nlinarith
  linarith

private theorem potential_linear_bound {T_sq E4 P_norm E2 A γ N : ℝ}
    (hA : 0 ≤ A) (hγ : 0 ≤ γ) (hN : 0 ≤ N) (hT : 0 ≤ T_sq)
    (hE : (E2 * P_norm) ^ 2 = E4 * P_norm ^ 2)
    (h : T_sq + (1 / 2) * E4 * P_norm ^ 2 ≤ A ^ 2 + 2 * γ ^ 2 * N ^ 2) :
    E2 * P_norm ≤ 2 * A + 2 * γ * N := by
  have hsq : (E2 * P_norm) ^ 2 ≤ (2 * A + 2 * γ * N) ^ 2 := by
    have hAN : 0 ≤ A * (γ * N) := mul_nonneg hA (mul_nonneg hγ hN)
    nlinarith [sq_nonneg A]
  exact nonneg_le_of_sq_le_sq (by linarith [mul_nonneg hγ hN]) hsq

private theorem scaled_resolvent_bound {E D R X Y : ℝ}
    (hE : 0 ≤ E) (hR : 0 ≤ R)
    (h1 : D ≤ R * X) (h2 : E * X ≤ Y) :
    E * D ≤ R * Y := by
  have hm1 := mul_le_mul_of_nonneg_left h1 hE
  have hm2 := mul_le_mul_of_nonneg_left h2 hR
  linarith

private theorem resolvent_difference_identity {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (R : H →L[ℂ] H) (x ht hs d : H) (r : ℝ)
    (hleft : R (ht + r • x) = x) (hdiff : ht - hs = d) :
    x - R (hs + r • x) = R d := by
  have hsub : (ht + r • x) - (hs + r • x) = d := by
    rw [← hdiff]
    abel
  calc
    x - R (hs + r • x) = R (ht + r • x) - R (hs + r • x) := by rw [hleft]
    _ = R ((ht + r • x) - (hs + r • x)) := (R.map_sub _ _).symm
    _ = R d := by rw [hsub]

section CommonDomain
variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
local notation "hw" => KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "Kr" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "Pot" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "Grow" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "Res" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "FullH" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k
local notation "RS" => KFCausalClockFloorResidualClockCore.resolvent ε hε h hh hw m g k
local notation "RG" => KFCausalClockFloorGrowingYosida.resolvent ε hε h hh hw m g k

theorem common_hamiltonian_resolvent_three_operator_cancel (t r : ℝ) (hr : 0 < r)
    (x : Hilbert) (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    RH t r ((T) ⟨x, hx.1.1.1⟩ +
      (Real.exp (2 * t) : ℂ) • ((Kr) ⟨x, hx.1.1.2⟩ + (Pot) ⟨x, hx.1.2⟩) + r • x) = x := by
  let xH : (FullH t).domain := ⟨x, common_domain_subset_hamiltonian ε hε h hh hb m g k t hx⟩
  have hH : FullH t xH = (T) ⟨x, hx.1.1.1⟩ +
      (Real.exp (2 * t) : ℂ) • ((Kr) ⟨x, hx.1.1.2⟩ + (Pot) ⟨x, hx.1.2⟩) :=
    (FullH t).mem_graph_snd_inj' ((FullH t).mem_graph xH)
      (unconditional_three_operator_hamiltonian_graph ε hε h hh hb m g k t
        x ((T) ⟨x, hx.1.1.1⟩) ((Kr) ⟨x, hx.1.1.2⟩) ((Pot) ⟨x, hx.1.2⟩)
        ((T).mem_graph ⟨x, hx.1.1.1⟩) ((Kr).mem_graph ⟨x, hx.1.1.2⟩)
        ((Pot).mem_graph ⟨x, hx.1.2⟩) hx.2) rfl
  rw [← hH]
  exact KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t r hr xH

theorem common_residual_resolvent_two_operator_cancel (t r : ℝ) (hr : 0 < r)
    (x : Hilbert) (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    RS t r ((T) ⟨x, hx.1.1.1⟩ +
      (Real.exp (2 * t) : ℂ) • (Pot) ⟨x, hx.1.2⟩ + r • x) = x := by
  let xS : (Res t).domain := ⟨x, common_domain_subset_residual ε hε h hh hb m g k t hx⟩
  have hS : Res t xS = (T) ⟨x, hx.1.1.1⟩ + (Real.exp (2 * t) : ℂ) • (Pot) ⟨x, hx.1.2⟩ :=
    (Res t).mem_graph_snd_inj' ((Res t).mem_graph xS)
      (unconditional_three_operator_residual_graph ε hε h hh hb m g k t
        x ((T) ⟨x, hx.1.1.1⟩) ((Pot) ⟨x, hx.1.2⟩)
        ((T).mem_graph ⟨x, hx.1.1.1⟩) ((Pot).mem_graph ⟨x, hx.1.2⟩) hx.2) rfl
  rw [← hS]
  exact KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t r hr xS

theorem common_growing_resolvent_two_operator_cancel (r : ℝ) (hr : 0 < r)
    (x : Hilbert) (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    RG r ((Kr) ⟨x, hx.1.1.2⟩ + (Pot) ⟨x, hx.1.2⟩ + r • x) = x := by
  let xG : (Grow).domain := ⟨x, common_domain_subset_growing ε hε h hh hb m g k hx⟩
  have hG : Grow xG = (Kr) ⟨x, hx.1.1.2⟩ + (Pot) ⟨x, hx.1.2⟩ := by
    have hmem : (x, (Kr) ⟨x, hx.1.1.2⟩ + (Pot) ⟨x, hx.1.2⟩) ∈ (Grow).graph := by
      rw [KFCausalClockFloorGrowingPotentialSum.operator_sum ε hε h hh hb m g k]
      exact (LinearPMap.mem_graph_iff _).mpr ⟨⟨x, ⟨hx.1.1.2, hx.1.2⟩⟩, rfl, rfl⟩
    exact (Grow).mem_graph_snd_inj' ((Grow).mem_graph xG) hmem rfl
  rw [← hG]
  exact KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k r hr xG

theorem common_hamiltonian_two_time_resolvent_defect (t s r : ℝ) (hr : 0 < r)
    (x : Hilbert) (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    x - RH t r (FullH s ⟨x, common_domain_subset_hamiltonian ε hε h hh hb m g k s hx⟩ + r • x) =
      ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) •
        RH t r ((Kr) ⟨x, hx.1.1.2⟩ + (Pot) ⟨x, hx.1.2⟩) := by
  let xHt : (FullH t).domain := ⟨x, common_domain_subset_hamiltonian ε hε h hh hb m g k t hx⟩
  have hleft := KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t r hr xHt
  have hdiff := unconditional_two_time_hamiltonian_three_operator_difference
    ε hε h hh hb m g k t s x hx
  have hres := resolvent_difference_identity (RH t r) x (FullH t xHt)
    (FullH s ⟨x, common_domain_subset_hamiltonian ε hε h hh hb m g k s hx⟩)
    (((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) •
      ((Kr) ⟨x, hx.1.1.2⟩ + (Pot) ⟨x, hx.1.2⟩)) r hleft hdiff
  rw [hres, ContinuousLinearMap.map_smul]

theorem common_residual_two_time_resolvent_defect (t s r : ℝ) (hr : 0 < r)
    (x : Hilbert) (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    x - RS t r (Res s ⟨x, common_domain_subset_residual ε hε h hh hb m g k s hx⟩ + r • x) =
      ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) •
        RS t r ((Pot) ⟨x, hx.1.2⟩) := by
  let xSt : (Res t).domain := ⟨x, common_domain_subset_residual ε hε h hh hb m g k t hx⟩
  have hleft := KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t r hr xSt
  have hdiff := unconditional_two_time_residual_difference ε hε h hh hb m g k t s x hx
  have hres := resolvent_difference_identity (RS t r) x (Res t xSt)
    (Res s ⟨x, common_domain_subset_residual ε hε h hh hb m g k s hx⟩)
    (((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) • (Pot) ⟨x, hx.1.2⟩) r hleft hdiff
  rw [hres, ContinuousLinearMap.map_smul]

end CommonDomain

section FinitePacket
variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i)
  (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ ε / 10)
local notation "ψ" => KFCausalReciprocalNeutralSuperposition.state n ε h a w p C b P hε ha hh hw
local notation "hb₀" => hamiltonian_strip ε h hε hb
local notation "hb₁" => KFCausalSingleGaussianMixedSquare.original_strip ε h hε hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "Kr" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "Pot" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hb₀
local notation "Grow" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hb₀
local notation "Res" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hb₀
local notation "FullH" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hb₀
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hb₀
local notation "RS" => KFCausalClockFloorResidualClockCore.resolvent ε hε h hh hb₀
local notation "RG" => KFCausalClockFloorGrowingYosida.resolvent ε hε h hh hb₀
local notation "RT" => KFCausalClockFloorStaticClockCore.resolvent ε hε h hh hb₀
local notation "RP" => KFCausalClockFloorPotentialClockResolvent.resolvent ε hε h hh hb₀

theorem finite_packet_growing_decomposition (m g k : ℝ)
    (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k) :
    Grow m g k (growingPoint n ε h a w p C b P hε ha hh hw hb m g k) =
      (Kr) (radialPoint n ε h a w p C b P hε ha hh hw hb) +
      (Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk) := by
  have hG : Grow m g k (growingPoint n ε h a w p C b P hε ha hh hw hb m g k) =
      KFCausalFiniteGrowingHamiltonianOutput.growingOutput n ε h a w p C b P hε ha hh hw hb m g k :=
    (Grow m g k).mem_graph_snd_inj' ((Grow m g k).mem_graph _)
      (KFCausalFiniteGrowingHamiltonianOutput.growing_graph n ε h a w p C b P hε ha hh hw hb m g k) rfl
  have hK : (Kr) (radialPoint n ε h a w p C b P hε ha hh hw hb) =
      KFCausalFinitePotentialStaticGraph.radialOutput n ε h a w p C b P hε ha hh hw hb :=
    (Kr).mem_graph_snd_inj' ((Kr).mem_graph _)
      (KFCausalFinitePotentialStaticGraph.radial_graph n ε h a w p C b P hε ha hh hw hb) rfl
  have hP : (Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk) =
      KFCausalOrderedStaticPotentialHilbertBound.weightedOutput n ε h a w p C b P hε ha hh hw hb m g k :=
    (Pot m g k).mem_graph_snd_inj' ((Pot m g k).mem_graph _)
      (KFCausalFinitePotentialStaticGraph.potential_graph n ε h a w p C b P hε ha hh hw hb m g k hm hg hk) rfl
  rw [hG, hK, hP]
  exact KFCausalFinitePotentialStaticGraph.growing_split n ε h a w p C b P hε ha hh hw hb m g k hm hg hk

theorem finite_packet_hamiltonian_resolvent_growing_cancel (m g k t r : ℝ) (hr : 0 < r) :
    RH m g k t r ((T) (staticPoint n ε h a w p C b P hε ha hh hw hb) +
      (Real.exp (2 * t) : ℂ) • Grow m g k (growingPoint n ε h a w p C b P hε ha hh hw hb m g k) +
      r • ψ) = ψ := by
  rw [← finite_packet_hamiltonian_decomposition n ε h a w p C b P hε ha hh hw hb m g k t]
  exact KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hb₀ m g k t r hr
    (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k t)

theorem finite_packet_hamiltonian_resolvent_three_operator_cancel (m g k t r : ℝ)
    (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k) (hr : 0 < r) :
    RH m g k t r ((T) (staticPoint n ε h a w p C b P hε ha hh hw hb) +
      (Real.exp (2 * t) : ℂ) •
        ((Kr) (radialPoint n ε h a w p C b P hε ha hh hw hb) +
          (Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk)) +
      r • ψ) = ψ := by
  rw [← finite_packet_three_operator_decomposition n ε h a w p C b P hε ha hh hw hb m g k t hm hg hk]
  exact KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hb₀ m g k t r hr
    (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k t)

theorem finite_packet_residual_resolvent_two_operator_cancel (m g k t r : ℝ)
    (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k) (hr : 0 < r) :
    RS m g k t r ((T) (staticPoint n ε h a w p C b P hε ha hh hw hb) +
      (Real.exp (2 * t) : ℂ) •
        (Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk) +
      r • ψ) = ψ := by
  rw [← residual_output_eq n ε h a w p C b P hε ha hh hw hb m g k t hm hg hk]
  exact KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hb₀ m g k t r hr
    (residualPoint n ε h a w p C b P hε ha hh hw hb m g k t hm hg hk)

theorem finite_packet_growing_resolvent_two_operator_cancel (m g k r : ℝ)
    (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k) (hr : 0 < r) :
    RG m g k r ((Kr) (radialPoint n ε h a w p C b P hε ha hh hw hb) +
      (Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk) +
      r • ψ) = ψ := by
  rw [← finite_packet_growing_decomposition n ε h a w p C b P hε ha hh hw hb m g k hm hg hk]
  exact KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hb₀ m g k r hr
    (growingPoint n ε h a w p C b P hε ha hh hw hb m g k)

theorem finite_packet_static_resolvent_cancel (m g k t r : ℝ) (hr : 0 < r) :
    RT m g k t r ((T) (staticPoint n ε h a w p C b P hε ha hh hw hb) + r • ψ) = ψ := by
  have hdom : ψ ∈ (KFCausalClockFloorStaticHamiltonian.hamiltonian ε hε h hh hb₀ m g k t).domain := by
    rw [KFCausalClockFloorStaticHamiltonian.hamiltonian_eq_operator]
    exact (staticPoint n ε h a w p C b P hε ha hh hw hb).property
  let xT : (KFCausalClockFloorStaticHamiltonian.hamiltonian ε hε h hh hb₀ m g k t).domain :=
    ⟨ψ, hdom⟩
  have hval : KFCausalClockFloorStaticHamiltonian.hamiltonian ε hε h hh hb₀ m g k t xT =
      (T) (staticPoint n ε h a w p C b P hε ha hh hw hb) := by
    have hg : (ψ, KFCausalClockFloorStaticHamiltonian.hamiltonian ε hε h hh hb₀ m g k t xT) ∈
        (T).graph := by
      rw [← KFCausalClockFloorStaticHamiltonian.hamiltonian_eq_operator ε hε h hh hb₀ m g k t]
      exact (KFCausalClockFloorStaticHamiltonian.hamiltonian ε hε h hh hb₀ m g k t).mem_graph xT
    exact (T).mem_graph_snd_inj' hg
      ((T).mem_graph (staticPoint n ε h a w p C b P hε ha hh hw hb)) rfl
  rw [← hval]
  exact KFCausalClockFloorStaticClockCore.left_inverse ε hε h hh hb₀ m g k t r hr xT

theorem finite_packet_potential_resolvent_cancel (m g k r : ℝ)
    (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k) (hr : 0 < r) :
    RP m g k r ((Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk) +
      r • ψ) = ψ :=
  KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hb₀ m g k r hr
    (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk)

theorem finite_packet_hamiltonian_two_time_resolvent_growing_defect (m g k t s r : ℝ)
    (hr : 0 < r) :
    ψ - RH m g k t r (FullH m g k s (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k s) +
      r • ψ) =
      ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) •
        RH m g k t r (Grow m g k (growingPoint n ε h a w p C b P hε ha hh hw hb m g k)) := by
  have hleft := KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hb₀ m g k t r hr
    (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k t)
  have hdiff := finite_packet_two_time_difference n ε h a w p C b P hε ha hh hw hb m g k t s
  have hres := resolvent_difference_identity (RH m g k t r) ψ
    (FullH m g k t (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k t))
    (FullH m g k s (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k s))
    (((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) •
      Grow m g k (growingPoint n ε h a w p C b P hε ha hh hw hb m g k)) r hleft hdiff
  rw [hres, ContinuousLinearMap.map_smul]

theorem finite_packet_hamiltonian_two_time_resolvent_three_operator_defect (m g k t s r : ℝ)
    (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k) (hr : 0 < r) :
    ψ - RH m g k t r (FullH m g k s (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k s) +
      r • ψ) =
      ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) •
        RH m g k t r ((Kr) (radialPoint n ε h a w p C b P hε ha hh hw hb) +
          (Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk)) := by
  rw [finite_packet_hamiltonian_two_time_resolvent_growing_defect
    n ε h a w p C b P hε ha hh hw hb m g k t s r hr,
    finite_packet_growing_decomposition n ε h a w p C b P hε ha hh hw hb m g k hm hg hk]

theorem finite_packet_hamiltonian_two_time_resolvent_defect_norm_le (m g k t s r : ℝ)
    (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k) (hr : 0 < r) :
    ‖ψ - RH m g k t r (FullH m g k s (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k s) +
      r • ψ)‖ ≤
      r⁻¹ * |Real.exp (2 * t) - Real.exp (2 * s)| *
        (‖(Kr) (radialPoint n ε h a w p C b P hε ha hh hw hb)‖ +
          ‖(Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk)‖) := by
  rw [finite_packet_hamiltonian_two_time_resolvent_three_operator_defect
    n ε h a w p C b P hε ha hh hw hb m g k t s r hm hg hk hr,
    norm_smul, Complex.norm_real, Real.norm_eq_abs]
  have hbound := KFCausalPositiveResolventBounds.resolvent_apply_norm_bound
    (FullH m g k t) (RH m g k t r) r hr
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hb₀ m g k t r hr)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hb₀ m g k t)
    ((Kr) (radialPoint n ε h a w p C b P hε ha hh hw hb) +
      (Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk))
  have htri := norm_add_le
    ((Kr) (radialPoint n ε h a w p C b P hε ha hh hw hb))
    ((Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk))
  have h1 : ‖RH m g k t r ((Kr) (radialPoint n ε h a w p C b P hε ha hh hw hb) +
      (Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk))‖ ≤
      r⁻¹ * (‖(Kr) (radialPoint n ε h a w p C b P hε ha hh hw hb)‖ +
        ‖(Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk)‖) :=
    hbound.trans (mul_le_mul_of_nonneg_left htri (inv_nonneg.mpr hr.le))
  calc
    |Real.exp (2 * t) - Real.exp (2 * s)| *
        ‖RH m g k t r ((Kr) (radialPoint n ε h a w p C b P hε ha hh hw hb) +
          (Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk))‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| *
        (r⁻¹ * (‖(Kr) (radialPoint n ε h a w p C b P hε ha hh hw hb)‖ +
          ‖(Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk)‖)) :=
      mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = r⁻¹ * |Real.exp (2 * t) - Real.exp (2 * s)| *
        (‖(Kr) (radialPoint n ε h a w p C b P hε ha hh hw hb)‖ +
          ‖(Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk)‖) := by ring

theorem finite_packet_hamiltonian_two_time_resolvent_domination_norm_le (m g k t s r : ℝ)
    (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 < k) (hr : 0 < r) :
    Real.exp (2 * s) *
        ‖ψ - RH m g k t r (FullH m g k s (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k s) +
          r • ψ)‖ ≤
      r⁻¹ * |Real.exp (2 * t) - Real.exp (2 * s)| *
        ((‖FullH m g k s (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k s)‖ +
            (|h| / ε) * Real.exp s * ‖ψ‖) +
          2 * (2 * ‖FullH m g k s (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k s)‖ +
            (|h| / ε) * Real.exp s * ‖ψ‖) +
          2 * ((2 * h ^ 2 / ε) * (12 + (m + 3 * g) / k)) * ‖ψ‖) := by
  have hdef := finite_packet_hamiltonian_two_time_resolvent_defect_norm_le
    n ε h a w p C b P hε ha hh hw hb m g k t s r hm hg hk.le hr
  have hK : KFCausalClockFloorHamiltonianRadialSum.radialOutput ε hε h hh hb₁ m g k s
      (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k s) =
      (Kr) (radialPoint n ε h a w p C b P hε ha hh hw hb) :=
    (Kr).mem_graph_snd_inj' ((Kr).mem_graph _)
      ((Kr).mem_graph (radialPoint n ε h a w p C b P hε ha hh hw hb)) rfl
  have hrad := radial_scaled_norm_le ε hε h hh hb₁ m g k s
    (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k s)
  rw [hK] at hrad
  change Real.exp (2 * s) * ‖(Kr) (radialPoint n ε h a w p C b P hε ha hh hw hb)‖ ≤
    ‖FullH m g k s (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k s)‖ +
      (|h| / ε) * Real.exp s * ‖ψ‖ at hrad
  have hsp := static_potential_hamiltonian_bound n ε h a w p C b P hε ha hh hw hb m g k s hm hg hk
  have hexp4 : (Real.exp (2 * s) *
      ‖(Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk.le)‖) ^ 2 =
      Real.exp (4 * s) *
        ‖(Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk.le)‖ ^ 2 := by
    rw [mul_pow, ← Real.exp_nat_mul, show (2 : ℕ) * (2 * s) = 4 * s by push_cast; ring]
  have hP_le := potential_linear_bound
    (add_nonneg (mul_nonneg zero_le_two (norm_nonneg _))
      (mul_nonneg (mul_nonneg (div_nonneg (abs_nonneg h) hε.le) (Real.exp_pos s).le) (norm_nonneg _)))
    (by positivity) (norm_nonneg _) (sq_nonneg _) hexp4 hsp
  have hsum : Real.exp (2 * s) *
      (‖(Kr) (radialPoint n ε h a w p C b P hε ha hh hw hb)‖ +
        ‖(Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk.le)‖) ≤
      (‖FullH m g k s (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k s)‖ +
        (|h| / ε) * Real.exp s * ‖ψ‖) +
      2 * (2 * ‖FullH m g k s (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k s)‖ +
        (|h| / ε) * Real.exp s * ‖ψ‖) +
      2 * ((2 * h ^ 2 / ε) * (12 + (m + 3 * g) / k)) * ‖ψ‖ := by
    rw [mul_add]
    linarith [hrad, hP_le]
  exact scaled_resolvent_bound (Real.exp_pos (2 * s)).le
    (mul_nonneg (inv_nonneg.mpr hr.le) (abs_nonneg _)) hdef hsum

theorem finite_packet_hamiltonian_two_time_resolvent_domination_sq_le (m g k t s r : ℝ)
    (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 < k) (hr : 0 < r) :
    Real.exp (4 * s) *
        ‖ψ - RH m g k t r (FullH m g k s (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k s) +
          r • ψ)‖ ^ 2 ≤
      (r⁻¹) ^ 2 * (Real.exp (2 * t) - Real.exp (2 * s)) ^ 2 *
        (2 * (‖FullH m g k s (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k s)‖ +
            (|h| / ε) * Real.exp s * ‖ψ‖) ^ 2 +
          4 * (2 * ‖FullH m g k s (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k s)‖ +
            (|h| / ε) * Real.exp s * ‖ψ‖) ^ 2 +
          8 * ((2 * h ^ 2 / ε) * (12 + (m + 3 * g) / k)) ^ 2 * ‖ψ‖ ^ 2) := by
  rw [finite_packet_hamiltonian_two_time_resolvent_growing_defect
    n ε h a w p C b P hε ha hh hw hb m g k t s r hr,
    norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hbound := KFCausalPositiveResolventBounds.resolvent_apply_norm_bound
    (FullH m g k t) (RH m g k t r) r hr
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hb₀ m g k t r hr)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hb₀ m g k t)
    (Grow m g k (growingPoint n ε h a w p C b P hε ha hh hw hb m g k))
  have hsq : ‖RH m g k t r (Grow m g k (growingPoint n ε h a w p C b P hε ha hh hw hb m g k))‖ ^ 2 ≤
      (r⁻¹) ^ 2 * ‖Grow m g k (growingPoint n ε h a w p C b P hε ha hh hw hb m g k)‖ ^ 2 := by
    have hp := pow_le_pow_left₀ (norm_nonneg _) hbound 2
    rwa [mul_pow] at hp
  have hgr := growing_hamiltonian_bound n ε h a w p C b P hε ha hh hw hb m g k s hm hg hk
  have hm1 := mul_le_mul_of_nonneg_left hsq
    (show 0 ≤ Real.exp (4 * s) * (Real.exp (2 * t) - Real.exp (2 * s)) ^ 2 by positivity)
  have hm2 := mul_le_mul_of_nonneg_left hgr
    (show 0 ≤ (r⁻¹) ^ 2 * (Real.exp (2 * t) - Real.exp (2 * s)) ^ 2 by positivity)
  linarith

theorem finite_packet_residual_two_time_difference (m g k t s : ℝ)
    (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k) :
    Res m g k t (residualPoint n ε h a w p C b P hε ha hh hw hb m g k t hm hg hk) -
      Res m g k s (residualPoint n ε h a w p C b P hε ha hh hw hb m g k s hm hg hk) =
      ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) •
        (Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk) := by
  rw [residual_output_eq n ε h a w p C b P hε ha hh hw hb m g k t hm hg hk,
    residual_output_eq n ε h a w p C b P hε ha hh hw hb m g k s hm hg hk,
    Complex.ofReal_sub, sub_smul]
  abel

theorem finite_packet_residual_two_time_resolvent_defect (m g k t s r : ℝ)
    (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k) (hr : 0 < r) :
    ψ - RS m g k t r (Res m g k s (residualPoint n ε h a w p C b P hε ha hh hw hb m g k s hm hg hk) +
      r • ψ) =
      ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) •
        RS m g k t r ((Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk)) := by
  have hleft := KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hb₀ m g k t r hr
    (residualPoint n ε h a w p C b P hε ha hh hw hb m g k t hm hg hk)
  have hdiff := finite_packet_residual_two_time_difference
    n ε h a w p C b P hε ha hh hw hb m g k t s hm hg hk
  have hres := resolvent_difference_identity (RS m g k t r) ψ
    (Res m g k t (residualPoint n ε h a w p C b P hε ha hh hw hb m g k t hm hg hk))
    (Res m g k s (residualPoint n ε h a w p C b P hε ha hh hw hb m g k s hm hg hk))
    (((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) •
      (Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk)) r hleft hdiff
  rw [hres, ContinuousLinearMap.map_smul]

theorem finite_packet_residual_two_time_resolvent_defect_norm_le (m g k t s r : ℝ)
    (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k) (hr : 0 < r) :
    ‖ψ - RS m g k t r (Res m g k s (residualPoint n ε h a w p C b P hε ha hh hw hb m g k s hm hg hk) +
      r • ψ)‖ ≤
      r⁻¹ * |Real.exp (2 * t) - Real.exp (2 * s)| *
        ‖(Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk)‖ := by
  rw [finite_packet_residual_two_time_resolvent_defect
    n ε h a w p C b P hε ha hh hw hb m g k t s r hm hg hk hr,
    norm_smul, Complex.norm_real, Real.norm_eq_abs]
  have hbound := KFCausalPositiveResolventBounds.resolvent_apply_norm_bound
    (Res m g k t) (RS m g k t r) r hr
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hb₀ m g k t r hr)
    (KFCausalClosedGraphForm.hamiltonian_positive
      (KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hb₀ m g k t))
    ((Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk))
  calc
    |Real.exp (2 * t) - Real.exp (2 * s)| *
        ‖RS m g k t r ((Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk))‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| *
        (r⁻¹ * ‖(Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk)‖) :=
      mul_le_mul_of_nonneg_left hbound (abs_nonneg _)
    _ = r⁻¹ * |Real.exp (2 * t) - Real.exp (2 * s)| *
        ‖(Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk)‖ := by ring

theorem finite_packet_residual_two_time_resolvent_domination_norm_le (m g k t s r : ℝ)
    (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 < k) (hr : 0 < r) :
    Real.exp (2 * s) *
        ‖ψ - RS m g k t r (Res m g k s (residualPoint n ε h a w p C b P hε ha hh hw hb m g k s hm hg hk.le) +
          r • ψ)‖ ≤
      r⁻¹ * |Real.exp (2 * t) - Real.exp (2 * s)| *
        (2 * ‖Res m g k s (residualPoint n ε h a w p C b P hε ha hh hw hb m g k s hm hg hk.le)‖ +
          2 * ((2 * h ^ 2 / ε) * (12 + (m + 3 * g) / k)) * ‖ψ‖) := by
  have hdef := finite_packet_residual_two_time_resolvent_defect_norm_le
    n ε h a w p C b P hε ha hh hw hb m g k t s r hm hg hk.le hr
  have hd := split_norm_domination n ε h a w p C b P hε ha hh hw hb m g k s hm hg hk
  have hexp4 : (Real.exp (2 * s) *
      ‖(Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk.le)‖) ^ 2 =
      Real.exp (4 * s) *
        ‖(Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk.le)‖ ^ 2 := by
    rw [mul_pow, ← Real.exp_nat_mul, show (2 : ℕ) * (2 * s) = 4 * s by push_cast; ring]
  have hP_le := potential_linear_bound (norm_nonneg _) (by positivity)
    (norm_nonneg _) (sq_nonneg _) hexp4 hd
  exact scaled_resolvent_bound (Real.exp_pos (2 * s)).le
    (mul_nonneg (inv_nonneg.mpr hr.le) (abs_nonneg _)) hdef hP_le

theorem finite_packet_residual_two_time_resolvent_domination_sq_le (m g k t s r : ℝ)
    (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 < k) (hr : 0 < r) :
    Real.exp (4 * s) *
        ‖ψ - RS m g k t r (Res m g k s (residualPoint n ε h a w p C b P hε ha hh hw hb m g k s hm hg hk.le) +
          r • ψ)‖ ^ 2 ≤
      2 * (r⁻¹) ^ 2 * (Real.exp (2 * t) - Real.exp (2 * s)) ^ 2 *
        (‖Res m g k s (residualPoint n ε h a w p C b P hε ha hh hw hb m g k s hm hg hk.le)‖ ^ 2 +
          2 * ((2 * h ^ 2 / ε) * (12 + (m + 3 * g) / k)) ^ 2 * ‖ψ‖ ^ 2) := by
  rw [finite_packet_residual_two_time_resolvent_defect
    n ε h a w p C b P hε ha hh hw hb m g k t s r hm hg hk.le hr,
    norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hbound := KFCausalPositiveResolventBounds.resolvent_apply_norm_bound
    (Res m g k t) (RS m g k t r) r hr
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hb₀ m g k t r hr)
    (KFCausalClosedGraphForm.hamiltonian_positive
      (KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hb₀ m g k t))
    ((Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk.le))
  have hsq : ‖RS m g k t r ((Pot m g k)
      (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk.le))‖ ^ 2 ≤
      (r⁻¹) ^ 2 * ‖(Pot m g k)
        (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk.le)‖ ^ 2 := by
    have hp := pow_le_pow_left₀ (norm_nonneg _) hbound 2
    rwa [mul_pow] at hp
  have hd := split_norm_domination n ε h a w p C b P hε ha hh hw hb m g k s hm hg hk
  have hT_nonneg : 0 ≤ ‖(T) (staticPoint n ε h a w p C b P hε ha hh hw hb)‖ ^ 2 := sq_nonneg _
  have hP_dom : Real.exp (4 * s) *
      ‖(Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk.le)‖ ^ 2 ≤
      2 * (‖Res m g k s (residualPoint n ε h a w p C b P hε ha hh hw hb m g k s hm hg hk.le)‖ ^ 2 +
        2 * ((2 * h ^ 2 / ε) * (12 + (m + 3 * g) / k)) ^ 2 * ‖ψ‖ ^ 2) := by
    linarith [hd, hT_nonneg]
  have hm1 := mul_le_mul_of_nonneg_left hsq
    (show 0 ≤ Real.exp (4 * s) * (Real.exp (2 * t) - Real.exp (2 * s)) ^ 2 by positivity)
  have hm2 := mul_le_mul_of_nonneg_left hP_dom
    (show 0 ≤ (r⁻¹) ^ 2 * (Real.exp (2 * t) - Real.exp (2 * s)) ^ 2 by positivity)
  linarith

end FinitePacket

#print axioms common_hamiltonian_resolvent_three_operator_cancel
#print axioms common_residual_resolvent_two_operator_cancel
#print axioms common_growing_resolvent_two_operator_cancel
#print axioms common_hamiltonian_two_time_resolvent_defect
#print axioms common_residual_two_time_resolvent_defect
#print axioms finite_packet_growing_decomposition
#print axioms finite_packet_hamiltonian_resolvent_growing_cancel
#print axioms finite_packet_hamiltonian_resolvent_three_operator_cancel
#print axioms finite_packet_residual_resolvent_two_operator_cancel
#print axioms finite_packet_growing_resolvent_two_operator_cancel
#print axioms finite_packet_static_resolvent_cancel
#print axioms finite_packet_potential_resolvent_cancel
#print axioms finite_packet_hamiltonian_two_time_resolvent_growing_defect
#print axioms finite_packet_hamiltonian_two_time_resolvent_three_operator_defect
#print axioms finite_packet_hamiltonian_two_time_resolvent_defect_norm_le
#print axioms finite_packet_hamiltonian_two_time_resolvent_domination_norm_le
#print axioms finite_packet_hamiltonian_two_time_resolvent_domination_sq_le
#print axioms finite_packet_residual_two_time_difference
#print axioms finite_packet_residual_two_time_resolvent_defect
#print axioms finite_packet_residual_two_time_resolvent_defect_norm_le
#print axioms finite_packet_residual_two_time_resolvent_domination_norm_le
#print axioms finite_packet_residual_two_time_resolvent_domination_sq_le
end
end UnifiedTheory.Audit.KFCausalFiniteThreeOperatorResolventRegularity
