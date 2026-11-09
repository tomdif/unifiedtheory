/- Norm domination of the residual operator S(t) on all of Dom H(t), and
joint domination of the static operator T, potential operator P, radial
operator Kr, and full growing operator G by the full Hamiltonian H(t) on
the original finite sourced packet family. -/
import UnifiedTheory.Audit.KFCausalFiniteResidualStaticPotentialDomination

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalFiniteFullHamiltonianDomination
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalFinitePotentialHamiltonianDomain (hamiltonian_strip)
open KFCausalFinitePotentialStaticMixedBound (potentialPoint staticPoint)
open KFCausalFiniteResidualStaticPotentialDomination (residualPoint split_norm_domination)

private theorem norm_add_sq_le_two (u v : Hilbert) :
    ‖u+v‖^2 ≤ 2*‖u‖^2+2*‖v‖^2 := by
  have h1 : ‖u+v‖ ≤ ‖u‖+‖v‖ := norm_add_le u v
  have h2 : ‖u+v‖^2 ≤ (‖u‖+‖v‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : 0 ≤ (‖u‖-‖v‖)^2 := sq_nonneg _
  nlinarith

theorem radial_scaled_norm_le (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (hb : |h| ≤ Real.pi*ε/3) (m g k t : ℝ)
    (x : (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh
      (KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb) m g k t).domain) :
    Real.exp (2*t)*‖KFCausalClockFloorHamiltonianRadialSum.radialOutput ε hε h hh hb m g k t x‖ ≤
      ‖KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh
        (KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb) m g k t x‖+
      (|h| /ε)*Real.exp t*‖(x:Hilbert)‖ := by
  have hr := KFCausalClockFloorHamiltonianRadialDomination.radial_norm ε hε h hh hb m g k t x
  have hm := mul_le_mul_of_nonneg_left hr (Real.exp_pos (2*t)).le
  change Real.exp (2*t)*‖KFCausalClockFloorHamiltonianRadialSum.radialOutput ε hε h hh hb m g k t x‖ ≤
    Real.exp (2*t)*(‖KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh
      (KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb) m g k t x‖/Real.exp (2*t)+
      (|h| /ε*‖(x:Hilbert)‖)/Real.exp t) at hm
  have he : Real.exp (2*t)=Real.exp t*Real.exp t := by
    rw [← Real.exp_add,show t+t=2*t by ring]
  have hrhs : Real.exp (2*t)*(‖KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh
      (KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb) m g k t x‖/Real.exp (2*t)+
      (|h| /ε*‖(x:Hilbert)‖)/Real.exp t)=
      ‖KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh
        (KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb) m g k t x‖+
      (|h| /ε)*Real.exp t*‖(x:Hilbert)‖ := by
    have h1 : Real.exp (2*t) ≠ 0 := (Real.exp_pos _).ne'
    have h2 : Real.exp t ≠ 0 := (Real.exp_pos _).ne'
    rw [mul_add,mul_div_cancel₀ _ h1,he,mul_assoc,mul_div_cancel₀ _ h2]
    ring
  exact hm.trans_eq hrhs

theorem residual_norm_le (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (hb : |h| ≤ Real.pi*ε/3) (m g k t : ℝ)
    (x : (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh
      (KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb) m g k t).domain) :
    ‖KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh
      (KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb) m g k t
      ⟨(x:Hilbert),KFCausalClockFloorHamiltonianRadialSum.residual_domain ε hε h hh hb m g k t x⟩‖ ≤
      2*‖KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh
        (KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb) m g k t x‖+
      (|h| /ε)*Real.exp t*‖(x:Hilbert)‖ := by
  rw [KFCausalClockFloorHamiltonianRadialSum.residual_output ε hε h hh hb m g k t x]
  have hsub := norm_sub_le
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh
      (KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb) m g k t x)
    ((Real.exp (2*t):ℂ) • KFCausalClockFloorHamiltonianRadialSum.radialOutput ε hε h hh hb m g k t x)
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] at hsub
  have hr := radial_scaled_norm_le ε hε h hh hb m g k t x
  linarith

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i)
  (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ ε/10)
local notation "ψ" => KFCausalReciprocalNeutralSuperposition.state n ε h a w p C b P hε ha hh hw
local notation "hb₀" => hamiltonian_strip ε h hε hb
local notation "hb₁" => KFCausalSingleGaussianMixedSquare.original_strip ε h hε hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "Pot" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hb₀
local notation "Grow" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hb₀
local notation "Res" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hb₀
local notation "FullH" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hb₀

def hamiltonianPoint (m g k t : ℝ) : (FullH m g k t).domain :=
  ⟨ψ,LinearPMap.mem_domain_of_mem_graph
    (KFCausalFiniteHamiltonianSquare.first_graph n ε h a w p C b P hε ha hh hw hb m g k t)⟩

def growingPoint (m g k : ℝ) : (Grow m g k).domain :=
  ⟨ψ,KFCausalFiniteGrowingHamiltonianOutput.growing_domain n ε h a w p C b P hε ha hh hw hb m g k⟩

theorem static_potential_hamiltonian_bound (m g k t : ℝ) (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 < k) :
    ‖(T) (staticPoint n ε h a w p C b P hε ha hh hw hb)‖^2+
      (1/2)*Real.exp (4*t)*‖(Pot m g k)
        (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk.le)‖^2 ≤
      (2*‖FullH m g k t (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k t)‖+
        (|h| /ε)*Real.exp t*‖ψ‖)^2+
      2*((2*h^2/ε)*(12+(m+3*g)/k))^2*‖ψ‖^2 := by
  have hd := split_norm_domination n ε h a w p C b P hε ha hh hw hb m g k t hm hg hk
  have hr := residual_norm_le ε hε h hh hb₁ m g k t
    (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k t)
  have hsq : ‖Res m g k t (residualPoint n ε h a w p C b P hε ha hh hw hb m g k t hm hg hk.le)‖^2 ≤
      (2*‖FullH m g k t (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k t)‖+
        (|h| /ε)*Real.exp t*‖ψ‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hr 2
  linarith

theorem growing_residual_bound (m g k t : ℝ) (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 < k) :
    Real.exp (4*t)*‖Grow m g k (growingPoint n ε h a w p C b P hε ha hh hw hb m g k)‖^2 ≤
      2*(Real.exp (2*t)*‖KFCausalClockFloorHamiltonianRadialSum.radialOutput ε hε h hh hb₁ m g k t
        (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k t)‖)^2+
      4*‖Res m g k t (residualPoint n ε h a w p C b P hε ha hh hw hb m g k t hm hg hk.le)‖^2+
      8*((2*h^2/ε)*(12+(m+3*g)/k))^2*‖ψ‖^2 := by
  have hG : Grow m g k (growingPoint n ε h a w p C b P hε ha hh hw hb m g k)=
      KFCausalFiniteGrowingHamiltonianOutput.growingOutput n ε h a w p C b P hε ha hh hw hb m g k :=
    (Grow m g k).mem_graph_snd_inj' ((Grow m g k).mem_graph _)
      (KFCausalFiniteGrowingHamiltonianOutput.growing_graph n ε h a w p C b P hε ha hh hw hb m g k) rfl
  have hK : KFCausalClockFloorHamiltonianRadialSum.radialOutput ε hε h hh hb₁ m g k t
      (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k t)=
      KFCausalFinitePotentialStaticGraph.radialOutput n ε h a w p C b P hε ha hh hw hb :=
    (KFCausalClockFloorRadialYosidaDomain.operator ε hε h).mem_graph_snd_inj'
      ((KFCausalClockFloorRadialYosidaDomain.operator ε hε h).mem_graph _)
      (KFCausalFinitePotentialStaticGraph.radial_graph n ε h a w p C b P hε ha hh hw hb) rfl
  have hP : (Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk.le)=
      KFCausalOrderedStaticPotentialHilbertBound.weightedOutput n ε h a w p C b P hε ha hh hw hb m g k :=
    (Pot m g k).mem_graph_snd_inj' ((Pot m g k).mem_graph _)
      (KFCausalFinitePotentialStaticGraph.potential_graph n ε h a w p C b P hε ha hh hw hb m g k hm hg hk.le) rfl
  have hsplit : Grow m g k (growingPoint n ε h a w p C b P hε ha hh hw hb m g k)=
      KFCausalClockFloorHamiltonianRadialSum.radialOutput ε hε h hh hb₁ m g k t
        (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k t)+
      (Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk.le) := by
    rw [hG,hK,hP]
    exact KFCausalFinitePotentialStaticGraph.growing_split n ε h a w p C b P hε ha hh hw hb m g k hm hg hk.le
  have h2 := norm_add_sq_le_two
    (KFCausalClockFloorHamiltonianRadialSum.radialOutput ε hε h hh hb₁ m g k t
      (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k t))
    ((Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk.le))
  rw [← hsplit] at h2
  have hm4 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos (4*t)).le
  have hexp : Real.exp (4*t)*(2*‖KFCausalClockFloorHamiltonianRadialSum.radialOutput ε hε h hh hb₁ m g k t
      (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k t)‖^2)=
      2*(Real.exp (2*t)*‖KFCausalClockFloorHamiltonianRadialSum.radialOutput ε hε h hh hb₁ m g k t
        (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k t)‖)^2 := by
    rw [mul_pow,← Real.exp_nat_mul,show (2:ℕ)*(2*t)=4*t by push_cast; ring]
    ring
  have hd := split_norm_domination n ε h a w p C b P hε ha hh hw hb m g k t hm hg hk
  have hT : 0 ≤ ‖(T) (staticPoint n ε h a w p C b P hε ha hh hw hb)‖^2 := sq_nonneg _
  linarith

theorem growing_hamiltonian_bound (m g k t : ℝ) (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 < k) :
    Real.exp (4*t)*‖Grow m g k (growingPoint n ε h a w p C b P hε ha hh hw hb m g k)‖^2 ≤
      2*(‖FullH m g k t (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k t)‖+
        (|h| /ε)*Real.exp t*‖ψ‖)^2+
      4*(2*‖FullH m g k t (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k t)‖+
        (|h| /ε)*Real.exp t*‖ψ‖)^2+
      8*((2*h^2/ε)*(12+(m+3*g)/k))^2*‖ψ‖^2 := by
  have hg' := growing_residual_bound n ε h a w p C b P hε ha hh hw hb m g k t hm hg hk
  have hr := radial_scaled_norm_le ε hε h hh hb₁ m g k t
    (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k t)
  have hs := residual_norm_le ε hε h hh hb₁ m g k t
    (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k t)
  have hrsq : (Real.exp (2*t)*‖KFCausalClockFloorHamiltonianRadialSum.radialOutput ε hε h hh hb₁ m g k t
      (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k t)‖)^2 ≤
      (‖FullH m g k t (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k t)‖+
        (|h| /ε)*Real.exp t*‖ψ‖)^2 :=
    pow_le_pow_left₀ (by positivity) hr 2
  have hssq : ‖Res m g k t (residualPoint n ε h a w p C b P hε ha hh hw hb m g k t hm hg hk.le)‖^2 ≤
      (2*‖FullH m g k t (hamiltonianPoint n ε h a w p C b P hε ha hh hw hb m g k t)‖+
        (|h| /ε)*Real.exp t*‖ψ‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hs 2
  linarith

#print axioms radial_scaled_norm_le
#print axioms residual_norm_le
#print axioms static_potential_hamiltonian_bound
#print axioms growing_residual_bound
#print axioms growing_hamiltonian_bound
end
end UnifiedTheory.Audit.KFCausalFiniteFullHamiltonianDomination
