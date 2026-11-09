/- Joint static and time-weighted potential norm domination by the residual
Hamiltonian S(t) on the original finite sourced packet family, obtained by
combining S(t)ψ = Tψ + exp(2t)Pψ with the whole-clock potential/static
mixed lower bound. -/
import UnifiedTheory.Audit.KFCausalFinitePotentialStaticMixedBound
import UnifiedTheory.Audit.KFCausalClockFloorResidualStaticPotentialDecomposition

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalFiniteResidualStaticPotentialDomination
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalFinitePotentialHamiltonianDomain (hamiltonian_strip)
open KFCausalFinitePotentialStaticMixedBound (potentialPoint staticPoint operator_mixed_lower)

private theorem norm_add_smul_exp_sq (y z : Hilbert) (t : ℝ) :
    ‖y+(Real.exp (2*t):ℂ) • z‖^2=
      ‖y‖^2+Real.exp (4*t)*‖z‖^2+2*Real.exp (2*t)*(inner ℂ z y).re := by
  have h1 : ‖y+(Real.exp (2*t):ℂ) • z‖^2=
      ‖y‖^2+2*(inner ℂ y ((Real.exp (2*t):ℂ) • z)).re+‖(Real.exp (2*t):ℂ) • z‖^2 :=
    norm_add_sq (𝕜 := ℂ) y ((Real.exp (2*t):ℂ) • z)
  have h2 : ‖(Real.exp (2*t):ℂ) • z‖^2=Real.exp (4*t)*‖z‖^2 := by
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
      mul_pow,← Real.exp_nat_mul,show (2:ℕ)*(2*t)=4*t by push_cast; ring]
  have hsymm : (inner ℂ y z).re=(inner ℂ z y).re := inner_re_symm (𝕜 := ℂ) y z
  have h3 : (inner ℂ y ((Real.exp (2*t):ℂ) • z)).re=
      Real.exp (2*t)*(inner ℂ z y).re := by
    rw [inner_smul_right,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero,hsymm]
  rw [h2,h3] at h1
  linarith

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i)
  (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ ε/10)
local notation "ψ" => KFCausalReciprocalNeutralSuperposition.state n ε h a w p C b P hε ha hh hw
local notation "hb₀" => hamiltonian_strip ε h hε hb
local notation "hb₁" => KFCausalSingleGaussianMixedSquare.original_strip ε h hε hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "Pot" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hb₀
local notation "Res" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hb₀
local notation "FullH" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hb₀

theorem residual_graph (m g k t : ℝ) (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k) :
    (ψ,(T) (staticPoint n ε h a w p C b P hε ha hh hw hb)+
      (Real.exp (2*t):ℂ) • (Pot m g k)
        (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk)) ∈
      (Res m g k t).graph := by
  let xH : (FullH m g k t).domain :=
    ⟨ψ,LinearPMap.mem_domain_of_mem_graph
      (KFCausalFiniteHamiltonianSquare.first_graph n ε h a w p C b P hε ha hh hw hb m g k t)⟩
  have hs : ψ ∈ (Res m g k t).domain :=
    KFCausalClockFloorHamiltonianRadialSum.residual_domain ε hε h hh hb₁ m g k t xH
  let SD := KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hb₀ m g k t
  let u := KFCausalClosedGraphForm.formLift SD ⟨ψ,hs⟩
  have hu : KFCausalClosedGraphForm.embedding SD u=ψ :=
    KFCausalClosedGraphForm.embedding_formLift SD ⟨ψ,hs⟩
  have ht : (KFCausalClosedGraphForm.embedding SD u,
      (T) (staticPoint n ε h a w p C b P hε ha hh hw hb)) ∈ (T).graph :=
    (congrArg (fun x : Hilbert =>
      (x,(T) (staticPoint n ε h a w p C b P hε ha hh hw hb)) ∈ (T).graph) hu.symm).mp
      ((T).mem_graph (staticPoint n ε h a w p C b P hε ha hh hw hb))
  have hp : (KFCausalClosedGraphForm.embedding SD u,
      (Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk)) ∈
      (Pot m g k).graph :=
    (congrArg (fun x : Hilbert =>
      (x,(Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk)) ∈
        (Pot m g k).graph) hu.symm).mp
      ((Pot m g k).mem_graph (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk))
  have hg' := KFCausalClockFloorResidualStaticPotentialDecomposition.sum_graph
    ε hε h hh hb₀ m g k t u _ _ ht hp
  exact (congrArg (fun x : Hilbert =>
    (x,(T) (staticPoint n ε h a w p C b P hε ha hh hw hb)+
      (Real.exp (2*t):ℂ) • (Pot m g k)
        (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk)) ∈
      (Res m g k t).graph) hu).mp hg'

def residualPoint (m g k t : ℝ) (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k) :
    (Res m g k t).domain :=
  ⟨ψ,LinearPMap.mem_domain_of_mem_graph
    (residual_graph n ε h a w p C b P hε ha hh hw hb m g k t hm hg hk)⟩

theorem residual_output_eq (m g k t : ℝ) (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k) :
    Res m g k t (residualPoint n ε h a w p C b P hε ha hh hw hb m g k t hm hg hk)=
      (T) (staticPoint n ε h a w p C b P hε ha hh hw hb)+
      (Real.exp (2*t):ℂ) • (Pot m g k)
        (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk) :=
  (Res m g k t).mem_graph_snd_inj'
    ((Res m g k t).mem_graph (residualPoint n ε h a w p C b P hε ha hh hw hb m g k t hm hg hk))
    (residual_graph n ε h a w p C b P hε ha hh hw hb m g k t hm hg hk) rfl

theorem residual_norm_sq_eq (m g k t : ℝ) (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k) :
    ‖Res m g k t (residualPoint n ε h a w p C b P hε ha hh hw hb m g k t hm hg hk)‖^2=
      ‖(T) (staticPoint n ε h a w p C b P hε ha hh hw hb)‖^2+
      Real.exp (4*t)*‖(Pot m g k)
        (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk)‖^2+
      2*Real.exp (2*t)*(inner ℂ ((Pot m g k)
        (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk))
        ((T) (staticPoint n ε h a w p C b P hε ha hh hw hb))).re := by
  rw [residual_output_eq]
  exact norm_add_smul_exp_sq _ _ t

theorem split_energy_bound (m g k t : ℝ) (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 < k) :
    ‖(T) (staticPoint n ε h a w p C b P hε ha hh hw hb)‖^2+
      Real.exp (4*t)*‖(Pot m g k)
        (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk.le)‖^2 ≤
      ‖Res m g k t (residualPoint n ε h a w p C b P hε ha hh hw hb m g k t hm hg hk.le)‖^2+
      2*Real.exp (2*t)*((2*h^2/ε)*(12+(m+3*g)/k))*
        (inner ℂ ψ ((Pot m g k)
          (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk.le))).re := by
  have he := residual_norm_sq_eq n ε h a w p C b P hε ha hh hw hb m g k t hm hg hk.le
  have hm' := operator_mixed_lower n ε h a w p C b P hε ha hh hw hb m g k hm hg hk
  have hexp : 0 ≤ 2*Real.exp (2*t) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hm' hexp
  linarith

theorem split_norm_domination (m g k t : ℝ) (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 < k) :
    ‖(T) (staticPoint n ε h a w p C b P hε ha hh hw hb)‖^2+
      (1/2)*Real.exp (4*t)*‖(Pot m g k)
        (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk.le)‖^2 ≤
      ‖Res m g k t (residualPoint n ε h a w p C b P hε ha hh hw hb m g k t hm hg hk.le)‖^2+
      2*((2*h^2/ε)*(12+(m+3*g)/k))^2*‖ψ‖^2 := by
  let γ := (2*h^2/ε)*(12+(m+3*g)/k)
  let pVec := (Pot m g k) (potentialPoint n ε h a w p C b P hε ha hh hw hb m g k hm hg hk.le)
  have hγ : 0 ≤ γ := by positivity
  have hs := split_energy_bound n ε h a w p C b P hε ha hh hw hb m g k t hm hg hk
  have hcs : (inner ℂ ψ pVec).re ≤ ‖ψ‖*‖pVec‖ := re_inner_le_norm (𝕜 := ℂ) ψ pVec
  have hmul : 2*Real.exp (2*t)*γ*(inner ℂ ψ pVec).re ≤
      2*Real.exp (2*t)*γ*(‖ψ‖*‖pVec‖) :=
    mul_le_mul_of_nonneg_left hcs (by positivity)
  have hexp4 : (Real.exp (2*t))^2=Real.exp (4*t) := by
    rw [← Real.exp_nat_mul,show (2:ℕ)*(2*t)=4*t by push_cast; ring]
  have hyoung : 2*Real.exp (2*t)*γ*(‖ψ‖*‖pVec‖) ≤
      (1/2)*Real.exp (4*t)*‖pVec‖^2+2*γ^2*‖ψ‖^2 := by
    have hsq : 0 ≤ ((1/2)*Real.exp (2*t)*‖pVec‖-γ*‖ψ‖)^2 := sq_nonneg _
    nlinarith [hsq,hexp4]
  linarith

#print axioms residual_graph
#print axioms residual_output_eq
#print axioms residual_norm_sq_eq
#print axioms split_energy_bound
#print axioms split_norm_domination
end
end UnifiedTheory.Audit.KFCausalFiniteResidualStaticPotentialDomination
