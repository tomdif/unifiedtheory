/- A stronger all-domain consequence of the radial cutoff argument.
The actual radial output has a positive mixed pairing with G-Kr. Thus
the squared norms of both separate outputs are controlled by G alone.
Identification of G-Kr with a separately completed potential Hamiltonian
is deliberately left to a subsequent domain theorem. -/
import UnifiedTheory.Audit.KFCausalClockFloorGrowingRadialDomination
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaStrongLimit

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGrowingRadialCrossEstimate
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorRadialYosidaSymbol (action)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialYosidaGrowing (formAction formAction_embedding)
open KFCausalClockFloorGrowingRadialDomination (form_lower radial_domain)
open KFCausalClockFloorRadialYosidaDomain (operator)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi*ε/3) (m g k : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "D" => KFCausalClockFloorGrowingHamiltonian.formData ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k

def radialOutput (x : (G).domain) : Hilbert :=
  operator ε hε h ⟨(x:Hilbert),radial_domain ε hε h hh hb m g k x⟩

def remainderOutput (x : (G).domain) : Hilbert :=
  G x-radialOutput ε hε h hh hb m g k x

theorem cutoff_pairing (N : ℝ) (hN : 0 < N) (x : (G).domain) :
    ‖action ε hε h N hN (x:Hilbert)‖^2 ≤
      (inner ℂ (G x) (action ε hε h N hN (x:Hilbert))).re := by
  have hl := form_lower ε hε h hh hb m g k N hN (KFCausalClosedGraphForm.formLift D x)
  have hp := KFCausalClosedGraphForm.hamiltonian_represents_form D x
    (formAction ε hε h N hN hb hh m g k (KFCausalClosedGraphForm.formLift D x))
  rw [hp,formAction_embedding,KFCausalClosedGraphForm.embedding_formLift] at hl
  exact hl

theorem radial_pairing (x : (G).domain) :
    ‖radialOutput ε hε h hh hb m g k x‖^2 ≤
      (inner ℂ (G x) (radialOutput ε hε h hh hb m g k x)).re := by
  have ht := KFCausalClockFloorRadialYosidaStrongLimit.domain_tendsto ε hε h
    ⟨(x:Hilbert),radial_domain ε hε h hh hb m g k x⟩
  have hl := ht.norm.pow 2
  have hr : Tendsto (fun n : ℕ =>
      (inner ℂ (G x) (action ε hε h ((n:ℝ)+1) (by positivity) (x:Hilbert))).re)
      atTop (𝓝 ((inner ℂ (G x) (radialOutput ε hε h hh hb m g k x)).re)) :=
    Complex.continuous_re.continuousAt.tendsto.comp
      (tendsto_const_nhds.inner ht)
  exact le_of_tendsto_of_tendsto hl hr
    (Eventually.of_forall (fun n => cutoff_pairing ε hε h hh hb m g k ((n:ℝ)+1) (by positivity) x))

theorem remainder_pairing (x : (G).domain) :
    0 ≤ (inner ℂ (remainderOutput ε hε h hh hb m g k x)
      (radialOutput ε hε h hh hb m g k x)).re := by
  have hp := radial_pairing ε hε h hh hb m g k x
  rw [remainderOutput,inner_sub_left,Complex.sub_re,inner_self_eq_norm_sq_to_K]
  change 0 ≤ (inner ℂ (G x) (radialOutput ε hε h hh hb m g k x)).re-
    ((‖radialOutput ε hε h hh hb m g k x‖:ℂ)^2).re
  rw [← Complex.ofReal_pow,Complex.ofReal_re]
  linarith

theorem split_norm_square (x : (G).domain) :
    ‖radialOutput ε hε h hh hb m g k x‖^2+
      ‖remainderOutput ε hε h hh hb m g k x‖^2 ≤ ‖G x‖^2 := by
  have hp := radial_pairing ε hε h hh hb m g k x
  rw [remainderOutput,norm_sub_sq (𝕜 := ℂ)]
  change ‖radialOutput ε hε h hh hb m g k x‖^2+
    (‖G x‖^2-2*(inner ℂ (G x) (radialOutput ε hε h hh hb m g k x)).re+
      ‖radialOutput ε hε h hh hb m g k x‖^2) ≤ ‖G x‖^2
  linarith

theorem remainder_norm (x : (G).domain) :
    ‖remainderOutput ε hε h hh hb m g k x‖ ≤ ‖G x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hs := split_norm_square ε hε h hh hb m g k x
  nlinarith only [hs,sq_nonneg ‖radialOutput ε hε h hh hb m g k x‖]

#print axioms cutoff_pairing
#print axioms radial_pairing
#print axioms remainder_pairing
#print axioms split_norm_square
#print axioms remainder_norm
end
end UnifiedTheory.Audit.KFCausalClockFloorGrowingRadialCrossEstimate
