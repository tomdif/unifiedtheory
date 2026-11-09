/- Conditional Hilbert-form supplier: a selfadjoint Hilbert contraction
which acts contractively on a closed energy form makes every positive
resolvent contractive for the bounded difference energy I-F. The form
intertwining and energy contraction are explicit hypotheses. No physical
static-heat or potential-domain preservation is asserted here. -/
import UnifiedTheory.Audit.KFCausalClosedGraphForm
import UnifiedTheory.Audit.KFCausalPositiveResolventBounds

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 900000

namespace UnifiedTheory.Audit.KFCausalFormContractiveResolventTransfer
noncomputable section
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] in
private theorem difference_nonnegative (F : H →L[ℂ] H)
    (hc : ∀ x, ‖F x‖≤‖x‖) (x : H) :
    0≤(inner ℂ x (x-F x)).re := by
  rw [inner_sub_right,Complex.sub_re]
  have hself : (inner ℂ x x).re=‖x‖^2 := inner_self_eq_norm_sq (𝕜:=ℂ) x
  rw [hself]
  have hi : (inner ℂ x (F x)).re≤‖x‖*‖F x‖ := re_inner_le_norm (𝕜:=ℂ) x (F x)
  have hn := mul_le_mul_of_nonneg_left (hc x) (norm_nonneg x)
  nlinarith

omit [CompleteSpace K] in
private theorem energy_difference_nonnegative (x y : K) (hy : ‖y‖≤‖x‖) :
    0≤(inner ℂ x (x-y)).re := by
  rw [inner_sub_right,Complex.sub_re]
  have hself : (inner ℂ x x).re=‖x‖^2 := inner_self_eq_norm_sq (𝕜:=ℂ) x
  rw [hself]
  have hi : (inner ℂ x y).re≤‖x‖*‖y‖ := re_inner_le_norm (𝕜:=ℂ) x y
  have hn := mul_le_mul_of_nonneg_left hy (norm_nonneg x)
  nlinarith

open KFCausalClosedGraphForm
variable (D : KFCausalClosedGraphForm.Data H K)
variable (F : H →L[ℂ] H)
  (lift : KFCausalClosedGraphForm.FormSpace D →L[ℂ] KFCausalClosedGraphForm.FormSpace D)
  (hJ : ∀ v, KFCausalClosedGraphForm.embedding D (lift v)=
    F (KFCausalClosedGraphForm.embedding D v))
  (hB : ∀ v, ‖KFCausalClosedGraphForm.energyOutput D (lift v)‖≤
    ‖KFCausalClosedGraphForm.energyOutput D v‖)
  (R : H →L[ℂ] H) (N : ℝ) (hN : 0<N)
  (hR : KFCausalPositiveResolventBounds.Resolves
    (KFCausalClosedGraphForm.hamiltonian D) R N)

include hJ hB hN hR in
theorem resolvent_difference_pairing (x : H) :
    (inner ℂ (R (N • x)) (R (N • x)-F (R (N • x)))).re≤
      (inner ℂ x (R (N • x)-F (R (N • x)))).re := by
  let u : (hamiltonian D).domain := KFCausalPositiveResolventBounds.point (hamiltonian D) R N hR (N • x)
  let v : FormSpace D := KFCausalClosedGraphForm.formLift D u
  have hj : embedding D v=R (N • x) := KFCausalClosedGraphForm.embedding_formLift D u
  have hb := energy_difference_nonnegative (energyOutput D v) (energyOutput D (lift v)) (hB v)
  have hp := KFCausalClosedGraphForm.hamiltonian_represents_form D u (v-lift v)
  rw [map_sub,map_sub,hJ,hj] at hp
  have hv : hamiltonian D u=N • x-N • R (N • x) :=
    KFCausalPositiveResolventBounds.point_value (hamiltonian D) R N hR (N • x)
  rw [hv,←smul_sub,inner_smul_left_eq_smul,inner_sub_left] at hp
  have he := congrArg Complex.re hp
  simp only [Complex.real_smul] at he
  rw [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.sub_re] at he
  change (inner ℂ (energyOutput D v) (energyOutput D v-energyOutput D (lift v))).re=
    N*((inner ℂ x (R (N • x)-F (R (N • x)))).re-
      (inner ℂ (R (N • x)) (R (N • x)-F (R (N • x)))).re) at he
  have hn : 0≤N*((inner ℂ x (R (N • x)-F (R (N • x)))).re-
      (inner ℂ (R (N • x)) (R (N • x)-F (R (N • x)))).re) := he ▸ hb
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hN).mp hn)

private theorem quadratic_contraction (F : H →L[ℂ] H)
    (hs : IsSelfAdjoint F) (hc : ∀x,‖F x‖≤‖x‖) (x u : H)
    (hp : (inner ℂ u (u-F u)).re≤(inner ℂ x (u-F u)).re) :
    (inner ℂ u (u-F u)).re≤(inner ℂ x (x-F x)).re := by
  have hn := difference_nonnegative F hc (x-u)
  have he : (inner ℂ u (x-F x)).re=(inner ℂ x (u-F u)).re := by
    rw [inner_sub_right,inner_sub_right,Complex.sub_re,Complex.sub_re]
    have hsym := hs.isSymmetric x u
    have hs' : (inner ℂ (F x) u).re=(inner ℂ x (F u)).re := congrArg Complex.re hsym
    have h1 : (inner ℂ u x).re=(inner ℂ x u).re := inner_re_symm (𝕜:=ℂ) u x
    have h2 : (inner ℂ u (F x)).re=(inner ℂ (F x) u).re := inner_re_symm (𝕜:=ℂ) u (F x)
    rw [h1,h2,hs']
  have hx : (x-u)-F (x-u)=(x-F x)-(u-F u) := by rw [map_sub]; abel
  rw [hx] at hn
  simp only [inner_sub_left,inner_sub_right,Complex.sub_re] at hn hp ⊢
  simp only [inner_sub_right,Complex.sub_re] at he
  linarith

include hJ hB hN hR in
theorem resolvent_difference_contraction (hs : IsSelfAdjoint F)
    (hc : ∀x,‖F x‖≤‖x‖) (x : H) :
    (inner ℂ (R (N • x)) (R (N • x)-F (R (N • x)))).re≤
      (inner ℂ x (x-F x)).re :=
  quadratic_contraction F hs hc x (R (N • x))
    (resolvent_difference_pairing D F lift hJ hB R N hN hR x)

#print axioms resolvent_difference_pairing
#print axioms resolvent_difference_contraction
end
end UnifiedTheory.Audit.KFCausalFormContractiveResolventTransfer
