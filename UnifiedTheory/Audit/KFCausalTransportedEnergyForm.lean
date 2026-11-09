/- Positive energy under a bounded coordinate change. A bounded output
term has a derived energy bound whenever the original form is coercive. -/
import UnifiedTheory.Audit.KFCausalWeightedMassEnergy
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalTransportedEnergyForm
noncomputable section
open UnifiedTheory.Audit.KFCausalWeightedMassEnergy
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

def metric (S F : V →L[ℂ] V) : V →L[ℂ] V := S.adjoint*(F*S)

theorem metric_pairing (S F : V →L[ℂ] V) (x y : V) :
    inner ℂ x (metric S F y) = inner ℂ (S x) (F (S y)) :=
  S.adjoint_inner_right x (F (S y))

theorem metric_energy (S F : V →L[ℂ] V) (x : V) : energy (metric S F) x = energy F (S x) :=
  congrArg Complex.re (metric_pairing S F x x)

theorem metric_symmetric (S F : V →L[ℂ] V) (hF : F.toLinearMap.IsSymmetric) :
    (metric S F).toLinearMap.IsSymmetric := by
  intro x y
  change inner ℂ (S.adjoint (F (S x))) y = inner ℂ x (S.adjoint (F (S y)))
  rw [S.adjoint_inner_left,S.adjoint_inner_right]
  exact hF (S x) (S y)

theorem metric_nonnegative (S F : V →L[ℂ] V) (hp : ∀ x, 0 ≤ energy F x) (x : V) :
    0 ≤ energy (metric S F) x := by rw [metric_energy]; exact hp _

omit [CompleteSpace V] in
theorem bounded_output_energy (F B : V →L[ℂ] V) (d : ℝ) (hd : 0 < d)
    (hco : ∀ x, d*‖x‖^2 ≤ energy F x) (x : V) :
    (inner ℂ x (F (B x))).re ≤ (‖F‖*‖B‖/d)*energy F x := by
  have hn : (inner ℂ x (F (B x))).re ≤ ‖F‖*‖B‖*‖x‖^2 := by
    calc
      _ ≤ ‖x‖*‖F (B x)‖ := re_inner_le_norm (𝕜 := ℂ) x (F (B x))
      _ ≤ ‖x‖*(‖F‖*(‖B‖*‖x‖)) := mul_le_mul_of_nonneg_left
        ((F.le_opNorm _).trans (mul_le_mul_of_nonneg_left (B.le_opNorm _) (norm_nonneg F))) (norm_nonneg x)
      _ = _ := by ring
  have he : ‖x‖^2 ≤ energy F x/d := (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using hco x)
  exact hn.trans ((mul_le_mul_of_nonneg_left he (mul_nonneg (norm_nonneg F) (norm_nonneg B))).trans_eq (by ring))

omit [CompleteSpace V] in
theorem bounded_transported_output (F S U B : V →L[ℂ] V) (d : ℝ) (hd : 0 < d)
    (hi : ∀ x, U (S x) = x) (hco : ∀ x, d*‖x‖^2 ≤ energy F x) (x : V) :
    (inner ℂ (S x) (F (B x))).re ≤ (‖F‖*‖B*U‖/d)*energy F (S x) := by
  have he := bounded_output_energy F (B*U) d hd hco (S x)
  simpa only [ContinuousLinearMap.mul_apply,hi] using he

omit [CompleteSpace V] in
theorem imaginary_output_zero (F : V →L[ℂ] V) (c : ℂ) (hc : c.re = 0)
    (x z : V) (hz : (inner ℂ x (F z)).im = 0) : (inner ℂ x (F (c • z))).re = 0 := by
  rw [map_smul,inner_smul_right]
  simp only [Complex.mul_re,hc,hz,zero_mul,mul_zero,sub_zero]

omit [CompleteSpace V] in
theorem graph_action (T G : V →ₗ.[ℂ] V) (S C : V →L[ℂ] V) (c : ℂ)
    (ha : ∀ x : G.domain, ∃ z, (S x,z) ∈ T.graph ∧ S (G x-C x) = c • z)
    (x y : V) (hxy : (x,y) ∈ G.graph) : ∃ z, (S x,z) ∈ T.graph ∧ S (y-C x) = c • z := by
  obtain ⟨hx,hval⟩ := (KFCausalMassFormOperator.graph_domain_iff G x y).mp hxy
  simpa only [hval] using ha ⟨x,hx⟩

theorem transformed_quasi_bound (T G : V →ₗ.[ℂ] V) (F S U C : V →L[ℂ] V) (c : ℂ) (d : ℝ)
    (hc : c.re = 0) (hd : 0 < d) (hi : ∀ x, U (S x) = x)
    (hco : ∀ x, d*‖x‖^2 ≤ energy F x)
    (ha : ∀ x : G.domain, ∃ z, (S x,z) ∈ T.graph ∧ S (G x-C x) = c • z)
    (hr : ∀ x z, (S x,z) ∈ T.graph → (inner ℂ (S x) (F z)).im = 0)
    (x y : V) (hxy : (x,y) ∈ G.graph) :
    (inner ℂ x (metric S F y)).re ≤ (‖F‖*‖(S*C)*U‖/d)*energy (metric S F) x := by
  obtain ⟨z,hz,he⟩ := graph_action T G S C c ha x y hxy
  have hs : S y = c • z+S (C x) := by
    rw [map_sub] at he
    exact sub_eq_iff_eq_add.mp he
  rw [metric_pairing,metric_energy,hs,map_add,inner_add_right,Complex.add_re,
    imaginary_output_zero F c hc (S x) z (hr x z hz),zero_add]
  exact bounded_transported_output F S U (S*C) d hd hi hco x

theorem quasi_bound_of_eq (T G : V →ₗ.[ℂ] V) (F S U C W : V →L[ℂ] V)
    (c : ℂ) (d ω : ℝ) (hW : W = metric S F) (hω : ω = ‖F‖*‖(S*C)*U‖/d)
    (hc : c.re = 0) (hd : 0 < d) (hi : ∀ x, U (S x) = x)
    (hco : ∀ x, d*‖x‖^2 ≤ energy F x)
    (ha : ∀ x : G.domain, ∃ z, (S x,z) ∈ T.graph ∧ S (G x-C x) = c • z)
    (hr : ∀ x z, (S x,z) ∈ T.graph → (inner ℂ (S x) (F z)).im = 0)
    (x y : V) (hxy : (x,y) ∈ G.graph) : (inner ℂ x (W y)).re ≤ ω*energy W x := by
  rw [hW,hω]
  exact transformed_quasi_bound T G F S U C c d hc hd hi hco ha hr x y hxy

theorem metric_bound_to_transported (S F A W : V →L[ℂ] V) (κ : ℝ)
    (hW : W = metric S F)
    (hb : ∀ x, (inner ℂ x (W (A x))).re ≤ κ*energy W x) (x : V) :
    (inner ℂ (S x) (F (S (A x)))).re ≤ κ*energy F (S x) := by
  simpa only [hW,metric_pairing,metric_energy] using hb x

omit [CompleteSpace V] in
theorem pairing_bound_to_transported (S F W : V →L[ℂ] V) (κ : ℝ) (x y : V)
    (hp : inner ℂ x (W y) = inner ℂ (S x) (F (S y)))
    (he : energy W x = energy F (S x))
    (hb : (inner ℂ x (W y)).re ≤ κ*energy W x) :
    (inner ℂ (S x) (F (S y))).re ≤ κ*energy F (S x) := by
  simpa only [hp,he] using hb

#print axioms metric_pairing
#print axioms metric_energy
#print axioms metric_symmetric
#print axioms metric_nonnegative
#print axioms bounded_output_energy
#print axioms bounded_transported_output
#print axioms imaginary_output_zero
#print axioms graph_action
#print axioms transformed_quasi_bound
#print axioms quasi_bound_of_eq
#print axioms metric_bound_to_transported
#print axioms pairing_bound_to_transported
end
end UnifiedTheory.Audit.KFCausalTransportedEnergyForm
