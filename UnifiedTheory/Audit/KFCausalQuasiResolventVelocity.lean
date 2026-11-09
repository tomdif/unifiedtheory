/- Uniform velocity-energy control from actual generator-output bounds.
The smoothed state and its regularization error retain exact graph identities. -/
import UnifiedTheory.Audit.KFCausalQuasiDissipativeResolvent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalQuasiResolventVelocity
noncomputable section
open UnifiedTheory.Audit.KFCausalWeightedMassEnergy
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem scaled_energy (T : V →ₗ.[ℂ] V) (W R : V →L[ℂ] V) (b ω : ℝ)
    (hW : W.toLinearMap.IsSymmetric) (hp : ∀ x, 0 ≤ energy W x)
    (hb : 0 < b) (hω : 0 ≤ ω) (hhalf : 2*ω ≤ b)
    (hR : ∀ f, (R f,b • R f-f) ∈ T.graph)
    (hq : ∀ x y, (x,y) ∈ T.graph → (inner ℂ x (W y)).re ≤ ω*energy W x) (f : V) :
    energy W (b • R f) ≤ 4*energy W f := by
  have hr := KFCausalQuasiDissipativeResolvent.resolvent_energy W hW hp f (R f) (b • R f-f)
    b ω (by linarith) (by abel) (hq _ _ (hR f))
  have hs : b^2 ≤ 4*(b-ω)^2 := by nlinarith only [hhalf,hω,hb]
  have hm := mul_le_mul_of_nonneg_right hs (hp (R f))
  rw [energy_real_smul]
  nlinarith only [hr,hm]

theorem approximation_on_graph (T : V →ₗ.[ℂ] V) (R A : V →L[ℂ] V) (b : ℝ)
    (hA : A = b • (b • R-1))
    (hl : ∀ x y, (x,y) ∈ T.graph → R (b • x-y) = x)
    (x y : V) (hxy : (x,y) ∈ T.graph) : A x = b • R y := by
  have he := hl x y hxy
  rw [map_sub,ContinuousLinearMap.map_smul_of_tower] at he
  have he' : b • R x-x = R y :=
    sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp he).trans (add_comm _ _))
  simpa only [hA,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply] using congrArg (fun v : V => b • v) he'

theorem smoothed_graph (T : V →ₗ.[ℂ] V) (R A : V →L[ℂ] V) (b : ℝ)
    (hA : A = b • (b • R-1)) (hR : ∀ f, (R f,b • R f-f) ∈ T.graph) (f : V) :
    (b • R f,A f) ∈ T.graph := by
  have he := T.graph.smul_mem (b:ℂ) (hR f)
  simpa only [hA,Prod.smul_mk,Complex.coe_smul,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply] using he

theorem smoothed_error (R A : V →L[ℂ] V) (b : ℝ) (hb : b ≠ 0)
    (hA : A = b • (b • R-1)) (f : V) : b • R f-f = (1/b) • A f := by
  simp only [hA,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply,smul_smul,one_div,inv_mul_cancel₀ hb,one_smul]

theorem velocity_energy (T : V →ₗ.[ℂ] V) (W R A : V →L[ℂ] V) (b ω : ℝ)
    (hW : W.toLinearMap.IsSymmetric) (hp : ∀ x, 0 ≤ energy W x)
    (hb : 0 < b) (hω : 0 ≤ ω) (hhalf : 2*ω ≤ b)
    (hA : A = b • (b • R-1)) (hR : ∀ f, (R f,b • R f-f) ∈ T.graph)
    (hl : ∀ x y, (x,y) ∈ T.graph → R (b • x-y) = x)
    (hq : ∀ x y, (x,y) ∈ T.graph → (inner ℂ x (W y)).re ≤ ω*energy W x)
    (x y : V) (hxy : (x,y) ∈ T.graph) : energy W (A x) ≤ 4*energy W y := by
  rw [approximation_on_graph T R A b hA hl x y hxy]
  exact scaled_energy T W R b ω hW hp hb hω hhalf hR hq y

theorem energy_transfer (W F S : V →L[ℂ] V) (x y : V) (C : ℝ)
    (hx : energy W x = energy F (S x)) (hy : energy W y = energy F (S y))
    (hb : energy W x ≤ C*energy W y) : energy F (S x) ≤ C*energy F (S y) := by
  simpa only [hx,hy] using hb

#print axioms scaled_energy
#print axioms approximation_on_graph
#print axioms smoothed_graph
#print axioms smoothed_error
#print axioms velocity_energy
#print axioms energy_transfer
end
end UnifiedTheory.Audit.KFCausalQuasiResolventVelocity
