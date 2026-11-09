/- A unitary physical group preserving the actual form Hamiltonian lifts
to its complete energy form. Density is used in the form norm. -/
import UnifiedTheory.Audit.KFCausalFormHamiltonian
import UnifiedTheory.Audit.KFCausalDenseUnitaryExtension

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalUnitaryFormLift
noncomputable section
open KFCausalFormHamiltonian KFCausalDenseUnitaryExtension
variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure Data (J : V →L[ℂ] H) (hi : Function.Injective J) (hd : DenseRange J) where
  physical : ℝ → H ≃ₗᵢ[ℂ] H
  initial : ∀ x, physical 0 x=x
  compose : ∀ s t x, physical (s+t) x=physical t (physical s x)
  continuous : ∀ x, Continuous (fun t => physical t x)
  domainMap : ℝ → (hamiltonian J hi hd).domain → (hamiltonian J hi hd).domain
  domain_coe : ∀ t x, (domainMap t x : H)=physical t (x:H)
  intertwine : ∀ t x, hamiltonian J hi hd (domainMap t x)=physical t (hamiltonian J hi hd x)

variable (J : V →L[ℂ] H) (hi : Function.Injective J) (hd : DenseRange J)
  (D : Data J hi hd)
local notation "T" => hamiltonian J hi hd
local notation "L" => formLift J hi hd

def liftLinear : (T).domain →ₗ[ℂ] V :=
  J.adjoint.toLinearMap.comp ((T).toFun+(T).domain.subtype)

theorem lift_dense : DenseRange (liftLinear J hi hd) := operator_domain_form_dense J hi hd

def domainEquiv (t : ℝ) : (T).domain ≃ₗ[ℂ] (T).domain where
  toFun := D.domainMap t
  invFun := D.domainMap (-t)
  map_add' := by
    intro x y
    apply Subtype.ext
    simp only [D.domain_coe,Submodule.coe_add,map_add]
  map_smul' := by
    intro c x
    apply Subtype.ext
    simp only [D.domain_coe,Submodule.coe_smul,map_smul,RingHom.id_apply]
  left_inv := by
    intro x
    apply Subtype.ext
    simp only [D.domain_coe,← D.compose,add_neg_cancel,D.initial]
  right_inv := by
    intro x
    apply Subtype.ext
    simp only [D.domain_coe,← D.compose,neg_add_cancel,D.initial]

theorem lift_norm_identity (x : (T).domain) :
    ‖L x‖^2=‖(x:H)‖^2+(inner ℂ (T x) (x:H)).re := by
  have hp := congrArg Complex.re (hamiltonian_form_pairing J hi hd x (L x))
  have h₁ : (inner ℂ (L x) (L x)).re=‖L x‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  have h₂ : (inner ℂ (x:H) (x:H)).re=‖(x:H)‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [embedding_formLift,Complex.sub_re,h₁,h₂] at hp
  linarith only [hp]

theorem lift_norm_preserved (t : ℝ) (x : (T).domain) :
    ‖liftLinear J hi hd (domainEquiv J hi hd D t x)‖=‖liftLinear J hi hd x‖ := by
  have he : ‖L (D.domainMap t x)‖^2=‖L x‖^2 := by
    rw [lift_norm_identity,lift_norm_identity,D.domain_coe,D.intertwine,
      (D.physical t).norm_map,(D.physical t).inner_map_map]
  change ‖L (D.domainMap t x)‖=‖L x‖
  nlinarith only [he,norm_nonneg (L (D.domainMap t x)),norm_nonneg (L x)]

def evolution (t : ℝ) : V ≃ₗᵢ[ℂ] V :=
  extension (liftLinear J hi hd) (lift_dense J hi hd) (domainEquiv J hi hd D t)
    (lift_norm_preserved J hi hd D t)

theorem evolution_lift (t : ℝ) (x : (T).domain) :
    evolution J hi hd D t (L x)=L (D.domainMap t x) :=
  extension_embedding (liftLinear J hi hd) (lift_dense J hi hd)
    (domainEquiv J hi hd D t) (lift_norm_preserved J hi hd D t) x

theorem evolution_embedding (t : ℝ) (v : V) :
    J (evolution J hi hd D t v)=D.physical t (J v) := by
  have he : (fun w => J (evolution J hi hd D t w))=(fun w => D.physical t (J w)) := by
    apply (lift_dense J hi hd).equalizer
      (J.continuous.comp (evolution J hi hd D t).continuous)
      ((D.physical t).continuous.comp J.continuous)
    funext x
    change J (evolution J hi hd D t (L x))=D.physical t (J (L x))
    rw [evolution_lift,embedding_formLift,embedding_formLift,D.domain_coe]
  exact congrFun he v

theorem evolution_initial (v : V) : evolution J hi hd D 0 v=v := by
  apply hi
  rw [evolution_embedding,D.initial]

theorem evolution_compose (s t : ℝ) (v : V) :
    evolution J hi hd D (s+t) v=evolution J hi hd D t (evolution J hi hd D s v) := by
  apply hi
  rw [evolution_embedding,evolution_embedding,evolution_embedding,D.compose]

theorem evolution_norm (t : ℝ) (v : V) : ‖evolution J hi hd D t v‖=‖v‖ :=
  (evolution J hi hd D t).norm_map v

theorem evolution_continuous (v : V) : Continuous (fun t => evolution J hi hd D t v) := by
  apply extension_strong_continuous (liftLinear J hi hd) (lift_dense J hi hd)
    (domainEquiv J hi hd D) (lift_norm_preserved J hi hd D) _ v
  intro x
  change Continuous (fun t => L (D.domainMap t x))
  have he : (fun t => L (D.domainMap t x))=
      (fun t => J.adjoint (D.physical t (T x)+D.physical t (x:H))) := by
    funext t
    simp only [formLift,D.intertwine,D.domain_coe]
  rw [he]
  exact J.adjoint.continuous.comp ((D.continuous (T x)).add (D.continuous (x:H)))

theorem energy_preserved (t : ℝ) (v : V) :
    ‖evolution J hi hd D t v‖^2-‖J (evolution J hi hd D t v)‖^2=‖v‖^2-‖J v‖^2 := by
  rw [evolution_norm,evolution_embedding,(D.physical t).norm_map]

#print axioms lift_dense
#print axioms lift_norm_identity
#print axioms lift_norm_preserved
#print axioms evolution_lift
#print axioms evolution_embedding
#print axioms evolution_initial
#print axioms evolution_compose
#print axioms evolution_norm
#print axioms evolution_continuous
#print axioms energy_preserved
end
end UnifiedTheory.Audit.KFCausalUnitaryFormLift
