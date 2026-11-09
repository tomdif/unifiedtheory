/- Lifted-domain propagation yields a bounded physical Hamiltonian output
after the initial resolvent, through the physical adjoint and closed graph. -/
import UnifiedTheory.Audit.KFCausalClosedGraphLift
import UnifiedTheory.Audit.KFCausalEmbeddedGraphExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalLiftedToPhysicalDomain
noncomputable section
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace V] in
theorem mass_shift (M Q : V →L[ℂ] V) (a : ℝ) (x y : V) (hQ : Q x = M y) :
    M (a • x+y) = a • M x+Q x := by
  rw [map_add,ContinuousLinearMap.map_smul_of_tower,hQ]

omit [CompleteSpace V] in
theorem inverse_pairing (A P : V →L[ℂ] V) (hAP : ∀ x, A (P x) = x)
    (hA : ∀ x y, inner ℂ (A x) y = inner ℂ x (A y)) :
    ∀ x y, inner ℂ (P x) y = inner ℂ x (P y) := by
  intro x y
  calc
    inner ℂ (P x) y = inner ℂ (P x) (A (P y)) := by rw [hAP]
    _ = inner ℂ (A (P x)) (P y) := (hA (P x) (P y)).symm
    _ = inner ℂ x (P y) := by rw [hAP]

theorem exists_graph_evolution (J : V →L[ℂ] H) (hJi : Function.Injective J) (hJd : DenseRange J)
    (M A₀ A₁ P : V →L[ℂ] V) (L₀ L₁ : V →ₗ.[ℂ] V)
    (T : H →ₗ.[ℂ] H) (U R : H →L[ℂ] H) (f : V →ₗ[ℂ] V) (a : ℝ)
    (hM : ∀ x y, inner ℂ (M x) y = inner ℂ (J x) (J y))
    (hA₀ : ∀ x y, inner ℂ (A₀ x) y = inner ℂ x (A₀ y))
    (hA₁ : ∀ x y, inner ℂ (A₁ x) y = inner ℂ x (A₁ y))
    (hAP : ∀ x, A₀ (P x) = x)
    (hLi : L₁.IsClosed) (hT : T.IsClosed)
    (hshift : ∀ x y, (x,y) ∈ L₁.graph → M (a • x+y) = A₁ x)
    (hphysical : ∀ x y, (x,y) ∈ L₁.graph → (J x,J y) ∈ T.graph)
    (hinit : ∀ v, P (M v) ∈ L₀.domain)
    (hprop : ∀ x : L₀.domain, f x ∈ L₁.domain)
    (he : ∀ x, J (f x) = U (J x))
    (hR : ∀ v, R (J v) = J (P (M v))) :
    ∃ E : H →L[ℂ] H, ∀ v, (U (R v),E v) ∈ T.graph := by
  obtain ⟨F,hF⟩ := KFCausalClosedGraphLift.exists_bounded_lift J hJi U f he
  let K := F.comp (P.comp M)
  have hK (v : V) : K v ∈ L₁.domain := by
    change F (P (M v)) ∈ L₁.domain
    rw [hF]
    exact hprop ⟨P (M v),hinit v⟩
  obtain ⟨B,hB⟩ := KFCausalClosedGraphLift.closed_action L₁ hLi K hK
  let W : V →L[ℂ] V := a • K+B
  let S : V →L[ℂ] V := P.comp (F.adjoint.comp A₁)
  have hMW (v : V) : M (W v) = A₁ (K v) := hshift (K v) (B v) (hB v)
  have hP := inverse_pairing A₀ P hAP hA₀
  have hpair (v w : V) : inner ℂ (J (W v)) (J w) = inner ℂ (J v) (J (S w)) := by
    calc
      inner ℂ (J (W v)) (J w) = inner ℂ (M (W v)) w := (hM (W v) w).symm
      _ = inner ℂ (A₁ (K v)) w := by rw [hMW]
      _ = inner ℂ (K v) (A₁ w) := hA₁ _ _
      _ = inner ℂ (P (M v)) (F.adjoint (A₁ w)) := (F.adjoint_inner_right _ _).symm
      _ = inner ℂ (M v) (S w) := hP _ _
      _ = inner ℂ (J v) (J (S w)) := hM _ _
  obtain ⟨E,hE⟩ := KFCausalEmbeddedGraphExtension.exists_extension J hJd W S hpair
  let D : H →L[ℂ] H := E-a • U.comp R
  have hstate (v : V) : U (R (J v)) = J (K v) := by
    rw [hR,← he,← hF]
    rfl
  have hg (v : V) : (U (R (J v)),D (J v)) ∈ T.graph := by
    change (U (R (J v)),E (J v)-a • U (R (J v))) ∈ T.graph
    rw [hstate,hE]
    have hout : J (W v)-a • J (K v) = J (B v) := by
      change J (a • K v+B v)-a • J (K v) = J (B v)
      rw [map_add,ContinuousLinearMap.map_smul_of_tower]
      abel
    rw [hout]
    exact hphysical _ _ (hB v)
  exact ⟨D,KFCausalEmbeddedGraphExtension.closed_graph_extension J hJd T hT (U.comp R) D hg⟩

#print axioms mass_shift
#print axioms inverse_pairing
#print axioms exists_graph_evolution
end
end UnifiedTheory.Audit.KFCausalLiftedToPhysicalDomain
